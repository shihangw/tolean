import {
  autocompletion,
  closeBrackets,
  closeBracketsKeymap,
  completionKeymap,
} from '@codemirror/autocomplete';
import { defaultKeymap, history, historyKeymap, indentWithTab } from '@codemirror/commands';
import { bracketMatching, foldGutter, foldKeymap, indentOnInput, indentUnit } from '@codemirror/language';
import { type Diagnostic, lintGutter, lintKeymap, setDiagnostics } from '@codemirror/lint';
import { highlightSelectionMatches, searchKeymap } from '@codemirror/search';
import { Annotation, type EditorState as State, EditorState, type Extension, type StateEffect, type Text } from '@codemirror/state';
import {
  EditorView,
  crosshairCursor,
  drawSelection,
  dropCursor,
  highlightActiveLine,
  highlightActiveLineGutter,
  highlightSpecialChars,
  keymap,
  lineNumbers,
  rectangularSelection,
} from '@codemirror/view';
import { useLayoutEffect, useRef } from 'react';

import type { FileDiagnostic } from '../diagnostics.ts';
import { indentFor, languageOf, languageSupport } from './languages.ts';
import { editorTheme } from './theme.ts';

/** Where the cursor is, for the status bar. Lines and columns count from 1. */
export interface Cursor {
  readonly line: number;
  readonly column: number;
  /** How many characters the selection covers. */
  readonly selected: number;
}

/** A request to show a line of a file, such as the line of a theorem. */
export interface Reveal {
  readonly path: string;
  readonly line: number;
  /** A new number asks again for the same line. */
  readonly nonce: number;
}

interface Callbacks {
  onChange(path: string, text: string): void;
  onCursor(cursor: Cursor): void;
  onCheckNow(): void;
}

interface Props extends Callbacks {
  /** A new session forgets every file's undo history, as when another workspace opens. */
  readonly session: string;
  readonly path: string;
  readonly text: string;
  readonly readOnly: boolean;
  readonly diagnostics: readonly FileDiagnostic[];
  readonly reveal: Reveal | null;
}

/** Marks a change that came from the page, not from the person typing. */
const fromPage = Annotation.define<true>();

function chevron(open: boolean): HTMLElement {
  const span = document.createElement('span');
  span.className = open ? 'fold-marker open' : 'fold-marker';
  span.innerHTML =
    '<svg viewBox="0 0 16 16" width="12" height="12" fill="none" stroke="currentColor" stroke-width="1.6" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="m4.5 6.5 3.5 3.5 3.5-3.5"/></svg>';
  return span;
}

function cursorOf(state: State): Cursor {
  const range = state.selection.main;
  const line = state.doc.lineAt(range.head);
  return { line: line.number, column: range.head - line.from + 1, selected: Math.abs(range.to - range.from) };
}

function extensions(path: string, readOnly: boolean, callbacks: { readonly current: Callbacks }): Extension[] {
  const language = languageOf(path);
  return [
    lineNumbers(),
    foldGutter({ markerDOM: chevron }),
    lintGutter(),
    highlightActiveLineGutter(),
    highlightSpecialChars(),
    history(),
    drawSelection(),
    dropCursor(),
    EditorState.allowMultipleSelections.of(true),
    indentOnInput(),
    bracketMatching(),
    closeBrackets(),
    autocompletion({ icons: false }),
    rectangularSelection(),
    crosshairCursor(),
    highlightActiveLine(),
    highlightSelectionMatches(),
    keymap.of([
      {
        key: 'Mod-Enter',
        run: () => {
          callbacks.current.onCheckNow();
          return true;
        },
      },
      // The page saves every edit already, so the browser's own save dialog would only get in the way.
      { key: 'Mod-s', run: () => true, preventDefault: true },
      ...closeBracketsKeymap,
      ...defaultKeymap,
      ...searchKeymap,
      ...historyKeymap,
      ...foldKeymap,
      ...completionKeymap,
      ...lintKeymap,
      indentWithTab,
    ]),
    editorTheme,
    languageSupport(language),
    indentUnit.of(indentFor(language)),
    EditorState.tabSize.of(language === 'go' ? 4 : 2),
    EditorState.readOnly.of(readOnly),
    EditorView.contentAttributes.of({ 'aria-label': `${path}${readOnly ? ', read-only' : ''}` }),
    EditorView.updateListener.of((u) => {
      if (u.docChanged && !u.transactions.some((tr) => tr.annotation(fromPage) === true)) {
        callbacks.current.onChange(path, u.state.doc.toString());
      }
      if (u.docChanged || u.selectionSet || u.focusChanged) callbacks.current.onCursor(cursorOf(u.state));
    }),
  ];
}

/** The offset of a column, counted in code points as Lean does, within a line. */
function offsetIn(doc: Text, line: number, column: number): number {
  const l = doc.line(Math.min(Math.max(line, 1), doc.lines));
  let offset = 0;
  let points = 0;
  for (const ch of l.text) {
    if (points >= column) break;
    offset += ch.length;
    points++;
  }
  return l.from + offset;
}

function toEditor(doc: Text, d: FileDiagnostic): Diagnostic {
  const from = offsetIn(doc, d.line, d.column);
  let to = d.end == null ? from : offsetIn(doc, d.end.line, d.end.column);
  if (to <= from) {
    // Without an end, underline the word at the start, or one character.
    const rest = doc.sliceString(from, doc.lineAt(from).to);
    to = from + Math.max(1, /^[^\s()[\]{},;]*/.exec(rest)![0].length);
  }
  return {
    from,
    to: Math.min(to, doc.length),
    severity: d.severity,
    source: d.source === 'lean' ? 'Lean' : 'Tolean',
    message: d.message,
  };
}

/** The smallest change that turns one text into another, so the view does not jump. */
function difference(from: string, to: string): { from: number; to: number; insert: string } {
  let start = 0;
  while (start < from.length && start < to.length && from[start] === to[start]) start++;
  let end = 0;
  while (end < from.length - start && end < to.length - start && from[from.length - 1 - end] === to[to.length - 1 - end]) end++;
  return { from: start, to: from.length - end, insert: to.slice(start, to.length - end) };
}

/**
 * One CodeMirror view for every file of a workspace. Each file keeps its own
 * editor state, so undo history, the cursor and the scroll position survive a
 * switch to another file and back.
 */
export function Editor(props: Props) {
  const { session, path, text, readOnly, diagnostics, reveal } = props;
  const host = useRef<HTMLDivElement>(null);
  const view = useRef<EditorView | null>(null);
  const callbacks = useRef<Callbacks>(props);
  callbacks.current = props;
  const saved = useRef(new Map<string, { state: State; scroll: StateEffect<unknown> }>());
  const shown = useRef<{ session: string; path: string } | null>(null);

  useLayoutEffect(() => {
    view.current = new EditorView({ parent: host.current! });
    return () => {
      view.current?.destroy();
      view.current = null;
      shown.current = null;
    };
  }, []);

  // Show the file: its saved state, or a new one.
  useLayoutEffect(() => {
    const v = view.current!;
    const before = shown.current;
    if (before != null && before.session === session) {
      saved.current.set(before.path, { state: v.state, scroll: v.scrollSnapshot() });
    } else {
      saved.current.clear();
    }
    const kept = saved.current.get(path);
    v.setState(kept?.state ?? EditorState.create({ doc: text, extensions: extensions(path, readOnly, callbacks) }));
    if (kept != null) v.dispatch({ effects: kept.scroll });
    shown.current = { session, path };
    callbacks.current.onCursor(cursorOf(v.state));
    // The text is read below; the state for a path is made once per session.
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [session, path]);

  // Follow a text that changed under the editor, such as generated Lean.
  useLayoutEffect(() => {
    const v = view.current!;
    const current = v.state.doc.toString();
    if (current !== text) v.dispatch({ changes: difference(current, text), annotations: fromPage.of(true) });
  }, [session, path, text]);

  // Between two checks, CodeMirror moves the underlines along with the edits.
  useLayoutEffect(() => {
    const v = view.current!;
    v.dispatch(setDiagnostics(v.state, diagnostics.map((d) => toEditor(v.state.doc, d))));
  }, [session, path, diagnostics]);

  // Each request shows its line once, so a return to the file later does not jump.
  const revealed = useRef<number | null>(null);
  useLayoutEffect(() => {
    const v = view.current!;
    if (reveal == null || reveal.path !== path || revealed.current === reveal.nonce) return;
    revealed.current = reveal.nonce;
    const line = v.state.doc.line(Math.min(Math.max(reveal.line, 1), v.state.doc.lines));
    v.dispatch({ selection: { anchor: line.from }, effects: EditorView.scrollIntoView(line.from, { y: 'center' }) });
    v.focus();
  }, [reveal, path]);

  return <div className="editor" ref={host} />;
}
