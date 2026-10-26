/**
 * The editor's look. Every colour is a CSS variable from styles.css, so the
 * light and dark themes switch without a new editor. Syntax colours come
 * from the `tok-*` classes that `classHighlighter` writes, and styles.css
 * colours them, so code outside an editor can use the same classes.
 */
import { syntaxHighlighting } from '@codemirror/language';
import { type Extension } from '@codemirror/state';
import { EditorView } from '@codemirror/view';
import { classHighlighter } from '@lezer/highlight';

const chrome = EditorView.theme({
  '&': { height: '100%', color: 'var(--text)', backgroundColor: 'var(--surface)', fontSize: '13px' },
  '&.cm-focused': { outline: 'none' },
  '.cm-scroller': { fontFamily: 'var(--font-code)', lineHeight: '1.65' },
  '.cm-content': { padding: '12px 0 30vh', caretColor: 'var(--accent)' },
  '.cm-line': { padding: '0 16px 0 8px' },
  '.cm-cursor, .cm-dropCursor': { borderLeft: '2px solid var(--accent)' },
  '&.cm-focused > .cm-scroller > .cm-selectionLayer .cm-selectionBackground, .cm-selectionBackground, .cm-content ::selection':
    { backgroundColor: 'var(--selection)' },
  '.cm-activeLine': { backgroundColor: 'var(--active-line)' },
  '.cm-gutters': { backgroundColor: 'var(--surface)', color: 'var(--faint)', border: 'none' },
  '.cm-lineNumbers .cm-gutterElement': { padding: '0 6px 0 16px', minWidth: '48px', fontSize: '11.5px' },
  '.cm-activeLineGutter': { backgroundColor: 'transparent', color: 'var(--text-2)' },
  '.cm-foldGutter .cm-gutterElement': { padding: '0 4px', color: 'var(--faint)', cursor: 'pointer' },
  '.cm-foldGutter .cm-gutterElement:hover': { color: 'var(--text)' },
  '.cm-foldPlaceholder': {
    backgroundColor: 'var(--surface-2)',
    border: '1px solid var(--border)',
    color: 'var(--muted)',
    borderRadius: '4px',
    padding: '0 6px',
    margin: '0 4px',
  },
  '.cm-matchingBracket': { backgroundColor: 'var(--accent-soft)', outline: '1px solid var(--accent-line)' },
  '.cm-nonmatchingBracket': { backgroundColor: 'var(--err-soft)' },
  '.cm-selectionMatch': { backgroundColor: 'var(--accent-soft)' },
  '.cm-searchMatch': { backgroundColor: 'var(--warn-soft)', outline: '1px solid var(--warn)' },
  '.cm-searchMatch.cm-searchMatch-selected': { backgroundColor: 'var(--warn-line)' },
  '.cm-panels': { backgroundColor: 'var(--surface-2)', color: 'var(--text)' },
  '.cm-panels.cm-panels-bottom': { borderTop: '1px solid var(--border)' },
  '.cm-panels.cm-panels-top': { borderBottom: '1px solid var(--border)' },
  '.cm-panel.cm-search': { padding: '6px 10px', fontFamily: 'var(--font-ui)', fontSize: '12.5px' },
  '.cm-panel.cm-search input, .cm-panel.cm-search button': { fontFamily: 'var(--font-ui)', fontSize: '12.5px' },
  '.cm-textfield': {
    backgroundColor: 'var(--surface)',
    border: '1px solid var(--border-strong)',
    borderRadius: '6px',
    padding: '3px 7px',
  },
  '.cm-button': {
    backgroundImage: 'none',
    backgroundColor: 'var(--surface)',
    border: '1px solid var(--border-strong)',
    borderRadius: '6px',
    padding: '3px 9px',
  },
  '.cm-tooltip': {
    backgroundColor: 'var(--surface)',
    color: 'var(--text)',
    border: '1px solid var(--border-strong)',
    borderRadius: '8px',
    boxShadow: 'var(--shadow-pop)',
    overflow: 'hidden',
  },
  '.cm-tooltip.cm-tooltip-autocomplete > ul': { fontFamily: 'var(--font-code)', fontSize: '12.5px', maxHeight: '16em' },
  '.cm-tooltip.cm-tooltip-autocomplete > ul > li': { padding: '2px 10px 2px 6px', lineHeight: '1.6' },
  '.cm-tooltip-autocomplete ul li[aria-selected]': { backgroundColor: 'var(--accent)', color: 'var(--on-accent)' },
  '.cm-completionDetail': { color: 'var(--muted)', fontStyle: 'normal', marginLeft: '8px' },
  '.cm-tooltip-autocomplete ul li[aria-selected] .cm-completionDetail': { color: 'inherit', opacity: '0.8' },
  '.cm-completionMatchedText': { textDecoration: 'none', fontWeight: '650' },
  '.cm-diagnostic': {
    fontFamily: 'var(--font-ui)',
    fontSize: '12.5px',
    padding: '6px 10px 6px 12px',
    whiteSpace: 'pre-wrap',
    maxWidth: 'min(560px, 80vw)',
  },
  '.cm-diagnostic-error': { borderLeft: '3px solid var(--err)' },
  '.cm-diagnostic-warning': { borderLeft: '3px solid var(--warn)' },
  '.cm-diagnostic-info': { borderLeft: '3px solid var(--info)' },
  '.cm-lintRange-error': { backgroundImage: 'none', textDecoration: 'underline wavy var(--err)', textUnderlineOffset: '3px' },
  '.cm-lintRange-warning': { backgroundImage: 'none', textDecoration: 'underline wavy var(--warn)', textUnderlineOffset: '3px' },
  '.cm-lintRange-info': { backgroundImage: 'none', textDecoration: 'underline dotted var(--info)', textUnderlineOffset: '3px' },
  '.cm-gutter-lint': { width: '14px' },
  '.cm-gutter-lint .cm-gutterElement': { padding: '0 0 0 4px' },
});

export const editorTheme: Extension = [chrome, syntaxHighlighting(classHighlighter)];
