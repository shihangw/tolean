/** The frame around the editor: the top bar, the panel divider and the status bar. */
import { type KeyboardEvent, type PointerEvent, useRef } from 'react';

import type { EngineState } from './checker.ts';
import type { Cursor } from './editor/Editor.tsx';
import { type Language, indentFor, languageNames } from './editor/languages.ts';
import { Icon, Mark } from './icons.tsx';
import type { Theme } from './prefs.ts';
import type { Workspace } from './workspace.ts';

const repository = 'https://github.com/shihangw/tolean';

/** The key that CodeMirror calls Mod: Command on Apple systems, Control elsewhere. */
const mod = /Mac|iPhone|iPad/.test(navigator.platform) ? '⌘' : 'Ctrl+';

interface TopbarProps {
  readonly workspaces: readonly Workspace[];
  readonly current: string | null;
  readonly keyOf: (w: Workspace) => string;
  readonly theme: Theme;
  readonly note: string | null;
  readonly onSelect: (key: string) => void;
  readonly onNew: () => void;
  readonly onShare: () => void;
  readonly onTheme: () => void;
}

export function Topbar(props: TopbarProps) {
  const { workspaces, current, keyOf } = props;
  const group = (kind: Workspace['kind']) =>
    workspaces
      .filter((w) => w.kind === kind)
      .map((w) => (
        <option key={keyOf(w)} value={keyOf(w)}>
          {w.name}
        </option>
      ));
  return (
    <header className="topbar">
      <a className="brand" href={repository} title="Tolean on GitHub">
        <Mark />
        <span className="brand-name">Tolean</span>
        <span className="brand-sub">Playground</span>
      </a>
      <span className="divider-v" />
      <label className="picker">
        <span className="visually-hidden">Workspace</span>
        <select value={current ?? ''} onChange={(e) => props.onSelect(e.target.value)}>
          <optgroup label="Examples">{group('example')}</optgroup>
          {workspaces.some((w) => w.kind === 'user') && <optgroup label="Your workspaces">{group('user')}</optgroup>}
        </select>
        <Icon name="chevron" size={14} className="picker-chevron" />
      </label>
      <button type="button" className="btn ghost" onClick={props.onNew}>
        <Icon name="plus" />
        <span className="wide-only">New workspace</span>
      </button>
      <span className="grow" />
      {props.note != null && (
        <span className="toast" role="status">
          <Icon name="check" size={14} />
          {props.note}
        </span>
      )}
      <button type="button" className="btn" onClick={props.onShare} title="Copy a link that holds this workspace">
        <Icon name="share" />
        <span className="wide-only">Share</span>
      </button>
      <button
        type="button"
        className="btn ghost icon-only"
        onClick={props.onTheme}
        title={props.theme === 'dark' ? 'Use the light theme' : 'Use the dark theme'}
        aria-label={props.theme === 'dark' ? 'Use the light theme' : 'Use the dark theme'}
      >
        <Icon name={props.theme === 'dark' ? 'sun' : 'moon'} />
      </button>
      <a className="btn ghost icon-only" href={`${repository}#readme`} title="Read the documentation" aria-label="Documentation">
        <Icon name="book" />
      </a>
      <a className="btn ghost icon-only" href={repository} title="Tolean on GitHub" aria-label="GitHub">
        <Icon name="github" />
      </a>
    </header>
  );
}

/** The handle between the editor and the claims panel. Drag it, or focus it and use the arrow keys. */
export function Divider({ width, onWidth }: { width: number; onWidth: (w: number) => void }) {
  const start = useRef<{ x: number; width: number } | null>(null);
  const down = (e: PointerEvent<HTMLDivElement>) => {
    e.currentTarget.setPointerCapture(e.pointerId);
    start.current = { x: e.clientX, width };
  };
  const move = (e: PointerEvent<HTMLDivElement>) => {
    if (start.current != null) onWidth(start.current.width + start.current.x - e.clientX);
  };
  const up = () => {
    start.current = null;
  };
  const key = (e: KeyboardEvent<HTMLDivElement>) => {
    if (e.key === 'ArrowLeft') onWidth(width + 24);
    else if (e.key === 'ArrowRight') onWidth(width - 24);
    else return;
    e.preventDefault();
  };
  return (
    <div
      className="split"
      role="separator"
      aria-orientation="vertical"
      aria-label="Resize the claims panel"
      aria-valuenow={width}
      tabIndex={0}
      onPointerDown={down}
      onPointerMove={move}
      onPointerUp={up}
      onPointerCancel={up}
      onKeyDown={key}
    />
  );
}

/** What the translator did with the latest edit. */
export type TranslatorState =
  | { readonly kind: 'loading' }
  | { readonly kind: 'unavailable' }
  | { readonly kind: 'translated'; readonly ms: number }
  | { readonly kind: 'refused'; readonly errors: number };

interface StatusProps {
  readonly translator: TranslatorState;
  readonly engine: EngineState;
  readonly checking: boolean;
  readonly language: Language | null;
  readonly cursor: Cursor | null;
  readonly saved: boolean;
}

function TranslatorStatus({ state }: { state: TranslatorState }) {
  switch (state.kind) {
    case 'loading':
      return (
        <span className="status-item">
          <span className="spinner" /> Loading the translator
        </span>
      );
    case 'unavailable':
      return <span className="status-item err">Translator unavailable</span>;
    case 'translated':
      return (
        <span className="status-item ok">
          <Icon name="check" size={12} /> Translated in {state.ms < 1 ? '<1' : state.ms.toFixed(0)} ms
        </span>
      );
    case 'refused':
      return (
        <span className="status-item err">
          <Icon name="x" size={12} /> Tolean refused the source ({state.errors})
        </span>
      );
    default: {
      const never: never = state;
      return never;
    }
  }
}

function LeanStatus({ engine, checking }: { engine: EngineState; checking: boolean }) {
  switch (engine.kind) {
    case 'off':
      return <span className="status-item">{checking ? 'Lean starting' : `Lean off · ${mod}Enter checks the proofs`}</span>;
    case 'loading':
      return (
        <span className="status-item">
          <span className="spinner" /> Downloading Lean
        </span>
      );
    case 'ready':
      return <span className="status-item ok">Lean ready</span>;
    case 'failed':
      return <span className="status-item err">Lean failed</span>;
    default: {
      const never: never = engine;
      return never;
    }
  }
}

export function StatusBar({ translator, engine, checking, language, cursor, saved }: StatusProps) {
  return (
    <footer className="statusbar">
      <TranslatorStatus state={translator} />
      <LeanStatus engine={engine} checking={checking} />
      <span className="grow" />
      {cursor != null && (
        <span className="status-item mono">
          Ln {cursor.line}, Col {cursor.column}
          {cursor.selected > 0 && ` (${cursor.selected} selected)`}
        </span>
      )}
      {language != null && (
        <>
          <span className="status-item">{indentFor(language) === '\t' ? 'Tabs' : 'Spaces: 2'}</span>
          <span className="status-item">{languageNames[language]}</span>
        </>
      )}
      <span className="status-item">{saved ? 'Saved in this browser' : 'Example · edits make a copy'}</span>
    </footer>
  );
}
