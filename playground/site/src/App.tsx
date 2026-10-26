import { useEffect, useMemo, useRef, useState } from 'react';

import { Claims } from './Claims.tsx';
import { type ClaimStatus, type EngineState, LeanChecker, statuses as readStatuses } from './checker.ts';
import { Editor } from './Editor.tsx';
import { shareLink, sharedFromLocation } from './share.ts';
import { type Translation, loadTranslator } from './translator.ts';
import { type WorkspaceFile, bundle, claims as readClaims, isProof, isSpec, proofDeclarations } from './lean.ts';
import {
  type ExampleData,
  type Workspace,
  isGenerated,
  loadUserWorkspaces,
  newWorkspaceFiles,
  saveUserWorkspaces,
} from './workspace.ts';

declare const __BUILD_ID__: string;

/** How long the page waits after an edit before it checks again. */
const checkDelayMs = 400;

function engineNotice(state: EngineState): string {
  switch (state.kind) {
    case 'loading':
      return 'Loading Lean (about 130 MB the first time; the browser keeps it after that)…';
    case 'ready':
      return 'Lean runs in your browser and checks the proofs as you edit. It is an unofficial WebAssembly build of a newer Lean than CI uses; CI checks the same proofs with the pinned Lean.';
    case 'failed':
      return `Lean could not run in this browser: ${state.message}`;
    default: {
      const never: never = state;
      return never;
    }
  }
}

/** A short hash of a text, to tell versions of a generated file apart. */
function hashText(text: string): string {
  let h = 0;
  for (let i = 0; i < text.length; i++) h = (Math.imul(h, 31) + text.charCodeAt(i)) | 0;
  return (h >>> 0).toString(36);
}

const keyOf = (w: Workspace) => (w.kind === 'example' ? `example:${w.name}` : `user:${w.id}`);

/** The folders of a workspace, in the order the file tree shows them. */
const folders = ['src', 'theorems'] as const;

export function App() {
  const [data, setData] = useState<ExampleData | null>(null);
  const [workspaces, setWorkspaces] = useState<Workspace[]>([]);
  const [currentKey, setCurrentKey] = useState<string | null>(null);
  const [openPath, setOpenPath] = useState<string | null>(null);
  const [statuses, setStatuses] = useState<ReadonlyMap<string, ClaimStatus>>(new Map());

  useEffect(() => {
    void fetch('./examples.json')
      .then((r) => r.json() as Promise<ExampleData>)
      .then(async (d) => {
        const examples: Workspace[] = d.examples.map((e) => ({ kind: 'example', ...e }));
        let all = [...examples, ...loadUserWorkspaces()];
        let selected = all[0] ?? null;
        // A share link opens its workspace as the viewer's own copy.
        const shared = await sharedFromLocation();
        if (shared != null) {
          selected = { kind: 'user', id: crypto.randomUUID(), name: shared.name, files: shared.files };
          all = [...all, selected];
          saveUserWorkspaces(all);
          history.replaceState(null, '', location.pathname + location.search);
        }
        setData(d);
        setWorkspaces(all);
        setCurrentKey(selected == null ? null : keyOf(selected));
      });
  }, []);

  const current = workspaces.find((w) => keyOf(w) === currentKey) ?? null;

  // The translator, compiled to WebAssembly. Until it loads, or if it cannot,
  // the page shows the generated Lean that came with the example.
  const [translate, setTranslate] = useState<((f: readonly WorkspaceFile[]) => Translation) | null>(null);
  const [translatorError, setTranslatorError] = useState<string | null>(null);
  useEffect(() => {
    loadTranslator(`./translator`).then(
      (t) => setTranslate(() => t),
      (e: unknown) => setTranslatorError(e instanceof Error ? e.message : String(e)),
    );
  }, []);

  // What the person wrote. Generated files are derived from it.
  const authored = useMemo(() => (current?.files ?? []).filter((f) => !isGenerated(f.path)), [current]);
  const translation = useMemo(
    () => (translate == null || current == null ? null : translate(authored)),
    [translate, current, authored],
  );
  const files = useMemo((): readonly WorkspaceFile[] => {
    if (translation == null || translation.kind === 'error') return current?.files ?? [];
    const generated = translation.units.flatMap((u) => (u.kind === 'ok' ? [{ path: u.output, text: u.lean }] : []));
    return [...authored, ...generated].sort((a, b) => a.path.localeCompare(b.path));
  }, [translation, current, authored]);
  const translationErrors =
    translation == null
      ? []
      : translation.kind === 'error'
        ? [translation.error]
        : translation.units.flatMap((u) => (u.kind === 'error' ? [u.error] : []));
  const open =
    files.find((f) => f.path === openPath) ??
    files.find((f) => f.path.startsWith('src/') && !isGenerated(f.path)) ??
    null;

  const claims = useMemo(() => readClaims(files), [files]);
  const proofs = useMemo(() => proofDeclarations(files), [files]);

  const [engine, setEngine] = useState<EngineState>({ kind: 'loading' });
  const checker = useRef<LeanChecker | null>(null);
  checker.current ??= new LeanChecker('./lean', `./lean-worker.js?v=${__BUILD_ID__}`, setEngine);

  useEffect(() => {
    if (data == null || current == null) return;
    const ordered = [
      ...files.filter((f) => isGenerated(f.path)),
      ...files.filter(isSpec),
      ...files.filter(isProof),
    ];
    const names = claims.map((c) => c.name);
    if (translationErrors.length > 0) {
      const reason = `Tolean could not translate the source: ${translationErrors[0]}`;
      setStatuses(new Map(names.map((n) => [n, { kind: 'broken', reason }])));
      return;
    }
    const b = bundle(data.goSpec, ordered, names);
    let cancelled = false;
    const timer = setTimeout(() => {
      setStatuses(new Map(names.map((n) => [n, { kind: 'checking' }])));
      void checker.current!.check(b.text).then(
        (diagnostics) => {
          if (!cancelled && diagnostics != null) setStatuses(readStatuses(diagnostics, b, names));
        },
        () => {
          if (!cancelled) setStatuses(new Map(names.map((n) => [n, { kind: 'unchecked' }])));
        },
      );
    }, checkDelayMs);
    return () => {
      cancelled = true;
      clearTimeout(timer);
    };
    // translationErrors is derived from translation, which is listed.
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [data, current, files, claims, translation]);

  function updateFile(path: string, text: string) {
    if (current == null) return;
    if (isGenerated(path)) return;
    const files = current.files.map((f): WorkspaceFile => (f.path === path ? { path, text } : f));
    let next: Workspace[];
    if (current.kind === 'example') {
      // The examples stay as they are; editing one makes the viewer's own copy.
      const copy: Workspace = { kind: 'user', id: crypto.randomUUID(), name: `${current.name} (edited)`, files };
      next = [...workspaces, copy];
      setCurrentKey(keyOf(copy));
    } else {
      next = workspaces.map((w) => (w === current ? { ...current, files } : w));
    }
    setWorkspaces(next);
    saveUserWorkspaces(next);
  }

  const [shareNote, setShareNote] = useState<string | null>(null);
  async function share() {
    if (current == null) return;
    const link = await shareLink({ name: current.name, files: authored });
    try {
      await navigator.clipboard.writeText(link);
      setShareNote('Link copied');
    } catch {
      // The clipboard can be blocked; show the link to copy by hand.
      window.prompt('Copy this link', link);
    }
  }

  function newWorkspace() {
    const w: Workspace = {
      kind: 'user',
      id: crypto.randomUUID(),
      name: `Workspace ${workspaces.filter((x) => x.kind === 'user').length + 1}`,
      files: newWorkspaceFiles(),
    };
    const next = [...workspaces, w];
    setWorkspaces(next);
    saveUserWorkspaces(next);
    setCurrentKey(keyOf(w));
    setOpenPath(null);
  }

  if (data == null) return <div className="loading">Loading the examples…</div>;

  return (
    <div className="app">
      <header className="top">
        <h1>Tolean Playground</h1>
        <select
          value={currentKey ?? ''}
          onChange={(e) => {
            setCurrentKey(e.target.value);
            setOpenPath(null);
          }}
          aria-label="Workspace"
        >
          <optgroup label="Examples">
            {workspaces
              .filter((w) => w.kind === 'example')
              .map((w) => (
                <option key={keyOf(w)} value={keyOf(w)}>
                  {w.name}
                </option>
              ))}
          </optgroup>
          {workspaces.some((w) => w.kind === 'user') && (
            <optgroup label="Your workspaces">
              {workspaces
                .filter((w) => w.kind === 'user')
                .map((w) => (
                  <option key={keyOf(w)} value={keyOf(w)}>
                    {w.name}
                  </option>
                ))}
            </optgroup>
          )}
        </select>
        <button type="button" onClick={newWorkspace}>
          New workspace
        </button>
        <button type="button" onClick={() => void share()}>
          Share
        </button>
        {shareNote != null && <span className="muted">{shareNote}</span>}
      </header>

      <nav className="tree" aria-label="Files">
        {folders.map((folder) => (
          <div key={folder}>
            <div className="folder">{folder}/</div>
            {files
              .filter((f) => f.path.startsWith(`${folder}/`))
              .map((f) => (
                <button
                  type="button"
                  key={f.path}
                  className={f.path === open?.path ? 'file active' : 'file'}
                  onClick={() => setOpenPath(f.path)}
                >
                  {f.path.slice(folder.length + 1)}
                  {isGenerated(f.path) && <span className="tag">generated</span>}
                </button>
              ))}
          </div>
        ))}
        {files.some((f) => f.path === 'tolean.json') && (
          <button
            type="button"
            className={open?.path === 'tolean.json' ? 'file top-level active' : 'file top-level'}
            onClick={() => setOpenPath('tolean.json')}
          >
            tolean.json
          </button>
        )}
      </nav>

      <main className="main">
        {open != null && (
          <>
            <div className="file-bar">
              {open.path}
              {isGenerated(open.path) && <span className="muted"> · written by Tolean, read-only</span>}
            </div>
            <Editor
              // A generated file changes under the viewer, so its editor restarts with the new text.
              key={`${currentKey}:${open.path}${isGenerated(open.path) ? `:${hashText(open.text)}` : ''}`}
              path={open.path}
              text={open.text}
              readOnly={isGenerated(open.path)}
              onChange={(text) => updateFile(open.path, text)}
            />
          </>
        )}
      </main>

      <aside className="side">
        <p className={engine.kind === 'failed' ? 'notice failed' : 'notice'}>{engineNotice(engine)}</p>
        {translatorError != null && (
          <p className="notice failed">
            The translator did not load ({translatorError}), so the generated Lean is the copy that came with the
            example and does not follow your edits.
          </p>
        )}
        {translationErrors.map((e) => (
          <p key={e} className="notice failed">
            Tolean refused the source: {e}
          </p>
        ))}
        <Claims claims={claims} proofs={proofs} statuses={statuses} />
      </aside>
    </div>
  );
}
