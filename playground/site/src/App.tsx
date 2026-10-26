import { useEffect, useMemo, useRef, useState } from 'react';

import { Claims } from './Claims.tsx';
import { type ClaimStatus, type EngineState, LeanChecker, statuses as readStatuses } from './checker.ts';
import { Editor } from './Editor.tsx';
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
      .then((d) => {
        const examples: Workspace[] = d.examples.map((e) => ({ kind: 'example', ...e }));
        const all = [...examples, ...loadUserWorkspaces()];
        setData(d);
        setWorkspaces(all);
        setCurrentKey(all[0] == null ? null : keyOf(all[0]));
      });
  }, []);

  const current = workspaces.find((w) => keyOf(w) === currentKey) ?? null;
  const files = current?.files ?? [];
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
  }, [data, current, files, claims]);

  function updateFile(path: string, text: string) {
    if (current == null) return;
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
              key={`${currentKey}:${open.path}`}
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
        <Claims claims={claims} proofs={proofs} statuses={statuses} />
      </aside>
    </div>
  );
}
