import { type CSSProperties, useEffect, useMemo, useRef, useState } from 'react';

import { Divider, StatusBar, Topbar, type TranslatorState } from './Chrome.tsx';
import { Claims } from './Claims.tsx';
import { type ClaimStatus, type EngineState, LeanChecker, statuses as readStatuses } from './checker.ts';
import { type FileDiagnostic, leanDiagnostics, translationDiagnostic } from './diagnostics.ts';
import { type Cursor, Editor, type Reveal } from './editor/Editor.tsx';
import { languageNames, languageOf } from './editor/languages.ts';
import { Files } from './Files.tsx';
import { Icon } from './icons.tsx';
import { type WorkspaceFile, bundle, claims as readClaims, isProof, isSpec, proofDeclarations } from './lean.ts';
import { useSideWidth, useTheme } from './prefs.ts';
import { Problems } from './Problems.tsx';
import { shareLink, sharedFromLocation } from './share.ts';
import { type Translation, loadTranslator } from './translator.ts';
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

/** The viewer turned proof checking on once; the browser then keeps Lean cached. */
const checkingKey = 'tolean-playground-check-proofs';
function readChecking(): boolean {
  try {
    return localStorage.getItem(checkingKey) === 'on';
  } catch {
    return false;
  }
}

const keyOf = (w: Workspace) => (w.kind === 'example' ? `example:${w.name}` : `user:${w.id}`);

const noDiagnostics: readonly FileDiagnostic[] = [];

export function App() {
  const [data, setData] = useState<ExampleData | null>(null);
  const [workspaces, setWorkspaces] = useState<Workspace[]>([]);
  const [currentKey, setCurrentKey] = useState<string | null>(null);
  // A new session starts when the viewer opens another workspace. Editing an
  // example makes a copy with a new key, but the session, and with it the
  // undo history, stays.
  const [session, setSession] = useState(0);
  const [openPath, setOpenPath] = useState<string | null>(null);
  const [reveal, setReveal] = useState<Reveal | null>(null);
  const [cursor, setCursor] = useState<Cursor | null>(null);
  const [statuses, setStatuses] = useState<ReadonlyMap<string, ClaimStatus>>(new Map());
  const [leanProblems, setLeanProblems] = useState<readonly FileDiagnostic[]>([]);
  const [theme, toggleTheme] = useTheme();
  const [sideWidth, setSideWidth] = useSideWidth();

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
  const translated = useMemo(() => {
    if (translate == null || current == null) return null;
    const start = performance.now();
    const result = translate(authored);
    return { result, ms: performance.now() - start };
  }, [translate, current, authored]);
  const translation = translated?.result ?? null;
  const files = useMemo((): readonly WorkspaceFile[] => {
    if (translation == null || translation.kind === 'error') return current?.files ?? [];
    const generated = translation.units.flatMap((u) => (u.kind === 'ok' ? [{ path: u.output, text: u.lean }] : []));
    return [...authored, ...generated].sort((a, b) => a.path.localeCompare(b.path));
  }, [translation, current, authored]);
  const translationErrors = useMemo(
    () =>
      translation == null
        ? []
        : translation.kind === 'error'
          ? [translation.error]
          : translation.units.flatMap((u) => (u.kind === 'error' ? [u.error] : [])),
    [translation],
  );
  const open =
    files.find((f) => f.path === openPath) ??
    files.find((f) => f.path.startsWith('src/') && !isGenerated(f.path)) ??
    null;

  const claims = useMemo(() => readClaims(files), [files]);
  const proofs = useMemo(() => proofDeclarations(files), [files]);

  // Lean downloads only when the viewer asks to check proofs.
  const [checking, setChecking] = useState(readChecking);
  const [engine, setEngine] = useState<EngineState>({ kind: 'off' });
  function turnOnChecking() {
    try {
      localStorage.setItem(checkingKey, 'on');
    } catch {
      // Without storage, the viewer turns checking on again on the next visit.
    }
    setChecking(true);
  }
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
      setLeanProblems([]);
      return;
    }
    if (!checking) {
      setStatuses(new Map(names.map((n) => [n, { kind: 'unchecked' }])));
      return;
    }
    const b = bundle(data.goSpec, ordered, names);
    let cancelled = false;
    const timer = setTimeout(() => {
      setStatuses(new Map(names.map((n) => [n, { kind: 'checking' }])));
      void checker.current!.check(b.text).then(
        (diagnostics) => {
          if (cancelled || diagnostics == null) return;
          setStatuses(readStatuses(diagnostics, b, names));
          setLeanProblems(leanDiagnostics(diagnostics, b, files));
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
  }, [data, current, files, claims, translationErrors, checking]);

  // Every problem in the workspace, and the ones for each file.
  const problems = useMemo(
    () => [...translationErrors.map(translationDiagnostic), ...leanProblems],
    [translationErrors, leanProblems],
  );
  const problemsByPath = useMemo(() => {
    const byPath = new Map<string, FileDiagnostic[]>();
    for (const d of problems) byPath.set(d.path, [...(byPath.get(d.path) ?? []), d]);
    return byPath;
  }, [problems]);

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

  function openWorkspace(key: string) {
    setCurrentKey(key);
    setOpenPath(null);
    setSession((s) => s + 1);
    setLeanProblems([]);
  }

  function openAt(path: string, line: number) {
    setOpenPath(path);
    setReveal({ path, line, nonce: Date.now() });
  }

  const [note, setNote] = useState<string | null>(null);
  useEffect(() => {
    if (note == null) return;
    const timer = setTimeout(() => setNote(null), 2400);
    return () => clearTimeout(timer);
  }, [note]);
  async function share() {
    if (current == null) return;
    const link = await shareLink({ name: current.name, files: authored });
    try {
      await navigator.clipboard.writeText(link);
      setNote('Link copied');
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
    openWorkspace(keyOf(w));
  }

  if (data == null) {
    return (
      <div className="boot">
        <span className="spinner large" />
        <p>Loading the examples…</p>
      </div>
    );
  }

  const translator: TranslatorState =
    translatorError != null
      ? { kind: 'unavailable' }
      : translated == null
        ? { kind: 'loading' }
        : translationErrors.length > 0
          ? { kind: 'refused', errors: translationErrors.length }
          : { kind: 'translated', ms: translated.ms };
  const language = open == null ? null : languageOf(open.path);
  const folder = open?.path.includes('/') === true ? open.path.slice(0, open.path.lastIndexOf('/') + 1) : '';

  return (
    <div className="app" style={{ '--side': `${sideWidth}px` } as CSSProperties}>
      <Topbar
        workspaces={workspaces}
        current={currentKey}
        keyOf={keyOf}
        theme={theme}
        note={note}
        onSelect={openWorkspace}
        onNew={newWorkspace}
        onShare={() => void share()}
        onTheme={toggleTheme}
      />

      <Files files={files} open={open?.path ?? null} diagnostics={problems} onOpen={setOpenPath} />

      <main className="main">
        {open != null && language != null && (
          <>
            <div className="pane-head">
              <span className="crumbs mono">
                <span className="faint">{folder}</span>
                {open.path.slice(folder.length)}
              </span>
              <span className={`badge ${language}`}>{languageNames[language]}</span>
              <span className="grow" />
              {isGenerated(open.path) ? (
                <span className="chip" title="Tolean writes this file from the source next to it, so it is read-only.">
                  <Icon name="lock" size={12} />
                  Written by Tolean
                </span>
              ) : current?.kind === 'example' ? (
                <span className="chip info" title="The examples stay as they are. Your first edit makes a copy.">
                  Example · edits make a copy
                </span>
              ) : null}
            </div>
            {translatorError != null && (
              <div className="banner warn">
                <Icon name="alert" />
                <span>
                  The translator did not load ({translatorError}), so the generated Lean is the copy that came with the
                  example, and it does not follow your edits.
                </span>
              </div>
            )}
            <Editor
              session={String(session)}
              path={open.path}
              text={open.text}
              readOnly={isGenerated(open.path)}
              diagnostics={problemsByPath.get(open.path) ?? noDiagnostics}
              reveal={reveal}
              onChange={updateFile}
              onCursor={setCursor}
              onCheckNow={() => {
                if (!checking) turnOnChecking();
              }}
            />
          </>
        )}
        <Problems diagnostics={problems} onOpen={openAt} />
      </main>

      <Divider width={sideWidth} onWidth={setSideWidth} />

      <aside className="side">
        <Claims
          claims={claims}
          proofs={proofs}
          statuses={statuses}
          files={files}
          engine={engine}
          checking={checking}
          onCheck={turnOnChecking}
          onOpen={openAt}
        />
      </aside>

      <StatusBar
        translator={translator}
        engine={engine}
        checking={checking}
        language={language}
        cursor={cursor}
        saved={current?.kind === 'user'}
      />
    </div>
  );
}
