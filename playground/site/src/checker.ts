import { type Bundle, locate } from './lean.ts';

/** The result of checking one claim. */
export type ClaimStatus =
  | { readonly kind: 'unchecked' }
  | { readonly kind: 'checking' }
  | { readonly kind: 'proved'; readonly axioms: readonly string[] }
  | { readonly kind: 'broken'; readonly reason: string };

/** A diagnostic that Lean prints as one JSON line. */
interface Diagnostic {
  readonly severity: 'error' | 'warning' | 'information';
  readonly pos?: { readonly line: number; readonly column: number };
  readonly data: string;
}

/** The state of the Lean that runs in the page. */
export type EngineState =
  | { readonly kind: 'loading' }
  | { readonly kind: 'ready' }
  | { readonly kind: 'failed'; readonly message: string };

/**
 * Read each claim's status from Lean's diagnostics. A claim is proved when
 * `#print axioms` names no `sorryAx`. Lean keeps a failed proof as `sorry`,
 * so a claim that relies on a broken lemma is broken too, and the reason is
 * the first error, with its file and line in the workspace.
 */
export function statuses(
  diagnostics: readonly Diagnostic[],
  bundle: Bundle,
  claims: readonly string[],
): Map<string, ClaimStatus> {
  const firstError = diagnostics.find((d) => d.severity === 'error');
  let reason = 'Lean did not check this claim.';
  if (firstError != null) {
    const where = firstError.pos == null ? null : locate(bundle.parts, firstError.pos.line);
    const message = firstError.data.split('\n')[0] ?? '';
    reason = where == null ? message : `${where.path}:${where.line}: ${message}`;
  }
  const result = new Map<string, ClaimStatus>();
  for (const claim of claims) {
    const escaped = claim.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
    const pattern = new RegExp(`'(?:_private\\.\\d+\\.)?Proof\\.${escaped}' (depends on axioms: \\[(.*)\\]|does not depend on any axioms)`);
    const line = diagnostics.map((d) => pattern.exec(d.data)).find((m) => m != null);
    if (line == null) {
      result.set(claim, { kind: 'broken', reason });
      continue;
    }
    const axioms = (line[2] ?? '').split(',').map((a) => a.trim()).filter(Boolean);
    result.set(claim, axioms.includes('sorryAx') ? { kind: 'broken', reason } : { kind: 'proved', axioms });
  }
  return result;
}

interface PackEntry {
  readonly path: string;
  readonly offset: number;
  readonly length: number;
}

type WorkerMessage =
  | { readonly type: 'ready' }
  | { readonly type: 'error'; readonly message: string }
  | { readonly type: 'log'; readonly text: string }
  | {
      readonly type: 'result';
      readonly id: number;
      readonly diagnostics: Diagnostic[];
      readonly output: string[];
      readonly elapsed: number;
    };

/** What every worker starts from: the compiled WebAssembly and the Init library. */
interface Runtime {
  readonly module: WebAssembly.Module;
  readonly index: readonly PackEntry[];
  readonly pack: ArrayBuffer;
}

/** A worker whose Lean has started and imported Init, ready for one check. */
interface Warm {
  check(code: string): Promise<Diagnostic[]>;
  stop(): void;
}

/**
 * Lean, compiled to WebAssembly, in workers. Each check runs on a fresh
 * worker, because this Lean build fails every check after one that unfolds a
 * recursive definition, and generated code is full of them.
 * See https://github.com/cauli/lean4-wasm-in-browser/issues/4. One spare worker
 * starts ahead of time, so a check does not wait for Lean to start.
 *
 * One check runs at a time. A check asked for while another runs replaces any
 * check still waiting, so only the latest edit is checked.
 */
export class LeanChecker {
  private runtime: Promise<Runtime> | null = null;
  private spare: Promise<Warm> | null = null;
  private busy = false;
  private waiting: { code: string; resolve: (d: Diagnostic[] | null) => void } | null = null;

  /** The URL of the folder with lean.js, lean.wasm and the Init library. */
  private readonly base: string;
  private readonly workerUrl: string;
  private readonly onState: (state: EngineState) => void;

  constructor(base: string, workerUrl: string, onState: (state: EngineState) => void) {
    this.base = base;
    this.workerUrl = workerUrl;
    this.onState = onState;
  }

  /** Start Lean: download it and warm up the first worker. */
  start(): Promise<Warm> {
    if (this.spare == null) {
      this.onState({ kind: 'loading' });
      this.spare = this.warm().then(
        (w) => {
          this.onState({ kind: 'ready' });
          return w;
        },
        (e: unknown) => {
          this.onState({ kind: 'failed', message: e instanceof Error ? e.message : String(e) });
          throw e;
        },
      );
    }
    return this.spare;
  }

  /** Check a bundle. Returns null when a later check replaced this one. */
  async check(code: string): Promise<Diagnostic[] | null> {
    await this.start();
    if (!this.busy) return this.run(code);
    this.waiting?.resolve(null);
    return new Promise((resolve) => {
      this.waiting = { code, resolve };
    });
  }

  private async run(code: string): Promise<Diagnostic[]> {
    this.busy = true;
    try {
      const worker = await this.start();
      this.spare = null;
      try {
        return await worker.check(code);
      } finally {
        worker.stop();
        // Start the next spare only now, so that two Leans never hold memory at once.
        void this.start().catch(() => {});
      }
    } finally {
      this.busy = false;
      const next = this.waiting;
      this.waiting = null;
      if (next != null) void this.run(next.code).then(next.resolve, () => next.resolve(null));
    }
  }

  private loadRuntime(): Promise<Runtime> {
    this.runtime ??= (async () => {
      if (!crossOriginIsolated) throw new Error('The page is not cross-origin isolated, so Lean cannot start.');
      const [module, index, pack] = await Promise.all([
        WebAssembly.compileStreaming(fetch(`${this.base}/lean.wasm`)),
        fetch(`${this.base}/init.index.json`).then((r) => r.json() as Promise<PackEntry[]>),
        fetch(`${this.base}/init.pack.bin`).then(async (r) => {
          if (!r.ok) throw new Error(`The Lean library did not download (${r.status}).`);
          // The file is gzipped, but some servers unpack it on the way, so
          // unpack only when the bytes still start with gzip's signature.
          const bytes = await r.arrayBuffer();
          const head = new Uint8Array(bytes, 0, 2);
          if (head[0] !== 0x1f || head[1] !== 0x8b) return bytes;
          return new Response(new Blob([bytes]).stream().pipeThrough(new DecompressionStream('gzip'))).arrayBuffer();
        }),
      ]);
      return { module, index, pack };
    })();
    return this.runtime;
  }

  private async warm(): Promise<Warm> {
    const { module, index, pack } = await this.loadRuntime();
    // Each worker gets its own copy of the library, which it takes over.
    const files = index.map((e) => ({ path: e.path, data: pack.slice(e.offset, e.offset + e.length) }));
    const worker = new Worker(this.workerUrl);
    let pending: ((d: Diagnostic[]) => void) | null = null;
    let failCheck: ((e: Error) => void) | null = null;
    await new Promise<void>((resolve, reject) => {
      worker.onmessage = (event: MessageEvent<WorkerMessage>) => {
        const msg = event.data;
        switch (msg.type) {
          case 'ready':
            resolve();
            break;
          case 'error':
            reject(new Error(msg.message));
            failCheck?.(new Error(msg.message));
            break;
          case 'log':
            console.debug('[lean]', msg.text);
            break;
          case 'result':
            if (msg.output.length > 0) console.debug('[lean]', msg.output.join('\n'));
            pending?.(msg.diagnostics);
            break;
          default: {
            const never: never = msg;
            return never;
          }
        }
      };
      worker.postMessage(
        { type: 'start', base: this.base, module, files },
        files.map((f) => f.data),
      );
    });
    return {
      check: (code) =>
        new Promise((resolve, reject) => {
          pending = resolve;
          failCheck = reject;
          worker.postMessage({ type: 'check', id: 1, code });
        }),
      stop: () => worker.terminate(),
    };
  }
}
