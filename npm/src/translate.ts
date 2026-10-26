/**
 * Tolean's translator, compiled to WebAssembly from the Lean sources by
 * `wasm/build.sh`. It is the same translator that the `tolean` command runs
 * and that per-file certificates are about; this package only loads it. The
 * build copies it into `translator/`.
 */
import { readFileSync } from 'node:fs';
import { gunzipSync } from 'node:zlib';

export class TranslateError extends Error {}

/**
 * The editions of ECMA-262 that a translation can target, as in
 * `tolean/TypeScript/Edition.lean`. The code runs as written (type stripping
 * keeps its syntax), so the target must have every feature it uses.
 */
export const EDITIONS = [
  'ES2015',
  'ES2016',
  'ES2017',
  'ES2018',
  'ES2019',
  'ES2020',
  'ES2021',
  'ES2022',
  'ES2023',
  'ES2024',
  'ES2025',
] as const;

export type Edition = (typeof EDITIONS)[number];

/** What Node 22 supports: the oldest Node release line still maintained. */
export const DEFAULT_TARGET: Edition = 'ES2024';

export function parseEdition(name: string): Edition | null {
  return EDITIONS.find((e) => e.toLowerCase() === name.toLowerCase()) ?? null;
}

/** One file of a workspace, by its path inside the workspace. */
export interface WorkspaceFile {
  readonly path: string;
  readonly text: string;
}

/** One unit's result: its generated Lean, or why the translator refused it. */
export type UnitResult =
  | { readonly kind: 'ok'; readonly output: string; readonly lean: string }
  | { readonly kind: 'error'; readonly sources: readonly string[]; readonly error: string };

interface TranslatorModule {
  _tolean_init(): number;
  _tolean_translate(input: number): number;
  _free(ptr: number): void;
  stringToNewUTF8(s: string): number;
  UTF8ToString(ptr: number): string;
}

let loading: Promise<(input: string) => string> | null = null;

function loadTranslator(): Promise<(input: string) => string> {
  loading ??= (async () => {
    const dir = new URL('../translator/', import.meta.url);
    const bytes = new Uint8Array(gunzipSync(readFileSync(new URL('tolean.wasm.bin', dir))));
    const { default: factory } = (await import(new URL('tolean.js', dir).href)) as {
      default: (m: object) => Promise<TranslatorModule>;
    };
    // The glue reads Module.instantiateWasm but not Module.wasmBinary.
    const m = await factory({
      instantiateWasm: (
        imports: WebAssembly.Imports,
        receive: (instance: WebAssembly.Instance, module: WebAssembly.Module) => void,
      ) => {
        void WebAssembly.instantiate(bytes, imports).then((r) => receive(r.instance, r.module));
        return {};
      },
    });
    if (m._tolean_init() !== 1) throw new Error('the translator did not start');
    return (input) => {
      const p = m.stringToNewUTF8(input);
      const r = m._tolean_translate(p);
      m._free(p);
      const out = m.UTF8ToString(r);
      m._free(r);
      return out;
    };
  })();
  return loading;
}

/**
 * Translate a whole workspace, as `tolean translate` does with `tolean.json`:
 * the files must include `tolean.json`, and each unit it names comes back as
 * Lean or as the translator's reason to refuse it.
 */
export async function translateWorkspace(files: readonly WorkspaceFile[]): Promise<UnitResult[]> {
  const translate = await loadTranslator();
  const json = JSON.parse(translate(JSON.stringify({ files }))) as
    | { error: string }
    | { units: ({ output: string; lean: string } | { sources: string[]; error: string })[] };
  if ('error' in json) throw new TranslateError(json.error);
  return json.units.map((u) =>
    'lean' in u ? { kind: 'ok', output: u.output, lean: u.lean } : { kind: 'error', sources: u.sources, error: u.error },
  );
}

/** Translate one TypeScript file to Lean, or throw TranslateError with the reason. */
export async function translateSource({
  fileName,
  text,
  namespace,
  target = DEFAULT_TARGET,
}: {
  fileName: string;
  text: string;
  namespace: string;
  /** The edition the code runs on. */
  target?: Edition;
}): Promise<string> {
  const config = {
    typescript: {
      sources: [fileName],
      target,
      overrides: [{ sources: [fileName], output: 'Output.lean', namespace }],
    },
  };
  const units = await translateWorkspace([
    { path: 'tolean.json', text: JSON.stringify(config) },
    { path: fileName, text },
  ]);
  const unit = units[0];
  if (unit == null) throw new TranslateError(`${fileName}: no such file`);
  if (unit.kind === 'error') throw new TranslateError(unit.error);
  return unit.lean;
}
