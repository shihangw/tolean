import type { WorkspaceFile } from './lean.ts';

/** One unit's result: its generated Lean, or why the translator refused it. */
export type UnitResult =
  | { readonly kind: 'ok'; readonly output: string; readonly lean: string }
  | { readonly kind: 'error'; readonly sources: readonly string[]; readonly error: string };

/** What the translator made of a whole workspace. */
export type Translation =
  | { readonly kind: 'units'; readonly units: readonly UnitResult[] }
  | { readonly kind: 'error'; readonly error: string };

interface TranslatorModule {
  _tolean_init(): number;
  _tolean_translate(input: number): number;
  _free(ptr: number): void;
  stringToNewUTF8(s: string): number;
  UTF8ToString(ptr: number): string;
}

type Translate = (files: readonly WorkspaceFile[]) => Translation;

let loading: Promise<Translate> | null = null;

/**
 * Load Tolean's translator, compiled to WebAssembly by playground/wasm/build.sh.
 * It runs on the page's own thread, because a translation takes milliseconds.
 */
export function loadTranslator(base: string): Promise<Translate> {
  loading ??= (async () => {
    const url = new URL(`${base}/tolean.js`, document.baseURI).href;
    const factory = ((await import(/* @vite-ignore */ url)) as { default: (m: object) => Promise<TranslatorModule> })
      .default;
    const m = await factory({ locateFile: (p: string) => new URL(`${base}/${p}`, document.baseURI).href });
    if (m._tolean_init() !== 1) throw new Error('The translator did not start.');
    return (files) => {
      const input = m.stringToNewUTF8(JSON.stringify({ files }));
      const result = m._tolean_translate(input);
      m._free(input);
      const text = m.UTF8ToString(result);
      m._free(result);
      return parse(text);
    };
  })();
  return loading;
}

function parse(text: string): Translation {
  const json = JSON.parse(text) as
    | { error: string }
    | { units: ({ output: string; lean: string } | { sources: string[]; error: string })[] };
  if ('error' in json) return { kind: 'error', error: json.error };
  return {
    kind: 'units',
    units: json.units.map((u) =>
      'lean' in u ? { kind: 'ok', output: u.output, lean: u.lean } : { kind: 'error', sources: u.sources, error: u.error },
    ),
  };
}
