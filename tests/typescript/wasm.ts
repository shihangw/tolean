/**
 * Load the playground's WebAssembly build of the translator (wasm/out, from
 * wasm/build.sh) in Node, and translate one TypeScript file with it, as the
 * native `tolean translate <input> <output> <Namespace>` does.
 */
import { readFileSync } from 'node:fs';
import { gunzipSync } from 'node:zlib';

interface TranslatorModule {
  _tolean_init(): number;
  _tolean_translate(input: number): number;
  _free(ptr: number): void;
  stringToNewUTF8(s: string): number;
  UTF8ToString(ptr: number): string;
  getExceptionMessage(error: unknown): [string, string];
}

const dir = new URL('../../wasm/out/', import.meta.url);
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
if (m._tolean_init() !== 1) throw new Error('the WebAssembly translator did not start');

export type WasmResult = { kind: 'lean'; text: string } | { kind: 'refused'; message: string };

/** Run the same project entry point that the native workspace command uses. */
export function translateWorkspaceInWasm(files: Array<{ path: string; text: string }>): unknown {
  const p = m.stringToNewUTF8(JSON.stringify({ files }));
  let r: number;
  try {
    r = m._tolean_translate(p);
  } catch (error) {
    if (error instanceof WebAssembly.Exception) {
      const [type, message] = m.getExceptionMessage(error);
      throw new Error(`the WebAssembly translator threw ${type}: ${message}`, { cause: error });
    }
    throw error;
  } finally {
    m._free(p);
  }
  const out: unknown = JSON.parse(m.UTF8ToString(r));
  m._free(r);
  return out;
}

/** Translate one file with the WebAssembly build, into the namespace `Test`. */
export function translateInWasm(path: string, text: string, target?: string): WasmResult {
  const config = {
    typescript: {
      sources: [path],
      ...(target === undefined ? {} : { target }),
      overrides: [{ sources: [path], output: 'Output.lean', namespace: 'Test' }],
    },
  };
  const out = translateWorkspaceInWasm([{ path: 'tolean.json', text: JSON.stringify(config) }, { path, text }]) as {
    units?: { lean?: string; error?: string }[]; error?: string;
  };
  const unit = out.units?.[0];
  if (unit?.lean !== undefined) return { kind: 'lean', text: unit.lean };
  return { kind: 'refused', message: unit?.error ?? out.error ?? 'no unit' };
}
