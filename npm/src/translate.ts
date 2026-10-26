/**
 * Tolean's translator, run as the native `tolean` command. The package finds
 * the binary in `$TOLEAN_BINARY`, or else in the package for this platform,
 * such as `@tolean/darwin-arm64`, and passes it the workspace as JSON on
 * stdin (`tolean translate-workspace`).
 */
import { spawn } from 'node:child_process';
import { existsSync } from 'node:fs';
import { createRequire } from 'node:module';

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

/** The platforms that Lean releases a toolchain for, and so that Tolean ships a binary for. */
export const PLATFORMS = ['darwin-arm64', 'darwin-x64', 'linux-arm64', 'linux-x64', 'win32-x64'] as const;

/** The path of the `tolean` binary for this machine. */
export function binaryPath(): string {
  const fromEnv = process.env.TOLEAN_BINARY;
  if (fromEnv !== undefined && fromEnv !== '') return fromEnv;
  const platform = `${process.platform}-${process.arch}`;
  const exe = process.platform === 'win32' ? 'tolean.exe' : 'tolean';
  try {
    const path = createRequire(import.meta.url).resolve(`@tolean/${platform}/bin/${exe}`);
    if (existsSync(path)) return path;
  } catch {
    // Not installed; the error below says what to do.
  }
  throw new Error(
    `no tolean binary for ${platform}: install @tolean/${platform}, or set TOLEAN_BINARY to a tolean command ` +
      `(Tolean ships binaries for ${PLATFORMS.join(', ')})`,
  );
}

/** Run `tolean translate-workspace` on the JSON text, and return its output. */
function run(input: string): Promise<string> {
  return new Promise((resolve, reject) => {
    const child = spawn(binaryPath(), ['translate-workspace'], { stdio: ['pipe', 'pipe', 'pipe'] });
    const out: Buffer[] = [];
    const err: Buffer[] = [];
    child.stdout.on('data', (b: Buffer) => out.push(b));
    child.stderr.on('data', (b: Buffer) => err.push(b));
    child.on('error', reject);
    child.on('close', (code) => {
      if (code === 0) resolve(Buffer.concat(out).toString('utf8'));
      else reject(new Error(`tolean exited with ${code}: ${Buffer.concat(err).toString('utf8')}`));
    });
    child.stdin.end(input);
  });
}

/**
 * Translate a whole workspace, as `tolean translate` does with `tolean.json`:
 * the files must include `tolean.json`, and each unit it names comes back as
 * Lean or as the translator's reason to refuse it.
 */
export async function translateWorkspace(files: readonly WorkspaceFile[]): Promise<UnitResult[]> {
  const json = JSON.parse(await run(JSON.stringify({ files }))) as
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
