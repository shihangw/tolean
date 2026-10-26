/**
 * Fetch the Lean that runs in the browser, check it, and write what the page
 * serves under public/lean/:
 *
 * - lean.js and lean.wasm.bin, the Lean compiled to WebAssembly, gzipped;
 * - init.pack.bin and init.index.json, the `.olean` files of `Init` joined into
 *   one gzipped file, so the page fetches one file and not 629.
 *
 * The runtime is the pinned release in lean-runtime.json, from
 * github.com/cauli/lean4-wasm-in-browser. The script refuses an archive or a
 * file whose SHA-256 differs from the pin. It keeps the archive in .cache/, so
 * it downloads it only once.
 */
import { execFileSync } from 'node:child_process';
import { createHash } from 'node:crypto';
import { existsSync, mkdirSync, readFileSync, readdirSync, rmSync, statSync, writeFileSync } from 'node:fs';
import path from 'node:path';
import { gzipSync } from 'node:zlib';

interface Pin {
  readonly fixture: { readonly url: string; readonly sha256: string };
  readonly objects: Readonly<Record<string, string>>;
}

const site = path.join(import.meta.dirname, '..');
const pin = JSON.parse(readFileSync(path.join(site, 'lean-runtime.json'), 'utf8')) as Pin;
const cache = path.join(site, '.cache');
const out = path.join(site, 'public/lean');

const sha256 = (file: string) => createHash('sha256').update(readFileSync(file)).digest('hex');

function check(file: string, expected: string) {
  const actual = sha256(file);
  if (actual !== expected) throw new Error(`${file}: SHA-256 is ${actual}, the pin says ${expected}`);
}

const archive = path.join(cache, `${pin.fixture.sha256}.tar.gz`);
if (!existsSync(archive)) {
  mkdirSync(cache, { recursive: true });
  console.log(`downloading ${pin.fixture.url}`);
  const response = await fetch(pin.fixture.url);
  if (!response.ok) throw new Error(`download failed: ${response.status}`);
  writeFileSync(`${archive}.part`, new Uint8Array(await response.arrayBuffer()));
  check(`${archive}.part`, pin.fixture.sha256);
  execFileSync('mv', [`${archive}.part`, archive]);
}
check(archive, pin.fixture.sha256);

const extracted = path.join(cache, 'runtime');
rmSync(extracted, { recursive: true, force: true });
mkdirSync(extracted, { recursive: true });
execFileSync('tar', ['-xzf', archive, '-C', extracted, 'bin/lean.js', 'bin/lean.wasm', 'lib/lean']);
for (const [file, expected] of Object.entries(pin.objects)) check(path.join(extracted, file), expected);

rmSync(out, { recursive: true, force: true });
mkdirSync(out, { recursive: true });
writeFileSync(path.join(out, 'lean.js'), readFileSync(path.join(extracted, 'bin/lean.js')));
// Gzip cuts lean.wasm from 101 MB to 17 MB. The page unpacks it itself, so it
// does not depend on whether the server compresses .wasm files.
writeFileSync(path.join(out, 'lean.wasm.bin'), gzipSync(readFileSync(path.join(extracted, 'bin/lean.wasm')), { level: 9 }));

// Lean reads only the .olean files of Init; the .ir files serve #eval of
// library code, which the playground does not need.
const lib = path.join(extracted, 'lib/lean');
const oleans: string[] = [];
const walk = (dir: string) => {
  for (const name of readdirSync(dir).sort()) {
    const full = path.join(dir, name);
    if (statSync(full).isDirectory()) walk(full);
    else if (name.endsWith('.olean')) oleans.push(path.relative(lib, full));
  }
};
walk(lib);

const index: { path: string; offset: number; length: number }[] = [];
const parts: Buffer[] = [];
let offset = 0;
for (const file of oleans) {
  const data = readFileSync(path.join(lib, file));
  index.push({ path: file, offset, length: data.length });
  parts.push(data);
  offset += data.length;
}
writeFileSync(path.join(out, 'init.pack.bin'), gzipSync(Buffer.concat(parts), { level: 9 }));
writeFileSync(path.join(out, 'init.index.json'), JSON.stringify(index));
console.log(`wrote public/lean: ${oleans.length} .olean files, ${(offset / 1e6).toFixed(0)} MB before gzip`);
