/**
 * Pack the npm release: one `@tolean/<platform>` package for each native
 * binary, and the `tolean` package, which lists them as optionalDependencies,
 * so npm installs only the one for the user's machine. This writes `.tgz`
 * files; it publishes nothing.
 *
 *   node scripts/pack.ts <binaries dir> <out dir>
 *
 * `<binaries dir>` holds one directory per platform, as CI downloads them:
 * `tolean-linux-x64/tolean`, `tolean-win32-x64/tolean.exe`, and so on. Run
 * `pnpm build` first, so that `dist/` and `lean/` exist.
 */
import { execFileSync } from 'node:child_process';
import { chmodSync, copyFileSync, cpSync, existsSync, mkdirSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import path from 'node:path';

import { PLATFORMS } from '../src/translate.ts';

const [binaries, outArg] = process.argv.slice(2);
if (binaries === undefined || outArg === undefined) {
  process.stderr.write('usage: node scripts/pack.ts <binaries dir> <out dir>\n');
  process.exit(2);
}
const npmDir = path.join(import.meta.dirname, '..');
const out = path.resolve(outArg);
const main = JSON.parse(readFileSync(path.join(npmDir, 'package.json'), 'utf8')) as Record<string, unknown> & {
  version: string;
};
rmSync(out, { recursive: true, force: true });
mkdirSync(out, { recursive: true });

const pack = (dir: string) => execFileSync('npm', ['pack', '--pack-destination', out], { cwd: dir, stdio: 'inherit' });

const optional: Record<string, string> = {};
for (const platform of PLATFORMS) {
  const [os, cpu] = platform.split('-') as [string, string];
  const exe = os === 'win32' ? 'tolean.exe' : 'tolean';
  const binary = path.join(binaries, `tolean-${platform}`, exe);
  if (!existsSync(binary)) throw new Error(`no binary for ${platform} at ${binary}`);
  const name = `@tolean/${platform}`;
  const dir = path.join(out, 'staging', platform);
  mkdirSync(path.join(dir, 'bin'), { recursive: true });
  copyFileSync(binary, path.join(dir, 'bin', exe));
  // Artifact downloads lose the executable bit.
  chmodSync(path.join(dir, 'bin', exe), 0o755);
  writeFileSync(
    path.join(dir, 'package.json'),
    JSON.stringify(
      {
        name,
        version: main.version,
        description: `The tolean binary for ${platform}, which the tolean package runs`,
        license: main.license,
        repository: main.repository,
        os: [os],
        cpu: [cpu],
        files: ['bin'],
      },
      null,
      2,
    ) + '\n',
  );
  cpSync(path.join(npmDir, 'LICENSE'), path.join(dir, 'LICENSE'));
  pack(dir);
  optional[name] = main.version;
}

// The main package, with the platform packages at the same version.
const dir = path.join(out, 'staging', 'tolean');
mkdirSync(dir, { recursive: true });
for (const f of ['dist', 'lean', 'LICENSE', 'README.md']) cpSync(path.join(npmDir, f), path.join(dir, f), { recursive: true });
const { scripts: _scripts, devDependencies: _dev, ...rest } = main;
writeFileSync(path.join(dir, 'package.json'), JSON.stringify({ ...rest, optionalDependencies: optional }, null, 2) + '\n');
pack(dir);
rmSync(path.join(out, 'staging'), { recursive: true, force: true });
console.log(`packed ${PLATFORMS.length + 1} packages into ${out}`);
