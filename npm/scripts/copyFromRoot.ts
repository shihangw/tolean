/**
 * Copy the license, the README and the Lean runtime into the package, from
 * the repository root. The package then carries its license, the page that
 * npm shows, and the Lake package that generated code imports. In `lean/`,
 * a consumer requires the runtime by path:
 *
 *   [[require]]
 *   name = "tolean"
 *   path = "../node_modules/tolean/lean"
 *
 * The runtime is the language specs and `#audit_claims`: what generated code
 * and proofs import. The parsers and translators stay out; they run as the
 * native `tolean` command.
 */
import { cpSync, mkdirSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { fileURLToPath } from 'node:url';

const root = fileURLToPath(new URL('../../', import.meta.url));
const out = fileURLToPath(new URL('../lean/', import.meta.url));

cpSync(`${root}LICENSE`, fileURLToPath(new URL('../LICENSE', import.meta.url)));

// npm shows the package's README, and the package's README is the
// repository's. npm cannot follow a path inside the repository, such as
// `docs/go/README.md`, so each relative link and image becomes a GitHub URL.
// The URLs name the release tag, so the page on npm matches its version.
const { version } = JSON.parse(readFileSync(new URL('../package.json', import.meta.url), 'utf8'));
const files = `https://github.com/shihangw/tolean/blob/v${version}/`;
const images = `https://raw.githubusercontent.com/shihangw/tolean/v${version}/`;
const relative = (url: string) => !/^([a-z][a-z+.-]*:|#|\/)/i.test(url);
const readme = readFileSync(`${root}README.md`, 'utf8')
  .replace(/src="([^"]+)"/g, (tag, url) => (relative(url) ? `src="${images}${url}"` : tag))
  .replace(/href="([^"]+)"/g, (tag, url) => (relative(url) ? `href="${files}${url}"` : tag))
  .replace(/\]\(([^)\s]+)\)/g, (link, url) => (relative(url) ? `](${files}${url})` : link));
writeFileSync(fileURLToPath(new URL('../README.md', import.meta.url)), readme);
rmSync(out, { recursive: true, force: true });
mkdirSync(`${out}tolean/TypeScript`, { recursive: true });
cpSync(`${root}lean-toolchain`, `${out}lean-toolchain`);
cpSync(`${root}lake-manifest.json`, `${out}lake-manifest.json`);
cpSync(`${root}tolean/Audit.lean`, `${out}tolean/Audit.lean`);
cpSync(`${root}tolean/TypeScript/Spec`, `${out}tolean/TypeScript/Spec`, { recursive: true });
mkdirSync(`${out}tolean/Go/Spec`, { recursive: true });
cpSync(`${root}tolean/Go/Spec`, `${out}tolean/Go/Spec`, { recursive: true });

writeFileSync(
  `${out}lakefile.toml`,
  [
    'name = "tolean"',
    'license = "Apache-2.0"',
    '',
    '[[lean_lib]]',
    'name = "tolean"',
    'globs = ["tolean.Audit", "tolean.TypeScript.Spec.+", "tolean.Go.Spec.+"]',
    '',
  ].join('\n'),
);
