/**
 * Copy the license, and the Lean runtime into `lean/`, from the repository
 * root. The package then carries its license and the Lake package that
 * generated code imports. A consumer requires it by path:
 *
 *   [[require]]
 *   name = "tolean"
 *   path = "../node_modules/tolean/lean"
 *
 * The runtime is the language specs and `#audit_claims`: what generated code
 * and proofs import. The parsers and translators stay out; they run as the
 * native `tolean` command.
 */
import { cpSync, mkdirSync, rmSync, writeFileSync } from 'node:fs';
import { fileURLToPath } from 'node:url';

const root = fileURLToPath(new URL('../../', import.meta.url));
const out = fileURLToPath(new URL('../lean/', import.meta.url));

cpSync(`${root}LICENSE`, fileURLToPath(new URL('../LICENSE', import.meta.url)));
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
