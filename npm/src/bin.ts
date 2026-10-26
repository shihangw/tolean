#!/usr/bin/env node
/**
 * tolean [--target ES20xx] <input.ts> <output.lean> <Lean.Namespace>
 *
 * Paths are relative to the working directory. The input path is written into
 * the generated header, so run it from the same directory every time or the
 * drift check will see a change.
 */
import { readFileSync, writeFileSync } from 'node:fs';

import {
  DEFAULT_TARGET,
  EDITIONS,
  type Edition,
  parseEdition,
  TranslateError,
  translateSource,
} from './translate.ts';

const usage = `usage: tolean [--target ES20xx] <input.ts> <output.lean> <Lean.Namespace>
editions: ${EDITIONS.join(', ')} (default ${DEFAULT_TARGET})
`;
const args = process.argv.slice(2);
let target: Edition = DEFAULT_TARGET;
if (args[0] === '--target') {
  const edition = parseEdition(args[1] ?? '');
  if (edition === null) {
    process.stderr.write(`unknown edition '${args[1] ?? ''}'\n${usage}`);
    process.exit(2);
  }
  target = edition;
  args.splice(0, 2);
}
const [input, output, namespace] = args;
if (input == null || output == null || namespace == null) {
  process.stderr.write(usage);
  process.exit(2);
}

try {
  const lean = translateSource({
    fileName: input,
    text: readFileSync(input, 'utf8'),
    namespace,
    target,
  });
  writeFileSync(output, lean);
} catch (error) {
  if (error instanceof TranslateError) {
    process.stderr.write(`${error.message}\n`);
    process.exit(1);
  }
  throw error;
}
