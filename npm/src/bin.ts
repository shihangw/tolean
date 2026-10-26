#!/usr/bin/env node
/**
 * The `tolean` command: the native binary for this platform, with the same
 * arguments. See `tolean --help` for the commands, such as `tolean translate`
 * with a `tolean.json`.
 */
import { spawnSync } from 'node:child_process';

import { binaryPath } from './translate.ts';

let path: string;
try {
  path = binaryPath();
} catch (error) {
  process.stderr.write(`${(error as Error).message}\n`);
  process.exit(2);
}
const run = spawnSync(path, process.argv.slice(2), { stdio: 'inherit' });
if (run.error !== undefined) throw run.error;
process.exit(run.status ?? 1);
