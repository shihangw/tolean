import { expect, test } from 'vitest';
import { spawnSync } from 'node:child_process';
import { cpSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';

import { translateSource } from './translate.ts';

test('returning loops compile with only the packaged Lean runtime', async () => {
  const work = mkdtempSync(join(tmpdir(), 'tolean-runtime-'));
  // Do not inherit the repository's Lean search path or compiled modules.
  const env = { ...process.env };
  delete env.LEAN_PATH;
  delete env.LEAN_SRC_PATH;
  const lake = (...args: string[]) => {
    const result = spawnSync('lake', args, { cwd: work, env, encoding: 'utf8' });
    if (result.error) throw result.error;
    return { status: result.status, output: result.stdout + result.stderr };
  };
  try {
    cpSync(new URL('../lean/', import.meta.url), work, { recursive: true });
    const lean = await translateSource({
      fileName: 'loopReturn.ts',
      text: readFileSync(new URL('../../tests/typescript/corpus/translate/accept/loopReturn.ts', import.meta.url), 'utf8'),
      namespace: 'Test',
    });
    writeFileSync(join(work, 'Consumer.lean'), lean);
    expect(lake('build', 'tolean.Runtime.LoopResult')).toEqual({ status: 0, output: expect.any(String) });
    const compiled = lake('env', 'lean', 'Consumer.lean');
    expect(compiled, compiled.output).toEqual({ status: 0, output: expect.any(String) });

    // A missing runtime module must fail, even when the repository is built.
    rmSync(join(work, '.lake/build/lib/lean/tolean/Runtime/LoopResult.olean'));
    const missing = lake('env', 'lean', 'Consumer.lean');
    expect(missing.status).not.toBe(0);
    expect(missing.output).toContain('LoopResult.olean');
  } finally {
    rmSync(work, { recursive: true, force: true });
  }
}, 120_000);
