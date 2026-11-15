import { spawnSync } from 'node:child_process';
import { mkdtempSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { fileURLToPath } from 'node:url';
import ts from 'typescript';
import { expect, test } from 'vitest';
import { tscAst } from './tscAst.ts';

const tolean = process.env.TOLEAN ?? fileURLToPath(new URL('../../.lake/build/bin/tolean', import.meta.url));
const operators = ['??', '===', '!==', '==', '!=', '+', '*', '/', '%', '**'];

test('the comparison translation fixtures type-check with pinned TypeScript', () => {
  const path = fileURLToPath(new URL('./corpus/translate/accept/comparisonTypeLookalikes.ts', import.meta.url));
  const program = ts.createProgram([path], {
    target: ts.ScriptTarget.ES2024, noEmit: true, strict: true, types: [], skipLibCheck: true,
  });
  expect(ts.getPreEmitDiagnostics(program).map((d) => ts.flattenDiagnosticMessageText(d.messageText, '\n'))).toEqual([]);
});

test('expression operators stop the type-argument probe in all five shapes', () => {
  const dir = mkdtempSync(join(tmpdir(), 'tolean-type-stops-'));
  try {
    for (const op of operators) {
      const shapes = [
        `a < b ${op} c > (d)`,
        `a < ${op} c > (d)`,
        `a < b ${op} c > d`,
        `a < b ${op} c >\nd`,
        `a < b ${op} c > \`tail\``,
      ];
      for (const expr of shapes) {
        const source = `export function f(a, b, c, d) { return ${expr}; }`;
        const sf = ts.createSourceFile('probe.ts', source, ts.ScriptTarget.Latest, true);
        let typeArguments = false;
        const visit = (node: ts.Node): void => {
          if ('typeArguments' in node && (node.typeArguments as ts.NodeArray<ts.TypeNode> | undefined)?.length) {
            typeArguments = true;
          }
          ts.forEachChild(node, visit);
        };
        visit(sf);
        expect(typeArguments, expr).toBe(false);
        const path = join(dir, 'probe.ts');
        writeFileSync(path, source);
        const run = spawnSync(tolean, ['parse', '--round-trip', path], { encoding: 'utf8' });
        const expected = tscAst(path, source);
        if (expected.kind === 'tree') {
          expect(run.status, `${expr}\n${run.stderr}`).toBe(0);
          expect(run.stdout.trimEnd(), expr).toBe(expected.sexp);
        } else {
          expect(run.status, `${expr}\n${expected.reason}`).toBe(1);
        }
      }
      const nested = `export function f(a, b, c, d) { return a < { [b ${op} c]: number } > (d); }`;
      const path = join(dir, 'nested.ts');
      writeFileSync(path, nested);
      const sf = ts.createSourceFile(path, nested, ts.ScriptTarget.Latest, true);
      let hasTypeArguments = false;
      const visit = (node: ts.Node): void => {
        if (ts.isCallExpression(node) && node.typeArguments?.length) hasTypeArguments = true;
        ts.forEachChild(node, visit);
      };
      visit(sf);
      expect(hasTypeArguments, nested).toBe(true);
      const run = spawnSync(tolean, ['parse', path], { encoding: 'utf8' });
      expect(run.status, nested).toBe(1);
      expect(run.stderr, nested).toContain('tsc may read this');
    }
    for (const expr of ['a < -1 > (d)', 'a < b | c > (d)', 'a < b<c >> (d)',
      'a < b & c > (d)', 'a < b.c > (d)', 'a < b > (d)',
      'a < b! > (d)', 'a < b ? c : d > (d)',
      'a < b >= d', 'a < b << c > d', 'a < b <= c > d']) {
      const path = join(dir, 'excluded.ts');
      writeFileSync(path, `export function f(a, b, c, d) { return ${expr}; }`);
      const run = spawnSync(tolean, ['parse', path], { encoding: 'utf8' });
      expect(run.status, expr).toBe(1);
      expect(run.stderr, expr).toContain('tsc may read this');
    }
  } finally {
    rmSync(dir, { recursive: true, force: true });
  }
}, 30000);
