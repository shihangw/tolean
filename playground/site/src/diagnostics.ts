/**
 * Messages about a place in a workspace file. Tolean's translator and Lean
 * both report them, and the editor underlines them.
 */
import type { Diagnostic as LeanDiagnostic } from './checker.ts';
import { type Bundle, type WorkspaceFile, locate } from './lean.ts';

export interface FileDiagnostic {
  readonly path: string;
  readonly source: 'tolean' | 'lean';
  readonly severity: 'error' | 'warning' | 'info';
  /** The first line is 1. */
  readonly line: number;
  /** The first column is 0, and a column counts Unicode code points, as Lean does. */
  readonly column: number;
  /** Where the range ends, when the reporter says. */
  readonly end: { readonly line: number; readonly column: number } | null;
  readonly message: string;
}

/**
 * Read a translator error such as `src/sort.ts:5:34: expected an expression`.
 * The translator counts columns from 1. An error without a place, such as
 * one about `tolean.json` as a whole, belongs to `tolean.json`.
 */
export function translationDiagnostic(error: string): FileDiagnostic {
  const m = /^([^:\s]+):(\d+):(\d+): ([\s\S]*)$/.exec(error);
  if (m == null) {
    const file = /^([^:\s]+): ([\s\S]*)$/.exec(error);
    return {
      path: file?.[1] ?? 'tolean.json',
      source: 'tolean',
      severity: 'error',
      line: 1,
      column: 0,
      end: null,
      message: file?.[2] ?? error,
    };
  }
  return {
    path: m[1]!,
    source: 'tolean',
    severity: 'error',
    line: Number(m[2]),
    column: Math.max(0, Number(m[3]) - 1),
    end: null,
    message: m[4]!,
  };
}

/**
 * Place Lean's diagnostics on the files of the workspace. A diagnostic about
 * the Go Spec, or about the claim checks at the end of the bundle, has no
 * file to sit in. The claim cards report those.
 */
export function leanDiagnostics(
  diagnostics: readonly LeanDiagnostic[],
  bundle: Bundle,
  files: readonly WorkspaceFile[],
): FileDiagnostic[] {
  const paths = new Set(files.map((f) => f.path));
  const found: FileDiagnostic[] = [];
  for (const d of diagnostics) {
    if (d.pos == null || d.pos.line >= bundle.checksLine) continue;
    const at = locate(bundle.parts, d.pos.line);
    if (at == null || !paths.has(at.path)) continue;
    const endAt = d.endPos == null ? null : locate(bundle.parts, d.endPos.line);
    found.push({
      path: at.path,
      source: 'lean',
      severity: d.severity === 'information' ? 'info' : d.severity,
      line: at.line,
      column: d.pos.column,
      end: endAt != null && endAt.path === at.path ? { line: endAt.line, column: d.endPos!.column } : null,
      message: d.data,
    });
  }
  return found;
}

/** A message on one line, for a list. Lean breaks a message over lines to show a term. */
export const oneLine = (message: string) => message.replace(/\s+/g, ' ').trim();
