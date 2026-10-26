/**
 * Reading and joining the Lean files of a workspace. This file has no Node or
 * DOM dependencies, so the page and the build scripts share it.
 */

/** One file of a workspace, by its path inside the workspace. */
export interface WorkspaceFile {
  readonly path: string;
  readonly text: string;
}

/** A top-level declaration of a Lean file, with the doc comment before it. */
export interface Declaration {
  readonly kind: 'def' | 'theorem';
  readonly name: string;
  readonly doc: string | null;
  /** The declaration's text, without its doc comment. */
  readonly text: string;
}

const declStart = /^(def|theorem) (\S+)/;

/**
 * Split a Lean file into its top-level `def` and `theorem` declarations. A
 * declaration runs until the next line that starts at column 0, so this
 * reads the layout that the examples use, not Lean's full grammar.
 */
export function declarations(text: string): Declaration[] {
  const lines = text.split('\n');
  const found: Declaration[] = [];
  for (let i = 0; i < lines.length; i++) {
    const m = declStart.exec(lines[i]!);
    if (m == null) continue;
    let end = i + 1;
    while (end < lines.length && (lines[end] === '' || /^\s/.test(lines[end]!))) end++;
    let docStart = i;
    if (i > 0 && lines[i - 1]!.endsWith('-/')) {
      docStart = i - 1;
      while (docStart > 0 && !lines[docStart]!.startsWith('/--')) docStart--;
    }
    const doc =
      docStart < i
        ? lines
            .slice(docStart, i)
            .join('\n')
            .replace(/^\/--\s*/, '')
            .replace(/\s*-\/$/, '')
            .replace(/\s*\n\s*/g, ' ')
        : null;
    found.push({
      kind: m[1] as 'def' | 'theorem',
      name: m[2]!,
      doc,
      text: lines.slice(i, end).join('\n').trimEnd(),
    });
  }
  return found;
}

/** A claim: a `def … : Prop` in a spec file. */
export interface Claim {
  readonly name: string;
  readonly doc: string | null;
  /** The proposition, the text after `:=`. */
  readonly statement: string;
}

export const isSpec = (f: WorkspaceFile) => f.path.endsWith('.spec.lean');
export const isProof = (f: WorkspaceFile) => f.path.endsWith('.proof.lean');

export function claims(files: readonly WorkspaceFile[]): Claim[] {
  return files.filter(isSpec).flatMap((f) =>
    declarations(f.text)
      .filter((d) => d.kind === 'def' && /^def \S+ : Prop/.test(d.text))
      .map((d) => ({
        name: d.name,
        doc: d.doc,
        statement: d.text.slice(d.text.indexOf(':=') + 2).trim(),
      })),
  );
}

/** The theorems and helper definitions of the proof files. */
export const proofDeclarations = (files: readonly WorkspaceFile[]): Declaration[] =>
  files.filter(isProof).flatMap((f) => declarations(f.text));

/**
 * One Lean file that imports only `Init`: the Go Spec, then the generated
 * code, the claims and the proofs, then a check of each claim. The check
 * stands in for `#audit_claims`, which needs `import Lean`:
 * `example : Spec.c := Proof.c` fails unless the theorem has exactly the
 * claim's type, and `#print axioms` lists what the theorem relies on.
 */
export function bundle(goSpec: string, files: readonly WorkspaceFile[], claimNames: readonly string[]): string {
  const body = (text: string) =>
    text
      .split('\n')
      .filter((line) => !line.startsWith('import ') && !line.startsWith('#audit_claims'))
      .join('\n');
  const parts = [`-- tolean/Go/Spec/Basic.lean\n${body(goSpec)}`].concat(
    files.map((f) => `-- ${f.path}\n${body(f.text)}`),
  );
  const checks = claimNames.map((c) => `example : Spec.${c} := Proof.${c}\n#print axioms Proof.${c}`);
  return [...parts, '-- claim checks', ...checks].join('\n\n') + '\n';
}
