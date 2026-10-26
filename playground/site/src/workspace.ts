import type { WorkspaceFile } from './lean.ts';

/** A workspace: an example, or one the viewer made with "New workspace". */
export type Workspace =
  | { readonly kind: 'example'; readonly name: string; readonly files: readonly WorkspaceFile[] }
  | { readonly kind: 'user'; readonly id: string; readonly name: string; readonly files: readonly WorkspaceFile[] };

export interface ExampleData {
  readonly goSpec: string;
  readonly examples: readonly { readonly name: string; readonly files: readonly WorkspaceFile[] }[];
}

/** Tolean writes these files, so the editor shows them read-only. */
export const isGenerated = (path: string) => path.startsWith('src/') && path.endsWith('.lean');

/** The files of a new workspace: a small Go function, one claim and its proof. */
export function newWorkspaceFiles(): WorkspaceFile[] {
  return [
    {
      path: 'tolean.json',
      text: `{
  "go": {
    "sources": ["src/*.go"],
    "overrides": [{ "sources": ["src/*.go"], "output": "src/Main.lean", "namespace": "Main" }]
  }
}
`,
    },
    {
      path: 'src/main.go',
      text: `package main

// Max returns the larger of a and b.
func Max(a int64, b int64) int64 {
	if a < b {
		return b
	}
	return a
}
`,
    },
    {
      path: 'theorems/Main.spec.lean',
      text: `import src.Main

namespace Spec
open Main

/-- \`Max\` returns a value at least as large as each argument. -/
def max_upper_bound : Prop :=
  ∀ a b : Int, a ≤ Max a b ∧ b ≤ Max a b

end Spec
`,
    },
    {
      path: 'theorems/Main.proof.lean',
      text: `import tolean.Audit
import theorems.«Main.spec»

namespace Proof
open Main

theorem max_upper_bound : Spec.max_upper_bound := by
  intro a b
  unfold Max
  split <;> omega

end Proof

#audit_claims Spec Proof
`,
    },
  ];
}

const storageKey = 'tolean-playground-workspaces';

/** The viewer's own workspaces, kept in this browser only. */
export function loadUserWorkspaces(): Workspace[] {
  try {
    const raw = localStorage.getItem(storageKey);
    return raw == null ? [] : (JSON.parse(raw) as Workspace[]);
  } catch {
    return [];
  }
}

export function saveUserWorkspaces(workspaces: readonly Workspace[]): void {
  try {
    localStorage.setItem(storageKey, JSON.stringify(workspaces.filter((w) => w.kind === 'user')));
  } catch {
    // Storage can be blocked; the workspace then lasts only for this visit.
  }
}
