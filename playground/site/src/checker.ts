/** The result of checking one claim. */
export type ClaimStatus =
  | { readonly kind: 'unchecked' }
  | { readonly kind: 'checking' }
  | { readonly kind: 'proved'; readonly axioms: readonly string[] }
  | { readonly kind: 'broken'; readonly reason: string };

/** Something that checks a bundled Lean file and reports on each claim. */
export interface Checker {
  readonly description: string;
  check(bundle: string, claims: readonly string[]): Promise<ReadonlyMap<string, ClaimStatus>>;
}

/**
 * The checker until Lean in WebAssembly is wired up: it reports every claim
 * as not checked, so the page never shows a claim as proved without a check.
 */
export const noChecker: Checker = {
  description: 'Lean does not run in the browser yet, so no claim is checked here.',
  check: async (_bundle, claims) => new Map(claims.map((c) => [c, { kind: 'unchecked' } as const])),
};

/**
 * Read a claim's status from Lean's output for the bundle. A claim is proved
 * when `#print axioms` lists no `sorryAx`: Lean keeps a failed proof as
 * `sorry`, so a claim that relies on a broken lemma is caught here too.
 */
export function statusFromAxioms(axiomLine: string | undefined, errors: readonly string[]): ClaimStatus {
  if (axiomLine == null) return { kind: 'broken', reason: errors[0] ?? 'Lean did not check this claim.' };
  const axioms = /\[(.*)\]/.exec(axiomLine)?.[1]?.split(',').map((a) => a.trim()).filter(Boolean) ?? [];
  if (axioms.includes('sorryAx')) {
    return { kind: 'broken', reason: errors[0] ?? 'The proof relies on a step that failed.' };
  }
  return { kind: 'proved', axioms };
}
