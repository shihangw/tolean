import type { ClaimStatus } from './checker.ts';
import type { Claim, Declaration } from './lean.ts';

interface Props {
  readonly claims: readonly Claim[];
  readonly proofs: readonly Declaration[];
  readonly statuses: ReadonlyMap<string, ClaimStatus>;
}

function Badge({ status }: { status: ClaimStatus }) {
  switch (status.kind) {
    case 'unchecked':
      return <span className="badge unchecked">not checked</span>;
    case 'checking':
      return <span className="badge checking">checking…</span>;
    case 'proved':
      return <span className="badge proved">✓ proved</span>;
    case 'broken':
      return <span className="badge broken">✗ broken</span>;
    default: {
      const never: never = status;
      return never;
    }
  }
}

/**
 * The claims first, because a person must read them. Each proof is folded
 * under its claim, and the helper lemmas sit in their own group.
 */
export function Claims({ claims, proofs, statuses }: Props) {
  const claimNames = new Set(claims.map((c) => c.name));
  const lemmas = proofs.filter((d) => !claimNames.has(d.name));
  return (
    <div className="claims">
      <h2>Claims</h2>
      {claims.length === 0 && <p className="muted">No claims yet. Add a `def … : Prop` to a .spec.lean file.</p>}
      {claims.map((claim) => {
        const status = statuses.get(claim.name) ?? { kind: 'unchecked' };
        const proof = proofs.find((d) => d.name === claim.name);
        return (
          <section key={claim.name} className="claim">
            <header>
              <code className="claim-name">{claim.name}</code>
              <Badge status={status} />
            </header>
            {claim.doc != null && <p className="claim-doc">{claim.doc}</p>}
            <pre className="claim-statement">{claim.statement}</pre>
            {status.kind === 'broken' && <p className="claim-reason">{status.reason}</p>}
            {status.kind === 'proved' && (
              <p className="muted">Relies on the axioms {status.axioms.join(', ') || 'none'}.</p>
            )}
            <details>
              <summary>{proof == null ? 'No proof yet' : 'Proof'}</summary>
              {proof != null && <pre className="proof">{proof.text}</pre>}
            </details>
          </section>
        );
      })}
      {lemmas.length > 0 && (
        <details className="lemmas">
          <summary>Supporting lemmas ({lemmas.length})</summary>
          {lemmas.map((d) => (
            <div key={d.name}>
              {d.doc != null && <p className="muted">{d.doc}</p>}
              <pre className="proof">{d.text}</pre>
            </div>
          ))}
        </details>
      )}
    </div>
  );
}
