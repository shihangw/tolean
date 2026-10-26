import type { ClaimStatus, EngineState } from './checker.ts';
import type { Progress } from './download.ts';
import { Icon } from './icons.tsx';
import { type Claim, type Declaration, type WorkspaceFile, declarationAt, isProof, isSpec } from './lean.ts';
import { DocText, LeanCode } from './Text.tsx';

interface Props {
  readonly claims: readonly Claim[];
  readonly proofs: readonly Declaration[];
  readonly statuses: ReadonlyMap<string, ClaimStatus>;
  readonly files: readonly WorkspaceFile[];
  readonly engine: EngineState;
  readonly checking: boolean;
  readonly onCheck: () => void;
  readonly onOpen: (path: string, line: number) => void;
}

const mb = (bytes: number) => (bytes / 1e6).toFixed(0);

function DownloadBar({ progress }: { progress: Progress }) {
  const { loaded, total } = progress;
  const label =
    total == null ? `${mb(loaded)} MB` : loaded >= total ? 'Starting Lean…' : `${mb(loaded)} of ${mb(total)} MB`;
  return (
    <div className="download">
      <progress value={total == null ? undefined : loaded} max={total ?? undefined} />
      <span>{label}</span>
    </div>
  );
}

/** What the Lean in the page is doing, and the button that starts it. */
function Engine({ engine, checking, onCheck }: Pick<Props, 'engine' | 'checking' | 'onCheck'>) {
  switch (engine.kind) {
    case 'off':
      return (
        <div className="engine">
          <div className="engine-text">
            <b>Check the proofs in your browser.</b> Lean is a download of about 44 MB, and the browser keeps it
            after the first visit.
          </div>
          {!checking && (
            <button type="button" className="btn accent" onClick={onCheck}>
              <Icon name="play" size={14} />
              Check proofs
            </button>
          )}
        </div>
      );
    case 'loading':
      return (
        <div className="engine">
          <div className="engine-text">
            <b>Downloading Lean.</b> The browser keeps it after the first visit.
          </div>
          <DownloadBar progress={engine.progress} />
        </div>
      );
    case 'ready':
      return (
        <p className="engine-note">
          Lean checks the proofs as you edit. It is an unofficial WebAssembly build of a newer Lean than CI uses, and
          CI checks the same proofs with the pinned Lean.
        </p>
      );
    case 'failed':
      return (
        <div className="engine failed">
          <Icon name="alert" />
          <div className="engine-text">Lean could not run in this browser: {engine.message}</div>
        </div>
      );
    default: {
      const never: never = engine;
      return never;
    }
  }
}

function StatusChip({ status }: { status: ClaimStatus }) {
  switch (status.kind) {
    case 'unchecked':
      return <span className="chip">Not checked</span>;
    case 'checking':
      return (
        <span className="chip info">
          <span className="spinner" />
          Checking
        </span>
      );
    case 'proved':
      return (
        <span className="chip ok">
          <Icon name="check" size={12} />
          Proved
        </span>
      );
    case 'broken':
      return (
        <span className="chip err">
          <Icon name="x" size={12} />
          Broken
        </span>
      );
    default: {
      const never: never = status;
      return never;
    }
  }
}

/** A reason such as `theorems/Sort.proof.lean:12: unsolved goals`, with a link to its line. */
function Reason({ reason, onOpen }: { reason: string; onOpen: Props['onOpen'] }) {
  const m = /^([^:\s]+):(\d+): ([\s\S]*)$/.exec(reason);
  return (
    <div className="reason">
      <span>{m == null ? reason : m[3]}</span>
      {m != null && (
        <button type="button" className="link mono" onClick={() => onOpen(m[1]!, Number(m[2]))}>
          {m[1]}:{m[2]}
        </button>
      )}
    </div>
  );
}

function Summary({ claims, statuses }: Pick<Props, 'claims' | 'statuses'>) {
  const proved = claims.filter((c) => statuses.get(c.name)?.kind === 'proved').length;
  const broken = claims.filter((c) => statuses.get(c.name)?.kind === 'broken').length;
  if (claims.length === 0) return null;
  if (broken > 0) return <span className="chip err">{broken} broken</span>;
  if (proved === claims.length) return <span className="chip ok">All {proved} proved</span>;
  return (
    <span className="chip">
      {proved} of {claims.length} proved
    </span>
  );
}

/**
 * The claims first, because a person must read them. Each card links to its
 * proof in the editor, and the helper lemmas sit in their own group.
 */
export function Claims(props: Props) {
  const { claims, proofs, statuses, files, onOpen } = props;
  const claimNames = new Set(claims.map((c) => c.name));
  const lemmas = proofs.filter((d) => !claimNames.has(d.name));
  return (
    <div className="claims">
      <div className="panel-head">
        <h2>Claims</h2>
        <Summary claims={claims} statuses={statuses} />
      </div>
      <Engine engine={props.engine} checking={props.checking} onCheck={props.onCheck} />
      {claims.length === 0 && (
        <p className="empty">
          No claims yet. A claim is a <code>def … : Prop</code> in a <code>.spec.lean</code> file.
        </p>
      )}
      {claims.map((claim) => {
        const status = statuses.get(claim.name) ?? { kind: 'unchecked' };
        const proof = declarationAt(files, claim.name, isProof);
        const spec = declarationAt(files, claim.name, isSpec);
        return (
          <article key={claim.name} className={`claim ${status.kind}`}>
            <header>
              <button
                type="button"
                className="claim-name mono"
                title="Show the claim in its spec file"
                onClick={() => spec != null && onOpen(spec.path, spec.line)}
              >
                {claim.name}
              </button>
              <StatusChip status={status} />
            </header>
            {claim.doc != null && <DocText className="doc" text={claim.doc} />}
            <LeanCode className="statement" text={claim.statement} />
            {status.kind === 'broken' && <Reason reason={status.reason} onOpen={onOpen} />}
            <footer>
              {status.kind === 'proved' && (
                <span className="axioms" title="The axioms that the proof relies on">
                  {status.axioms.length === 0 ? (
                    <span className="muted">No axioms</span>
                  ) : (
                    status.axioms.map((a) => (
                      <code key={a} className="axiom">
                        {a}
                      </code>
                    ))
                  )}
                </span>
              )}
              <span className="grow" />
              {proof == null ? (
                <span className="muted">No proof yet</span>
              ) : (
                <button type="button" className="link" onClick={() => onOpen(proof.path, proof.line)}>
                  Open proof
                  <Icon name="arrow" size={13} />
                </button>
              )}
            </footer>
          </article>
        );
      })}
      {lemmas.length > 0 && (
        <details className="lemmas">
          <summary>
            <Icon name="chevron" size={14} />
            Supporting lemmas <span className="count">{lemmas.length}</span>
          </summary>
          <ul>
            {lemmas.map((d) => {
              const at = declarationAt(files, d.name, isProof);
              return (
                <li key={d.name}>
                  <button
                    type="button"
                    className="lemma"
                    onClick={() => at != null && onOpen(at.path, at.line)}
                    disabled={at == null}
                  >
                    <span className="lemma-kind">{d.kind}</span>
                    <code>{d.name}</code>
                  </button>
                  {d.doc != null && <DocText className="doc small" text={d.doc} />}
                </li>
              );
            })}
          </ul>
        </details>
      )}
    </div>
  );
}
