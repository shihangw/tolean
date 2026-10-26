import { useState } from 'react';

import { type FileDiagnostic, oneLine } from './diagnostics.ts';
import { Icon } from './icons.tsx';

interface Props {
  readonly diagnostics: readonly FileDiagnostic[];
  readonly onOpen: (path: string, line: number) => void;
}

/** Every error and warning in the workspace, under the editor. A click shows its line. */
export function Problems({ diagnostics, onOpen }: Props) {
  const [open, setOpen] = useState(true);
  const shown = diagnostics.filter((d) => d.severity !== 'info');
  if (shown.length === 0) return null;
  const errors = shown.filter((d) => d.severity === 'error').length;
  return (
    <section className={open ? 'problems open' : 'problems'} aria-label="Problems">
      <button type="button" className="problems-head" aria-expanded={open} onClick={() => setOpen(!open)}>
        <Icon name="chevron" size={14} className="turn" />
        Problems
        {errors > 0 && <span className="count err">{errors}</span>}
        {shown.length > errors && <span className="count warn">{shown.length - errors}</span>}
      </button>
      {open && (
        <ul>
          {shown.map((d, i) => (
            <li key={`${d.path}:${d.line}:${d.column}:${i}`}>
              <button type="button" className="problem" onClick={() => onOpen(d.path, d.line)}>
                <Icon name={d.severity === 'error' ? 'x' : 'alert'} size={13} className={d.severity} />
                <span className="problem-message">{oneLine(d.message)}</span>
                <span className="problem-where mono">
                  {d.source === 'lean' ? 'Lean' : 'Tolean'} · {d.path}:{d.line}
                </span>
              </button>
            </li>
          ))}
        </ul>
      )}
    </section>
  );
}
