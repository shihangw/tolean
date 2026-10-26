import type { FileDiagnostic } from './diagnostics.ts';
import { type Language, languageOf } from './editor/languages.ts';
import { Icon } from './icons.tsx';
import type { WorkspaceFile } from './lean.ts';
import { isGenerated } from './workspace.ts';

const badges: Readonly<Record<Language, string>> = { typescript: 'TS', go: 'GO', lean: 'LN', json: '{}', text: 'TXT' };

/** The folders of a workspace, in the order the tree shows them, with what each one holds. */
const folders = [
  { name: 'src', about: 'The source code, and the Lean that Tolean writes from it' },
  { name: 'theorems', about: 'The claims in .spec.lean files, and their proofs in .proof.lean files' },
] as const;

interface Props {
  readonly files: readonly WorkspaceFile[];
  readonly open: string | null;
  readonly diagnostics: readonly FileDiagnostic[];
  readonly onOpen: (path: string) => void;
}

function FileRow({ path, label, active, problems, onOpen }: {
  path: string;
  label: string;
  active: boolean;
  problems: number;
  onOpen: Props['onOpen'];
}) {
  const language = languageOf(path);
  const generated = isGenerated(path);
  return (
    <button
      type="button"
      className={active ? 'file active' : 'file'}
      aria-current={active ? 'page' : undefined}
      title={generated ? `${path}, written by Tolean` : path}
      onClick={() => onOpen(path)}
    >
      <span className={`badge ${language}`}>{badges[language]}</span>
      <span className="file-label">{label}</span>
      {problems > 0 && <span className="count err">{problems}</span>}
      {generated && <Icon name="lock" size={13} className="faint" />}
    </button>
  );
}

/** The files of the workspace, by folder. */
export function Files({ files, open, diagnostics, onOpen }: Props) {
  const problems = (path: string) => diagnostics.filter((d) => d.path === path && d.severity === 'error').length;
  const topLevel = files.filter((f) => !f.path.includes('/'));
  return (
    <nav className="files" aria-label="Files">
      {folders.map((folder) => (
        <div key={folder.name} className="folder">
          <div className="folder-name" title={folder.about}>
            <Icon name="folder" size={14} />
            {folder.name}
          </div>
          {files
            .filter((f) => f.path.startsWith(`${folder.name}/`))
            .map((f) => (
              <FileRow
                key={f.path}
                path={f.path}
                label={f.path.slice(folder.name.length + 1)}
                active={f.path === open}
                problems={problems(f.path)}
                onOpen={onOpen}
              />
            ))}
        </div>
      ))}
      {topLevel.length > 0 && (
        <div className="folder">
          {topLevel.map((f) => (
            <FileRow
              key={f.path}
              path={f.path}
              label={f.path}
              active={f.path === open}
              problems={problems(f.path)}
              onOpen={onOpen}
            />
          ))}
        </div>
      )}
      <p className="files-note">
        <Icon name="lock" size={12} /> Tolean writes the Lean in <code>src/</code> from the source next to it.
      </p>
    </nav>
  );
}
