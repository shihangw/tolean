import { go } from '@codemirror/lang-go';
import { EditorState } from '@codemirror/state';
import { EditorView, basicSetup } from 'codemirror';
import { useEffect, useRef } from 'react';

interface Props {
  readonly path: string;
  readonly text: string;
  readonly readOnly: boolean;
  readonly onChange: (text: string) => void;
}

/** A CodeMirror editor for one file. It starts again when the file changes. */
export function Editor({ path, text, readOnly, onChange }: Props) {
  const host = useRef<HTMLDivElement>(null);
  const onChangeRef = useRef(onChange);
  onChangeRef.current = onChange;

  useEffect(() => {
    if (host.current == null) return;
    const view = new EditorView({
      parent: host.current,
      state: EditorState.create({
        doc: text,
        extensions: [
          basicSetup,
          path.endsWith('.go') ? go() : [],
          EditorState.readOnly.of(readOnly),
          EditorView.updateListener.of((u) => {
            if (u.docChanged) onChangeRef.current(u.state.doc.toString());
          }),
        ],
      }),
    });
    return () => view.destroy();
    // The editor owns the text while it is open; it restarts only for another file.
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [path, readOnly]);

  return <div className="editor" ref={host} />;
}
