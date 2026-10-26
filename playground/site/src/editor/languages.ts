/** The language of each kind of workspace file, chosen by its extension. */
import { go } from '@codemirror/lang-go';
import { javascript } from '@codemirror/lang-javascript';
import { StreamLanguage } from '@codemirror/language';
import { type Extension } from '@codemirror/state';

import { lean } from './lean.ts';

export type Language = 'typescript' | 'go' | 'lean' | 'json' | 'text';

export function languageOf(path: string): Language {
  if (path.endsWith('.ts')) return 'typescript';
  if (path.endsWith('.go')) return 'go';
  if (path.endsWith('.lean')) return 'lean';
  if (path.endsWith('.json')) return 'json';
  return 'text';
}

export const languageNames: Readonly<Record<Language, string>> = {
  typescript: 'TypeScript',
  go: 'Go',
  lean: 'Lean 4',
  json: 'JSON',
  text: 'Plain text',
};

/** JSON, read one token at a time. A string followed by `:` is a key. */
const json = StreamLanguage.define<null>({
  name: 'json',
  startState: () => null,
  token(stream) {
    if (stream.eatSpace()) return null;
    if (stream.match(/^"(?:[^"\\]|\\.)*"?/)) return stream.match(/^\s*:/, false) ? 'propertyName' : 'string';
    if (stream.match(/^-?\d+(?:\.\d+)?(?:[eE][+-]?\d+)?/)) return 'number';
    if (stream.match(/^(?:true|false)\b/)) return 'bool';
    if (stream.match(/^null\b/)) return 'null';
    if (stream.match(/^[{}[\]]/)) return 'bracket';
    stream.next();
    return 'punctuation';
  },
  languageData: { closeBrackets: { brackets: ['{', '[', '"'] } },
});

export function languageSupport(language: Language): Extension {
  switch (language) {
    case 'typescript':
      return javascript({ typescript: true });
    case 'go':
      return go();
    case 'lean':
      return lean();
    case 'json':
      return json;
    case 'text':
      return [];
    default: {
      const never: never = language;
      return never;
    }
  }
}

/** Go code is indented with tabs; the other languages use two spaces. */
export const indentFor = (language: Language) => (language === 'go' ? '\t' : '  ');
