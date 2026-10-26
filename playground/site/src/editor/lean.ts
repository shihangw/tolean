/**
 * Lean 4 for CodeMirror: a highlighter, folds by indentation, and the
 * backslash abbreviations that Lean's editors use to type symbols such as ∀
 * and →. The highlighter reads tokens line by line, so it is not Lean's
 * grammar. It only has to colour the code that Tolean writes and the proofs
 * that people write next to it.
 */
import { type Completion, type CompletionContext, type CompletionResult } from '@codemirror/autocomplete';
import { type EditorState, type Extension } from '@codemirror/state';
import { EditorView } from '@codemirror/view';
import { LanguageSupport, StreamLanguage, type StringStream, foldService } from '@codemirror/language';
import { tags as t } from '@lezer/highlight';

const keywords = new Set(
  (
    'def theorem lemma abbrev structure inductive instance class where with match fun let have show from by at ' +
    'in if then else do return namespace end open section variable import set_option noncomputable private ' +
    'protected partial unsafe mutual deriving example calc termination_by decreasing_by universe macro syntax ' +
    'elab attribute local scoped export axiom opaque for unless break continue mut'
  ).split(' '),
);

/** Words that start a declaration; the next word is the name it defines. */
const declarers = new Set(['def', 'theorem', 'lemma', 'abbrev', 'structure', 'inductive', 'instance', 'class', 'axiom', 'opaque']);

const tactics = new Set(
  (
    'intro intros exact refine apply simp simp_all dsimp simpa omega decide rfl unfold split rename_i rcases ' +
    'obtain rintro cases induction constructor contradiction subst revert generalize rw rewrite rwa assumption ' +
    'exists use left right trivial by_cases by_contra repeat first all_goals any_goals try skip next case funext ' +
    'ext congr specialize suffices change exfalso nofun native_decide injection symm trans calc conv'
  ).split(' '),
);

interface State {
  /** How deep the reader is inside nested block comments. */
  comment: number;
  /** The open comment is a doc comment, `/--` or `/-!`. */
  doc: boolean;
  /** The last word declared a name, so the next word is that name. */
  declaring: boolean;
}

function blockComment(stream: StringStream, state: State): string {
  const kind = state.doc ? 'docComment' : 'comment';
  while (!stream.eol()) {
    if (stream.match('/-')) state.comment++;
    else if (stream.match('-/')) {
      state.comment--;
      if (state.comment === 0) break;
    } else stream.next();
  }
  return kind;
}

const identifier =
  /^(?:«[^»]*»|[A-Za-z_Ͱ-Ͽᴀ-ᶿ][\w'!?Ͱ-Ͽ₀-₉]*)(?:\.(?:«[^»]*»|[A-Za-z_][\w'!?₀-₉]*))*/;

const leanLanguage = StreamLanguage.define<State>({
  name: 'lean',
  startState: () => ({ comment: 0, doc: false, declaring: false }),
  token(stream, state) {
    if (state.comment > 0) return blockComment(stream, state);
    if (stream.eatSpace()) return null;
    if (stream.match('--')) {
      stream.skipToEnd();
      return 'lineComment';
    }
    if (stream.match('/-')) {
      state.comment = 1;
      state.doc = stream.match(/^[-!]/) != null;
      return blockComment(stream, state);
    }
    if (stream.match(/^"(?:[^"\\]|\\.)*"?/)) return 'string';
    if (stream.match(/^'(?:[^'\\]|\\.)'/)) return 'string';
    if (stream.match(/^@\[[^\]]*\]/) || stream.match(/^#[a-z_]+/)) return 'meta';
    if (stream.match(/^\d+(?:\.\d+)?/)) return 'number';
    if (stream.match(/^[⊢→←↔∀∃λ≤≥≠∧∨¬×∘▸⟨⟩∣∈∉⊆·↑]/)) return 'operator';
    const word = stream.match(identifier) as RegExpMatchArray | null;
    if (word != null) {
      const w = word[0];
      if (state.declaring) {
        state.declaring = false;
        return 'definition';
      }
      if (keywords.has(w)) {
        state.declaring = declarers.has(w);
        return 'keyword';
      }
      if (tactics.has(w)) return 'tactic';
      if (w === 'true' || w === 'false' || w === 'True' || w === 'False') return 'bool';
      if (/^[A-Z]/.test(w)) return 'typeName';
      return 'variableName';
    }
    if (stream.match(/^[()[\]{}]/)) return 'bracket';
    if (stream.match(/^[:=<>+\-*/|&!^%$?~.,;]+/)) return 'operator';
    stream.next();
    return null;
  },
  languageData: {
    commentTokens: { line: '--', block: { open: '/-', close: '-/' } },
    closeBrackets: { brackets: ['(', '[', '{', '⟨', '"'] },
  },
  tokenTable: {
    definition: t.definition(t.variableName),
    tactic: t.macroName,
    lineComment: t.lineComment,
    docComment: t.docComment,
    bracket: t.bracket,
  },
});

/**
 * Fold a line together with the lines below it that are indented further,
 * which is how a Lean declaration or tactic block is laid out.
 */
const foldByIndent = foldService.of((state: EditorState, from: number) => {
  const line = state.doc.lineAt(from);
  const indent = (text: string) => text.length - text.trimStart().length;
  if (line.text.trim() === '') return null;
  const base = indent(line.text);
  let end = line.number;
  for (let n = line.number + 1; n <= state.doc.lines; n++) {
    const next = state.doc.line(n);
    if (next.text.trim() === '') continue;
    if (indent(next.text) <= base) break;
    end = n;
  }
  return end > line.number ? { from: line.to, to: state.doc.line(end).to } : null;
});

/** The abbreviations that Lean's editors expand after a backslash. */
export const abbreviations: Readonly<Record<string, string>> = {
  to: '→', r: '→', imp: '→', l: '←', gets: '←', iff: '↔', lr: '↔',
  forall: '∀', all: '∀', ex: '∃', exists: '∃', fun: 'λ', lam: 'λ',
  and: '∧', or: '∨', not: '¬', neg: '¬', ne: '≠', le: '≤', ge: '≥',
  x: '×', times: '×', in: '∈', notin: '∉', sub: '⊆', subseteq: '⊆', ssub: '⊂',
  cup: '∪', cap: '∩', union: '∪', inter: '∩', comp: '∘', circ: '∘',
  '<': '⟨', '>': '⟩', langle: '⟨', rangle: '⟩', 'f<': '«', 'f>': '»',
  '|-': '⊢', vdash: '⊢', '.': '·', cdot: '·', tr: '▸', u: '↑', top: '⊤', bot: '⊥',
  N: 'ℕ', Z: 'ℤ', Q: 'ℚ', R: 'ℝ', equiv: '≡', '==': '≡', '~': '∼', inf: '∞',
  a: 'α', b: 'β', g: 'γ', d: 'δ', e: 'ε', s: 'σ', t: 'τ', p: 'π', o: 'ω', S: 'Σ', P: 'Π',
  '0': '₀', '1': '₁', '2': '₂', '3': '₃', '4': '₄', '5': '₅', '6': '₆', '7': '₇', '8': '₈', '9': '₉',
};

const abbreviationOptions: Completion[] = Object.entries(abbreviations).map(([name, symbol]) => ({
  label: `\\${name}`,
  displayLabel: `${symbol}  \\${name}`,
  apply: symbol,
  type: 'text',
}));

/** Suggest the symbols whose abbreviation starts with what follows the backslash. */
function completeAbbreviation(context: CompletionContext): CompletionResult | null {
  const before = context.matchBefore(/\\[^\s\\]*/);
  if (before == null) return null;
  return { from: before.from, options: abbreviationOptions, validFor: /^\\[^\s\\]*$/ };
}

const wordOptions: Completion[] = [
  ...[...keywords].map((label) => ({ label, type: 'keyword' })),
  ...[...tactics].map((label) => ({ label, type: 'function', detail: 'tactic' })),
];

/** Suggest Lean's keywords and tactics, and the names declared in this file. */
function completeWord(context: CompletionContext): CompletionResult | null {
  const word = context.matchBefore(/[A-Za-z_][\w'.]*/);
  if (word == null || (word.from === word.to && !context.explicit)) return null;
  // After a backslash, the person is typing an abbreviation.
  if (context.state.sliceDoc(word.from - 1, word.from) === '\\') return null;
  const declared = new Set<string>();
  for (const m of context.state.doc.toString().matchAll(/^(?:theorem|def|lemma|abbrev)\s+(\S+)/gm)) declared.add(m[1]!);
  const names = [...declared].map((label) => ({ label, type: 'variable' }));
  return { from: word.from, options: [...names, ...wordOptions], validFor: /^[\w'.]*$/ };
}

/**
 * Expand an abbreviation when the person types a space or a bracket after it,
 * as Lean's editors do. `\to ` becomes `→ `.
 */
const expandOnBoundary = EditorView.inputHandler.of((view, from, to, text) => {
  if (!/^[\s()[\]{},:]$/.test(text) || from !== to) return false;
  const line = view.state.doc.lineAt(from);
  const m = /\\([^\s\\]+)$/.exec(line.text.slice(0, from - line.from));
  const symbol = m == null ? undefined : abbreviations[m[1]!];
  if (m == null || symbol == null) return false;
  const start = from - m[0].length;
  view.dispatch({
    changes: { from: start, to, insert: symbol + text },
    selection: { anchor: start + symbol.length + text.length },
    userEvent: 'input.type',
  });
  return true;
});

/** Lean with its folds, abbreviations and completions. */
export function lean(): Extension {
  return [
    new LanguageSupport(leanLanguage, [foldByIndent]),
    leanLanguage.data.of({ autocomplete: completeAbbreviation }),
    leanLanguage.data.of({ autocomplete: completeWord }),
    expandOnBoundary,
  ];
}

export { leanLanguage };
