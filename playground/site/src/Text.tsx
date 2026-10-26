/** Text from the workspace, shown outside the editor: doc comments and Lean code. */
import { highlightCode, classHighlighter } from '@lezer/highlight';
import { Marked } from 'marked';
import { type ReactNode, useMemo } from 'react';

import { leanLanguage } from './editor/lean.ts';

const escapeHtml = (text: string) =>
  text.replace(/[&<>"']/g, (c) => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' })[c]!);

/**
 * Markdown for doc comments. A share link can carry any text, so raw HTML
 * shows as text, and a link or an image shows only its words.
 */
const markdown = new Marked({
  async: false,
  renderer: {
    html: ({ text }) => escapeHtml(text),
    link({ tokens }) {
      return this.parser.parseInline(tokens);
    },
    image: ({ text }) => escapeHtml(text),
  },
});

/** One doc comment, with its inline Markdown: code, emphasis and the like. */
export function DocText({ text, className }: { text: string; className?: string }) {
  const html = useMemo(() => markdown.parseInline(text) as string, [text]);
  return <p className={className} dangerouslySetInnerHTML={{ __html: html }} />;
}

/** Lean code, coloured with the same `tok-*` classes as the editor. */
export function LeanCode({ text, className }: { text: string; className?: string }) {
  const nodes = useMemo(() => {
    const out: ReactNode[] = [];
    highlightCode(
      text,
      leanLanguage.parser.parse(text),
      classHighlighter,
      (piece, classes) => out.push(classes === '' ? piece : <span key={out.length} className={classes}>{piece}</span>),
      () => out.push('\n'),
    );
    return out;
  }, [text]);
  return <pre className={className == null ? 'code' : `code ${className}`}>{nodes}</pre>;
}
