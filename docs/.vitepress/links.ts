// A markdown-it plugin that makes the links of the repository's Markdown work
// on the site. A link in a doc is relative to the doc's file in the
// repository, as GitHub reads it. The plugin resolves each one against that
// file, and then:
//
// - a link to a published file becomes a link to its page, anchor included;
// - a link to an image or another file under `docs/` stays relative, so
//   VitePress bundles the file;
// - a link to any other file in the repository becomes a link to that file
//   on GitHub, at the commit that the site was built from.
//
// It does this for Markdown links and images, and for `src` and `href` in
// HTML tags. A link that names a scheme, such as `https:`, stays as it is.
// The plugin also ends each page with a line that names its source file.
//
// VitePress checks that a link's page exists but not that its anchor does.
// So the plugin records each anchor, and `checkAnchors` checks them once the
// pages are built.

import fs from 'node:fs';
import path from 'node:path';
import type MarkdownIt from 'markdown-it';
import type Token from 'markdown-it/lib/token.mjs';
import { commit, docsDir, githubRepo, githubUrl, repoRoot, type Page } from './pages.ts';

interface Anchor {
  from: string;
  link: string;
  hash: string;
}

const anchors: Anchor[] = [];
// The files under `docs/` that pages link to, from `docs/`.
const files = new Set<string>();

const posix = path.posix;
const hasScheme = (url: string) => /^[a-z][a-z0-9+.-]*:/i.test(url) || url.startsWith('//');

export function linksPlugin(pages: Page[]) {
  const bySource = new Map(pages.map((p) => [p.source, p]));
  const byFile = new Map(pages.map((p) => [p.file, p]));

  // The URL that `url`, written in `page`'s source file, should have on the site.
  function resolve(url: string, page: Page): string {
    if (url === '' || hasScheme(url)) return url;
    const split = url.search(/[?#]/);
    const target = split < 0 ? url : url.slice(0, split);
    const hash = split < 0 ? '' : url.slice(split);
    if (target === '') {
      if (hash.startsWith('#')) anchors.push({ from: page.source, link: page.link, hash: hash.slice(1) });
      return url;
    }
    if (target.startsWith('/'))
      throw new Error(`${page.source}: the link "${url}" starts with "/". Write it relative to the file.`);
    const repoPath = posix.normalize(posix.join(posix.dirname(page.source), decodeURI(target)));
    // GitHub shows a folder's README, so a link to the folder is a link to it.
    const linked = bySource.get(repoPath) ?? bySource.get(posix.join(repoPath, 'README.md'));
    if (linked) {
      if (hash.startsWith('#')) anchors.push({ from: page.source, link: linked.link, hash: hash.slice(1) });
      return linked.link + hash;
    }
    const full = path.join(repoRoot, repoPath);
    if (repoPath.startsWith('../') || !fs.existsSync(full))
      throw new Error(`${page.source}: the link "${url}" names ${repoPath}, which does not exist.`);
    if (repoPath.startsWith('docs/')) {
      // VitePress bundles an image, but not a file that a page only links
      // to, so `copyFiles` copies it. The URL is relative to the file that
      // VitePress reads, which for the README's copy is not where the README
      // is. A page's URL has the same folder as its file, so the URL works
      // both for an image and for a copied file.
      files.add(repoPath.slice('docs/'.length));
      const fromDir = posix.dirname(posix.join('docs', page.file));
      const relative = posix.relative(fromDir, repoPath);
      return (relative.startsWith('../') ? relative : './' + relative) + hash;
    }
    return githubUrl(repoPath, fs.statSync(full).isDirectory() ? 'tree' : 'blob') + hash;
  }

  const resolveHtml = (html: string, page: Page) =>
    html.replace(/\b(src|href)=(["'])(.*?)\2/g, (_, attr, quote, url) => `${attr}=${quote}${resolve(url, page)}${quote}`);

  function resolveTokens(tokens: Token[], page: Page) {
    for (const token of tokens) {
      if (token.type === 'link_open') token.attrSet('href', resolve(token.attrGet('href') ?? '', page));
      else if (token.type === 'image') token.attrSet('src', resolve(token.attrGet('src') ?? '', page));
      else if (token.type === 'html_block' || token.type === 'html_inline') token.content = resolveHtml(token.content, page);
      if (token.children) resolveTokens(token.children, page);
    }
  }

  return (md: MarkdownIt) => {
    md.core.ruler.push('tolean-links', (state) => {
      // VitePress gives the rewritten path as `path` and the file as `realPath`,
      // except when it renders for search, which has only `path`.
      const real = state.env.realPath ?? state.env.path;
      const page = byFile.get(path.relative(docsDir, real).split(path.sep).join('/'));
      if (!page) return;
      resolveTokens(state.tokens, page);
      const source = new state.Token('html_block', '', 0);
      source.content =
        `<p class="page-source">This page is <a href="${githubUrl(page.source)}"><code>${page.source}</code></a>` +
        ` at commit <a href="${githubRepo}/commit/${commit}"><code>${commit.slice(0, 7)}</code></a>.</p>\n`;
      state.tokens.push(source);
    });
  };
}

// Copy the files that pages link to into the site, at their paths in `docs/`.
export function copyFiles(outDir: string) {
  for (const file of files) {
    fs.mkdirSync(path.dirname(path.join(outDir, file)), { recursive: true });
    fs.copyFileSync(path.join(docsDir, file), path.join(outDir, file));
  }
}

// The HTML file that VitePress writes for the URL `link`.
const htmlFile = (outDir: string, link: string) =>
  path.join(outDir, link.endsWith('/') ? link + 'index.html' : link + '.html');

// Fail if a link names an anchor that its page does not have.
export function checkAnchors(outDir: string) {
  const ids = new Map<string, Set<string>>();
  const idsOf = (link: string) => {
    let set = ids.get(link);
    if (!set) {
      const html = fs.readFileSync(htmlFile(outDir, link), 'utf8');
      set = new Set([...html.matchAll(/\sid="([^"]+)"/g)].map((m) => m[1]));
      ids.set(link, set);
    }
    return set;
  };
  const dead = anchors.filter((a) => !idsOf(a.link).has(decodeURIComponent(a.hash)));
  if (dead.length > 0)
    throw new Error(
      'Links to anchors that do not exist:\n' +
        [...new Set(dead.map((a) => `  ${a.from}: ${a.link}#${a.hash}`))].join('\n'),
    );
}
