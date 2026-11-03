// The docs site. `pages.ts` finds the pages and `links.ts` fixes their links.
// The site is served under /tolean/docs/, next to the playground.

import fs from 'node:fs';
import path from 'node:path';
import { defineConfig } from 'vitepress';
import { checkAnchors, copyFiles, linksPlugin } from './links.ts';
import { categories, githubRepo, readPages, repoRoot, writeGenerated } from './pages.ts';

const base = '/tolean/docs/';

// A page that moved keeps its old URL working: the key is the old URL and the
// value is the new one, both without the base, such as
// '/guides/layout': '/project-layout'.
const redirects: Record<string, string> = {
  '/decisions/lean-not-smt': '/decisions/2026-10-25-lean-not-smt',
};

const pages = readPages();
writeGenerated(pages);

// GitHub's anchor for a heading, so that a link written for GitHub works on
// the site too: lowercase, without punctuation, with a hyphen for each space.
const slugify = (heading: string) =>
  heading
    .trim()
    .toLowerCase()
    .replace(/[^\p{L}\p{M}\p{N}\p{Pc} -]/gu, '')
    .replace(/ /g, '-');

export default defineConfig({
  base,
  title: 'Tolean',
  description: 'Translate source code into Lean 4, so that proofs about a program are about its real source.',
  cleanUrls: true,
  lastUpdated: false,
  // VitePress adds the base to the theme's logo, but not to a link in `head`.
  head: [
    ['link', { rel: 'icon', href: `${base}favicon.ico`, sizes: '16x16 32x32 48x48' }],
    ['link', { rel: 'icon', href: `${base}icon-192.png`, type: 'image/png', sizes: '192x192' }],
    ['link', { rel: 'apple-touch-icon', href: `${base}apple-touch-icon.png` }],
  ],
  rewrites: Object.fromEntries(pages.filter((p) => p.file !== p.page).map((p) => [p.file, p.page])),
  markdown: {
    anchor: { slugify },
    config: linksPlugin(pages),
  },
  themeConfig: {
    logo: '/logo.png',
    nav: [
      { text: 'Playground', link: 'https://shihangw.github.io/tolean/' },
      { text: 'GitHub', link: githubRepo },
    ],
    sidebar: categories
      .map((category) => ({
        text: category,
        items: pages.filter((p) => p.category === category).map((p) => ({ text: p.title, link: p.link })),
      }))
      .filter((group) => group.items.length > 0),
    outline: { level: [2, 3] },
    search: { provider: 'local' },
  },
  vite: {
    plugins: [
      {
        // In `vitepress dev`, keep the README's copy and the front page current.
        name: 'tolean-generated-pages',
        configureServer(server) {
          server.watcher.add(path.join(repoRoot, 'README.md'));
          server.watcher.on('change', (file) => {
            if (file.endsWith('.md')) writeGenerated();
          });
        },
      },
    ],
  },
  buildEnd(site) {
    checkAnchors(site.outDir);
    copyFiles(site.outDir);
    for (const [from, to] of Object.entries(redirects)) {
      const target = base + to.replace(/^\//, '');
      const file = path.join(site.outDir, from.endsWith('/') ? from + 'index.html' : from + '.html');
      fs.mkdirSync(path.dirname(file), { recursive: true });
      fs.writeFileSync(
        file,
        `<!doctype html><meta charset="utf-8"><link rel="canonical" href="${target}">` +
          `<meta http-equiv="refresh" content="0; url=${target}"><a href="${target}">${target}</a>\n`,
      );
    }
  },
});
