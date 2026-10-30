# Plan: a docs site built from the repository

**Status:** planned, not built · **Date:** 2026-10-29

The Markdown files in the repository are the only source of the docs. On
every push to `main`, CI builds them into a site with VitePress and publishes
it on GitHub Pages, next to the playground. Nobody edits the site, because it
has nothing to edit. A change to a doc is a pull request, like a change to
the code.

The docs stay in the repository for three reasons. A change to a doc goes
through the same pull request as the code it describes. Agents read
checked-in files, so they see the docs too. And CI can check every link.

VitePress fits because the playground is already a Vite site built with
pnpm, so the docs need no new toolchain. It resolves relative links between
Markdown files and keeps folders as paths. It also has full-text search, and
it fails the build on a dead link.

## What the site publishes

The site publishes `README.md` and every Markdown file under `docs/`. It
leaves out `AGENTS.md` and `.agents/`, because those files are for agents.

The site lives in `docs/.vitepress/`, with `docs/` as its source folder.
VitePress serves a folder's `index.md` as the folder's page, so its
`rewrites` option maps each `README.md` to the folder:

| Source | Page |
|---|---|
| `README.md` | `/docs/overview` |
| `docs/typescript/README.md` | `/docs/typescript/` |
| `docs/plans/effects.md` | `/docs/plans/effects` |
| `docs/vs_aeneas.md` | `/docs/vs_aeneas` |

The root `README.md` sits outside `docs/`, so a build step copies it into the
source folder as `overview.md` before VitePress runs. The copy is not
committed.

A page's path follows from its file's path, so moving a file changes its
URL. Moving a doc is rare, and when it happens, the pull request adds a
redirect in the config.

## Links and images

VitePress resolves a link from one Markdown file to another, anchor
included, so `../typescript/README.md#certificates` works as written. It
also serves an image from where it lives, so `![…](verification.svg)` in
`docs/typescript/README.md` needs no change. Two kinds of link need a small
plugin for the Markdown parser:

- A link to a file that the site does not publish, such as
  `tolean/TypeScript/Spec/Eval.lean`, becomes a link to that file on GitHub,
  at the commit that the site was built from.
- A link or image in the root `README.md` is relative to the repository
  root, but its copy sits in `docs/`. The plugin resolves the copy's links
  against the original's path. This covers the HTML tags too, such as
  `<img src="docs/images/banner.webp">`.

A link that starts with `http` stays as it is.

## Index and categories

Each page gets its category automatically, from where its file lives:

| Category | Files |
|---|---|
| Overview | `README.md` |
| Languages | `docs/<language>/README.md` |
| Guides | Other files in `docs/`, such as `project-layout.md` |
| Comparisons | `docs/vs_*.md` |
| Plans | `docs/plans/` |
| Decisions | `docs/decisions/` |

The config reads the files when the site builds, and it makes two things
from them:

- **The sidebar.** It lists every page under its category, so every page
  shows the whole index.
- **The front page.** It lists every page by category, with its title and
  its first sentence. The title is the file's first heading.

A plan also shows its status, which the config reads from the line
`**Status:** …` at the top of the file. So a reader sees at once which plans
are built. The build fails for a plan without a status line, so every plan
keeps one.

A file can set its category with a comment on its first line, such as
`<!-- category: Guides -->`. A comment does not show when GitHub renders the
file, which front matter would. The comment is needed only when the folder
gives the wrong category.

Every page ends with a line that names its source file and the commit, and
links to the file on GitHub.

## CI

A repository has one Pages site, and the playground already uses it. The
`wasm` job in `.github/workflows/ci.yml` builds `playground/site/dist` and
uploads it as the Pages artifact, and the `pages` job deploys it. The docs
join that artifact:

1. A new `docs` job builds the site on every pull request and on `main`. So a
   dead link, a clash between two paths or a plan without a status fails the
   pull request. Nothing checks the links of the docs today.
2. On `main`, the `docs` job uploads the built site as an artifact. The
   `wasm` job downloads it into `playground/site/dist/docs/` before it
   uploads the Pages artifact.
3. The `pages` job deploys both, as it does now.

The `docs` job does not wait for the WebAssembly build, so a pull request
that changes only docs gets its check quickly.

## Steps

1. Add VitePress under `docs/.vitepress/` with the rewrites, and build the
   site locally. Check that the three `verification.svg` files and the
   banner show, and that links between pages and their anchors work.
2. Add the step that copies `README.md`, and the plugin for links to files
   that the site does not publish.
3. Add the categories, the sidebar, the front page and the status of plans.
4. Add the `docs` job to CI for pull requests.
5. Add the docs to the Pages artifact on `main`, deploy, and review the site.
   Then link the site from the README.

## Open questions

- Should the site keep the docs of each release, or show only `main`?
- Should a page list the pages that link to it? The config sees every link,
  so it can.
