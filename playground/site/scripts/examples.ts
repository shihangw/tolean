/**
 * Write the page's data: every example under playground/examples, with its
 * files, and the Go Spec that the page bundles with them. The page reads it
 * from public/examples.json. Also copy the service worker that lets GitHub
 * Pages serve the page cross-origin isolated, which the threaded Lean needs.
 */
import { copyFileSync, existsSync, mkdirSync, readFileSync, readdirSync, writeFileSync } from 'node:fs';
import path from 'node:path';

import { exampleFiles, goSpecPath } from '../../bundle.ts';

const site = path.join(import.meta.dirname, '..');
const examplesDir = path.join(site, '../examples');

const examples = readdirSync(examplesDir, { withFileTypes: true })
  .filter((d) => d.isDirectory())
  .map((d) => d.name)
  .sort()
  .map((name) => {
    const dir = path.join(examplesDir, name);
    const { src, theorems } = exampleFiles(dir);
    const config = { path: 'tolean.json', text: readFileSync(path.join(dir, 'tolean.json'), 'utf8') };
    return { name, files: [config, ...src, ...theorems] };
  });

writeFileSync(
  path.join(site, 'public/examples.json'),
  JSON.stringify({ goSpec: readFileSync(goSpecPath, 'utf8'), examples }, null, 2) + '\n',
);
// The translator, from wasm/build.sh, when it has been built.
const translator = path.join(site, '../../wasm/out');
if (existsSync(path.join(translator, 'tolean.js'))) {
  mkdirSync(path.join(site, 'public/translator'), { recursive: true });
  for (const name of ['tolean.js', 'tolean.wasm.bin']) {
    copyFileSync(path.join(translator, name), path.join(site, 'public/translator', name));
  }
} else {
  console.warn('wasm/out has no translator; run wasm/build.sh, or the page shows the committed Lean only');
}
copyFileSync(
  path.join(site, 'node_modules/coi-serviceworker/coi-serviceworker.min.js'),
  path.join(site, 'public/coi-serviceworker.min.js'),
);
console.log(`wrote ${examples.length} examples to public/examples.json`);
