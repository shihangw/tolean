// Runs Lean, compiled to WebAssembly, in a worker. Based on the persistent
// worker of github.com/cauli/lean4-wasm-in-browser (Apache-2.0), whose Lean
// build this is.
//
// Messages in:  { type: 'start', base, wasm, files: [{ path, data }] }
//               { type: 'check', id, code }
//
// `wasm` is the bytes of lean.wasm, which the page downloads gzipped and
// unpacks once. This lean.js reads neither Module.wasmBinary nor
// Module.instantiateWasm; it always fetches lean.wasm. So the worker answers
// that one fetch with the bytes it was given. The page runs one check per worker: after a check that
// unfolds a recursive definition, this Lean build fails every later check, so
// the page starts a fresh worker instead. See
// https://github.com/cauli/lean4-wasm-in-browser/issues/4.
// Messages out: { type: 'ready' } | { type: 'error', message }
//               { type: 'result', id, diagnostics, elapsed }
//
// Lean prints each diagnostic as one JSON line on stdout, so a check collects
// the lines that `lean_wasm_compile` prints while it runs.

let capture = null;
let output = null;

function onLine(text) {
  if (capture == null) {
    self.postMessage({ type: 'log', text });
    return;
  }
  if (text.startsWith('{')) {
    try {
      const d = JSON.parse(text);
      if (d && typeof d.severity === 'string') {
        capture.push(d);
        return;
      }
    } catch {
      // Not a diagnostic.
    }
  }
  output.push(text);
}

function mkdirp(FS, dir) {
  let current = '';
  for (const part of dir.split('/').filter(Boolean)) {
    current += '/' + part;
    try {
      FS.mkdir(current);
    } catch {
      // It exists.
    }
  }
}

function leanString(text) {
  const ptr = Module.stringToNewUTF8(text);
  const obj = Module._lean_mk_string(ptr);
  Module._free(ptr);
  return obj;
}

// The device may refuse a large shared memory, so try smaller sizes.
function pickMemory() {
  const page = 65536;
  for (const mb of [2048, 1536, 1024, 768]) {
    try {
      const memory = new WebAssembly.Memory({ initial: (mb * 1024 * 1024) / page, maximum: 65536, shared: true });
      return { wasmMemory: memory, INITIAL_MEMORY: mb * 1024 * 1024 };
    } catch {
      // Try a smaller size.
    }
  }
  return {};
}

function start(base, wasm, files) {
  self.Module = {
    ...pickMemory(),
    noInitialRun: true,
    locateFile: (p) => base + '/' + p,
    // The threads that this worker starts load lean.js, not this file.
    mainScriptUrlOrBlob: base + '/lean.js',
    print: onLine,
    printErr: onLine,
    preRun: [
      () => {
        const FS = Module.FS;
        Module.ENV['LEAN_PATH'] = '/lib/lean';
        for (const d of ['/lib/lean', '/workspace', '/bin']) mkdirp(FS, d);
        for (const f of files) {
          const full = '/lib/lean/' + f.path;
          mkdirp(FS, full.slice(0, full.lastIndexOf('/')));
          FS.writeFile(full, new Uint8Array(f.data));
        }
        files = null;
        FS.chdir('/workspace');
      },
    ],
    onRuntimeInitialized: () => {
      try {
        Module._lean_initialize_runtime_module();
        Module._lean_initialize();
        Module._lean_io_mark_end_initialization();
        if (Module._lean_init_task_manager) Module._lean_init_task_manager();
        if (Module._lean_enable_initializer_execution) Module._lean_enable_initializer_execution();
        const res = Module._lean_init_search_path();
        if ((Module.getValue(res + 7, 'i8') & 0xff) !== 0) throw new Error('lean_init_search_path failed');
        // The first check imports Init, which takes a few seconds; do it now,
        // after Emscripten has finished starting, not inside this callback.
        setTimeout(() => {
          check('#check Nat');
          self.postMessage({ type: 'ready' });
        }, 0);
      } catch (e) {
        self.postMessage({ type: 'error', message: 'Lean did not start: ' + (e && e.message ? e.message : e) });
      }
    },
    onAbort: (what) => self.postMessage({ type: 'error', message: 'Lean stopped: ' + (what || 'unknown') }),
  };
  const wasmUrl = new URL(base + '/lean.wasm', self.location.href).href;
  const realFetch = self.fetch.bind(self);
  self.fetch = (input, init) => {
    const url = new URL(typeof input === 'string' ? input : input.url, self.location.href).href;
    if (url === wasmUrl) return Promise.resolve(new Response(wasm, { headers: { 'Content-Type': 'application/wasm' } }));
    return realFetch(input, init);
  };
  try {
    importScripts(base + '/lean.js');
  } catch (e) {
    self.postMessage({ type: 'error', message: 'Could not load lean.js: ' + (e && e.message ? e.message : e) });
  }
}

function check(code) {
  capture = [];
  output = [];
  const t0 = performance.now();
  const res = Module._lean_wasm_compile(leanString(code), leanString('/workspace/Bundle.lean'));
  const failed = (Module.getValue(res + 7, 'i8') & 0xff) !== 0;
  if (failed) Module._lean_io_result_show_error(res);
  const diagnostics = capture;
  capture = null;
  if (failed) {
    const detail = output.join(' ').trim();
    diagnostics.push({ severity: 'error', data: 'Lean could not run the check' + (detail ? ': ' + detail : '.') });
  }
  const lines = output;
  output = null;
  return { diagnostics, output: lines, elapsed: performance.now() - t0 };
}

self.onmessage = (event) => {
  const msg = event.data;
  if (msg.type === 'start') start(msg.base, msg.wasm, msg.files);
  else if (msg.type === 'check') self.postMessage({ type: 'result', id: msg.id, ...check(msg.code) });
};
