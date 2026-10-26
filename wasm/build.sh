#!/usr/bin/env bash
# Build the translator as WebAssembly: wasm/out/tolean.js and
# wasm/out/tolean.wasm.bin (gzipped). The playground and the npm package both
# use it. Run it in the wasm dev shell: `nix develop .#wasm -c wasm/build.sh`.
# TOLEAN_WASM_OUT sets another output directory.
#
# Lean ships no WebAssembly build, so this compiles everything the translator
# runs from C, as github.com/nathsou/ariadne does for its playground:
#   1. Lean's runtime, from the Lean sources at the toolchain's tag, without
#      threads, because the translator needs none;
#   2. the C of the standard library modules that Web imports, which the
#      toolchain's own `lean` generates from the sources it ships;
#   3. the C of Tolean's translator and Web.lean, which Lake generates.
# Lean's code generator writes portable C, so the C that a 64-bit host
# generates compiles for wasm32.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
work=${TOLEAN_WASM_WORK:-$here/.build}
out=${TOLEAN_WASM_OUT:-$here/out}
mkdir -p "$work" "$out"

prefix=$(lean --print-prefix)
version=$(lean --version | sed -E 's/.*version ([0-9.]+).*/\1/')
jobs=$(getconf _NPROCESSORS_ONLN 2>/dev/null || echo 4)

# 1. The runtime.
lean4=$work/lean4-v$version
if [ ! -d "$lean4" ]; then
  git clone --quiet --depth 1 --branch "v$version" https://github.com/leanprover/lean4 "$lean4"
  # No threads, and a stub whose signature differs from its header.
  sed -i.orig 's/set(EMSCRIPTEN_SETTINGS "-s ALLOW_MEMORY_GROWTH=1 -fwasm-exceptions -pthread -flto")/set(EMSCRIPTEN_SETTINGS "-fwasm-exceptions -flto")/; s/string(APPEND LEANC_EXTRA_CC_FLAGS " -pthread")//' \
    "$lean4/src/CMakeLists.txt"
  sed -i.orig 's/^extern "C" LEAN_EXPORT lean_obj_res lean_uv_os_get_group() {/extern "C" LEAN_EXPORT lean_obj_res lean_uv_os_get_group(uint64_t gid) {/' \
    "$lean4/src/runtime/uv/system.cpp"
  # Lean 4.30 builds without threads or libuv only after three more fixes:
  # two stubs whose signatures differ from their headers, and a lock stub
  # that lacks what lean_io_condvar_wait uses.
  sed -i.orig 's/lean_uv_dns_get_info(b_obj_arg name, b_obj_arg service, uint8_t family, int8_t protocol) {/lean_uv_dns_get_info(b_obj_arg name, b_obj_arg service, uint8_t family) {/' \
    "$lean4/src/runtime/uv/dns.cpp"
  perl -0pi.orig -e 's/extern "C" LEAN_EXPORT lean_obj_res lean_uv_event_loop_alive\(\) \{\n    return io_result_mk_error\("lean_uv_event_loop_alive is not supported"\);/extern "C" LEAN_EXPORT uint8_t lean_uv_event_loop_alive() {\n    return 0;/' \
    "$lean4/src/runtime/uv/event_loop.cpp"
  perl -0pi.orig -e 's/template<typename T> class unique_lock \{\npublic:\n    unique_lock\(T const &\) \{\}/template<typename T> class unique_lock {\npublic:\n    unique_lock(T const &) {}\n    unique_lock(T const &, std::adopt_lock_t) {}\n    void release() {}/' \
    "$lean4/src/runtime/thread.h"
fi
runtime=$work/runtime
if [ ! -f "$runtime/lib/lean/libleanrt.a" ]; then
  emcmake cmake -S "$lean4/src" -B "$runtime" -DSTAGE=1 -DMULTI_THREAD=OFF -DUSE_GMP=OFF -DUSE_MIMALLOC=OFF \
    -DCMAKE_BUILD_TYPE=Release >/dev/null
  emmake make -C "$runtime" -j"$jobs" leanrt >/dev/null
fi

# 3, first, because it decides which standard library modules are needed.
(cd "$here" && lake build Web >/dev/null)
closure=$(LEAN_SRC_PATH="$here:$here/..:$prefix/src/lean" node "$here/closure.ts" Web)

# 2. The standard library modules in the closure.
stdlib=$work/stdlib
mkdir -p "$stdlib"
cat > "$stdlib/lakefile.toml" <<TOML
name = "stdlib"
bootstrap = true
srcDir = "$prefix/src/lean"
# Lean builds its own library with this option (src/CMakeLists.txt, kept in
# sync with stdlib_flags.h); without it some of its proofs do not check.
moreLeanArgs = ["-Dbackward.do.legacy=false"]

[[lean_lib]]
name = "Init"

[[lean_lib]]
name = "Std"

[[lean_lib]]
name = "Lean"
TOML
cp "$here/lean-toolchain" "$stdlib/"
targets=$(echo "$closure" | grep -E '^(Init|Std|Lean)(\.|$)' | sed 's/^/+/; s/$/:c/')
(cd "$stdlib" && lake build $targets >/dev/null)

# Compile and link.
objects=$work/obj
cflags="-O3 -DNDEBUG -fwasm-exceptions -I$runtime/include -w"
compile() { # SOURCE OBJECT
  if [ ! "$2" -nt "$1" ]; then mkdir -p "$(dirname "$2")" && emcc $cflags -c "$1" -o "$2"; fi
}
export -f compile
export cflags
for m in $closure; do
  path=$(echo "$m" | tr . /).c
  for dir in "$stdlib/.lake/build/ir" "$here/../.lake/build/ir" "$here/.lake/build/ir"; do
    if [ -f "$dir/$path" ]; then echo "$dir/$path $objects/${path%.c}.o"; break; fi
  done
done | xargs -P "$jobs" -n 2 bash -c 'compile "$0" "$1"'
compile "$here/glue.c" "$objects/glue.o"

expected=$(( $(echo "$closure" | wc -l) + 1 ))
[ "$(find "$objects" -name '*.o' | wc -l)" -eq "$expected" ] ||
  { echo "missing object files: expected $expected" >&2; exit 1; }

rm -f "$out/tolean.js" "$out/tolean.wasm"
em++ -O3 -fwasm-exceptions $(find "$objects" -name '*.o' | sort) \
  "$runtime/lib/lean/libleanrt.a" "$runtime/libuv/src/libuv/libuv.a" \
  -sMODULARIZE=1 -sEXPORT_ES6=1 -sENVIRONMENT=worker,node -sALLOW_MEMORY_GROWTH=1 -sSTACK_SIZE=16MB \
  -sEXPORTED_FUNCTIONS=_tolean_init,_tolean_translate,_free \
  -sEXPORTED_RUNTIME_METHODS=UTF8ToString,stringToNewUTF8,getExceptionMessage -sEXPORT_EXCEPTION_HANDLING_HELPERS \
  -o "$out/tolean.js" 2>&1 | grep -v 'signature mismatch\|>>> defined as' || true
test -f "$out/tolean.wasm"
# The page fetches the gzipped copy and unpacks it, whatever the server does.
gzip -9 -c "$out/tolean.wasm" > "$out/tolean.wasm.bin"
rm "$out/tolean.wasm"
echo "built $(du -h "$out/tolean.wasm.bin" | cut -f1) $out/tolean.wasm.bin (gzipped)"
