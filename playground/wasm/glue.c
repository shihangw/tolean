/* The page's entry point into the translator (Web.lean): a C string in, a
   malloc'd C string out. Based on the glue of github.com/nathsou/ariadne. */
#include <emscripten.h>
#include <lean/lean.h>
#include <stdlib.h>
#include <string.h>

lean_object* initialize_web_Web(uint8_t builtin);
lean_object* tolean_web_translate(lean_object* input);
void lean_initialize_runtime_module(void);
void lean_io_mark_end_initialization(void);

/* The modules that Web uses from the Lean package (Lean.Data.Json) call
   lean_initialize, which natively also sets up the elaborator's C++ side.
   The translator never elaborates, so starting the runtime is enough. */
void lean_initialize(void) { lean_initialize_runtime_module(); }

EMSCRIPTEN_KEEPALIVE int tolean_init(void) {
  lean_initialize_runtime_module();
  lean_object* res = initialize_web_Web(1);
  int ok = lean_io_result_is_ok(res);
  lean_dec_ref(res);
  lean_io_mark_end_initialization();
  return ok;
}

EMSCRIPTEN_KEEPALIVE char* tolean_translate(const char* input) {
  lean_object* s = tolean_web_translate(lean_mk_string(input));
  size_t n = lean_string_size(s);
  char* out = malloc(n);
  memcpy(out, lean_string_cstr(s), n);
  lean_dec_ref(s);
  return out;
}
