{
  description = "tolean: translate source code to Lean 4 and prove things about it";

  # Lean 4.30.0.
  inputs.nixpkgs.url = "github:nixos/nixpkgs/2fcb964de67fcf60b43471c55d5d99e61a9ccb5a";

  outputs =
    { nixpkgs, ... }:
    let
      systems = [
        "aarch64-darwin"
        "x86_64-darwin"
        "aarch64-linux"
        "x86_64-linux"
      ];
      forEachSystem = f: nixpkgs.lib.genAttrs systems (system: f nixpkgs.legacyPackages.${system});
      # The JS engines the Spec is tested on: every Node release line still
      # maintained. A law or model holds only for the engines it passes on.
      engines = pkgs: [
        pkgs.nodejs_22
        pkgs.nodejs_24
      ];
    in
    {
      # `nix develop`, then `lake build --wfail`. The shell's C compiler can
      # link the `tolean` executable on macOS, which Lean alone cannot.
      #
      # nixpkgs' Lean has no C compiler of its own, so Lake compiles Lean's C
      # output with the shell's $CC. The shell uses clang, as Lean's own
      # releases do. On Linux the default would be GCC, which compiles this
      # C much more slowly at -O3.
      devShells = forEachSystem (pkgs: {
        default = pkgs.mkShell.override { stdenv = pkgs.clangStdenv; } {
          packages = [
            pkgs.lean4
            pkgs.nodejs_24
            # pnpm 10, which wrote the lockfiles.
            pkgs.pnpm_10
            # go/parser is the reference for the Go front end (tests/go).
            pkgs.go
            # A real PostgreSQL is the reference for the SQL translator (tests/sql).
            pkgs.postgresql
            # `tolean chain graph` prints DOT; `dot -Tsvg` draws it.
            pkgs.graphviz
          ];
        };
        # `nix develop .#docs`: only what builds the docs site (docs/), so
        # the docs check in CI does not wait for Lean, Go or PostgreSQL.
        docs = pkgs.mkShell {
          packages = [
            pkgs.nodejs_24
            pkgs.pnpm_10
          ];
        };
        # `nix develop .#wasm`: the toolchain that builds the translator as
        # WebAssembly for the playground (wasm/build.sh).
        wasm = pkgs.mkShell {
          packages = [
            pkgs.lean4
            pkgs.nodejs_24
            pkgs.pnpm_10
            pkgs.emscripten
            pkgs.cmake
            pkgs.git
          ];
          # Emscripten writes its cache next to itself, which the Nix store forbids.
          shellHook = ''
            export EM_CACHE="$PWD/.emcache"
          '';
        };
      });

      # `nix run .#test-engines`, from the repository root after
      # `pnpm install` in tests/typescript: the JS number laws, bigint
      # division and the interpreter against Node, on every engine.
      apps = forEachSystem (pkgs: {
        test-engines = {
          type = "app";
          program = toString (
            pkgs.writeShellScript "test-engines" ''
              set -eu
              cd tests/typescript
              export PATH=${pkgs.lean4}/bin:$PATH
              for node in ${pkgs.lib.concatMapStringsSep " " (n: "${n}/bin/node") (engines pkgs)}; do
                echo "== node $($node --version)"
                $node node_modules/vitest/vitest.mjs run
              done
            ''
          );
        };
      });
    };
}
