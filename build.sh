#!/bin/sh
# Build Cubo: the proofs first (a broken law stops the build), then the
# game, compiled for this machine (see cc-native.sh). With glslc, the
# compute shader (effs/scene.comp.in) is recompiled into effs/screen.c
# first; without it the SPIR-V already there is used.
#
#   ./build.sh          # PROOF.bend, then ./cubo
#   ./build.sh bench    # also the headless benchmark, ./bench
#   ./build.sh test     # also the collision test, ./clash, and runs it
#   ./build.sh chunks   # the collision test of the crowd in chunks
#   ./build.sh cem      # 100 mil cubos de verdade, medidos (./cem)
#
# Bend 2 is $BEND, else ~/.bend/bin/bend (where its installer puts it), else
# the bend on PATH -- which must be Bend 2: Bend 1 (bend-lang 0.2) shares
# the name.
set -e
cd "$(dirname "$0")"
export BEND_NO_TELEMETRY="${BEND_NO_TELEMETRY:-1}"
# The checker walks the tick's whole term; with rotation in, that needs
# more stack than the 8 MB a shell hands out. `unlimited` does not do it
# (Linux keeps the main stack where it is), so ask for a big finite one,
# and tell the engine behind bend to use it.
ulimit -s 1000000 2>/dev/null || true
export BUN_JSC_maxPerThreadStackUsage="${BUN_JSC_maxPerThreadStackUsage:-805306368}"
if [ -z "${BEND:-}" ]; then
  if [ -x "$HOME/.bend/bin/bend" ]; then
    BEND="$HOME/.bend/bin/bend"
  else
    BEND=bend
  fi
fi
# `bend version` since 2.0.11; older ones only answer --version
case "$("$BEND" version 2>/dev/null || "$BEND" --version 2>/dev/null)" in
  "bend 2."*) ;;
  *) echo "build.sh: $BEND is not Bend 2 (install it: curl -fsSL https://bend-lang.com/install.sh | sh)" >&2
     exit 1 ;;
esac
"$BEND" PROOF.bend
if command -v glslc > /dev/null; then
  ./effs/spv.sh
fi
CC="$(pwd)/cc-native.sh" "$BEND" main.bend -o cubo
if [ "${1:-}" = bench ]; then
  CC="$(pwd)/cc-native.sh" "$BEND" bench.bend -o bench
fi
if [ "${1:-}" = cem ]; then
  CC="$(pwd)/cc-native.sh" "$BEND" bench100.bend -o cem
  ./cem
fi
if [ "${1:-}" = chunks ]; then
  CC="$(pwd)/cc-native.sh" "$BEND" chunks.bend -o chunks
  ./chunks
fi
if [ "${1:-}" = test ]; then
  CC="$(pwd)/cc-native.sh" "$BEND" clash.bend -o clash
  ./clash
  CC="$(pwd)/cc-native.sh" "$BEND" fast.bend -o fast
  ./fast
fi
echo "built ./cubo"
