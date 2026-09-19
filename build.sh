#!/bin/sh
# Build Cubo: the proofs first (a broken law stops the build), then the
# game, compiled for this machine (see cc-native.sh). With glslc, the
# compute shader (effs/scene.comp.in) is recompiled into effs/screen.c
# first; without it the SPIR-V already there is used.
#
#   ./build.sh          # PROOF.bend, then ./cubo
#   ./build.sh bench    # also the headless benchmark, ./bench
#
# Bend 2 is $BEND, else ~/.bend/bin/bend (where its installer puts it), else
# the bend on PATH -- which must be Bend 2: Bend 1 (bend-lang 0.2) shares
# the name.
set -e
cd "$(dirname "$0")"
export BEND_NO_TELEMETRY="${BEND_NO_TELEMETRY:-1}"
if [ -z "${BEND:-}" ]; then
  if [ -x "$HOME/.bend/bin/bend" ]; then
    BEND="$HOME/.bend/bin/bend"
  else
    BEND=bend
  fi
fi
case "$("$BEND" --version 2>/dev/null)" in
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
echo "built ./cubo"
