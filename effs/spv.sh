#!/bin/sh
# effs/scene.comp.in (with effs/font.glsl put in at its #include), the
# compute shader, into the SPIR-V words at the end of effs/screen.c
# (between its scene.spv lines), so the game builds without a shader
# compiler. build.sh runs it when glslc is installed.
set -e
cd "$(dirname "$0")"
src=$(mktemp --suffix=.comp)
words=$(mktemp)
trap 'rm -f "$src" "$words" screen.c.new' EXIT
sed -e '/#include "font.glsl"/r font.glsl' -e '/#include "font.glsl"/d' scene.comp.in > "$src"
glslc -O --target-env=vulkan1.0 -mfmt=num "$src" -o "$words"
awk -v words="$words" '
  /^\/\/ scene\.spv begin/ { print; while ((getline line < words) > 0) print "  " line; skip = 1; next }
  /^\/\/ scene\.spv end/ { skip = 0 }
  !skip { print }
' screen.c > screen.c.new
if ! cmp -s screen.c screen.c.new; then
  cat screen.c.new > screen.c
fi
