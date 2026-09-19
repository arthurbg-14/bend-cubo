#!/bin/sh
# clang tuned for this machine, for `CC=./cc-native.sh bend main.bend -o cubo`:
# -march=native opens the machine's whole instruction set; -ffp-contract=off
# keeps Bend's float semantics (no fused multiply-adds).
exec clang -march=native -ffp-contract=off "$@"
