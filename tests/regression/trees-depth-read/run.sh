#!/bin/sh
set -eu
root=$(CDPATH= cd -- "$(dirname -- "$0")/../../.." && pwd)
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT HUP INT TERM
python3 "$root/tests/regression/trees-depth-read/generate.py" "$root" "$work"
${CC:-cc} -std=c11 -O1 -g -fsanitize=address,undefined -fno-omit-frame-pointer \
  "$work/depth.c" -o "$work/depth-c"
env -u LSAN_OPTIONS UBSAN_OPTIONS=halt_on_error=1 "$work/depth-c" > "$work/c.out"
cd "$root"
if ! lake env lean --run "$work/Depth.lean" > "$work/lean.out"; then
  cat "$work/lean.out"
  exit 1
fi
diff -u "$work/c.out" "$work/lean.out"
printf '%s\n' 'PASS: six C/Lean depth cases agree; source check requires the selected-field reload'
