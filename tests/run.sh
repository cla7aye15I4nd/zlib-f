#!/usr/bin/env bash
# Differential test: for every driver listed in tests/list.txt, run the REAL C function and the Lean
# translation on the same inputs and compare the outputs byte for byte.
#
#   ZLIB_SRC=<zlib checkout>  bash tests/run.sh      # builds the patched copy of zlib, then tests
#   ZLIB_BUILD=<dir>          bash tests/run.sh      # reuse a copy made by build-zlib.sh
#   ONLY=<name>               run only that list entry
#   SAN=1                     build zlib and the C drivers with ASan+UBSan (and run them so)
# Exit status: 0 all equal, 1 a difference (the first one is printed), 2 a setup error.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
export PATH="$HOME/.elan/bin:$PATH"
build="$here/build"
sfx=""; cflags=""
if [ "${SAN:-0}" = 1 ]; then sfx="-san"; cflags="-fsanitize=address,undefined -fno-sanitize-recover=undefined -g"; fi
ZLIB_BUILD=${ZLIB_BUILD:-$build/zlib$sfx}
if [ ! -f "$ZLIB_BUILD/libz.a" ]; then
  [ -n "${ZLIB_SRC:-}" ] || { echo "run.sh: set ZLIB_SRC (a zlib checkout) or ZLIB_BUILD" >&2; exit 2; }
  CFLAGS="$cflags" bash "$here/build-zlib.sh" "$ZLIB_SRC" "$ZLIB_BUILD"
fi
ZLIB_BUILD=$(cd "$ZLIB_BUILD" && pwd)
echo "zlib under test: patches applied: $(tr '\n' ' ' < "$ZLIB_BUILD/PATCHES_APPLIED")"
mkdir -p "$build/bin$sfx" "$build/data"
cd "$here"
names=$(grep -v '^[[:space:]]*\(#\|$\)' list.txt)
total=0
for name in $names; do
  [ -z "${ONLY:-}" ] || [ "$ONLY" = "$name" ] || continue
  cc -O2 -Wall -Wextra $cflags -I"$ZLIB_BUILD" "c/$name.c" "$ZLIB_BUILD/libz.a" -o "$build/bin$sfx/c_$name"
  lake build "difftest_$name" >"$build/lake_$name.log" 2>&1 || { cat "$build/lake_$name.log"; echo "run.sh: lake build failed for $name" >&2; exit 2; }
  python3 "gen/$name.py" > "$build/data/$name.in"
  in="$build/data/$name.in"
  "$build/bin$sfx/c_$name" < "$in" > "$build/data/$name.c.out"
  .lake/build/bin/difftest_$name < "$in" > "$build/data/$name.lean.out"
  nin=$(grep -c . "$in"); nc=$(grep -c . "$build/data/$name.c.out"); nl=$(grep -c . "$build/data/$name.lean.out")
  if [ "$nin" != "$nc" ] || [ "$nin" != "$nl" ]; then
    echo "DIFFERENCE ($name): $nin inputs, $nc C results, $nl Lean results"; exit 1
  fi
  if ! cmp -s "$build/data/$name.c.out" "$build/data/$name.lean.out"; then
    n=$(awk 'NR==FNR{a[NR]=$0;next} a[FNR]!=$0{print FNR; exit}' "$build/data/$name.c.out" "$build/data/$name.lean.out")
    echo "DIFFERENCE ($name) at input line $n:"
    echo "  input : $(sed -n "${n}p" "$in" | cut -c1-300) (line length $(sed -n "${n}p" "$in" | wc -c))"
    echo "  C     : $(sed -n "${n}p" "$build/data/$name.c.out")"
    echo "  Lean  : $(sed -n "${n}p" "$build/data/$name.lean.out")"
    echo "  files : $in  $build/data/$name.c.out  $build/data/$name.lean.out"
    exit 1
  fi
  echo "== $name: $nin inputs, outputs identical"
  awk '{print $1}' "$in" | sort | uniq -c | awk '{printf "     %-20s %s inputs\n", $2, $1}'
  total=$((total + nin))
done
echo "PASS: $total inputs, C and Lean agree byte for byte"

# A consumed byte can contain unchecked lookahead after the output fills.
if [ -z "${ONLY:-}" ] || [ "$ONLY" = inflate-deferred-distance ]; then
  ZLIB_BUILD="$ZLIB_BUILD" bash "$here/regression/inflate-deferred-distance/run.sh"
fi
