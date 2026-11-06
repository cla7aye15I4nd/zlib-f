#!/usr/bin/env bash
# Regression runner: compress/compress2 allocation behaviour, old vs new
# translation, plus the uncompress2_z specification-review case and
# AddressSanitizer/UBSan witnesses.
#
# Self-contained from a checkout: the workspace root is derived from this
# script's location or given as the first argument. Generated evidence goes to
# regression-evidence/compress-allocation/ (second argument, optional).
#
# Differential-test evidence only, not proof.
set -euo pipefail

here=$(cd "$(dirname "$0")" && pwd)
WS=${1:-$(cd "$here/../../.." && pwd)}
EV=${2:-"$WS/regression-evidence/compress-allocation"}
T=${3:-3600}
export LB_SLOTS=${LB_SLOTS:-2} LB_MIN_GB=${LB_MIN_GB:-8}

echo "workspace: $WS"
echo "evidence:  $EV"
[ -f "$WS/lakefile.toml" ] && [ -f "$WS/tests/build-zlib.sh" ] \
    || { echo "not a workspace: $WS" >&2; exit 2; }

mkdir -p "$EV/build" "$EV/rows" "$EV/scratch"

echo "== [1/8] building patched pinned zlib (plain) =="
timeout "$T" bash "$WS/tests/build-zlib.sh" "$WS/zlib" "$EV/build/zlib" \
    | tee "$EV/build/build-plain.log"

echo "== [2/8] compiling and running the C driver =="
cc -O1 -g -Wall -Wextra -I"$EV/build/zlib" "$here/driver.c" \
    "$EV/build/zlib/libz.a" -Wl,--wrap=malloc -Wl,--wrap=free \
    -o "$EV/build/driver_plain" 2> "$EV/build/driver_plain.cc.log"
timeout "$T" "$EV/build/driver_plain" | tee "$EV/rows/c.txt"

echo "== [3/8] building the Lean modules (imports only) =="
( cd "$WS" && timeout "$T" env LB_SLOTS=2 LB_MIN_GB=8 \
    lake build ZlibF.Zlib.«compress.c» ZlibF.Zlib.«uncompr.c» ) \
    | tee "$EV/build/lake-build.log"

echo "== [4/8] running the Lean driver (current translation) =="
( cd "$WS" && timeout "$T" lake env lean --run "$here/Driver.lean" ) \
    | tee "$EV/rows/lean-current.txt"

echo "== [5/8] scratch copy of the old translation (allocZStream) =="
# Private cache copy for the scratch run. Imported main-cache files are read only.
rm -rf "$EV/scratch/cache"
mkdir -p "$EV/scratch/cache"
cp -a "$WS/.lake/build/lib" "$EV/scratch/cache/lib"
# the ONLY change: `let strm ← allocLocalZ` -> `let strm ← allocZStream`
mkdir -p "$EV/scratch/ScratchOld"
sed 's/let strm ← allocLocalZ/let strm ← allocZStream/' \
    "$WS/ZlibF/Zlib/compress.c.lean" > "$EV/scratch/ScratchOld/Compress.lean"
if cmp -s "$WS/ZlibF/Zlib/compress.c.lean" "$EV/scratch/ScratchOld/Compress.lean"; then
    echo "scratch copy is identical to the current source: the replacement failed" >&2
    exit 1
fi
diff <(grep -c 'let strm ← allocZStream' "$EV/scratch/ScratchOld/Compress.lean") \
     <(echo 1) >/dev/null \
    || { echo "scratch copy changed more than one line" >&2; exit 1; }
# the old driver: Driver.lean with the compress import redirected
sed 's|^import ZlibF.Zlib.«compress.c»$|import ScratchOld.Compress|' \
    "$here/Driver.lean" > "$EV/scratch/DriverOld.lean"
LP=$(cd "$WS" && lake env printenv LEAN_PATH)
# compile the scratch module once, into the scratch cache copy (never the main .lake)
( cd "$EV/scratch" && timeout "$T" \
    env LEAN_PATH="$EV/scratch/cache/lib/lean:$LP" \
    lean -o ScratchOld/Compress.olean ScratchOld/Compress.lean ) \
    2>&1 | tee "$EV/build/scratch-old-cc.log"
( cd "$WS" && timeout "$T" \
    env LEAN_PATH="$EV/scratch:$EV/scratch/cache/lib/lean:$LP" \
    lean --run "$EV/scratch/DriverOld.lean" ) | tee "$EV/rows/lean-old.txt"

echo "== [6/8] comparing rows =="
python3 "$here/compare.py" "$EV/rows/c.txt" "$EV/rows/lean-current.txt" \
    "$EV/rows/lean-old.txt" "$EV/rows/compare-report.txt" \
    > "$EV/rows/compare-console.txt"
CMP=$?
cat "$EV/rows/compare-console.txt"

echo "== [7/8] sanitizer build and runs (ASan+UBSan, no suppressions) =="
CFLAGS="-fsanitize=address,undefined -fno-omit-frame-pointer -g -O1" \
    timeout "$T" bash "$WS/tests/build-zlib.sh" "$WS/zlib" "$EV/build/zlib-asan" \
    | tee "$EV/build/build-asan.log"
SAN="-fsanitize=address,undefined -fno-sanitize-recover=all -fno-omit-frame-pointer -g -O1"
cc $SAN -I"$EV/build/zlib-asan" "$here/driver.c" "$EV/build/zlib-asan/libz.a" \
    -Wl,--wrap=malloc -Wl,--wrap=free -o "$EV/build/driver_asan" \
    2> "$EV/build/driver_asan.cc.log"
set +e
env ASAN_OPTIONS=detect_leaks=1 LSAN_OPTIONS= UBSAN_OPTIONS=halt_on_error=1 timeout "$T" "$EV/build/driver_asan" > "$EV/rows/c-asan.txt" 2> "$EV/rows/c-asan.stderr"
DRC=$?
set -e
echo "driver_asan rc=$DRC (stdout rows: $(grep -c '^ROW ' "$EV/rows/c-asan.txt" || true); stderr in rows/c-asan.stderr)" \
    | tee "$EV/rows/asan-summary.txt"
if [ "$DRC" -ne 0 ] || [ -s "$EV/rows/c-asan.stderr" ]; then
    cat "$EV/rows/c-asan.stderr" >&2
    echo "FAIL: sanitizer execution did not complete cleanly" >&2
    exit 1
fi
python3 "$here/compare.py" "$EV/rows/c-asan.txt" "$EV/rows/lean-current.txt" \
    "$EV/rows/lean-old.txt" "$EV/rows/asan-compare-report.txt" > "$EV/rows/asan-compare-console.txt"
cc $SAN -I"$EV/build/zlib-asan" "$here/ubwitness.c" "$EV/build/zlib-asan/libz.a" \
    -o "$EV/build/ubwitness" 2> "$EV/build/ubwitness.cc.log"
for w in compress2 compress; do
    set +e
    env ASAN_OPTIONS=detect_leaks=1 LSAN_OPTIONS= UBSAN_OPTIONS=halt_on_error=1 timeout 120 "$EV/build/ubwitness" "$w" \
        > "$EV/rows/ubwitness-$w.txt" 2> "$EV/rows/ubwitness-$w.stderr"
    URC=$?
    echo "ubwitness $w rc=$URC" | tee -a "$EV/rows/asan-summary.txt"
    set -e
    if [ "$URC" -eq 0 ] || ! grep -Eq 'runtime error: load of null pointer|AddressSanitizer.*SEGV' "$EV/rows/ubwitness-$w.stderr"; then
        echo "FAIL: expected wrapper null-dereference diagnostic was not observed" >&2
        exit 1
    fi
done

echo "== [8/8] done (comparison exit status: $CMP) =="
exit "$CMP"
