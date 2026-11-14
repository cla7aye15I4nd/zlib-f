#!/usr/bin/env bash
# Usage: build-zlib.sh <zlib-checkout> <output-dir>
# Copies the zlib checkout (the upstream submodule, at the pinned commit) to <output-dir>, applies
# ../patches/*.patch there in name order, and builds libz.a (static, default configuration).
# The checkout itself is never modified. Set CFLAGS to add flags (e.g. sanitizers).
#        build-zlib.sh --patch-digest   prints the digest of the current patches (one line per patch).
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
patches="$here/../patches"
# One line per patch, in application order: its SHA-256 and name. Recorded in PATCHES_SHA256 of every build,
# so that a reused build directory can be checked against the current patches (zlib-build-current.sh).
patch_digest() {
  local p
  for p in $(ls "$patches"/*.patch 2>/dev/null | LC_ALL=C sort); do
    printf '%s  %s\n' "$(python3 -c 'import hashlib,sys; print(hashlib.sha256(open(sys.argv[1],"rb").read()).hexdigest())' "$p")" "$(basename "$p")"
  done
}
if [ "${1:-}" = "--patch-digest" ]; then patch_digest; exit 0; fi
src=${1:?usage: build-zlib.sh <zlib-checkout> <output-dir>}
out=${2:?usage: build-zlib.sh <zlib-checkout> <output-dir>}
[ -f "$src/zlib.h" ] || { echo "build-zlib: $src is not a zlib checkout" >&2; exit 2; }
case "$out" in "$src"|"$src"/*) echo "build-zlib: output must be outside the checkout" >&2; exit 2;; esac
rm -rf "$out"
mkdir -p "$out"
(cd "$src" && tar --exclude=.git -cf - .) | tar -C "$out" -xf -
: > "$out/PATCHES_APPLIED"
for p in $(ls "$patches"/*.patch 2>/dev/null | LC_ALL=C sort); do
  echo "applying $(basename "$p")"
  (cd "$out" && patch -p1 --batch --forward < "$p")
  basename "$p" >> "$out/PATCHES_APPLIED"
done
patch_digest > "$out/PATCHES_SHA256"
cd "$out"
./configure --static >configure.log 2>&1 || { cat configure.log; exit 1; }
make libz.a >make.log 2>&1 || { cat make.log; exit 1; }
echo "built $out/libz.a with patches: $(tr '\n' ' ' < PATCHES_APPLIED)"
