#!/usr/bin/env bash
# Usage: zlib-build-current.sh <build-dir>
# Exit 0 when <build-dir> holds a libz.a that build-zlib.sh made from the current ../patches/*.patch
# (same names, same contents, same order); exit 1 otherwise. The differential test and the harness reuse a
# build directory across commits, so a tree built before a patch was added or changed must not be reused.
set -euo pipefail
dir=${1:?usage: zlib-build-current.sh <build-dir>}
here=$(cd "$(dirname "$0")" && pwd)
[ -f "$dir/libz.a" ] && [ -f "$dir/PATCHES_SHA256" ] || exit 1
expected=$(bash "$here/build-zlib.sh" --patch-digest)
[ "$(cat "$dir/PATCHES_SHA256")" = "$expected" ]
