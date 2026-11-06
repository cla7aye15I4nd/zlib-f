#!/usr/bin/env bash
# Two disjoint shards; each selftest owns its source, build cache and positive baselines.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
ZLIB_BUILD=${ZLIB_BUILD:-$here/build/zlib}
if [ ! -f "$ZLIB_BUILD/libz.a" ]; then
  [ -n "${ZLIB_SRC:-}" ] || { echo 'set ZLIB_SRC or ZLIB_BUILD' >&2; exit 2; }
  bash "$here/build-zlib.sh" "$ZLIB_SRC" "$ZLIB_BUILD"
fi
ZLIB_BUILD=$(cd "$ZLIB_BUILD" && pwd)
export ZLIB_BUILD
logs=$(mktemp -d)
pids=()
cleanup() {
  for pid in $(jobs -pr); do kill "$pid" 2>/dev/null || true; done
  rm -rf "$logs"
}
trap cleanup EXIT
for shard in 0 1; do
  MUTATION_SHARD_COUNT=2 MUTATION_SHARD_INDEX="$shard" \
    bash "$here/selftest.sh" > "$logs/$shard.log" 2>&1 &
  pids+=("$!")
done
failed=0
for shard in 0 1; do
  if ! wait "${pids[$shard]}"; then failed=1; fi
  cat "$logs/$shard.log"
done
exit "$failed"
