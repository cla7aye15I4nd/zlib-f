#!/bin/bash
# Proof mutants for the stream-management functions of inflate.c: a mutated translation must make the proof
# modules fail to check, with the error in a proof file of that function (ZlibF/Proof/inflate.c.*).
# Run from the repository root on the build host. The translation is restored after each mutant.
set -u
T=ZlibF/Zlib/inflate.c.lean
cp "$T" /tmp/inflate.c.lean.orig
trap 'cp /tmp/inflate.c.lean.orig "$T"' EXIT
fail=0
# name @ old @ new @ proof module that must fail
mutants=(
 "check-mode-range@s.mode < HEAD || s.mode > SYNC@s.mode < HEAD || s.mode > MEM@inflate.c.base"
 "resetkeep-sane@sane := 1, back := -1@sane := 0, back := -1@inflate.c.base"
 "update-big@if copy >= s.wsize then@if copy > s.wsize then@inflate.c.uw"
 "end-no-free-window@if s.window != .null then ZFREEB strm s.window@if False then ZFREEB strm s.window@inflate.c.end"
 "prime-limit@if bits > 16 ||@if bits > 17 ||@inflate.c.misc2"
 "init-size@if stream_size != 112 then@if stream_size != 113 then@inflate.c.start"
 "setdict-adler@if dictid != s.check then@if dictid == s.check then@inflate.c.dict"
 "getdict-copy@(s.whave - s.wnext).toNat@(s.whave).toNat@inflate.c.dict"
)
for m in "${mutants[@]}"; do
  IFS='@' read -r name old new mod <<< "$m"
  cp /tmp/inflate.c.lean.orig "$T"
  python3 - "$T" "$old" "$new" <<'PY'
import sys
p, old, new = sys.argv[1:4]
s = open(p).read()
if old not in s:
    print("MUTANT NOT APPLICABLE:", old); sys.exit(2)
open(p, 'w').write(s.replace(old, new, 1))
PY
  [ $? = 2 ] && { echo "$name: not applicable"; fail=1; continue; }
  out=$(lake build "ZlibF.Proof.«$mod»" 2>&1)
  if echo "$out" | grep -q "^error: ZlibF/Proof/inflate.c"; then echo "$name: detected"
  else echo "$name: NOT DETECTED"; fail=1; fi
done
exit $fail
