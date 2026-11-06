#!/usr/bin/env bash
# Proof mutation check: change one thing in a COPY of a translation file and require that the PROOFS
# of that function no longer check, with the first error inside the expected proof files.
# (tests/selftest.sh is a different check: it needs the differential test to notice.)
#
#   bash tests/audit/proofmut.sh tests/audit/proofmut/adler32.tsv [name-filter-regex]
#
# List format, one mutant per line, fields separated by TAB (lines starting with # are comments):
#   NAME<TAB>FILE<TAB>OLD<TAB>NEW<TAB>PROOF_MODULES[<TAB>same:REASON]    (a literal \n in OLD or NEW is a newline)
#   FILE           translation file, relative to the workspace root (e.g. ZlibF/Zlib/adler32.c.lean)
#   OLD            text that must occur exactly once in FILE; it is replaced by NEW
#   PROOF_MODULES  comma-separated modules under ZlibF/Proof (file name without .lean, e.g. adler32.c);
#                  these are the only targets built, and the first error must be in one of them
#   same:REASON    optional; marks an equivalent mutant: the proofs must still build (SAME)
#   gap:REASON     optional; marks a known hole: the theorems do not cover the mutated code, so the proofs
#                  still build (GAP). It does not fail the run; the reason says what is not proved. When
#                  such a mutant is killed after all, the flag is stale and must be removed.
#
# Verdicts: KILLED (proof error in an expected module: pass), SAME (equivalent mutant, builds: pass),
#   GAP (known hole, see above), SURVIVED (proofs still build: fail), BAD MUTANT (the translation file, or something outside
#   ZlibF/Proof, has the error: fail), WRONG PLACE (error in an unexpected proof module: fail),
#   NO ERROR (build failed without an error line, e.g. timeout: fail), UNEXPECTED (marked same but
#   the build failed: fail), NOT APPLIED (OLD does not occur exactly once: fail).
#
# Environment:
#   PROOFMUT_CACHE    a warm `.lake` directory (default: <workspace>/.lake). It is copied for every mutant
#                     and never modified.
#   PROOFMUT_TIMEOUT  seconds per build (default 3600)
#   PROOFMUT_BASELINE 1 (default): first build the unmutated copy of the listed modules; it must pass
#   PROOFMUT_KEEP     1: keep the temporary copies (default: remove)
#   PROOFMUT_STRICT   1: require the baseline and reject every known proof gap (final acceptance)
# One mutant runs at a time.
set -uo pipefail
here=$(cd "$(dirname "$0")" && pwd)
ws=$(cd "$here/../.." && pwd)
list=${1:?usage: proofmut.sh <list> [name-regex]}
filter=${2:-.}
[ -f "$list" ] || { echo "proofmut.sh: no such list: $list" >&2; exit 2; }
list=$(cd "$(dirname "$list")" && pwd)/$(basename "$list")
export PATH="$HOME/.elan/bin:$PATH"
cache=${PROOFMUT_CACHE:-$ws/.lake}
tmo=${PROOFMUT_TIMEOUT:-3600}
[ -d "$cache" ] || { echo "proofmut.sh: no warm .lake at $cache (set PROOFMUT_CACHE)" >&2; exit 2; }
root=$(mktemp -d "${TMPDIR:-/tmp}/proofmut.XXXXXX")
cleanup() { pkill -P $$ 2>/dev/null; [ "${PROOFMUT_KEEP:-0}" = 1 ] || rm -rf "$root"; }
trap cleanup EXIT
trap 'exit 130' INT TERM

mkcopy() {  # mkcopy <dir>: fresh copy of the workspace with a copy of the warm cache
  mkdir -p "$1"
  (cd "$ws" && tar --exclude=.git --exclude=.lake --exclude=tests/build --exclude=zlib -cf - .) | tar -C "$1" -xf -
  cp -a "$cache" "$1/.lake"
}
targets() {  # targets <comma list> -> lake targets
  local m out=""
  IFS=, read -ra ms <<< "$1"
  for m in "${ms[@]}"; do out="$out ZlibF.Proof.«${m}»"; done
  [ -n "$out" ] || return 1
  echo "$out"
}
build() {  # build <dir> <comma list> <log>
  local target_list
  target_list=$(targets "$2") || return 1
  # shellcheck disable=SC2046
  (cd "$1" && timeout -k 30 "$tmo" lake build $target_list > "$3" 2>&1)
}
fld() {  # fld <line> <index>: one |||-separated field (empty when absent)
  LINE="$1" python3 -I -c 'import os,sys
p = os.environ["LINE"].split("\t") + [""] * 6
sys.stdout.write(p[int(sys.argv[1])])' "$2"
}
first_error_file() {  # path of the first `error: <file>:<line>:<col>:` line, or empty
  grep -m1 -E '^error: [^ ]+\.lean:[0-9]+:[0-9]+' "$1" | sed -E 's/^error: ([^ ]+\.lean):[0-9]+:[0-9]+.*/\1/'
}

fail=0; killed=0; same=0; bad=0; gap=0
if [ "${PROOFMUT_STRICT:-0}" = 1 ]; then PROOFMUT_BASELINE=1; fi
if [ "${PROOFMUT_BASELINE:-1}" = 1 ]; then
  mods=$(grep -v '^[[:space:]]*#' "$list" | awk -F'\t' 'NF>=5{print $5}' | tr ',' '\n' | sort -u | paste -sd, -)
  [ -n "$mods" ] || { echo "proofmut.sh: empty list" >&2; exit 2; }
  mkcopy "$root/base"
  if ! build "$root/base" "$mods" "$root/base.log"; then
    tail -30 "$root/base.log"; echo "PROOFMUT FAIL: the unmutated build of the listed modules does not pass"; exit 1
  fi
  echo "baseline: the listed proof modules build unmutated"
  rm -rf "$root/base"
fi

while IFS= read -r line || [ -n "$line" ]; do
  case "$line" in ''|'#'*) continue;; esac
  name=$(fld "$line" 0); file=$(fld "$line" 1); mods=$(fld "$line" 4); flag=$(fld "$line" 5)
  [[ "$name" =~ $filter ]] || continue
  d="$root/m"; rm -rf "$d"; mkcopy "$d"
  if ! LINE="$line" python3 -I - "$d/$file" <<'PY'
import os, sys
path = sys.argv[1]
p = os.environ["LINE"].split("\t")
old, new = p[2].replace("\\n", "\n"), p[3].replace("\\n", "\n")
s = open(path).read()
if old == new or s.count(old) != 1:
    sys.exit(1)
open(path, "w").write(s.replace(old, new))
PY
  then
    printf '%-40s NOT APPLIED (old text must occur exactly once)\n' "$name"; fail=1; continue
  fi
  log="$root/m.log"
  t0=$(date +%s)
  if build "$d" "$mods" "$log"; then built=1; else built=0; fi
  if [ $built = 0 ] && [ -z "$(first_error_file "$log")" ]; then  # killed from outside: one retry
    if build "$d" "$mods" "$log"; then built=1; else built=0; fi
  fi
  secs=$(( $(date +%s) - t0 ))
  if [ $built = 1 ]; then
    if [[ "$flag" == same:* ]]; then verdict="SAME ok"; same=$((same+1))
    elif [[ "$flag" == gap:* ]]; then verdict="GAP (known)"; gap=$((gap+1))
    else verdict="SURVIVED"; fail=1; fi
    detail=""
  else
    ef=$(first_error_file "$log")
    detail=$(grep -m1 -E '^error: [^ ]+\.lean:[0-9]+:[0-9]+' "$log" | cut -c1-140)
    if [ -z "$ef" ]; then verdict="NO ERROR"; fail=1
    elif [[ "$flag" == same:* ]]; then verdict="UNEXPECTED (marked same, build failed)"; fail=1
    elif [ "$ef" = "$file" ] || [[ "$ef" != ZlibF/Proof/* ]]; then verdict="BAD MUTANT"; fail=1; bad=$((bad+1))
    else
      okp=0
      IFS=, read -ra ms <<< "$mods"
      for m in "${ms[@]}"; do [ "$ef" = "ZlibF/Proof/$m.lean" ] && okp=1; done
      if [ $okp = 1 ]; then verdict="KILLED"; if [[ "$flag" == gap:* ]]; then verdict="KILLED (stale gap flag)"; fail=1; fi; killed=$((killed+1)); else verdict="WRONG PLACE"; fail=1; fi
    fi
  fi
  printf '%-40s %-12s %4ss %s\n' "$name" "$verdict" "$secs" "$detail"
  if [ -n "${PROOFMUT_SHOWLOG:-}" ] && { [ "$verdict" = SURVIVED ] || [ "$verdict" = "BAD MUTANT" ]; }; then tail -15 "$log"; fi
  rm -rf "$d"
done < "$list"
echo "$killed killed, $same equivalent (build as expected), $gap known gaps (proofs still build), $bad bad mutants"
if [ "${PROOFMUT_STRICT:-0}" = 1 ] && { [ "$gap" -gt 0 ] || [ $((killed + same)) = 0 ]; }; then
  echo "strict acceptance requires checked mutants and no known proof gaps"
  fail=1
fi
if [ "$fail" = 0 ]; then echo "PROOFMUT PASS"; else echo "PROOFMUT FAIL: see the lines above that are not KILLED or SAME ok"; exit 1; fi
