#!/usr/bin/env python3
"""Extract the actual C and Lean merge-depth expressions for comparison."""
from pathlib import Path
import re
import sys


root, work = map(Path, sys.argv[1:])
c_source = (root / 'zlib/trees.c').read_text()
statement = re.search(r's->depth\[node\] = \(uch\)\(\(s->depth\[n\].*?;', c_source, re.S)
if statement is None:
    raise RuntimeError('missing upstream merge-depth statement')
lean_source = (root / 'ZlibF/Zlib/trees.c.lean').read_text().split('def build_tree (', 1)[1]
fragment = '      let dp ← pDepth s' + lean_source.split('      let dp ← pDepth s', 1)[1].split('      -- tree[n].Dad', 1)[0]
reload = 'let mx ← if dn ≥ dm then Ptr.index dp n.toInt else Ptr.index dp m.toInt'
def require_reload(text):
    if text.count(reload) != 1 or 'let mx := if dn ≥ dm then dn else dm' in text:
        raise RuntimeError('the selected depth must be read again after the comparison')
    if text.count('Ptr.index dp n.toInt') != 2 or text.count('Ptr.index dp m.toInt') != 2:
        raise RuntimeError('unexpected merge-depth read structure')

require_reload(fragment)
try:
    require_reload(fragment.replace(reload, "let mx := if dn ≥ dm then dn else dm"))
except RuntimeError:
    pass
else:
    raise RuntimeError("the source check accepted the former cached expression")

cases = ((0, 0), (3, 7), (8, 1), (255, 254), (254, 255), (255, 255))
c_cases = ', '.join('{' + str(a) + ',' + str(b) + '}' for a, b in cases)
(work / 'depth.c').write_text('''#include <stdio.h>
typedef unsigned char uch;
typedef struct { uch depth[573]; } state;
int main(void) {
    unsigned inputs[][2] = {''' + c_cases + '''};
    for (unsigned i = 0; i < sizeof(inputs) / sizeof(inputs[0]); i++) {
        state st = {0}; state *s = &st;
        int n = 0, m = 1, node = 2;
        st.depth[n] = (uch)inputs[i][0]; st.depth[m] = (uch)inputs[i][1];
        ''' + statement.group(0) + '''
        printf("%u\\n", (unsigned)st.depth[node]);
    }
    return 0;
}
''')
lean_cases = ', '.join(f'({a}, {b})' for a, b in cases)
(work / 'Depth.lean').write_text('''import ZlibF.Zlib.«trees.c»
open C Zlib.Trees
def fragment (s : DeflateStatePtr) (n m node : Int32) : M Unit := do
''' + fragment + '''
def main : IO Unit := do
  let inputs : Array (UInt8 × UInt8) := #[''' + lean_cases + ''']
  for (a, b) in inputs do
    let d : DeflateState := { (default : DeflateState) with
      depth := ((Array.replicate 573 0).set! 0 a).set! 1 b }
    let h : Heap := { Heap.empty with dstates := upd Tbl.empty 0 (some d) }
    match fragment (some (.tab 0)) 0 1 2 h with
    | .error _ => throw (IO.userError "merge-depth fragment faulted")
    | .ok (_, h') =>
      let e := (h'.dstates 0).getD default
      IO.println e.depth[2]!.toNat
''')
