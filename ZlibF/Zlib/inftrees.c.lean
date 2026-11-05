import ZlibF.Runtime.Alloc
import ZlibF.Runtime.Tables
import ZlibF.Zlib.«inffixed.h»

/-!
# inftrees.c — faithful translation

Source: `inftrees.c` (with `inftrees.h`, `inffixed.h`), default x86_64 Linux build. `MAKEFIXED`, `BUILDFIXED`,
`Z_ONCE` are undefined, so `buildtables`, `z_once` and `main` are dead and `inflate_fixed` uses the tables of
`inffixed.h` (`inffixed.h.lean`, copied entry for entry). `inflate_copyright` is a `const char[]` that nothing reads;
it is not translated.

Decisions (the C line of each is in the code):

* `unsigned short FAR *lens`, `*work` are `WPtr`. `code FAR * FAR *table` and `unsigned FAR *bits` point to fields of
  `inflate_state` (`&state->next`, `&state->lenbits`, ...), which the schema does not model: the function takes their
  values and returns the new ones, `(ret, table', bits')`. On `return -1` and `return 1` the C stores nothing through
  them, so the inputs are returned; table entries written so far stay written.
* `count[16]`, `offs[16]` are local `unsigned short` arrays: `Array UInt16`, indexed with a check (an index outside
  0..15 is a fault; the C says "assumes, but does not check" that every `lens[i] <= 15`).
* `lbase`, `lext`, `dbase`, `dext` are function-local `static const` tables that are only indexed: `Array UInt16`
  constants. `base` and `extra` are NULL for `CODES`: the empty array, so a read through them is a fault.
* Signed `int` arithmetic (`left`) is checked; shifts fault for a count outside the width of the type
  (and a signed `1 << curr` faults when the result does not fit in `int`).
* `min` is reused at C line "min = fill" as in the C: one variable, new meaning.
-/

namespace Zlib.Inftrees
open C

/-! ### Small checked operations -/

/-- A signed `int` result: a fault if it does not fit. -/
def chk32 (v : Int) : M Int32 :=
  if -2147483648 ≤ v ∧ v ≤ 2147483647 then pure (Int32.ofInt v) else ub "signed integer overflow"

/-- `x << n` for `unsigned`: undefined if `n >= 32`. -/
def shl32 (x n : UInt32) : M UInt32 :=
  if n < 32 then pure (x <<< n) else ub "shift count out of range"

/-- `x >> n` for `unsigned`: undefined if `n >= 32`. -/
def shr32 (x n : UInt32) : M UInt32 :=
  if n < 32 then pure (x >>> n) else ub "shift count out of range"

/-- `1 << n` for `int`: undefined if `n >= 32` or the result is not representable (`n = 31`). -/
def shl1i32 (n : UInt32) : M Int32 :=
  if n < 31 then pure (1 <<< n.toInt32) else ub "signed shift out of range"

/-- `a[i]` for a local array. -/
def geta (a : Array UInt16) (i : Nat) : M UInt16 :=
  match a[i]? with
  | some v => pure v
  | none => ub "array index outside its object"

/-- `a[i] = v` for a local array. -/
def seta (a : Array UInt16) (i : Nat) (v : UInt16) : M (Array UInt16) :=
  if i < a.size then pure (a.set! i v) else ub "array index outside its object"

/-- `p[i] = v` for a pointer into an array of `code`. -/
def storeCode (p : CodePtr) (i : Nat) (v : Code) : M Unit := do
  let q ← p.add i
  Ptr.store q v

/-! ### Tables -/

def MAXBITS : UInt32 := 15

/-- `static const unsigned short lbase[31]` -/
def lbase : Array UInt16 :=
  #[3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31,
    35, 43, 51, 59, 67, 83, 99, 115, 131, 163, 195, 227, 258, 0, 0]
/-- `static const unsigned short lext[31]` -/
def lext : Array UInt16 :=
  #[16, 16, 16, 16, 16, 16, 16, 16, 17, 17, 17, 17, 18, 18, 18, 18,
    19, 19, 19, 19, 20, 20, 20, 20, 21, 21, 21, 21, 16, 68, 193]
/-- `static const unsigned short dbase[32]` -/
def dbase : Array UInt16 :=
  #[1, 2, 3, 4, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97, 129, 193,
    257, 385, 513, 769, 1025, 1537, 2049, 3073, 4097, 6145,
    8193, 12289, 16385, 24577, 0, 0]
/-- `static const unsigned short dext[32]` -/
def dext : Array UInt16 :=
  #[16, 16, 16, 16, 17, 17, 18, 18, 19, 19, 20, 20, 21, 21, 22, 22,
    23, 23, 24, 24, 25, 25, 26, 26, 27, 27,
    28, 28, 29, 29, 64, 64]

/-- The `Statics` with the contents that `inftrees.c` fixes: `lenfix` and `distfix` (from `inffixed.h`). -/
def initStatics (s : Statics) : Statics :=
  { s with lenfix := Zlib.InffixedH.lenfix, distfix := Zlib.InffixedH.distfix }

/-! ### `inflate_table` -/

/-- Loop-carried locals of the main loop of `inflate_table` (`for (;;)`). `exit` is 0 while the loop runs, 1 after
the `break`, 2 after `return 1`. -/
structure TS where
  huff : UInt32
  sym : UInt32
  len : UInt32
  curr : UInt32
  drop : UInt32
  low : UInt32
  used : UInt32
  min : UInt32
  fill : UInt32
  incr : UInt32
  mask : UInt32
  left : Int32
  next : CodePtr
  here : Code
  count : Array UInt16
  exit : UInt8

/-- What the main loop reads and never changes. -/
structure Ctx where
  type : UInt32
  lens : WPtr
  work : WPtr
  table : CodePtr
  root : UInt32
  max : UInt32
  base : Array UInt16
  extra : Array UInt16
  match_ : UInt32

/-- `(type == LENS && used > ENOUGH_LENS) || (type == DISTS && used > ENOUGH_DISTS)` -/
def tooBig (type used : UInt32) : Bool :=
  (type == LENS && used > ENOUGH_LENS.toUInt32) || (type == DISTS && used > ENOUGH_DISTS.toUInt32)

/-- One pass of the body of the `for (;;)` loop of `inflate_table`. -/
def buildStep (c : Ctx) (s : TS) : M TS := do
  let mut s := s
  -- here.bits = (unsigned char)(len - drop);
  s := { s with here := { s.here with bits := (s.len - s.drop).toUInt8 } }
  -- if (work[sym] + 1U < match) {
  let w ← c.work.index s.sym.toNat
  if w.toUInt32 + 1 < c.match_ then
    -- here.op = (unsigned char)0; here.val = work[sym];
    s := { s with here := { s.here with op := 0 } }
    let w ← c.work.index s.sym.toNat
    s := { s with here := { s.here with val := w } }
  else
    -- else if (work[sym] >= match) {
    let w ← c.work.index s.sym.toNat
    if w.toUInt32 ≥ c.match_ then
      -- here.op = (unsigned char)(extra[work[sym] - match]);
      let w ← c.work.index s.sym.toNat
      let e ← geta c.extra (w.toUInt32 - c.match_).toNat
      s := { s with here := { s.here with op := e.toUInt8 } }
      -- here.val = base[work[sym] - match];
      let w ← c.work.index s.sym.toNat
      let b ← geta c.base (w.toUInt32 - c.match_).toNat
      s := { s with here := { s.here with val := b } }
    else
      -- here.op = (unsigned char)(32 + 64); here.val = 0;   /* end of block */
      s := { s with here := { s.here with op := 96, val := 0 } }
  -- incr = 1U << (len - drop); fill = 1U << curr; min = fill;
  let incr ← shl32 1 (s.len - s.drop)
  let fill ← shl32 1 s.curr
  s := { s with incr, fill, min := fill }
  -- do { fill -= incr; next[(huff >> drop) + fill] = here; } while (fill != 0);
  s ← cdoWhile
    (fun s => do
      let fill := s.fill - s.incr
      let hd ← shr32 s.huff s.drop
      storeCode s.next (hd + fill).toNat s.here
      pure { s with fill })
    (fun s => pure (s.fill != 0, s)) s
  -- incr = 1U << (len - 1);
  let incr ← shl32 1 (s.len - 1)
  s := { s with incr }
  -- while (huff & incr) incr >>= 1;
  s ← cwhile (fun s => pure (s.huff &&& s.incr != 0, s)) (fun s => pure { s with incr := s.incr >>> 1 }) s
  -- if (incr != 0) { huff &= incr - 1; huff += incr; } else huff = 0;
  if s.incr != 0 then
    s := { s with huff := s.huff &&& (s.incr - 1) }
    s := { s with huff := s.huff + s.incr }
  else
    s := { s with huff := 0 }
  -- sym++;
  s := { s with sym := s.sym + 1 }
  -- if (--(count[len]) == 0) {
  let cl ← geta s.count s.len.toNat
  let cl := cl - 1
  s := { s with count := ← seta s.count s.len.toNat cl }
  if cl == 0 then
    -- if (len == max) break;
    if s.len == c.max then
      return { s with exit := 1 }
    -- len = lens[work[sym]];
    let w ← c.work.index s.sym.toNat
    let l ← c.lens.index w.toNat
    s := { s with len := l.toUInt32 }
  -- if (len > root && (huff & mask) != low) {
  if s.len > c.root && (s.huff &&& s.mask) != s.low then
    -- if (drop == 0) drop = root;
    if s.drop == 0 then s := { s with drop := c.root }
    -- next += min;   /* here min is 1 << curr */
    s := { s with next := ← s.next.add s.min.toNat }
    -- curr = len - drop; left = (int)(1 << curr);
    s := { s with curr := s.len - s.drop }
    s := { s with left := ← shl1i32 s.curr }
    -- while (curr + drop < max) { left -= count[curr + drop]; if (left <= 0) break; curr++; left <<= 1; }
    let (curr, left, _) ← cwhile
      (fun (curr, left, brk) => pure (!brk && curr + s.drop < c.max, (curr, left, brk)))
      (fun (curr, left, brk) => do
        let cc ← geta s.count (curr + s.drop).toNat
        let left ← chk32 (left.toInt - cc.toNat)
        if left ≤ 0 then pure (curr, left, true)
        else
          let curr := curr + 1
          let left ← chk32 (left.toInt * 2)
          pure (curr, left, brk))
      (s.curr, s.left, false)
    s := { s with curr, left }
    -- used += 1U << curr;
    let u ← shl32 1 s.curr
    s := { s with used := s.used + u }
    -- if ((type == LENS && used > ENOUGH_LENS) || (type == DISTS && used > ENOUGH_DISTS)) return 1;
    if tooBig c.type s.used then
      return { s with exit := 2 }
    -- low = huff & mask;
    s := { s with low := s.huff &&& s.mask }
    -- (*table)[low].op = (unsigned char)curr;
    let q ← c.table.add s.low.toNat
    let e ← q.load
    q.store { e with op := s.curr.toUInt8 }
    -- (*table)[low].bits = (unsigned char)root;
    let q ← c.table.add s.low.toNat
    let e ← q.load
    q.store { e with bits := c.root.toUInt8 }
    -- (*table)[low].val = (unsigned short)(next - *table);
    let d ← s.next.diff c.table
    let q ← c.table.add s.low.toNat
    let e ← q.load
    q.store { e with val := d.toUInt64.toUInt16 }
  pure s

/-- `int ZLIB_INTERNAL inflate_table(codetype type, unsigned short FAR *lens, unsigned codes, code FAR * FAR *table,
unsigned FAR *bits, unsigned short FAR *work)`

`table` and `bits` are passed as the values `*table`, `*bits`; the result is `(return value, *table, *bits)` after
the call. -/
def inflate_table (type : UInt32) (lens : WPtr) (codes : UInt32) (table : CodePtr) (bits : UInt32) (work : WPtr) :
    M (Int32 × CodePtr × UInt32) := do
  -- unsigned short count[MAXBITS+1]; unsigned short offs[MAXBITS+1];   (uninitialised in C; count is cleared below)
  let count : Array UInt16 := Array.replicate 16 0
  let offs : Array UInt16 := Array.replicate 16 0
  -- for (len = 0; len <= MAXBITS; len++) count[len] = 0;
  let (_, count) ← cwhile (fun (len, count) => pure (len ≤ MAXBITS, (len, count)))
    (fun (len, count) => do pure (len + 1, ← seta count len.toNat 0)) ((0 : UInt32), count)
  -- for (sym = 0; sym < codes; sym++) count[lens[sym]]++;
  let (_, count) ← cwhile (fun (sym, count) => pure (sym < codes, (sym, count)))
    (fun (sym, count) => do
      let l ← lens.index sym.toNat
      let c ← geta count l.toNat
      pure (sym + 1, ← seta count l.toNat (c + 1))) ((0 : UInt32), count)
  -- root = *bits;
  let mut root := bits
  -- for (max = MAXBITS; max >= 1; max--) if (count[max] != 0) break;
  let (max, _) ← cwhile (fun (max, brk) => pure (!brk && max ≥ 1, (max, brk)))
    (fun (max, brk) => do
      if (← geta count max.toNat) != 0 then pure (max, true) else pure (max - 1, brk)) (MAXBITS, false)
  -- if (root > max) root = max;
  if root > max then root := max
  -- if (max == 0) {  /* no symbols to code at all */
  if max == 0 then
    -- here.op = 64; here.bits = 1; here.val = 0;
    let here : Code := ⟨64, 1, 0⟩
    -- *(*table)++ = here; *(*table)++ = here;
    Ptr.store table here
    let table ← table.add 1
    Ptr.store table here
    let table ← table.add 1
    -- *bits = 1; return 0;
    return (0, table, 1)
  -- for (min = 1; min < max; min++) if (count[min] != 0) break;
  let (min, _) ← cwhile (fun (min, brk) => pure (!brk && min < max, (min, brk)))
    (fun (min, brk) => do
      if (← geta count min.toNat) != 0 then pure (min, true) else pure (min + 1, brk)) ((1 : UInt32), false)
  -- if (root < min) root = min;
  if root < min then root := min
  -- left = 1; for (len = 1; len <= MAXBITS; len++) { left <<= 1; left -= count[len]; if (left < 0) return -1; }
  let (left, bad, _) ← cwhile (fun (left, bad, len) => pure (!bad && len ≤ MAXBITS, (left, bad, len)))
    (fun (left, bad, len) => do
      if left < 0 then ub "left shift of a negative value" else
      let left ← chk32 (left.toInt * 2)
      let cc ← geta count len.toNat
      let left ← chk32 (left.toInt - cc.toNat)
      if left < 0 then pure (left, true, len) else pure (left, bad, len + 1)) ((1 : Int32), false, (1 : UInt32))
  -- /* over-subscribed */ return -1;
  if bad then return (-1, table, bits)
  -- if (left > 0 && (type == CODES || max != 1)) return -1;   /* incomplete set */
  if left > 0 && (type == CODES || max != 1) then return (-1, table, bits)
  -- offs[1] = 0;
  let offs ← seta offs 1 0
  -- for (len = 1; len < MAXBITS; len++) offs[len + 1] = offs[len] + count[len];
  let (_, offs) ← cwhile (fun (len, offs) => pure (len < MAXBITS, (len, offs)))
    (fun (len, offs) => do
      let a ← geta offs len.toNat
      let b ← geta count len.toNat
      pure (len + 1, ← seta offs (len + 1).toNat (a + b))) ((1 : UInt32), offs)
  -- for (sym = 0; sym < codes; sym++) if (lens[sym] != 0) work[offs[lens[sym]]++] = (unsigned short)sym;
  let (_, offs) ← cwhile (fun (sym, offs) => pure (sym < codes, (sym, offs)))
    (fun (sym, offs) => do
      let l ← lens.index sym.toNat
      if l != 0 then
        let l ← lens.index sym.toNat
        let o ← geta offs l.toNat
        let offs ← seta offs l.toNat (o + 1)
        let q ← work.add o.toNat
        Ptr.store q sym.toUInt16
        pure (sym + 1, offs)
      else pure (sym + 1, offs)) ((0 : UInt32), offs)
  -- switch (type) { case CODES: match = 20; break; case LENS: base = lbase; extra = lext; match = 257; break;
  --                 case DISTS: base = dbase; extra = dext; }
  let mut base : Array UInt16 := #[]      -- NULL
  let mut extra : Array UInt16 := #[]     -- NULL
  let mut match_ : UInt32 := 0
  if type == CODES then
    match_ := 20
  else if type == LENS then
    base := lbase; extra := lext; match_ := 257
  else if type == DISTS then
    base := dbase; extra := dext
  -- huff = 0; sym = 0; len = min; next = *table; curr = root; drop = 0; low = (unsigned)(-1);
  -- used = 1U << root; mask = used - 1;
  let used ← shl32 1 root
  let s : TS := { huff := 0, sym := 0, len := min, curr := root, drop := 0, low := 0xffffffff, used,
                  min := min, fill := 0, incr := 0, mask := used - 1, left, next := table, here := default,
                  count, exit := 0 }
  -- if ((type == LENS && used > ENOUGH_LENS) || (type == DISTS && used > ENOUGH_DISTS)) return 1;
  if tooBig type used then return (1, table, bits)
  -- for (;;) { ... }
  let c : Ctx := { type, lens, work, table, root, max, base, extra, match_ }
  let s ← cwhile (fun s => pure (s.exit == 0, s)) (buildStep c) s
  -- (return 1 from inside the loop)
  if s.exit == 2 then return (1, table, bits)
  let mut s := s
  -- if (huff != 0) {
  if s.huff != 0 then
    -- here.op = (unsigned char)64; here.bits = (unsigned char)(len - drop); here.val = (unsigned short)0;
    s := { s with here := ⟨64, (s.len - s.drop).toUInt8, 0⟩ }
    -- next[huff] = here;
    storeCode s.next s.huff.toNat s.here
  -- *table += used; *bits = root; return 0;
  let table ← table.add s.used.toNat
  return (0, table, root)

/-- `void inflate_fixed(struct inflate_state FAR *state)` -/
def inflate_fixed (state : InflateStatePtr) : M Unit := do
  -- state->lencode = lenfix;
  let st ← ldInflateState state
  stInflateState state { st with lencode := .ref .st_lenfix 0 }
  -- state->lenbits = 9;
  let st ← ldInflateState state
  stInflateState state { st with lenbits := 9 }
  -- state->distcode = distfix;
  let st ← ldInflateState state
  stInflateState state { st with distcode := .ref .st_distfix 0 }
  -- state->distbits = 5;
  let st ← ldInflateState state
  stInflateState state { st with distbits := 5 }

end Zlib.Inftrees
