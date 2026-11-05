import ZlibF.Zlib.«trees.c»
import DiffTest.Common

/-!
Lean side of the differential test for `trees.c`. It calls the translation in `ZlibF/Zlib/trees.c.lean`
(the module the proofs are about) and prints exactly what `tests/c/trees.c` prints. See that file for the
line formats; `tests/gen/trees.py` writes the inputs.
-/

open DiffTest C Zlib.Trees

def zid : Nat := 5
def sidn : Nat := 7

/-- Build a deflate state like `deflate.c` does and run `_tr_init`, then set the bit buffer. -/
def setup (lit : Nat) (level strategy dt : Int32) (bi_buf : UInt16) (bi_valid : Int32) (pend0 : UInt64) :
    M DeflateStatePtr := do
  let pb ← allocBytes (Array.replicate (4 * lit + 1024) 0)
  let sb ← Ptr.add pb (lit : Int)
  let z : ZStream := { ZStream.garbage (fun _ => 0) with data_type := dt }
  let base := DeflateState.garbage (fun _ => 0)
  let st : DeflateState := { base with
    -- stale values that `_tr_init` and `init_block` must reset (as in tests/c/trees.c)
    bi_buf := 0x1234, bi_valid := 9, bi_used := 5, opt_len := 77, static_len := 88, sym_next := 5,
    «matches» := 6,
    dyn_ltree := ((base.dyn_ltree.set! 3 ⟨9, 0⟩).set! 285 ⟨2, 0⟩).set! 256 ⟨7, 0⟩,
    dyn_dtree := base.dyn_dtree.set! 29 ⟨3, 0⟩, bl_tree := base.bl_tree.set! 18 ⟨4, 0⟩,
    bl_count := Array.ofFn (n := 16) fun i => UInt16.ofNat (i.val + 3), heap_len := 5, heap_max := 7,
    strm := some (.tab zid), pending_buf := pb, pending_buf_size := UInt64.ofNat (4 * lit), pending := pend0,
    lit_bufsize := UInt32.ofNat lit, sym_buf := sb, sym_end := UInt32.ofNat ((lit - 1) * 3), level, strategy }
  (fun h => .ok ((), { h with streams := upd h.streams zid (some z), dstates := upd h.dstates sidn (some st) }) : M Unit)
  let s : DeflateStatePtr := some (.tab sidn)
  «_tr_init» s
  if bi_valid != -99 then   -- -99: keep what `_tr_init` left
    md s fun d => { d with bi_buf := bi_buf, bi_valid := bi_valid }
  pure s

def fnvStep (h : UInt64) (v : UInt32) : UInt64 := Id.run do
  let mut h := h
  for i in [0:4] do
    h := (h ^^^ ((v >>> (8 * i).toUInt32) &&& 0xff).toUInt64) * 1099511628211
  return h

def fnvInit : UInt64 := 14695981039346656037

def hexDigits (v : Nat) (width : Nat) : String :=
  String.ofList ((List.range width).reverse.map fun i => Nat.digitChar ((v >>> (4 * i)) % 16))

def hashTree (p : CtDataPtr) (n : Nat) : M UInt64 := do
  let mut h := fnvInit
  for i in [0:n] do
    let e ← Ptr.index p i
    h := fnvStep (fnvStep h e.fc.toUInt32) e.dl.toUInt32
  return h

def hex16 (v : UInt64) : String := hexDigits v.toNat 16

def dump (s : DeflateStatePtr) : M String := do
  let d ← rd s
  let mut out := s!"P={d.pending.toNat} O="
  for i in [0:d.pending.toNat] do
    out := out ++ hexDigits (← Ptr.index d.pending_buf i).toNat 2
  let z ← ldZStream d.strm
  out := out ++ s!" B={d.bi_buf.toNat},{d.bi_valid.toInt},{d.bi_used.toInt} L={d.opt_len.toNat},{d.static_len.toNat}"
  out := out ++ s!" S={d.sym_next.toNat},{d.«matches».toNat} H={d.heap_len.toInt},{d.heap_max.toInt} D={z.data_type.toInt}"
  out := out ++ s!" M={d.l_desc.max_code.toInt},{d.d_desc.max_code.toInt},{d.bl_desc.max_code.toInt}"
  out := out ++ s!" TL={hex16 (← hashTree (← pLtree s) 573)} TD={hex16 (← hashTree (← pDtree s) 61)} TB={hex16 (← hashTree (← pBltree s) 39)}"
  let mut h := fnvInit
  for i in [0:573] do h := fnvStep h (i2u d.heap[i]!)
  out := out ++ s!" HP={hex16 h}"
  h := fnvInit
  for i in [0:573] do h := fnvStep h d.depth[i]!.toUInt32
  out := out ++ s!" DP={hex16 h} BC="
  out := out ++ ",".intercalate ((List.range 16).map fun i => toString d.bl_count[i]!.toNat)
  return out

/-- "i:v,a-b:v" or "-" -/
def parseSpec (s : String) : Except String (List (Nat × Int)) := do
  if s == "-" then return []
  let mut out := []
  for tok in s.splitOn "," do
    match tok.splitOn ":" with
    | [r, v] =>
      let v ← match v.toInt? with | some v => pure v | none => throw s!"bad spec value {v}"
      match r.splitOn "-" with
      | [_] => out := out ++ [((← parseNat r), v)]
      | [a, b] =>
        for i in [(← parseNat a):(← parseNat b) + 1] do out := out ++ [(i, v)]
      | _ => throw "bad spec range"
    | _ => throw s!"bad spec {tok}"
  return out

def parseInt32 (s : String) : Except String Int32 :=
  match s.toInt? with
  | some n => if -(2 ^ 31 : Int) ≤ n ∧ n < 2 ^ 31 then pure (Int32.ofInt n) else throw s!"out of range int {s}"
  | none => throw s!"bad int {s}"

def parseU32 (s : String) : Except String UInt32 := do
  let n ← parseNat s
  if n < 2 ^ 32 then pure (UInt32.ofNat n) else throw s!"out of range unsigned {s}"

/-- A buffer for `stored`/`block`: `null` or `ramp:` of the given length is built from the length argument. -/
def mkbuf (spec : String) (len : Nat) : M BPtr :=
  if spec == "null" then pure .null
  else allocBytes (Array.ofFn (n := len) fun i => UInt8.ofNat ((i.val * 7 + 3) % 256))

/-- Tally all symbols of a spec; returns the count and the first `cap - 1` flush results. -/
def tallyAll (s : DeflateStatePtr) (spec : String) (cap : Nat) : Except String (M (Nat × String)) := do
  if spec == "-" then return pure (0, "")
  let mut toks : List (UInt32 × UInt32 × Nat) := []
  for tok in spec.splitOn "," do
    let (body, n) ← match tok.splitOn "*" with
      | [b] => pure (b, 1)
      | [b, n] => do pure (b, ← parseNat n)
      | _ => throw "bad symbol"
    if body.startsWith "l" then
      toks := toks ++ [(0, ← parseU32 (body.drop 1).toString, n)]
    else if body.startsWith "m" then
      match (body.drop 1).toString.splitOn ":" with
      | [d, l] => toks := toks ++ [(← parseU32 d, ← parseU32 l, n)]
      | _ => throw "bad match symbol"
    else throw "bad symbol"
  return do
    let mut cnt := 0
    let mut rets := ""
    for (dist, lc, n) in toks do
      for _ in [0:n] do
        let r ← «_tr_tally» s dist lc
        if cnt < cap - 1 then rets := rets ++ (if r == 0 then "0" else "1")
        cnt := cnt + 1
    return (cnt, rets)

def runM (m : M String) : String :=
  match C.run m (install_trees Heap.empty) with
  | .ok (v, _) => v
  | .error f => showFault f

def handle (fn : String) (args : List String) : Except String String :=
  match fn, args with
  | "bi_reverse", [c, l] => do
    let c ← parseU32 c
    let l ← parseInt32 l
    return runM (do pure (toString (← bi_reverse c l).toNat))
  | "sendbits", [bb, bv, p0, spec] => do
    let bb ← parseNat bb
    let bv ← parseInt32 bv
    let p0 ← parseU64 p0
    let mut pairs : List (Int32 × Int32) := []
    if spec != "-" then
      for t in spec.splitOn "," do
        match t.splitOn ":" with
        | [v, l] => pairs := pairs ++ [(← parseInt32 v, ← parseInt32 l)]
        | _ => throw "bad pair"
    return runM (do
      let s ← setup 16 1 0 0 (UInt16.ofNat bb) bv p0
      for (v, l) in pairs do send_bits s v l
      dump s)
  | "bitop", [name, bb, bv, p0] => do
    let bb ← parseNat bb
    let bv ← parseInt32 bv
    let p0 ← parseU64 p0
    if !(["windup", "flush", "flushbits", "align"].contains name) then throw "bad bitop"
    return runM (do
      let s ← setup 16 1 0 0 (UInt16.ofNat bb) bv p0
      match name with
      | "windup" => bi_windup s
      | "flush" => bi_flush s
      | "flushbits" => «_tr_flush_bits» s
      | _ => «_tr_align» s
      dump s)
  | "stored", [bb, bv, p0, last, buf, len] => do
    let bb ← parseNat bb
    let bv ← parseInt32 bv
    let p0 ← parseU64 p0
    let last ← parseInt32 last
    let len ← parseNat len
    return runM (do
      let s ← setup (len / 2 + 16) 1 0 0 (UInt16.ofNat bb) bv p0
      let b ← mkbuf buf len
      «_tr_stored_block» s b (UInt64.ofNat len) last
      dump s)
  | "detect", [spec] => do
    let sp ← parseSpec spec
    return runM (do
      let s ← setup 16 1 0 0 0 0 0
      for (i, v) in sp do setFc (← pLtree s) i (UInt16.ofNat v.toNat)
      pure s!"R={(← detect_data_type s).toInt}")
  | "gen_codes", [mc, bcs, lens] => do
    let mc ← parseInt32 mc
    let bc ← (bcs.splitOn ",").mapM parseNat
    let sp ← parseSpec lens
    return runM (do
      let s ← setup 16 1 0 0 0 0 0
      let mut k := 0
      for v in bc do
        setAt (← pBlCount s) k (UInt16.ofNat v)
        k := k + 1
      for (i, v) in sp do setDl (← pLtree s) i (UInt16.ofNat v.toNat)
      gen_codes (← pLtree s) mc (← pBlCount s)
      let mut out ← dump s
      for n in [0:288] do
        out := out ++ (if n == 0 then " C=" else ",") ++ toString (← getFc (← pLtree s) n).toNat
      pure out)
  | "buildtree", [which, opt, stat, spec] => do
    let opt ← parseU64 opt
    let stat ← parseU64 stat
    let sp ← parseSpec spec
    if !(["l", "d", "bl"].contains which) then throw "bad tree"
    return runM (do
      let s ← setup 16 1 0 0 0 0 0
      md s fun d => { d with opt_len := opt, static_len := stat }
      let (desc, t, ne) ← match which with
        | "l" => do pure (← pLdesc s, ← pLtree s, 286)
        | "d" => do pure (← pDdesc s, ← pDtree s, 30)
        | _ => do pure (← pBldesc s, ← pBltree s, 19)
      for (i, v) in sp do setFc t i (UInt16.ofNat v.toNat)
      build_tree s desc
      let mut out ← dump s
      for n in [0:ne + 1] do
        let e ← Ptr.index t n
        out := out ++ (if n == 0 then " C=" else ",") ++ s!"{e.fc.toNat}/{e.dl.toNat}"
      pure out)
  | "trees", [lmax, llens, dmax, dlens, bb, bv, p0] => do
    let lmax ← parseInt32 lmax
    let dmax ← parseInt32 dmax
    let ll ← parseSpec llens
    let dl ← parseSpec dlens
    let bb ← parseNat bb
    let bv ← parseInt32 bv
    let p0 ← parseU64 p0
    return runM (do
      let s ← setup 16 1 0 0 (UInt16.ofNat bb) bv p0
      md s fun d => { d with l_desc := { d.l_desc with max_code := lmax }, d_desc := { d.d_desc with max_code := dmax } }
      for (i, v) in ll do setDl (← pLtree s) i (UInt16.ofNat v.toNat)
      for (i, v) in dl do setDl (← pDtree s) i (UInt16.ofNat v.toNat)
      let r ← build_bl_tree s
      let d ← rd s
      send_all_trees s (← iadd d.l_desc.max_code 1) (← iadd d.d_desc.max_code 1) (← iadd r 1)
      pure s!"R={r.toInt} {← dump s}")
  | "block", [level, strategy, dt, bb, bv, lit, slen, buf, last, syms] => do
    let level ← parseInt32 level
    let strategy ← parseInt32 strategy
    let dt ← parseInt32 dt
    let bb ← parseNat bb
    let bv ← parseInt32 bv
    let lit ← parseNat lit
    let slen ← parseNat slen
    let last ← parseInt32 last
    return runM (do
      let s ← setup lit level strategy dt (UInt16.ofNat bb) bv 0
      let b ← mkbuf buf slen
      let (cnt, rets) ← match tallyAll s syms 64 with
        | .ok m => m
        | .error e => ub e
      let pre := s!"N={cnt} F={rets} "
      «_tr_flush_block» s b (UInt64.ofNat slen) last
      pure (pre ++ (← dump s)))
  | "tally", [lit, syms] => do
    let lit ← parseNat lit
    return runM (do
      let s ← setup lit 1 0 0 0 0 0
      let (cnt, rets) ← match tallyAll s syms 4096 with
        | .ok m => m
        | .error e => ub e
      pure (s!"N={cnt} F={rets} " ++ (← dump s)))
  | "tables", [] => do
    let h := install_trees Heap.empty
    let st := h.static
    let hb (a : Array UInt8) : UInt64 := a.foldl (fun h v => fnvStep h v.toUInt32) fnvInit
    let hi (a : Array Int32) : UInt64 := a.foldl (fun h v => fnvStep h (i2u v)) fnvInit
    let hc (a : Array CtData) : UInt64 := a.foldl (fun h e => fnvStep (fnvStep h e.fc.toUInt32) e.dl.toUInt32) fnvInit
    let desc (d : StaticTreeDesc) (tr : CtDataPtr) (ex : IPtr) : String :=
      s!"{d.extra_base.toInt},{d.elems.toInt},{d.max_length.toInt},{if d.static_tree == tr then 1 else 0},{if d.extra_bits == ex then 1 else 0}"
    return s!"SL={hex16 (hc st.static_ltree)} SD={hex16 (hc st.static_dtree)} DC={hex16 (hb st.dist_code)} LC={hex16 (hb st.length_code)} BL={hex16 (hi st.base_length)} BD={hex16 (hi st.base_dist)} XL={hex16 (hi st.extra_lbits)} XD={hex16 (hi st.extra_dbits)} XB={hex16 (hi st.extra_blbits)} BO={hex16 (hb bl_order)} LD={desc st.static_l_desc (.ref .st_static_ltree 0) (.ref .st_extra_lbits 0)} DD={desc st.static_d_desc (.ref .st_static_dtree 0) (.ref .st_extra_dbits 0)} BLD={desc st.static_bl_desc .null (.ref .st_extra_blbits 0)}"
  | "init", [] =>
    return runM (do
      let s ← setup 16 1 0 0 7 (-99) 0
      dump s)
  | _, _ => throw s!"unknown function or wrong arity: {fn}"

def main : IO UInt32 := mainLoop handle
