import ZlibF.Zlib.«deflate.c»
import ZlibF.Zlib.«compress.c»
import ZlibF.Zlib.«zutil.c»
import DiffTest.Common

/-!
Lean side of the differential test for `deflate.c` and `compress.c`. It calls the translations in
`ZlibF/Zlib/deflate*.c.lean` and `compress.c.lean` and prints exactly what `tests/c/deflate.c` prints.
Grammar: `tests/gen/deflate.py`.
-/

open DiffTest C Zlib.Deflate

/-- The heap of the tests: the static tables that the translations read are installed. -/
def startHeap : Heap :=
  { Heap.empty with static := Zlib.Crc32.initStatics (Zlib.Trees.trees_statics Heap.empty.static) }

def hexByte (b : UInt8) : String :=
  let d := fun (n : Nat) => Nat.digitChar n
  String.ofList [d (b.toNat / 16), d (b.toNat % 16)]

def hexOf (a : Array UInt8) : String := String.join (a.toList.map hexByte)

/-- The `n` bytes at `p`, read one by one. -/
def readBytes (p : BPtr) (n : Nat) : M (Array UInt8) := do
  let mut out : Array UInt8 := #[]
  for i in [0:n] do
    out := out.push (← index8 p i)
  return out

def readCStr (p : BPtr) : M String := do
  if p == .null then return "-"
  let n ← strlenB p
  let bs ← readBytes p n.toNat
  return String.ofList (bs.toList.map fun b => Char.ofNat b.toNat)

def state (strm : ZStreamPtr) (rc : Int32) : M String := do
  let z ← ldZStream strm
  let m ← readCStr z.msg
  return s!"{rc.toInt},{z.avail_in},{z.avail_out},{z.total_in},{z.total_out},{z.adler},{z.data_type.toInt},{m}"

structure Sess where
  strm : ZStreamPtr
  inb : BPtr
  N : Nat
  fed : Nat
  consumed : Nat
  outb : BPtr
  ocap : Nat
  ended : Bool
  out : String
  done : Bool

def ints (s : String) : List Int := (s.splitOn ":").map fun x => (x.toInt?).getD 0

def i32 (x : Int) : Int32 := Int32.ofInt x

def feed (st : Sess) (ic : Nat) : M Sess := do
  let fed := min (st.fed + ic) st.N
  let ni ← padd st.inb st.consumed
  zwr st.strm (fun z => { z with next_in := ni, avail_in := UInt32.ofNat (fed - st.consumed) })
  return { st with fed }

def after (st : Sess) : M Sess := do
  let ai ← zrd st.strm (·.avail_in)
  return { st with consumed := st.fed - ai.toNat }

/-- The header of `H:text:time:os:hcrc:extra:name:comment`. -/
def mkHeader (f : List String) : M GzHeaderPtr := do
  let get := fun (i : Nat) => f.getD i "-"
  let hexs := fun (s : String) => (parseHex s).toOption.getD #[]
  let ptrOf : String → Bool → M (BPtr × Nat) := fun s nul => do
    if s == "-" then return (.null, 0)
    let bs := hexs s
    let n := bs.size
    let p ← allocBytes (if nul then bs.push 0 else bs)
    return (p, n)
  let (extra, el) ← ptrOf (get 4) false
  let (name, nl) ← ptrOf (get 5) true
  let (comment, cl) ← ptrOf (get 6) true
  let p ← allocGzHeader
  stGzHeader p { GzHeader.zeroed with
    text := i32 ((get 0).toInt?.getD 0), time := (get 1).toNat?.getD 0 |>.toUInt64, os := i32 ((get 2).toInt?.getD 0),
    hcrc := i32 ((get 3).toInt?.getD 0), extra, extra_len := UInt32.ofNat el, extra_max := UInt32.ofNat el,
    name, name_max := UInt32.ofNat (nl + 1), comment, comm_max := UInt32.ofNat (cl + 1) }
  return p

def runToken (st0 : Sess) (t : String) : M Sess := do
  let strm := st0.strm
  let mut st := st0
  if t.startsWith "IN:" then
    let bs := (parseHex (t.drop 3).toString).toOption.getD #[]
    let inb ← allocBytes (if bs.isEmpty then #[0] else bs)
    let ocap := bs.size + bs.size / 2 + 4096
    let outb ← allocBytes (Array.replicate ocap 0)
    zwr strm (fun z => { z with next_out := outb, avail_out := 0 })
    st := { st with inb, N := bs.size, ocap, outb }
  else if t.startsWith "I1:" then
    let lv := i32 (ints (t.drop 3).toString |>.headD 0)
    let ver ← Zlib.Zutil.zlibVersion
    let rc ← deflateInit_ strm lv ver sizeof_z_stream
    st := { st with out := st.out ++ s!"I={rc.toInt} " }
    if rc != 0 then return { st with done := true }
  else if t.startsWith "I:" then
    let parts := (t.drop 2).toString.splitOn ":"
    let nums := (parts.take 5).map fun x => (x.toInt?).getD 0
    let fl := parts.getD 5 ""
    let ver ← if fl == "v" then allocBytes ("0.9".toUTF8.data.push 0) else Zlib.Zutil.zlibVersion
    let ssz : Int32 := if fl == "s" then 111 else sizeof_z_stream
    let rc ← deflateInit2_ strm (i32 (nums.getD 0 0)) (i32 (nums.getD 1 0)) (i32 (nums.getD 2 0))
      (i32 (nums.getD 3 0)) (i32 (nums.getD 4 0)) ver ssz
    st := { st with out := st.out ++ s!"I={rc.toInt} " }
    if rc != 0 then return { st with done := true }
  else if t.startsWith "D:" then
    let a := ints (t.drop 2).toString
    let fl := i32 (a.getD 0 0); let ic := (a.getD 1 0).toNat; let oc0 := (a.getD 2 0).toNat
    let no ← zrd strm (·.next_out)
    let used := (match no, st.outb with
      | .ref _ o, _ => o
      | _, _ => 0)
    let oc := min oc0 (st.ocap - used)
    st ← feed st ic
    zwr strm (fun z => { z with avail_out := UInt32.ofNat oc })
    let rc ← deflate strm fl
    st ← after st
    st := { st with out := st.out ++ "D=" ++ (← state strm rc) ++ " " }
  else if t.startsWith "P:" then
    let a := ints (t.drop 2).toString
    st ← feed st 0
    let rc ← deflateParams strm (i32 (a.getD 0 0)) (i32 (a.getD 1 0))
    st ← after st
    st := { st with out := st.out ++ "P=" ++ (← state strm rc) ++ " " }
  else if t.startsWith "S:" then
    let bs := (parseHex (t.drop 2).toString).toOption.getD #[]
    let d ← allocBytes (if bs.isEmpty then #[0] else bs)
    let rc ← deflateSetDictionary strm d (UInt32.ofNat bs.size)
    let ad ← zrd strm (·.adler)
    st := { st with out := st.out ++ s!"S={rc.toInt},{ad} " }
  else if t == "G" then
    let d ← allocBytes (Array.replicate 32768 0)
    let (rc, len) ← deflateGetDictionary strm d true
    let l := len.getD 0
    let bs ← readBytes d (if rc == 0 then l.toNat else 0)
    st := { st with out := st.out ++ s!"G={rc.toInt},{l}," ++ hexOf bs ++ " " }
  else if t == "R" then
    let rc ← deflateReset strm
    st := { st with out := st.out ++ s!"R={rc.toInt} " }
  else if t.startsWith "K:" then
    let a := ints (t.drop 2).toString
    let rc ← deflatePrime strm (i32 (a.getD 0 0)) (i32 (a.getD 1 0))
    st := { st with out := st.out ++ s!"K={rc.toInt} " }
  else if t == "C" then
    let d ← allocZStream
    let rc ← deflateCopy d strm
    st := { st with out := st.out ++ s!"C={rc.toInt} " }
    if rc == 0 then
      let _ ← deflateEnd strm
      st := { st with strm := d }
  else if t == "B" then
    let b ← deflateBound strm (UInt64.ofNat st.N)
    let b2 ← deflateBound_z strm (UInt64.ofNat st.N)
    st := { st with out := st.out ++ s!"B={b},{b2} " }
  else if t.startsWith "T:" then
    let a := ints (t.drop 2).toString
    let rc ← deflateTune strm (i32 (a.getD 0 0)) (i32 (a.getD 1 0)) (i32 (a.getD 2 0)) (i32 (a.getD 3 0))
    st := { st with out := st.out ++ s!"T={rc.toInt} " }
  else if t == "Q" then
    let (rc, p, b) ← deflatePending strm true true
    st := { st with out := st.out ++ s!"Q={rc.toInt},{p.getD 7},{(b.getD 7).toInt} " }
  else if t == "U" then
    let (rc, b) ← deflateUsed strm true
    st := { st with out := st.out ++ s!"U={rc.toInt},{(b.getD 7).toInt} " }
  else if t.startsWith "H:" then
    let h ← mkHeader ((t.drop 2).toString.splitOn ":")
    let rc ← deflateSetHeader strm h
    st := { st with out := st.out ++ s!"H={rc.toInt} " }
  else if t == "E" then
    let rc ← deflateEnd strm
    st := { st with out := st.out ++ s!"E={rc.toInt} ", ended := true }
  else
    ub s!"bad token {t}"
  return st

def initSess : M Sess := do
  let strm ← allocZStream
  zwr strm (fun z => { z with zalloc := FnPtr.null, zfree := FnPtr.null, «opaque» := .null })
  let inb0 ← allocBytes #[0]
  return { strm, inb := inb0, N := 0, fed := 0, consumed := 0, outb := .null, ocap := 0, ended := false, out := "",
           done := false }

def finishSess (st0 : Sess) : M String := do
  let mut st := st0
  let used ← if st.outb == .null then pure 0 else do
    match (← zrd st.strm (·.next_out)) with
    | .ref _ o => pure o
    | _ => pure 0
  if !st.ended then
    let rc ← deflateEnd st.strm
    st := { st with out := st.out ++ s!"E={rc.toInt} " }
  let bs ← if st.outb == .null then pure #[] else readBytes st.outb used
  return st.out ++ "OUT=" ++ hexOf bs


def runSession (toks : List String) : M String := do
  let mut st ← initSess
  for t in toks do
    if st.done then break
    st ← runToken st t
  if st.done then return st.out
  finishSess st

def runCompress (fn : String) (lv : Int32) (dc : Nat) (src : Array UInt8) : M String := do
  let s ← allocBytes (if src.isEmpty then #[0] else src)
  let d ← allocBytes (Array.replicate (dc + 1) 0)
  let n := UInt64.ofNat src.size
  let dcu := UInt64.ofNat dc
  let (rc, dl) ← match fn with
    | "compress2" => Zlib.Compress.compress2 d (some dcu) s n lv
    | "compress" => Zlib.Compress.compress d (some dcu) s n
    | "compress2_z" => do
      let (rc, dl) ← Zlib.Compress.compress2_z d (some dcu) s n lv
      pure (rc, dl.getD 0)
    | _ => do
      let (rc, dl) ← Zlib.Compress.compress_z d (some dcu) s n
      pure (rc, dl.getD 0)
  let bs ← readBytes d (if dl ≤ dcu then dl.toNat else 0)
  return s!"{rc.toInt},{dl}," ++ hexOf bs

def handle (fn : String) (args : List String) : Except String String :=
  match fn with
  | "session" =>
    let r := C.run (runSession args) startHeap
    match r with
    | .ok (s, _) => .ok s
    | .error f => .ok (showFault f)
  | "compress2" | "compress" | "compress2_z" | "compress_z" =>
    match args with
    | [lv, dc, hx] => do
      let src ← parseHex (hx.drop 1).toString
      let r := C.run (runCompress fn (Int32.ofInt (lv.toInt?.getD 0)) (← parseNat dc) src) startHeap
      match r with
      | .ok (s, _) => .ok s
      | .error f => .ok (showFault f)
    | _ => .error "arity"
  | "bound" =>
    match args with
    | [l] => do
      let v ← parseU64 l
      .ok s!"{Zlib.Compress.compressBound v},{Zlib.Compress.compressBound_z v}"
    | _ => .error "arity"
  | _ => .error s!"unknown {fn}"

def main : IO UInt32 := mainLoop handle
