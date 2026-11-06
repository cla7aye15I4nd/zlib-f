import ZlibF.Zlib.«inffast.c»
import ZlibF.Zlib.«inftrees.c»
import DiffTest.Common

/-!
Lean side of the differential test for `inffast.c`. It calls the translation in
`ZlibF/Zlib/inffast.c.lean` (the module the proofs are about); the decoding tables are built with the
translation of `inftrees.c` (tested on its own), the way `inflate()` builds them.
-/

open DiffTest C

def heap0 : Heap := { Heap.empty with static := Zlib.Inftrees.initStatics default }

def hexOf (a : Array UInt8) : String :=
  a.foldl (fun s b =>
    let d := "0123456789abcdef".toList
    s.push (d[(b / 16).toNat]!) |>.push (d[(b % 16).toNat]!)) ""

def digits (s : String) : Except String (Array UInt16) := do
  if s == "-" then return #[]
  let mut a : Array UInt16 := #[]
  for c in s.toList do
    match hexVal c.toNat.toUInt8 with
    | some v => a := a.push v.toUInt16
    | none => throw "bad digit"
  return a

def optHex (s : String) : Except String (Array UInt8) := if s == "-" then pure #[] else parseHex s

/-- The text of a `char *`, or `-` for NULL. -/
def readMsg (p : BPtr) : M String := do
  if p == .null then return "-"
  let n ← strlenB p
  let mut a : Array UInt8 := #[]
  for i in [0:n.toNat] do
    a := a.push (← index8 p i)
  pure (String.fromUTF8! (ByteArray.mk a))

def offOf : BPtr → Nat
  | .ref _ o => o
  | .null => 0

/-- `Ok none`: the tables were rejected (TABFAIL). -/
def runCase (tab : String) (wsize whave wnext : Nat) (hold : UInt64) (bits avail_out : Nat)
    (window prior input : Array UInt8) (lit dist : Array UInt16) (fixed : Bool) : M String := do
  let inp ← allocBytes input
  let outBuf ← allocBytes (prior ++ Array.replicate avail_out 0xa5)
  let outp ← outBuf.add prior.size
  let win ← if wsize == 0 then pure (Ptr.null : BPtr) else allocBytes window
  let some sref ← allocZStream | ub "allocation failed"
  let some iref ← allocInflateState | ub "allocation failed"
  let ipt : InflateStatePtr := some iref
  let spt : ZStreamPtr := some sref
  let id := match iref with | .tab i => i
  let nlen := lit.size
  let st : InflateState :=
    { (default : InflateState) with
        strm := spt, mode := LEN, wsize := wsize.toUInt32, whave := whave.toUInt32, wnext := wnext.toUInt32,
        window := win, hold := hold, bits := bits.toUInt32, sane := 1, nlen := nlen.toUInt32,
        ndist := dist.size.toUInt32,
        lens := (lit ++ dist) ++ Array.replicate (320 - nlen - dist.size) 0,
        work := Array.replicate 288 0, codes := Array.replicate 1444 ⟨0, 0, 0⟩ }
  stInflateState ipt st
  let mut tabfail := false
  if fixed then
    Zlib.Inftrees.inflate_fixed ipt
  else
    let next0 : CodePtr := .ref (.istate_codes id) 0
    let s ← ldInflateState ipt
    stInflateState ipt { s with next := next0, lencode := next0, lenbits := 9 }
    let (ret, next1, lb) ← Zlib.Inftrees.inflate_table LENS (.ref (.istate_lens id) 0) nlen.toUInt32 next0 9
      (.ref (.istate_work id) 0)
    let s ← ldInflateState ipt
    stInflateState ipt { s with next := next1, lenbits := lb }
    if ret != 0 then tabfail := true
    else
      let s ← ldInflateState ipt
      stInflateState ipt { s with distcode := next1, distbits := 6 }
      let (ret, next2, db) ← Zlib.Inftrees.inflate_table DISTS (.ref (.istate_lens id) nlen) dist.size.toUInt32
        next1 6 (.ref (.istate_work id) 0)
      let s ← ldInflateState ipt
      stInflateState ipt { s with next := next2, distbits := db }
      if ret != 0 then tabfail := true
  if tabfail then return "TABFAIL"
  let zs0 : ZStream := default
  let zs : ZStream := { zs0 with next_in := inp }
  let zs : ZStream := { zs with avail_in := input.size.toUInt32, next_out := outp }
  let zs : ZStream := { zs with avail_out := avail_out.toUInt32, state := StateRef.ofInflateState ipt }
  stZStream spt zs
  Zlib.Inffast.inflate_fast spt (prior.size + avail_out).toUInt32
  let sm ← ldZStream spt
  let s ← ldInflateState ipt
  let msg ← readMsg sm.msg
  let mut a : Array UInt8 := #[]
  for i in [0:prior.size + avail_out] do
    a := a.push (← index8 outBuf i)
  let inOff := offOf sm.next_in
  let outOff := offOf sm.next_out
  let hx := hexOf a
  return String.intercalate " " [toString s.mode.toNat, msg, toString inOff, toString sm.avail_in.toNat,
    toString outOff, toString sm.avail_out.toNat, toString s.hold.toNat, toString s.bits.toNat, hx]

def handle (fn : String) (args : List String) : Except String String :=
  match fn, args with
  | "inflate_fast", [tab, ws, wh, wn, hd, bt, ao, win, pri, inp] => do
    let wsize ← parseNat ws
    let window ← optHex win
    if window.size != wsize then throw "window length"
    let prior ← optHex pri
    let input ← parseHex inp
    let (fixed, lit, dist) ←
      if tab == "fixed" then pure (true, (#[] : Array UInt16), (#[] : Array UInt16))
      else if tab.startsWith "dyn:" then
        match (tab.drop 4).toString.splitOn ":" with
        | [l, d] => do pure (false, ← digits l, ← digits d)
        | _ => throw "bad tab"
      else throw "bad tab"
    let r := runCase tab wsize (← parseNat wh) (← parseNat wn) (← parseU64 hd) (← parseNat bt) (← parseNat ao)
      window prior input lit dist fixed
    return match run r heap0 with
      | .ok (s, _) => s
      | .error f => showFault f
  | _, _ => throw s!"unknown function or wrong arity: {fn}"

def main : IO UInt32 := mainLoop handle
