import ZlibF.Zlib.«inftrees.c»
import DiffTest.Common

/-!
Lean side of the differential test for `inftrees.c`. It calls the translation in
`ZlibF/Zlib/inftrees.c.lean` (the module the proofs are about), nothing else.
The arrays of the C driver (lens[320], work[288], codes[1444]) are the three array fields of one inflate state.
-/

open DiffTest C

def fnvStep (h : UInt64) (b : UInt64) : UInt64 := (h ^^^ (b &&& 0xff)) * 1099511628211
def fnvInit : UInt64 := 14695981039346656037

def hashCodes (a : Array Code) : UInt64 :=
  a.foldl (fun h c => fnvStep (fnvStep (fnvStep (fnvStep h c.op.toUInt64) c.bits.toUInt64) c.val.toUInt64)
    ((c.val.toUInt64 >>> (8 : UInt64)))) fnvInit

def hashWords (a : Array UInt16) : UInt64 :=
  a.foldl (fun h w => fnvStep (fnvStep h w.toUInt64) ((w.toUInt64 >>> (8 : UInt64)))) fnvInit

def heap0 : Heap := { Heap.empty with static := Zlib.Inftrees.initStatics default }

def fixedTest : String :=
  let st : InflateState := default
  let h := { heap0 with istates := upd heap0.istates 0 (some st), nextBlk := 1 }
  match run (Zlib.Inftrees.inflate_fixed (some (.tab 0))) h with
  | .error f => showFault f
  | .ok (_, h) =>
    match h.istates 0 with
    | none => "FAULT state vanished"
    | some st =>
      let rd (p : CodePtr) (n : Nat) : Except Fault (Array Code) :=
        match run (do
          let mut a : Array Code := #[]
          for i in [0:n] do a := a.push (← Ptr.index p i)
          pure a) h with
        | .ok (a, _) => .ok a
        | .error f => .error f
      match rd st.lencode 512, rd st.distcode 32 with
      | .ok l, .ok d => s!"{(hashCodes l).toNat} {st.lenbits.toNat} {(hashCodes d).toNat} {st.distbits.toNat}"
      | .error f, _ => showFault f
      | _, .error f => showFault f

def tableTest (type bits loff toff : Nat) (lens : String) : Except String String := do
  let ls := if lens == "-" then "" else lens
  let codes := ls.length
  if loff + codes > 320 || toff > 1444 then throw "out of range"
  let mut la : Array UInt16 := Array.replicate 320 0
  let mut i := 0
  for c in ls.toList do
    match hexVal c.toNat.toUInt8 with
    | some v => la := la.set! (loff + i) v.toUInt16
    | none => throw "bad digit"
    i := i + 1
  let st : InflateState :=
    { (default : InflateState) with lens := la, work := Array.replicate 288 0xABCD,
                                    codes := Array.replicate 1444 ⟨0xAA, 0xBB, 0xCCCC⟩ }
  let h := { heap0 with istates := upd heap0.istates 0 (some st), nextBlk := 1 }
  let tbl : CodePtr := .ref (.istate_codes 0) toff
  match run (Zlib.Inftrees.inflate_table type.toUInt32 (.ref (.istate_lens 0) loff) codes.toUInt32 tbl
      bits.toUInt32 (.ref (.istate_work 0) 0)) h with
  | .error f => return showFault f
  | .ok ((ret, t', b'), h') =>
    match h'.istates 0 with
    | none => return "FAULT state vanished"
    | some st' =>
      let adv : Int := match t' with
        | .ref _ o => (o : Int) - toff
        | .null => 0
      return s!"{ret.toInt} {b'.toNat} {adv} {(hashCodes st'.codes).toNat} {(hashWords st'.work).toNat}"

def handle (fn : String) (args : List String) : Except String String :=
  match fn, args with
  | "inflate_table", [t, b, lo, to, l] => do
    tableTest (← parseNat t) (← parseNat b) (← parseNat lo) (← parseNat to) l
  | "inflate_fixed", [] => .ok fixedTest
  | _, _ => throw s!"unknown function or wrong arity: {fn}"

def main : IO UInt32 := mainLoop handle
