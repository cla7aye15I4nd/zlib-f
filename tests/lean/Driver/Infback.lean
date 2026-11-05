import ZlibF.Zlib.«infback.c»
import ZlibF.Zlib.«crc32.c»
import DiffTest.Common

/-!
Lean side of the differential test for `infback.c`; see `tests/c/infback.c` for the format of a case. The call-backs
`in` and `out` are Lean functions of the heap (caller code): their counters live in the byte block `ctl` that is passed
as the descriptor; the input is one block and `in` returns a pointer into it, as the C call-back does.
-/

open DiffTest C Zlib.Infback
open Zlib.Inflate (wrZ)

def heap0 : Heap :=
  { Heap.empty with static := Zlib.Crc32.initStatics (Zlib.Inftrees.initStatics default) }

/-- Same heap, tables rebuilt with exactly the block numbers below `nextBlk` (driver only). -/
def flatten : M Unit := fun h =>
  let n := h.nextBlk
  let bs := Array.ofFn (n := n) fun i => h.bytes i.val
  let ws := Array.ofFn (n := n) fun i => h.words i.val
  let ro := Array.ofFn (n := n) fun i => h.ro i.val
  let zs := Array.ofFn (n := n) fun i => h.streams i.val
  let gh := Array.ofFn (n := n) fun i => h.gzheaders i.val
  let ds := Array.ofFn (n := n) fun i => h.dstates i.val
  let is := Array.ofFn (n := n) fun i => h.istates i.val
  let gs := Array.ofFn (n := n) fun i => h.gzstates i.val
  .ok ((), { h with
    bytes := ⟨bs⟩
    words := ⟨ws⟩
    ro := ⟨ro⟩
    streams := ⟨zs⟩
    gzheaders := ⟨gh⟩
    dstates := ⟨ds⟩
    istates := ⟨is⟩
    gzstates := ⟨gs⟩ })

/-- The 32-bit little-endian word `i` of the control block. -/
def get32 (ctl : BPtr) (i : Nat) : M UInt32 := do
  let b0 ← index8 ctl (4 * i); let b1 ← index8 ctl (4 * i + 1); let b2 ← index8 ctl (4 * i + 2); let b3 ← index8 ctl (4 * i + 3)
  return b0.toUInt32 ||| (b1.toUInt32 <<< 8) ||| (b2.toUInt32 <<< 16) ||| (b3.toUInt32 <<< 24)

def set32 (ctl : BPtr) (i : Nat) (v : UInt32) : M Unit := do
  store8 (← ctl.add (4 * i)) v.toUInt8
  store8 (← ctl.add (4 * i + 1)) (v >>> 8).toUInt8
  store8 (← ctl.add (4 * i + 2)) (v >>> 16).toUInt8
  store8 (← ctl.add (4 * i + 3)) (v >>> 24).toUInt8

-- `flatten` is a driver-only step (see Inflate.lean): the call-backs rebuild the heap tables as finite maps.
-- control block words: 0 pos, 1 nin, 2 nout, 3 olen, 4 len, 5 inch, 6 opts, 7.. olens[0..15]

def hexDigit (n : UInt8) : String := String.singleton (Char.ofNat (if n < 10 then 48 + n.toNat else 87 + n.toNat))

def readBytes (p : BPtr) (n : Nat) : M (Array UInt8) := do
  let mut a : Array UInt8 := #[]
  for i in [0:n] do
    a := a.push (← index8 p i)
  return a

def hexs (bs : Array UInt8) : String :=
  bs.foldl (fun (acc : String) (b : UInt8) => acc ++ hexDigit (b >>> 4) ++ hexDigit (b &&& 15)) ""

def runCase (wb : Int32) (inch : Nat) (opts : Nat) (input : Array UInt8) : M String := do
  let inb ← allocBytes (input ++ #[0])        -- one spare byte: a valid pointer for the empty input
  let obuf ← allocBytes (Array.replicate (1 <<< 20) 0)
  let ctl ← allocBytes (Array.replicate 128 0)
  set32 ctl 4 input.size.toUInt32
  set32 ctl 5 (if inch == 0 then 1 else inch).toUInt32
  set32 ctl 6 opts.toUInt32
  let inCb : InCb := fun d buf => do
    flatten
    let pos ← get32 d 0
    let len ← get32 d 4
    let inch ← get32 d 5
    set32 d 1 ((← get32 d 1) + 1)
    let n := if len - pos < inch then len - pos else inch
    set32 d 0 (pos + n)
    return (n, ← inb.add pos.toNat)
  let outCb : OutCb := fun d buf len => do
    flatten
    let nout ← get32 d 2
    if nout < 16 then set32 d (7 + nout.toNat) len
    set32 d 2 (nout + 1)
    let olen ← get32 d 3
    memcpyB (← obuf.add olen.toNat) buf len.toNat
    set32 d 3 (olen + len)
    let opts ← get32 d 6
    if opts &&& 2 != 0 && nout + 1 == 1 then return 1
    if opts &&& 1 != 0 && nout + 1 == 2 then return 1
    return 0
  let strm ← allocZStream
  stZStream strm (ZStream.zeroed)
  let win ← allocB (if 0 ≤ wb.toInt && wb.toInt < 16 then 1 <<< wb.toInt.toNat else 1)
  let ver ← allocBytesRO ("1.3.2.1-motley".toUTF8.data.push 0)
  let init ← inflateBackInit_ strm wb win ver 112
  let mut line := s!"init={init.toInt}"
  if init == Z_OK then
    if opts &&& 4 != 0 then
      let k := min input.size 5
      wrZ strm fun z => { z with next_in := inb, avail_in := k.toUInt32 }
      set32 ctl 0 k.toUInt32
    let ret ← inflateBack strm inCb ctl outCb ctl
    let z ← ldZStream strm
    line := line ++ s!" rc={ret.toInt} ain={z.avail_in.toNat} nin="
    line := line ++ (match z.next_in with
      | .null => "null"
      | .ref _ off => toString off)
    let nin ← get32 ctl 1
    let nout ← get32 ctl 2
    line := line ++ s!" calls={nin.toNat},{nout.toNat} olens="
    let mut ol : List String := []
    for i in [0:(min nout.toNat 16)] do
      ol := ol ++ [toString (← get32 ctl (7 + i)).toNat]
    line := line ++ String.intercalate "," ol ++ " msg="
    if z.msg == .null then line := line ++ "-"
    else
      let mut a : Array UInt8 := #[]
      for i in [0:64] do
        let b ← index8 z.msg i
        if b == 0 then break
        a := a.push b
      line := line ++ hexs a
    line := line ++ s!" end={(← inflateBackEnd strm).toInt}"
    let olen ← get32 ctl 3
    line := line ++ " out=" ++ hexs (← readBytes obuf olen.toNat)
  return line

def handle (fn : String) (args : List String) : Except String String :=
  match fn, args with
  | "infback", [wb, inch, opts, input] => do
    let wb ← parseI64 wb
    let inch ← parseNat inch
    let opts ← parseNat opts
    let input ← match ← parseBuf input with
      | .bytes b => pure b
      | .null _ => throw "null input"
    return match C.run (runCase wb.toInt32 inch opts input) heap0 with
      | .ok (s, _) => s
      | .error f => showFault f
  | _, _ => throw s!"unknown function or wrong arity: {fn}"

def main : IO UInt32 := mainLoop handle
