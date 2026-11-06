import ZlibF.Zlib.«inflate.c»
import ZlibF.Zlib.«zutil.c»

/-! A paired execution of the actual translated decoder. No API model is imported. -/

namespace DistanceRegression
open C Zlib.Inflate

def initial : Heap :=
  { Heap.empty with static := Zlib.Crc32.initStatics (Zlib.Inftrees.initStatics Heap.empty.static) }

def localStream : M ZStreamPtr := fun h =>
  match allocZStream {h with allocOk := fun _ => true} with
  | .error e => .error e
  | .ok (p, h') => .ok (p, {h' with allocOk := h.allocOk, nalloc := h.nalloc})

def hex (p : BPtr) (n : Nat) : M String := do
  let mut out := ""
  for i in [0:n] do
    let b ← index8 p i
    out := out.push (Nat.digitChar (b.toNat / 16))
    out := out.push (Nat.digitChar (b.toNat % 16))
  return out

def observe (tag : String) (rc : Int32) (strm : ZStreamPtr) (src dst : BPtr) : M String := do
  let z ← ldZStream strm
  let s ← ldInflateState (← castInflateState z.state)
  let used := (← z.next_in.diff src).toInt.toNat
  let produced := (← z.next_out.diff dst).toInt.toNat
  return s!"{tag} rc={rc.toInt} used={used} produced={produced} avail_in={z.avail_in.toNat} avail_out={z.avail_out.toNat} total_in={z.total_in.toNat} total_out={z.total_out.toNat} hold={s.hold.toNat} bits={s.bits.toNat} mode={s.mode.toNat} length={s.length.toNat} offset={s.offset.toNat} whave={s.whave.toNat} msgnull={if z.msg == .null then 1 else 0} prefix={← hex src used} output={← hex dst produced} buffer={← hex dst 16}"

def program : M (List String) := do
  let src ← allocBytes #[0x73, 0x04, 0x42, 0x00]
  let dst ← allocBytes (Array.replicate 16 0xa5)
  let strm ← localStream
  stZStream strm ZStream.zeroed
  let version ← Zlib.Zutil.zlibVersion
  let init ← inflateInit2_ strm (-15) version 112
  if init != Z_OK then ub "distance test init failed"
  wrZ strm (fun z => {z with next_in := src, avail_in := 4, next_out := dst, avail_out := 1})
  let rc ← inflate strm Z_NO_FLUSH
  let first ← observe "first" rc strm src dst
  wrZ strm (fun z => {z with avail_out := 8})
  let rc ← inflate strm Z_NO_FLUSH
  let second ← observe "second" rc strm src dst
  let ended ← inflateEnd strm
  let z ← ldZStream strm
  let finish := s!"end rc={ended.toInt} state_null={if z.state == none then 1 else 0}"
  if ended != Z_OK || z.state != none then ub "distance test end failed"
  freeZStream strm
  freeB src
  freeB dst
  return [first, second, finish]

end DistanceRegression

def main : IO UInt32 := do
  match C.run DistanceRegression.program DistanceRegression.initial with
  | .ok (rows, after) =>
    if (List.range after.nextBlk).any after.slotUsed then
      IO.eprintln "distance test left live heap blocks"
      return 1
    for row in rows do IO.println row
    return 0
  | .error fault =>
    IO.eprintln s!"runtime fault: {repr fault}"
    return 1
