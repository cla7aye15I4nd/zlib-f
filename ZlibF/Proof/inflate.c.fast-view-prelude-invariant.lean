import ZlibF.Proof.«inflate.c.fast-view-loop-entry-core»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- Proof-only cut at the translated `inflate_fast` loop entry. The
statements before the returned pair occur in their original source order. -/
def fastEntryPrefix (strm : ZStreamPtr)
    (start : UInt32) : M (Zlib.Inffast.Ctx × Zlib.Inffast.L) := do
  let sm ← ldZStream strm
  let state ← castInflateState sm.state
  let in_ := sm.next_in
  let last ← in_.add (sm.avail_in - 5).toNat
  let out := sm.next_out
  let beg ← Zlib.Inffast.subn out (start - sm.avail_out)
  let end_ ← out.add (sm.avail_out - 257).toNat
  let s ← ldInflateState state
  let lmask := (← Zlib.Inffast.shl32 1 s.lenbits) - 1
  let dmask := (← Zlib.Inffast.shl32 1 s.distbits) - 1
  let c : Zlib.Inffast.Ctx := {
    strm, state, last, beg, end_, wsize := s.wsize,
    whave := s.whave, wnext := s.wnext,
    window := s.window, lcode := s.lencode,
    dcode := s.distcode, lmask, dmask }
  let l : Zlib.Inffast.L := {
    in_, out, hold := s.hold, bits := s.bits,
    here := default, op := 0, len := 0, dist := 0,
    from_ := default, broke := false,
    againL := false, againD := false }
  return (c, l)

/-- Proof-only remainder after the translated fast loop. -/
def fastAfterLoop (c : Zlib.Inffast.Ctx)
    (l : Zlib.Inffast.L) : M Unit := do
  let len := l.bits >>> 3
  let in_ ← Zlib.Inffast.subn l.in_ len
  let bits := l.bits - (len <<< 3)
  let hold := l.hold &&&
    ((← Zlib.Inffast.shl32 1 bits) - 1).toUInt64
  let ai : Int64 ←
    if ← Ptr.lt in_ c.last then do
      let d ← c.last.diff in_
      Zlib.Inffast.chk64 (5 + d.toInt)
    else do
      let d ← in_.diff c.last
      Zlib.Inffast.chk64 (5 - d.toInt)
  let ao : Int64 ←
    if ← Ptr.lt l.out c.end_ then do
      let d ← c.end_.diff l.out
      Zlib.Inffast.chk64 (257 + d.toInt)
    else do
      let d ← l.out.diff c.end_
      Zlib.Inffast.chk64 (257 - d.toInt)
  let sm ← ldZStream c.strm
  stZStream c.strm { sm with next_in := in_, next_out := l.out, avail_in := ai.toUInt64.toUInt32, avail_out := ao.toUInt64.toUInt32 }
  let s ← ldInflateState c.state
  stInflateState c.state { s with hold, bits }

/-- Proof-only remainder after the source-order fast entry prefix. -/
def fastAfterPrefix (c : Zlib.Inffast.Ctx)
    (initial : Zlib.Inffast.L) : M Unit := do
  let l ← cdoWhile (Zlib.Inffast.inflate_fast_body c)
    (fun l => do
      if l.broke then pure (false, l)
      else if ← Ptr.lt l.in_ c.last then
        pure (← Ptr.lt l.out c.end_, l)
      else pure (false, l)) initial
  fastAfterLoop c l

/-- Proof-only entry continuation with the same source statements before
the loop. -/
def fastEntryWith (strm : ZStreamPtr) (start : UInt32)
    (k : Zlib.Inffast.Ctx → Zlib.Inffast.L → M Unit) : M Unit := do
  let sm ← ldZStream strm
  let state ← castInflateState sm.state
  let in_ := sm.next_in
  let last ← in_.add (sm.avail_in - 5).toNat
  let out := sm.next_out
  let beg ← Zlib.Inffast.subn out (start - sm.avail_out)
  let end_ ← out.add (sm.avail_out - 257).toNat
  let s ← ldInflateState state
  let lmask := (← Zlib.Inffast.shl32 1 s.lenbits) - 1
  let dmask := (← Zlib.Inffast.shl32 1 s.distbits) - 1
  let c : Zlib.Inffast.Ctx := {
    strm, state, last, beg, end_, wsize := s.wsize,
    whave := s.whave, wnext := s.wnext,
    window := s.window, lcode := s.lencode,
    dcode := s.distcode, lmask, dmask }
  let l : Zlib.Inffast.L := {
    in_, out, hold := s.hold, bits := s.bits,
    here := default, op := 0, len := 0, dist := 0,
    from_ := default, broke := false,
    againL := false, againD := false }
  k c l

/-- The continuation cut is definitionally the translated fast call. -/
theorem inflate_fast_entry_with
    (strm : ZStreamPtr) (start : UInt32) :
    Zlib.Inffast.inflate_fast strm start =
      fastEntryWith strm start fastAfterPrefix := by
  rfl

/-- Running the source-order prefix then a continuation has the same
behavior as returning its context and registers first. -/
theorem fastEntryWith_eq_bind
    (strm : ZStreamPtr) (start : UInt32)
    (k : Zlib.Inffast.Ctx → Zlib.Inffast.L → M Unit) :
    fastEntryWith strm start k =
      (do
        let pair ← fastEntryPrefix strm start
        k pair.1 pair.2) := by
  funext h
  unfold fastEntryWith fastEntryPrefix
  simp only [bind_app]
  repeat' (split <;> try rfl)

/-- The return-pair cut is also exactly the translated fast call. -/
theorem inflate_fast_prefix_split
    (strm : ZStreamPtr) (start : UInt32) :
    Zlib.Inffast.inflate_fast strm start =
      (do
        let pair ← fastEntryPrefix strm start
        fastAfterPrefix pair.1 pair.2) := by
  rw [inflate_fast_entry_with, fastEntryWith_eq_bind]

/-- The exact source-order prelude runs safely on general caller byte views.
Its pointer offsets and masks equal those used by the loop invariant. -/
theorem fastEntryPrefix_run
    {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState}
    {slow : IL} {bs : List UInt8}
    (good : Good h r zs z s)
    (fit : ZlibF.PlatformMemory.ByteObjectsFit h)
    (buffers : DispatchBuffers h r slow bs)
    (tables : DataTablesSafe h s)
    (inputCursor : z.next_in = slow.next)
    (inputCount : z.avail_in = slow.have_)
    (outputCursor : z.next_out = slow.put)
    (outputCount : z.avail_out = slow.left)
    (stateHold : s.hold = slow.hold)
    (stateBits : s.bits = slow.bits)
    (fast : (slow.have_ >= 6 && slow.left >= 258 &&
      slow.bits < 8) = true) :
    ∃ (ir dest : BRef) (io oo : Nat),
      slow.next = .ref ir io ∧
      slow.put = .ref dest oo ∧
      C.run (fastEntryPrefix (some r) slow.out_) h =
        .ok (({
          strm := some r, state := some (.tab zs),
          last := .ref ir (io + slow.have_.toNat - 5),
          beg := .ref dest
            (oo - (slow.out_.toNat - slow.left.toNat)),
          end_ := .ref dest
            (oo + slow.left.toNat - 257),
          wsize := s.wsize, whave := s.whave,
          wnext := s.wnext, window := s.window,
          lcode := s.lencode, dcode := s.distcode,
          lmask := ((1 : UInt32) <<< s.lenbits) - 1,
          dmask := ((1 : UInt32) <<< s.distbits) - 1 },
          {
          in_ := slow.next, out := slow.put,
          hold := slow.hold, bits := slow.bits,
          here := default, op := 0, len := 0, dist := 0,
          from_ := default, broke := false,
          againL := false, againD := false }), h) := by
  obtain ⟨ir, dest, io, oo, nextPtr, putPtr,
    lastRun, begRun, endRun⟩ :=
    buffers.fast_pointer_setup good fit fast
  obtain ⟨_, _, _, _, _, lenSafe⟩ :=
    tables.lengthTable
  obtain ⟨_, _, _, _, _, distSafe⟩ :=
    tables.distanceTable
  have lenWidth : s.lenbits.toNat < 32 := by
    have width := lenSafe.1
    omega
  have distWidth : s.distbits.toNat < 32 := by
    have width := distSafe.1
    omega
  change (Ptr.add slow.next (slow.have_ - 5).toNat) h =
      .ok (.ref ir (io + slow.have_.toNat - 5), h)
    at lastRun
  change (Zlib.Inffast.subn slow.put
      (slow.out_ - slow.left)) h =
      .ok (.ref dest
        (oo - (slow.out_.toNat - slow.left.toNat)), h)
    at begRun
  change (Ptr.add slow.put (slow.left - 257).toNat) h =
      .ok (.ref dest (oo + slow.left.toNat - 257), h)
    at endRun
  refine ⟨ir, dest, io, oo, nextPtr, putPtr, ?_⟩
  change (fastEntryPrefix (some r) slow.out_) h =
    .ok (({
      strm := some r, state := some (.tab zs),
      last := .ref ir (io + slow.have_.toNat - 5),
      beg := .ref dest
        (oo - (slow.out_.toNat - slow.left.toNat)),
      end_ := .ref dest
        (oo + slow.left.toNat - 257),
      wsize := s.wsize, whave := s.whave,
      wnext := s.wnext, window := s.window,
      lcode := s.lencode, dcode := s.distcode,
      lmask := ((1 : UInt32) <<< s.lenbits) - 1,
      dmask := ((1 : UInt32) <<< s.distbits) - 1 },
      {
      in_ := slow.next, out := slow.put,
      hold := slow.hold, bits := slow.bits,
      here := default, op := 0, len := 0, dist := 0,
      from_ := default, broke := false,
      againL := false, againD := false }), h)
  unfold fastEntryPrefix
  simp only [bind_app, ldZStream_ok good.live.hz,
    good.live.zst, castInflateState_ok,
    inputCursor, inputCount, outputCursor, outputCount]
  simp only [lastRun, begRun, endRun,
    ldInflateState_tab good.live.hs,
    Zlib.Inffast.Proofs.shl32_eq lenWidth,
    Zlib.Inffast.Proofs.shl32_eq distWidth,
    pure_app, stateHold, stateBits]

end Zlib.Inflate.Proofs
