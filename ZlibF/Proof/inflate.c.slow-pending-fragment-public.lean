import ZlibF.Proof.«inflate.c.slow-copy-fragment-public»
namespace Zlib.Inflate.Proofs.SlowInputFragment
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inffast.Proofs Zlib.Inffast.Spec ZlibF.Math.LZ77Copy
open SlowMatchCompletion SlowCopyTokenPath
set_option autoImplicit false
set_option maxRecDepth 10000
/-- A resumed output fragment includes both its exact original-token
fields and the real public return on output exhaustion. -/
def PendingMatchFragmentResult {L D : List Nat} (p : CopySyntax L D) (c : Ctx)
    (h : Heap) (s : InflateState) (l : IL) (bs dict : List UInt8) (future : List Bool)
    (r : ZStreamRef) (zs : Nat) (z : ZStream) (dest : BRef) (outOffset : Nat) (output : Array UInt8) : Prop :=
    ∃ made regs after state array steps,
      made = min s.length.toNat l.left.toNat ∧
      MatchSteps c l h regs after steps ∧ steps ≤ made ∧
      Good after r zs z state ∧ DataTablesSafe after state ∧ BitInv after regs bs ∧
      InflateDictionary after state dict ∧ DecodeStateFrame s state ∧ EmitRegFrame l regs ∧
      state.length.toNat + made = s.length.toNat ∧
      state.offset = s.offset ∧ state.was = s.was ∧ state.back = s.back ∧
      regs.left.toNat + made = l.left.toNat ∧ regs.put = .ref dest (outOffset + made) ∧
      Space.get after dest = some array ∧ array.size = output.size ∧ Space.ro after dest = false ∧
      Separate regs.next regs.have_.toNat regs.put regs.left.toNat ∧
      stream regs bs = stream l bs ∧ FutureSource regs bs future p.rest ∧
      writtenBytes array (outOffset + made) (l.out_.toNat - l.left.toNat + made) =
        copyBack dict s.offset.toNat made (writtenBytes output outOffset (l.out_.toNat - l.left.toNat)) ∧
      after = setI (Space.put h dest array) zs state ∧
      DispatchBuffers after r regs bs ∧ ByteViewSizes h after ∧
      (∀ ref : BRef, Space.ro after ref = Space.ro h ref) ∧
      after.static = h.static ∧ regs.bits = l.bits ∧
      ((state.mode = LEN ∧ state.length = 0) ∨
       (state.mode = MATCH ∧ 0 < state.length.toNat ∧ regs.left = 0 ∧
        PendingSyntax p state p.rest ∧
        runX (inflate_MATCH c) regs after = .ok ((.error Ex.leave, regs), after) ∧
        runX (inflate_dispatch c) regs after = .ok ((.error Ex.leave, regs), after) ∧
        runX (xwhile (pure true) (inflate_dispatch c)) l h = .ok ((.error Ex.leave, regs), after) ∧
        PendingPublicReturn p c after state regs bs future p.rest r zs z))

/-- The initial scalar invariant supplies positivity. All outgoing fields,
buffers and bit bounds are produced by the actual resumed MATCH. -/
theorem pending_match_fragment_public_prefix
    {L D : List Nat} {p : CopySyntax L D}
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (E : Env c h r zs z s) (good : Good h r zs z s) (tables : DataTablesSafe h s)
    {dict : List UInt8} (dictionary : InflateDictionary h s dict)
    {l : IL} {bs : List UInt8} {future : List Bool} {dest : BRef} {output : Array UInt8} {outOffset : Nat}
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = MATCH) (phase : PendingSyntax p s p.rest)
    (source : FutureSource l bs future p.rest) (pending : DataPendingInvariant s)
    (initialBits : l.bits.toNat ≤ 39) (allocator : z.zalloc = .fn "zcalloc")
    (statics : Zlib.Crc32.Proofs.StaticsOK h)
    (put : l.put = .ref dest outOffset) (get : Space.get h dest = some output) (write : Space.ro h dest = false)
    (room : outOffset + l.left.toNat ≤ output.size)
    (count : l.left.toNat ≤ l.out_.toNat) (produced : l.out_.toNat - l.left.toNat ≤ outOffset)
    (privateWindow : ∀ w, s.window = .ref (.blk w) 0 → dest ≠ .blk w)
    (separate : Separate l.next l.have_.toNat l.put l.left.toNat)
    (available : s.offset.toNat ≤ dict.length + (l.out_.toNat - l.left.toNat)) :
    PendingMatchFragmentResult p c h s l bs dict future r zs z dest outOffset output := by
  obtain ⟨made, regs, after, state, array, steps, amount, trace, stepBound, current, currentTables, currentBits,
    currentDict, frame, regFrame, remaining, nextOffset, nextWas, nextBack, left, cursor, arrayGet, arraySize, arrayRo,
    finalSeparate, sameSource, futureSource, bytes, heap, finalBuffers, sizes, readonly, static, bitsEq, outcome⟩ :=
      resume_pending_match_fragment_buffers E good tables dictionary buffers mode phase source
        (by rw [pending.sane]; decide) put get write (pending.matching mode).1 room count produced privateWindow separate available
  refine ⟨made, regs, after, state, array, steps, amount, trace, stepBound, current, currentTables, currentBits,
    currentDict, frame, regFrame, remaining, nextOffset, nextWas, nextBack, left, cursor, arrayGet, arraySize, arrayRo,
    finalSeparate, sameSource, futureSource, bytes, heap, finalBuffers, sizes, readonly, static, bitsEq, ?_⟩
  rcases outcome with done | pendingOutput
  · exact Or.inl done
  · obtain ⟨nextMode, positive, zero, nextPhase, matchWait, dispatchWait⟩ := pendingOutput
    have scalarBounds := copy_syntax_scalar_bounds p
    have fields := pending_matching_fields mode phase
    have stepsBound : steps ≤ 258 := by have bound := Nat.min_le_left s.length.toNat l.left.toNat; omega
    have loop := dispatch_prefix_then_leave trace dispatchWait (by unfold fuel; omega)
    have env : Env c after r zs z state := ⟨E.strm, E.st, current.live.hz, current.live.hs⟩
    have currentStatics : Zlib.Crc32.Proofs.StaticsOK after := by
      simpa only [Zlib.Crc32.Proofs.StaticsOK, static] using statics
    have currentSane : state.sane = 1 := by rw [frame, pending.sane]
    have bitBound : regs.bits.toNat ≤ 39 := by rw [bitsEq]; exact initialBits
    have returned : PendingPublicReturn p c after state regs bs future p.rest r zs z :=
      pending_return_source env current (pending_match_safe nextMode nextPhase positive currentSane)
        allocator currentStatics finalBuffers (fun _ => currentTables) bitBound nextPhase futureSource
    exact Or.inr ⟨nextMode, positive, zero, nextPhase, matchWait, dispatchWait, loop, returned⟩

#print axioms pending_match_fragment_public_prefix
end Zlib.Inflate.Proofs.SlowInputFragment
