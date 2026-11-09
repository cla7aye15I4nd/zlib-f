import ZlibF.Proof.«inflate.c.header-progress-history»
import ZlibF.Proof.«inflate.c.header-progress-complete»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- From a zero-counter state, a finite actual waiting/rebuffer segment
and a completing LENLENS read prefix supply the independent alphabet at
the actual constructor cut. The seed is the initial held word; subsequent
bytes are the original public observations or bytes pulled by completion.
The original TABLE count-field origin and constructor/payload continuation
remain separate obligations. Each caller edit retains the explicit
accepted per-object platform bound in LenlensWaitingTrace. -/
theorem LenlensWaitingTrace.alphabet_at_constructor
    {start after : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {input output : List UInt8}
    (initial : DefaultOriginState start r zs z s) (allocator : DefAlloc z)
    (zero : s.«have» = 0) (history : LenlensWaitingTrace start r zs after input output) :
    ∃ stream state, DefaultOriginState after r zs stream state ∧ DefAlloc stream ∧ output = [] ∧
      ∀ c bs, c.strm = some r → c.st = some (.tab zs) → state.mode = LENLENS →
        Bytes after stream.next_in stream.avail_in.toNat bs →
        3 * (state.ncode.toNat - state.«have».toNat) ≤
          (Zlib.Inflate.Proofs.stream (dispatchRegs stream state) bs).length →
        ∃ regs used filled, used ≤ bs.length ∧
          BitInv after regs (bs.drop used) ∧ filled.WellFormed ∧ Good3 filled.lens 19 ∧
          runX (inflate_LENLENS c) (dispatchRegs stream state) after =
            runX (llTail c) regs (setI after zs filled) ∧
          ∀ future, readCodeLenLens state.ncode.toNat
            (((natBits s.bits.toNat s.hold.toNat ++ bytesBits input) ++ bytesBits (bs.take used)) ++ future) = some
            (Zlib.Inftrees.Proofs.lensOf (fun k => (filled.lens.getD k 0).toNat) 19,
             natBits regs.bits.toNat regs.hold.toNat ++ future) := by
  obtain ⟨stream, state, current, currentAllocator, trace, empty⟩ :=
    history.sound_from_zero initial allocator zero
  refine ⟨stream, state, current, currentAllocator, empty, ?_⟩
  intro c bs _streamPointer statePointer mode inputBytes enough
  obtain ⟨ncode, haveBound, _nlen, _ndist, prefixValues⟩ := current.headerLengths mode
  have view := header_input_view_of_bytes (s := state) inputBytes current.held
  exact inflate_LENLENS_resumed_alphabet_prefix statePointer current.good.live.hs
    current.good.inv.wf ncode haveBound prefixValues view trace enough

/-- General phase composition starts from the actual stored prefix, which
may already be nonempty after the call that first entered LENLENS.
Its supplied phase index is advanced only by subsequent real observations.
The phase-entry producer must establish this initial relation. -/
theorem LenlensWaitingTrace.alphabet_from_progress
    {start after : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {input output : List UInt8} {received : List Bool}
    (initial : DefaultOriginState start r zs z s) (allocator : DefAlloc z)
    (progress : LenlensProgress s s.hold s.bits received)
    (history : LenlensWaitingTrace start r zs after input output) :
    ∃ stream state, DefaultOriginState after r zs stream state ∧ DefAlloc stream ∧ output = [] ∧
      ∀ c bs, c.strm = some r → c.st = some (.tab zs) → state.mode = LENLENS →
        Bytes after stream.next_in stream.avail_in.toNat bs →
        3 * (state.ncode.toNat - state.«have».toNat) ≤
          (Zlib.Inflate.Proofs.stream (dispatchRegs stream state) bs).length →
        ∃ regs used filled, used ≤ bs.length ∧
          BitInv after regs (bs.drop used) ∧ filled.WellFormed ∧ Good3 filled.lens 19 ∧
          runX (inflate_LENLENS c) (dispatchRegs stream state) after =
            runX (llTail c) regs (setI after zs filled) ∧
          ∀ future, readCodeLenLens state.ncode.toNat
            (((received ++ bytesBits input) ++ bytesBits (bs.take used)) ++ future) = some
            (Zlib.Inftrees.Proofs.lensOf (fun k => (filled.lens.getD k 0).toNat) 19,
             natBits regs.bits.toNat regs.hold.toNat ++ future) := by
  obtain ⟨stream, state, current, currentAllocator, trace, empty⟩ :=
    history.sound initial allocator progress
  refine ⟨stream, state, current, currentAllocator, empty, ?_⟩
  intro c bs _streamPointer statePointer mode inputBytes enough
  obtain ⟨ncode, haveBound, _nlen, _ndist, prefixValues⟩ := current.headerLengths mode
  have view := header_input_view_of_bytes (s := state) inputBytes current.held
  exact inflate_LENLENS_resumed_alphabet_prefix statePointer current.good.live.hs
    current.good.inv.wf ncode haveBound prefixValues view trace enough

#print axioms LenlensWaitingTrace.alphabet_from_progress

#print axioms LenlensWaitingTrace.alphabet_at_constructor
end Zlib.Inflate.Proofs
