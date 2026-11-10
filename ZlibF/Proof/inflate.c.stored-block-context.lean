import ZlibF.Proof.«inflate.c.stored-block-producer»
import ZlibF.Proof.«inflate.c.header-loop-continuation»

namespace Zlib.Inflate.Proofs.StoredBlockProducer
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.StoredHistory Zlib.Inflate.Proofs.WrapperGlue
open Zlib.Inflate.Proofs.StoredGeneric Zlib.Inflate.Proofs.HeaderSourceTrace
set_option autoImplicit false

/-- The real normal TYPE dispatch advances the same original main call
into its STORED consumer. Both loop endpoints are terminating source
states, so equality follows from actual finite-trace uniqueness, without
restarting fuel or assuming a final payload result. -/
theorem StoredBlockEntry.main_consumer
    {c : Ctx} {start h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs future dictionary prior payload logical credited : List UInt8}
    {final : Nat} {rest : List Bool}
    (E : Env c h r zs z s) (origin : DefaultOriginState h r zs z s)
    (packet : DispatchBuffers h r l bs) (bits : l.bits.toNat ≤ 39)
    (mainCut : runX (inflate_run c) IL.init start =
      runX (xwhile (pure true) (inflate_dispatch c)) l h)
    (entry : StoredBlockEntry c h r zs z s l bs future dictionary prior payload logical credited final rest) :
    ∃ regs after state used,
      used ≤ bs.length ∧ runX (inflate_dispatch c) l h = .ok ((.ok (), regs), after) ∧
      runX (inflate_run c) IL.init start = runX (xwhile (pure true) (inflate_dispatch c)) regs after ∧
      DefaultOriginState after r zs z state ∧ state.mode = STORED ∧ state.last = u2i final.toUInt32 ∧
      DispatchBuffers after r regs (bs.drop used) ∧ regs.bits.toNat ≤ 39 ∧
      AdlerCredit z state credited ∧
      InflateDictionary after state (logical.drop (logical.length - 2 ^ state.wbits.toNat)) ∧
      regs.next = inputAdvance l.next used ∧ regs.have_.toNat + used = l.have_.toNat ∧
      regs.put = l.put ∧ regs.left = l.left ∧ regs.in_ = l.in_ ∧ regs.out_ = l.out_ ∧
      StoredHeaderObservation c after r zs z state regs (bs.drop used) future dictionary prior payload credited rest := by
  obtain ⟨regs, after, state, used, bound, actual, current, mode, flag,
    currentPacket, currentBits, credit, saved, next, haveCount, put, left, in_, out_, header⟩ :=
    StoredBlockEntry.header_consumer E entry
  have currentEnv : Env c after r zs z state := ⟨E.strm, E.st, current.good.live.hz, current.good.live.hs⟩
  have continuation := loop_prefix_continuation E origin packet bits currentEnv current
    currentPacket currentBits (.step .begin actual)
  exact ⟨regs, after, state, used, bound, actual, mainCut.trans continuation,
    current, mode, flag, currentPacket, currentBits, credit, saved,
    next, haveCount, put, left, in_, out_, header⟩

/-- All valid stored block tag cases in the unchanged original call:
TYPE pause and input exhaustion give actual whole-main leave; the
normal case gives the real same-call STORED/LEN/COPY continuation.
Both final and non-final blocks, prior histories, held bits, current/future
input splits, flush values and output capacities remain unrestricted. -/
theorem stored_source_main_consumer
    {c : Ctx} {start h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs future dictionary prior payload logical credited : List UInt8}
    {final : Nat} {middle bodyInput rest : List Bool}
    (E : Env c h r zs z s) (origin : DefaultOriginState h r zs z s)
    (packet : DispatchBuffers h r l bs) (modes : s.mode = TYPE ∨ s.mode = TYPEDO)
    (last : s.last = 0) (bits : l.bits.toNat ≤ 39) (credit : AdlerCredit z s credited)
    (saved : InflateDictionary h s (logical.drop (logical.length - 2 ^ s.wbits.toNat)))
    (mainCut : runX (inflate_run c) IL.init start =
      runX (xwhile (pure true) (inflate_dispatch c)) l h)
    (first : readBits 1 (stream l bs ++ bytesBits future) = some (final, middle))
    (second : readBits 2 middle = some (0, bodyInput))
    (body : Body dictionary 0 prior bodyInput rest (prior ++ payload)) :
    (∃ pulled used, used ≤ bs.length ∧
      runX (inflate_run c) IL.init start = .ok ((.error Ex.leave, pulled), h) ∧
      DispatchBuffers h r pulled (bs.drop used) ∧ pulled.bits.toNat ≤ 39 ∧
      stream pulled (bs.drop used) = stream l bs ∧
      pulled.next = inputAdvance l.next used ∧ pulled.have_.toNat + used = l.have_.toNat ∧
      pulled.put = l.put ∧ pulled.left = l.left ∧ pulled.in_ = l.in_ ∧ pulled.out_ = l.out_) ∨
    (∃ regs after state used,
      used ≤ bs.length ∧ runX (inflate_dispatch c) l h = .ok ((.ok (), regs), after) ∧
      runX (inflate_run c) IL.init start = runX (xwhile (pure true) (inflate_dispatch c)) regs after ∧
      DefaultOriginState after r zs z state ∧ state.mode = STORED ∧ state.last = u2i final.toUInt32 ∧
      DispatchBuffers after r regs (bs.drop used) ∧ regs.bits.toNat ≤ 39 ∧
      AdlerCredit z state credited ∧
      InflateDictionary after state (logical.drop (logical.length - 2 ^ state.wbits.toNat)) ∧
      regs.next = inputAdvance l.next used ∧ regs.have_.toNat + used = l.have_.toNat ∧
      regs.put = l.put ∧ regs.left = l.left ∧ regs.in_ = l.in_ ∧ regs.out_ = l.out_ ∧
      StoredHeaderObservation c after r zs z state regs (bs.drop used) future dictionary prior payload credited rest) := by
  rcases stored_dispatch_body_source E origin packet modes last bits credit saved first second body with
    ⟨_type, _pause, actual⟩ | waiting | entry
  · have loop := xwhile_run_chain (inflate_dispatch c) (fun _ => l) (fun _ => h)
      0 (by unfold fuel; decide) Ex.leave l h (by intro j impossible; omega) actual
    exact Or.inl ⟨l, 0, by omega, mainCut.trans loop, by simpa only [List.drop_zero] using packet,
      bits, by simp only [List.drop_zero], (inputAdvance_zero l.next).symm, by omega, rfl, rfl, rfl, rfl⟩
  · obtain ⟨pulled, used, bound, actual, currentPacket, currentBits, source,
      next, count, put, left, in_, out_⟩ := waiting
    have loop := xwhile_run_chain (inflate_dispatch c) (fun _ => l) (fun _ => h)
      0 (by unfold fuel; decide) Ex.leave pulled h (by intro j impossible; omega) actual
    exact Or.inl ⟨pulled, used, bound, mainCut.trans loop, currentPacket, currentBits,
      source, next, count, put, left, in_, out_⟩
  · exact Or.inr (StoredBlockEntry.main_consumer E origin packet bits mainCut entry)

#print axioms StoredBlockEntry.main_consumer
#print axioms stored_source_main_consumer
end Zlib.Inflate.Proofs.StoredBlockProducer
