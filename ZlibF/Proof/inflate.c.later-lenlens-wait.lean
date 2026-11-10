import ZlibF.Proof.«inflate.c.later-dynamic-entry»
namespace Zlib.Inflate.Proofs.LaterHeader
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.HeaderPhaseView
set_option autoImplicit false
set_option maxHeartbeats 1500000

/-- A genuine partial LENLENS call retains the live header prefix and its
actual initialized packet, with arbitrary saved window and output cursor. -/
theorem lenlens_short_source
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8} {received : List Bool}
    (E : Env c h r zs z s) (origin : DefaultOriginState h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = LENLENS)
    (progress : LenlensProgress s l.hold l.bits received)
    (short : (stream l bs).length < 3 * (s.ncode.toNat - s.«have».toNat)) :
    ∃ regs state used,
      used ≤ bs.length ∧ runX (inflate_LENLENS c) l h = .ok ((.error Ex.leave, regs), setI h zs state) ∧
      DefaultOriginState (setI h zs state) r zs z state ∧ DispatchBuffers (setI h zs state) r regs (bs.drop used) ∧
      HeaderFrame s state ∧ state.last = s.last ∧ state.nlen = s.nlen ∧ state.ndist = s.ndist ∧ state.ncode = s.ncode ∧ state.mode = LENLENS ∧
      LenlensProgress state regs.hold regs.bits (received ++ bytesBits (bs.take used)) ∧
      regs.next = inputAdvance l.next used ∧ regs.have_.toNat + used = l.have_.toNat ∧
      regs.put = l.put ∧ regs.left = l.left ∧ regs.out_ = l.out_ ∧ regs.bits.toNat ≤ max l.bits.toNat 10 := by
  obtain ⟨ncode, haveBound, _nlen, _ndist, _good⟩ := origin.headerLengths mode
  obtain ⟨outcome, regs, used, read, bound, inv, _source, _shape, waiting, _normal, cursor, bits⟩ :=
    ll1_run_cursor E.st E.hs origin.good.inv.wf.1 ncode haveBound buffers.bits
  have shortM : min (s.ncode.toNat - s.«have».toNat) ((stream l bs).length / 3) < s.ncode.toNat - s.«have».toNat := by omega
  obtain ⟨leave, _zero, _all, _below⟩ := waiting shortM
  subst outcome
  obtain ⟨outcome0, regs0, after, state0, used0, bound0, read0, current, packet, _sizes, _cursor, count, put, left, out, _bits, _budget⟩ :=
    ll1_default_J E origin.toDefaultDecodeJ buffers mode
  rw [read] at read0
  cases read0
  let state := llSt s (stream l bs) (min (s.ncode.toNat - s.«have».toNat) ((stream l bs).length / 3))
  have sameState : state0 = state := Option.some.inj (current.good.live.hs.symm.trans (setI_istates_same ..))
  subst state0
  have sameUsed : used0 = used := by
    have a := packet.bits.have_eq
    have b := inv.have_eq
    simp only [List.length_drop] at a b
    omega
  subst used0
  have config : DefaultConfigFrame s state := ⟨rfl, rfl, rfl, rfl⟩
  have stateJ := origin.toDefaultStateJ.config_update current config (origin.construction_format (Or.inr (Or.inl mode)))
  have nextOrigin := origin.of_fields stateJ rfl rfl rfl
  obtain ⟨outcome1, regs1, used1, count1, countEq, read1, bound1, inv1, nextProgress⟩ :=
    ll1_header_progress E.st E.hs origin.good.inv.wf.1 ncode haveBound buffers.bits progress
  rw [countEq, read] at read1
  cases read1
  have sameUse1 : used1 = used := by
    have a := inv1.have_eq
    have b := inv.have_eq
    simp only [List.length_drop] at a b
    omega
  subst used1
  rw [countEq] at nextProgress
  refine ⟨regs, state, used, bound, ?_, nextOrigin, packet, ?_, rfl, rfl, rfl, rfl, mode, nextProgress, cursor, count, put, left, out, bits⟩
  · rw [inflate_LENLENS_eq, runX_bind, read]
  · rfl

#print axioms lenlens_short_source
end Zlib.Inflate.Proofs.LaterHeader
