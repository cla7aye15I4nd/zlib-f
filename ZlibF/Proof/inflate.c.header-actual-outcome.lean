import ZlibF.Proof.«inflate.c.header-actual-lenlens-classifier»
namespace Zlib.Inflate.Proofs.ActualHeader
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.HeaderPhaseView
set_option autoImplicit false

/-- Result relation of the actual LENLENS branch classifier. It is only
an output package for actual runs and their computed return cases. -/
def LenlensBranchOutcome (c : Ctx) (h : Heap) (r : ZStreamRef) (zs : Nat) (z : ZStream)
    (s : InflateState) (l : IL) (bs : List UInt8) (received : List Bool) : Prop :=
    (∃ regs state used, used ≤ bs.length ∧
      runX (inflate_LENLENS c) l h = .ok ((.error Ex.leave, regs), setI h zs state) ∧
      DefaultOriginState (setI h zs state) r zs z state ∧ DispatchBuffers (setI h zs state) r regs (bs.drop used) ∧
      LenlensProgress state regs.hold regs.bits (received ++ bytesBits (bs.take used))) ∨
    (∃ (regs : IL) (used : Nat) (filled : InflateState) (ret : Int32)
      (next : CodePtr) (root : UInt32) (work : Array UInt16) (codes : Array Code),
      used ≤ bs.length ∧
      runX (do xwhile (llCond c) (llBody c); xwhile (lzCond c) (lzBody c)) l h = .ok ((.ok (), regs), setI h zs filled) ∧
      runX (llInstall c) regs (setI h zs filled) = .ok ((.ok ret, {regs with ret := ret}),
        setI h zs {llPre zs filled with next := next, lenbits := root, work := work, codes := codes}) ∧
      (ret = 0 ∨ ret = -1) ∧
      (ret = 0 ↔ Acceptable .codeLength (Zlib.Inftrees.Proofs.lensOf (fun k => (filled.lens.getD k 0).toNat) 19)) ∧
      (∀ tail, readCodeLenLens s.ncode.toNat ((received ++ bytesBits (bs.take used)) ++ tail) =
        some (Zlib.Inftrees.Proofs.lensOf (fun k => (filled.lens.getD k 0).toNat) 19, natBits regs.bits.toNat regs.hold.toNat ++ tail)) ∧
      (ret = -1 → ∃ i,
        runX (inflate_LENLENS c) l h = .ok ((.ok (), {regs with ret := -1}),
          tcBadHeap (setI h zs {llPre zs filled with next := next, lenbits := root, work := work, codes := codes}) r zs z
            {llPre zs filled with next := next, lenbits := root, work := work, codes := codes} i)) ∧
      (ret = 0 →
        let state := {llPre zs filled with next := next, lenbits := root, work := work, codes := codes, «have» := 0, mode := CODELENS}
        DefaultOriginState (setI h zs state) r zs z state ∧
        DispatchBuffers (setI h zs state) r {regs with ret := 0} (bs.drop used) ∧
        LengthTableFrame s state ∧ state.nlen = s.nlen ∧ state.ndist = s.ndist ∧ state.last = s.last ∧
        runX (inflate_LENLENS c) l h = runX (inflate_CODELENS c) {regs with ret := 0} (setI h zs state) ∧
        Nonempty (CodeReadObservation c (setI h zs state) r zs z state {regs with ret := 0} (bs.drop used)
          (Zlib.Inftrees.Proofs.lensOf (fun k => (filled.lens.getD k 0).toNat) 19))))

theorem lenlens_branch_observation
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8} {received : List Bool}
    (E : Env c h r zs z s) (origin : DefaultOriginState h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = LENLENS)
    (literalCount : 256 < s.nlen.toNat) (progress : LenlensProgress s l.hold l.bits received) :
    LenlensBranchOutcome c h r zs z s l bs received :=
  lenlens_branch_classifier E origin buffers mode literalCount progress

#print axioms lenlens_branch_observation
end Zlib.Inflate.Proofs.ActualHeader
