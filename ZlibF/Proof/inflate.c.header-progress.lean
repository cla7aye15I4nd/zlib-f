import ZlibF.Math.«inflate-header-progress»
import ZlibF.Proof.«inflate.c.header-chunks»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec
set_option autoImplicit false

/-- The actual read loop preserves the phase relation on zero reads,
waiting and normal completion, including resumed nonempty prefixes. -/
theorem ll1_header_progress {c : Ctx} {l : IL} {h : Heap} {zs : Nat}
    {s : InflateState} {bs : List UInt8} {received : List Bool}
    (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s)
    (size : s.lens.size = 320) (bound : s.ncode.toNat ≤ 19)
    (haveBound : s.«have».toNat ≤ s.ncode.toNat) (B : BitInv h l bs)
    (progress : LenlensProgress s l.hold l.bits received) :
    ∃ outcome regs used count,
      count = min (s.ncode.toNat - s.«have».toNat) ((stream l bs).length / 3) ∧
      runX (xwhile (llCond c) (llBody c)) l h =
        .ok ((outcome, regs), setI h zs (llSt s (stream l bs) count)) ∧
      used ≤ bs.length ∧ BitInv (setI h zs (llSt s (stream l bs) count)) regs (bs.drop used) ∧
      LenlensProgress (llSt s (stream l bs) count) regs.hold regs.bits
        (received ++ bytesBits (bs.take used)) := by
  obtain ⟨outcome, regs, used, count, values, countEq, run, usedBound, inv, ledger, fields, _small⟩ :=
    ll1_header_consumed_input hc hs size bound haveBound B
  exact ⟨outcome, regs, used, count, countEq, run, usedBound, inv, progress.advance fields ledger⟩


/-- The actual zeroing loop completes the independent alphabet without
consuming bits. Its transient have=19 is not treated as nineteen input fields. -/
theorem lz_header_alphabet {c : Ctx} {l : IL} {h : Heap} {zs : Nat}
    {s : InflateState} {received : List Bool}
    (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s)
    (size : s.lens.size = 320) (bound : s.ncode.toNat ≤ 19)
    (complete : s.«have».toNat = s.ncode.toNat) (good : Good3 s.lens s.«have».toNat)
    (progress : LenlensProgress s l.hold l.bits received) :
    ∃ state,
      runX (xwhile (lzCond c) (lzBody c)) l h = .ok ((.ok (), l), setI h zs state) ∧
      ∀ future, readCodeLenLens s.ncode.toNat (received ++ future) = some
        (Zlib.Inftrees.Proofs.lensOf (fun k => (state.lens.getD k 0).toNat) 19,
         natBits l.bits.toNat l.hold.toNat ++ future) := by
  refine ⟨lzSt s (19 - s.«have».toNat), lz_run hc hs size (by omega), ?_⟩
  intro future
  exact progress.alphabet (by omega) bound complete good future

#print axioms lz_header_alphabet

#print axioms ll1_header_progress
end Zlib.Inflate.Proofs
