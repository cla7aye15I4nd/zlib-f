import ZlibF.Math.«inflate-header-chunks»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec
set_option autoImplicit false

/-- Every actual LENLENS read loop, including a resumed or waiting call,
appends precisely the independently read fields to the source-order view. -/
theorem ll1_header_field_prefix {c : Ctx} {l : IL} {h : Heap} {zs : Nat}
    {s : InflateState} {bs : List UInt8}
    (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s)
    (size : s.lens.size = 320) (bound : s.ncode.toNat ≤ 19)
    (haveBound : s.«have».toNat ≤ s.ncode.toNat) (B : BitInv h l bs) :
    ∃ outcome regs used count values,
      count = min (s.ncode.toNat - s.«have».toNat) ((stream l bs).length / 3) ∧
      runX (xwhile (llCond c) (llBody c)) l h =
        .ok ((outcome, regs), setI h zs (llSt s (stream l bs) count)) ∧
      used ≤ bs.length ∧ BitInv (setI h zs (llSt s (stream l bs) count)) regs (bs.drop used) ∧
      readNats 3 count (stream l bs) = some (values, stream regs (bs.drop used)) ∧
      headerFields (llSt s (stream l bs) count).lens (llSt s (stream l bs) count).«have».toNat =
        headerFields s.lens s.«have».toNat ++ values ∧
      (∀ value ∈ values, value ≤ 7) := by
  let count := min (s.ncode.toNat - s.«have».toNat) ((stream l bs).length / 3)
  have countBound : s.«have».toNat + count ≤ 19 := by
    have limited := Nat.min_le_left (s.ncode.toNat - s.«have».toNat) ((stream l bs).length / 3)
    dsimp only [count]
    omega
  have enough : 3 * count ≤ (stream l bs).length := by
    have limited := Nat.min_le_right (s.ncode.toNat - s.«have».toNat) ((stream l bs).length / 3)
    dsimp only [count]
    omega
  obtain ⟨outcome, regs, used, run, usedBound, inv, remaining, _shape, _wait, _complete⟩ :=
    ll1_run hc hs size bound haveBound B
  change runX (xwhile (llCond c) (llBody c)) l h =
    .ok ((outcome, regs), setI h zs (llSt s (stream l bs) count)) at run
  change stream regs (bs.drop used) = (stream l bs).drop (3 * count) at remaining
  have parsed := readNats_three_groups count (stream l bs) enough
  rw [← remaining] at parsed
  have fields := lensRead_headerFields (a := s.lens) (by omega) (stream l bs) s.«have».toNat count countBound
  have updatedCount := llSt_have s (stream l bs) count countBound
  change headerFields (llSt s (stream l bs) count).lens (s.«have».toNat + count) =
    headerFields s.lens s.«have».toNat ++ (List.range count).map (grp (stream l bs)) at fields
  rw [← updatedCount] at fields
  refine ⟨outcome, regs, used, count, (List.range count).map (grp (stream l bs)), rfl,
    run, usedBound, inv.tc_setI zs (llSt s (stream l bs) count), parsed, fields, ?_⟩
  intro value member
  obtain ⟨index, _indexBound, rfl⟩ := List.mem_map.mp member
  exact grp_le (stream l bs) index

/-- The actual loop's consumed-input ledger cancels the unread bytes.
It therefore mentions only held bits, bytes pulled and newly read fields. -/
theorem ll1_header_consumed_input {c : Ctx} {l : IL} {h : Heap} {zs : Nat}
    {s : InflateState} {bs : List UInt8}
    (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s)
    (size : s.lens.size = 320) (bound : s.ncode.toNat ≤ 19)
    (haveBound : s.«have».toNat ≤ s.ncode.toNat) (B : BitInv h l bs) :
    ∃ outcome regs used count values,
      count = min (s.ncode.toNat - s.«have».toNat) ((stream l bs).length / 3) ∧
      runX (xwhile (llCond c) (llBody c)) l h =
        .ok ((outcome, regs), setI h zs (llSt s (stream l bs) count)) ∧
      used ≤ bs.length ∧ BitInv (setI h zs (llSt s (stream l bs) count)) regs (bs.drop used) ∧
      natBits l.bits.toNat l.hold.toNat ++ bytesBits (bs.take used) =
        values.flatMap (fun value => Zlib.Inffast.Proofs.bitsOfNat value 3) ++ natBits regs.bits.toNat regs.hold.toNat ∧
      headerFields (llSt s (stream l bs) count).lens (llSt s (stream l bs) count).«have».toNat =
        headerFields s.lens s.«have».toNat ++ values ∧ (∀ value ∈ values, value ≤ 7) := by
  obtain ⟨outcome, regs, used, count, values, countEq, run, usedBound, inv, parsed, fields, small⟩ :=
    ll1_header_field_prefix hc hs size bound haveBound B
  have source := readNats_word parsed
  have before : (natBits l.bits.toNat l.hold.toNat ++ bytesBits (bs.take used)) ++ bytesBits (bs.drop used) = stream l bs := by
    rw [List.append_assoc, ← bytesBits_append, List.take_append_drop]
    rfl
  have after : (values.flatMap (fun value => Zlib.Inffast.Proofs.bitsOfNat value 3) ++ natBits regs.bits.toNat regs.hold.toNat) ++ bytesBits (bs.drop used) =
      values.flatMap (fun value => Zlib.Inffast.Proofs.bitsOfNat value 3) ++ stream regs (bs.drop used) := by
    rw [List.append_assoc]
    rfl
  exact ⟨outcome, regs, used, count, values, countEq, run, usedBound, inv,
    List.append_cancel_right (before.trans (source.trans after.symm)), fields, small⟩

#print axioms ll1_header_field_prefix
#print axioms ll1_header_consumed_input
end Zlib.Inflate.Proofs
