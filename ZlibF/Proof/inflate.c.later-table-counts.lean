import ZlibF.Proof.«inflate.c.later-lenlens-wait»
namespace Zlib.Inflate.Proofs.LaterHeader
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.HeaderPhaseView Zlib.Inflate.Proofs.CumulativeTableBoundary
set_option autoImplicit false
set_option maxHeartbeats 1500000

theorem table_header_count_source
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8} {future payload : List Bool} {L D : List Nat}
    (E : Env c h r zs z s) (initial : DefaultOriginState h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = TABLE)
    (available : 14 ≤ (stream l bs).length)
    (header : ZlibF.Math.InflateHuffmanBodyContext.Header 2 (stream l bs ++ future) L D payload) :
    ∃ (pulled : IL) (tableUsed : Nat),
      runX (NEEDBITS 14) l h = .ok ((.ok (), pulled), h) ∧ tableUsed ≤ bs.length ∧
      BitInv h pulled (bs.drop tableUsed) ∧ 14 ≤ pulled.bits.toNat ∧
      (pulled.put = l.put ∧ pulled.left = l.left ∧ pulled.out_ = l.out_) ∧
      ¬ ((tableCounts s pulled.hold).nlen > 286 ∨ (tableCounts s pulled.hold).ndist > 30) ∧
      let nextS := { tableCounts s pulled.hold with «have» := 0, mode := LENLENS }
      DefaultOriginState (setI h zs nextS) r zs z nextS ∧
      DispatchBuffers (setI h zs nextS) r (tableRegs pulled) (bs.drop tableUsed) ∧
      LenlensProgress nextS (tableRegs pulled).hold (tableRegs pulled).bits
        (natBits (tableRegs pulled).bits.toNat (tableRegs pulled).hold.toNat) ∧
      ∃ hlit hdist hclen firstRest secondRest,
        readBits 5 (stream l bs) = some (hlit, firstRest) ∧
        readBits 5 firstRest = some (hdist, secondRest) ∧
        readBits 4 secondRest = some (hclen, stream (tableRegs pulled) (bs.drop tableUsed)) ∧
        nextS.nlen.toNat = hlit + 257 ∧ nextS.ndist.toNat = hdist + 1 ∧ nextS.ncode.toNat = hclen + 4 ∧
        runX (inflate_TABLE c) l h = runX (inflate_LENLENS c) (tableRegs pulled) (setI h zs nextS) := by
  obtain ⟨hlit, hdist, hclen, firstRest, secondRest, thirdRest, formatAlphabet, alphabetRest, decoded,
    first, second, third, countBounds, formatRead, acceptable, parsed, eob, validL, validD, actualL, actualD⟩ := dynamic_header_fields header
  obtain ⟨pulled, tableUsed, pull, tableBound, tableInv, source, full, _count, _upper, _noPull⟩ :=
    CodeLensCompletion.needbits_normal_of_available buffers.bits 14 (by decide) available
  have outputFields := needbits_output_fields buffers.bits (by decide : (14 : UInt32).toNat ≤ 49) pull
  obtain ⟨outcome0, pulled0, used0, pull0, bound0, inv0, accepted⟩ := inflate_TABLE_header_phase_start E initial buffers mode
  rw [pull] at pull0
  cases pull0
  have sameUsed : used0 = tableUsed := by
    have a := tableInv.have_eq
    have b := inv0.have_eq
    simp only [List.length_drop] at a b
    omega
  subst used0
  obtain ⟨actualLit, actualDist, actualCode, actualFirst, actualSecond, read1, read2, read3, litCount, distCount, codeCount⟩ :=
    tableCounts_read_fields s tableInv full
  rw [source] at read1
  have firstExtended := readBits_append read1 future
  have eq1 := Option.some.inj (firstExtended.symm.trans first)
  have litEq := congrArg Prod.fst eq1
  have firstEq := congrArg Prod.snd eq1
  dsimp only at litEq firstEq
  have secondExtended := readBits_append read2 future
  rw [firstEq] at secondExtended
  have eq2 := Option.some.inj (secondExtended.symm.trans second)
  have distEq := congrArg Prod.fst eq2
  have secondEq := congrArg Prod.snd eq2
  dsimp only at distEq secondEq
  have thirdExtended := readBits_append read3 future
  rw [secondEq] at thirdExtended
  have eq3 := Option.some.inj (thirdExtended.symm.trans third)
  have codeEq := congrArg Prod.fst eq3
  have remainingEq := congrArg Prod.snd eq3
  dsimp only at codeEq remainingEq
  have valid : ¬ ((tableCounts s pulled.hold).nlen > 286 ∨ (tableCounts s pulled.hold).ndist > 30) := by
    intro invalid
    rcases invalid with bad | bad
    · have n := UInt32.lt_iff_toNat_lt.mp bad
      change 286 < (tableCounts s pulled.hold).nlen.toNat at n
      rw [litCount, litEq] at n
      omega
    · have n := UInt32.lt_iff_toNat_lt.mp bad
      change 30 < (tableCounts s pulled.hold).ndist.toNat at n
      rw [distCount, distEq] at n
      omega
  obtain ⟨phase, packet, seed, _fields, tableCut⟩ := accepted rfl valid
  refine ⟨pulled, tableUsed, pull, tableBound, tableInv, full, outputFields, valid, phase, packet, seed,
    actualLit, actualDist, actualCode, actualFirst, actualSecond, read1, read2, read3,
    litCount, distCount, codeCount, tableCut⟩



#print axioms table_header_count_source
end Zlib.Inflate.Proofs.LaterHeader
