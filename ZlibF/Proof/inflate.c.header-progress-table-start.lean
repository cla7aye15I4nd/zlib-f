import ZlibF.Proof.«inflate.c.header-progress-table»
import ZlibF.Proof.«inflate.c.table-fields-meaning»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The actual count-reading prefix produces an explicit LENLENS state,
input packet and phase seed when its actual validity check accepts.
The state is the actual tableCounts update, so all three count origins
remain visible for subsequent composition. There is no assumed callee run. -/
theorem inflate_TABLE_header_phase_start
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultOriginState h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = TABLE) :
    ∃ outcome pulled used,
      runX (NEEDBITS 14) l h = .ok ((outcome, pulled), h) ∧ used ≤ bs.length ∧
      BitInv h pulled (bs.drop used) ∧
      (outcome = .ok () →
        ¬ ((tableCounts s pulled.hold).nlen > 286 ∨ (tableCounts s pulled.hold).ndist > 30) →
        let state := { tableCounts s pulled.hold with «have» := 0, mode := LENLENS }
        let after := setI h zs state
        DefaultOriginState after r zs z state ∧
        DispatchBuffers after r (tableRegs pulled) (bs.drop used) ∧
        LenlensProgress state (tableRegs pulled).hold (tableRegs pulled).bits
          (natBits (tableRegs pulled).bits.toNat (tableRegs pulled).hold.toNat) ∧
        (∃ hlit hdist hclen firstRest secondRest,
          readBits 5 (stream l bs) = some (hlit, firstRest) ∧
          readBits 5 firstRest = some (hdist, secondRest) ∧
          readBits 4 secondRest = some (hclen, stream (tableRegs pulled) (bs.drop used)) ∧
          state.nlen.toNat = hlit + 257 ∧ state.ndist.toNat = hdist + 1 ∧
          state.ncode.toNat = hclen + 4) ∧
        runX (inflate_TABLE c) l h = runX (inflate_LENLENS c) (tableRegs pulled) after) := by
  obtain ⟨outcome, pulled, used, pull, bound, inv, source, _wait, full⟩ :=
    inflate_TABLE_run E.strm E.st E.hz E.hs buffers.bits
  obtain ⟨outcome0, pulled0, used0, pull0, bound0, inv0, _source0,
    _bitCount, shape, _bitBound, _, _, _, _kinds, cursor⟩ :=
    NEEDBITS_run_cursor buffers.bits 14 (by decide)
  rw [pull] at pull0
  cases pull0
  have sameUse : used0 = used := by
    have first := inv.have_eq
    have second := inv0.have_eq
    rw [List.length_drop] at first second
    omega
  subst used0
  refine ⟨outcome, pulled, used, pull, bound, inv, ?_⟩
  intro normal valid
  obtain ⟨enough, dropInv, _remaining, _bad, ready⟩ := full normal
  let state := { tableCounts s pulled.hold with «have» := 0, mode := LENLENS }
  have frame : TableCountsFrame s state := rfl
  have lengths : LengthHeaderInvariant state := tableCounts_header_invariant s pulled.hold valid
  have nextJ := invariant.toDefaultStateJ.toDefaultDecodeJ.counts_update frame
    (stream := z) rfl (Or.inr rfl) lengths
  have count : pulled.have_.toNat + used = l.have_.toNat := by
    rw [inv.have_eq, buffers.bits.have_eq, List.length_drop]
    omega
  obtain ⟨packet, _sizes⟩ := buffers.metadata_advance invariant.good nextJ.good rfl
    dropInv cursor count (by rw [shape]; rfl) (by rw [shape]; rfl) (by rw [shape]; rfl)
  rw [ZStreamRef.put_self E.hz] at nextJ packet
  have config : DefaultConfigFrame s state := ⟨rfl, rfl, rfl, rfl, rfl⟩
  have nextState := invariant.toDefaultStateJ.config_update nextJ config
    (invariant.construction_format (Or.inl mode))
  have origin := invariant.of_fields nextState rfl rfl rfl
  refine ⟨origin, packet, LenlensProgress.initial rfl _ _, ?_, ready valid⟩
  obtain ⟨hlit, hdist, hclen, firstRest, secondRest, firstRead, secondRead, thirdRead,
    litCount, distCount, codeCount⟩ := tableCounts_read_fields s inv enough
  rw [source] at firstRead
  exact ⟨hlit, hdist, hclen, firstRest, secondRest, firstRead, secondRead, thirdRead,
    litCount, distCount, codeCount⟩

#print axioms inflate_TABLE_header_phase_start
end Zlib.Inflate.Proofs
