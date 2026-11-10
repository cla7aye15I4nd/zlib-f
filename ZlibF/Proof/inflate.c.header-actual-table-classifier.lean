import ZlibF.Proof.«inflate.c.header-actual-outcome»
namespace Zlib.Inflate.Proofs.ActualHeader
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.HeaderPhaseView
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- Actual TABLE selection with its true numeric count rejection, genuine
input wait and automatic LENLENS/CODES/reader branch observation.
There is no independent Header, future parse or success selector input. -/
structure TableBranchObservation (c : Ctx) (h : Heap) (r : ZStreamRef) (zs : Nat) (z : ZStream)
    (s : InflateState) (l : IL) (bs : List UInt8) where
  outcome : Except Ex Unit
  pulled : IL
  used : Nat
  pull : runX (NEEDBITS 14) l h = .ok ((outcome, pulled), h)
  bound : used ≤ bs.length
  bits : BitInv h pulled (bs.drop used)
  source : stream pulled (bs.drop used) = stream l bs
  cursor : pulled.next = inputAdvance l.next used
  count : pulled.have_.toNat + used = l.have_.toNat
  shape : TcRegShape l pulled
  bitBound : pulled.bits.toNat ≤ max l.bits.toNat 21
  kinds : outcome = .ok () ∨ outcome = .error Ex.leave
  wait : outcome = .error Ex.leave → runX (inflate_TABLE c) l h = .ok ((.error Ex.leave, pulled), h) ∧
    DispatchBuffers h r pulled (bs.drop used)
  normal : outcome = .ok () →
    (∃ i, strTable[i]? = some "too many length or distance symbols" ∧
      runX (inflate_TABLE c) l h = .ok ((.ok (), tableRegs pulled), tcBadHeap h r zs z (tableCounts s pulled.hold) i)) ∨
    (let state := {tableCounts s pulled.hold with «have» := 0, mode := LENLENS}
     DefaultOriginState (setI h zs state) r zs z state ∧
     DispatchBuffers (setI h zs state) r (tableRegs pulled) (bs.drop used) ∧
     LenlensProgress state (tableRegs pulled).hold (tableRegs pulled).bits
       (natBits (tableRegs pulled).bits.toNat (tableRegs pulled).hold.toNat) ∧
     (∃ hlit hdist hclen r1 r2,
       readBits 5 (stream l bs) = some (hlit, r1) ∧ readBits 5 r1 = some (hdist, r2) ∧
       readBits 4 r2 = some (hclen, stream (tableRegs pulled) (bs.drop used)) ∧
       state.nlen.toNat = hlit + 257 ∧ state.ndist.toNat = hdist + 1 ∧ state.ncode.toNat = hclen + 4) ∧
     runX (inflate_TABLE c) l h = runX (inflate_LENLENS c) (tableRegs pulled) (setI h zs state) ∧
     LenlensBranchOutcome c (setI h zs state) r zs z state (tableRegs pulled) (bs.drop used)
       (natBits (tableRegs pulled).bits.toNat (tableRegs pulled).hold.toNat))

theorem table_branch_classifier
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (origin : DefaultOriginState h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = TABLE) :
    Nonempty (TableBranchObservation c h r zs z s l bs) := by
  obtain ⟨outcome, pulled, used, pull, bound, B, source, wait, full⟩ := inflate_TABLE_run E.strm E.st E.hz E.hs buffers.bits
  obtain ⟨outcome0, pulled0, used0, pull0, bound0, B0, accepted⟩ := inflate_TABLE_header_phase_start E origin buffers mode
  rw [pull] at pull0
  cases pull0
  have sameUsed : used0 = used := by
    have a := B0.have_eq
    have b := B.have_eq
    simp only [List.length_drop] at a b
    omega
  subst used0
  obtain ⟨outcome1, pulled1, used1, pull1, bound1, B1, _source1, _bitCount, shape, upper, _same, _full, _wait, kinds, cursor⟩ :=
    NEEDBITS_run_cursor buffers.bits 14 (by decide)
  rw [pull] at pull1
  cases pull1
  have sameUse1 : used1 = used := by
    have a := B1.have_eq
    have b := B.have_eq
    simp only [List.length_drop] at a b
    omega
  subst used1
  have count : pulled.have_.toNat + used = l.have_.toNat := by rw [B.have_eq, buffers.bits.have_eq, List.length_drop]; omega
  refine ⟨⟨outcome, pulled, used, pull, bound, B, source, cursor, count, shape, upper, kinds, ?_, ?_⟩⟩
  · intro leave
    have packet := buffers.consume origin.good origin.good rfl (fun _ => rfl) (fun _ => rfl) (by rw [shape]; rfl) cursor bound B
    exact ⟨(wait leave).2.2.2, packet⟩
  · intro normal
    obtain ⟨_full, _dropB, _source, bad, good⟩ := full normal
    by_cases invalid : (tableCounts s pulled.hold).nlen > 286 ∨ (tableCounts s pulled.hold).ndist > 30
    · exact Or.inl (bad invalid)
    · obtain ⟨current, packet, progress, reads, actual⟩ := accepted normal invalid
      let state := {tableCounts s pulled.hold with «have» := 0, mode := LENLENS}
      have lower : 256 < state.nlen.toNat := by
        obtain ⟨hlit, hdist, hclen, r1, r2, _first, _second, _third, nlen, _ndist, _ncode⟩ := reads
        change 256 < (tableCounts s pulled.hold).nlen.toNat
        rw [nlen]
        omega
      have env : Env c (setI h zs state) r zs z state := ⟨E.strm, E.st, current.good.live.hz, current.good.live.hs⟩
      have cases := lenlens_branch_observation env current packet rfl lower progress
      exact Or.inr ⟨current, packet, progress, reads, actual, cases⟩

#print axioms table_branch_classifier
end Zlib.Inflate.Proofs.ActualHeader
