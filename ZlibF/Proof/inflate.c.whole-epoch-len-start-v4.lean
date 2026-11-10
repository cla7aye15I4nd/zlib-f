import ZlibF.Proof.«inflate.c.whole-epoch-replace-initial-v4»
import ZlibF.Proof.«inflate.c.whole-epoch-inline-cut»

namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.FunctionalTrailer
set_option autoImplicit false
set_option maxHeartbeats 1800000

/-- At either length-entry mode the additive source phase contains the
already established compressed boundary and its exact last-bit witness. -/
theorem SourcePhase4.ready_of_length
    {log : DataLog} {s : InflateState} {wire : List Bool}
    (phase : SourcePhase4 log s wire) (mode : s.mode = LEN_ ∨ s.mode = LEN) :
    ∃ (boundary : Compressed log.dictionary wire log.output)
      (selected : s.mode = LEN_ ∨ s.mode = LEN)
      (last : s.last = Int32.ofNat boundary.block.last),
      phase = .legacy (.ready boundary selected last) := by
  rcases mode with mode | mode
  all_goals
    cases phase with
    | legacy previous =>
      cases previous with
      | ready boundary selected last => exact ⟨boundary, selected, last, rfl⟩
      | tag _ _ choices _ _ _ =>
        rcases choices with bad | bad <;> rw [mode] at bad <;> cases bad
      | copying choices _ =>
        rcases choices with bad | bad <;> rw [mode] at bad <;> cases bad
      | reading choices _ =>
        rcases choices with bad | bad | bad | bad <;> rw [mode] at bad <;> cases bad
      | afterBlocks choices _ _ =>
        rcases choices with bad | bad <;> rw [mode] at bad <;> cases bad
      | trailer choices _ _ _ _ _ =>
        rcases choices with bad | bad <;> rw [mode] at bad <;> cases bad
      | _ =>
        simp_all [HEAD, DICTID, DICT, TABLE, LENLENS, CODELENS,
          STORED, LEN_, LEN, MATCH, BAD, MEM, DONE]
    | _ => simp_all [STORED, MATCH, MEM, LEN_, LEN]

/-- Execute the actual inline LEN_ mode store without inserting a loop
trip. Every call fact and materialized source field is retained, and the
first dispatcher and entire original mainwhile agree exactly. -/
theorem EpochCallCut4.normalize_len_start
    {c : Ctx} {entryHeap h : Heap} {r : ZStreamRef} {zs : Nat} {entryZ z : ZStream}
    {s : InflateState} {l : IL} {base : DataLog} {raw : List UInt8}
    (before : EpochCallCut4 c entryHeap h r zs entryZ z s l base raw)
    (mode : s.mode = LEN_) :
    ∃ _next : EpochCallCut4 c entryHeap (setI h zs {s with mode := LEN}) r zs entryZ z
        {s with mode := LEN} l base raw,
      runX (inflate_dispatch c) l h =
        runX (inflate_dispatch c) l (setI h zs {s with mode := LEN}) := by
  let cut := before.facts
  let state := {s with mode := LEN}
  let heap := setI h zs state
  let original := cut.origin.toDefaultStateJ
  have frame : DecodeStateFrame s state := rfl
  have good := original.good.decode_update frame (by change HEAD ≤ LEN ∧ LEN ≤ SYNC; decide)
  have oldMode : DataTableMode s.mode := by rw [mode]; unfold DataTableMode; decide
  have tables := (original.tables oldMode).decode_update original.good.live.hs frame
  have pending : DataPendingInvariant state := by
    apply dataPendingInvariant_idle (s := state) original.pending.sane
    change LEN ≠ LENEXT ∧ LEN ≠ DIST ∧ LEN ≠ DISTEXT ∧ LEN ≠ MATCH
    decide
  have decoded := original.toDefaultDecodeJ.decode_update good (fun _ => tables) pending frame
    (by change DataExitMode LEN; exact Or.inl (by unfold DataTableMode; decide))
    (byte_view_sizes_setI h zs state) rfl
  have currentJ : DefaultStateJ heap r zs z state :=
    ⟨decoded, original.requestedBits, original.requestedWrap,
      Or.inr (Or.inr (Or.inr (Or.inr (original.data_format oldMode))))⟩
  have origin : DefaultOriginState heap r zs z state := cut.origin.of_fields currentJ rfl rfl rfl
  have buffers : DispatchBuffers heap r l (raw.drop cut.used) :=
    cut.buffers.byte_views original.good good rfl
      (byte_view_get_setI h zs state) (byte_view_ro_setI h zs state)
  have env : Env c heap r zs z state := ⟨cut.env.strm, cut.env.st, good.live.hz, good.live.hs⟩
  have same : runX (inflate_dispatch c) l h = runX (inflate_dispatch c) l heap := by
    rw [inflate_dispatch_LEN_start cut.env l mode, inflate_dispatch_LEN env l rfl]
    unfold inflate_LEN_
    rw [runX_bind, runX_setMode cut.env]
  have main := cut.main.trans
    (while_inline_cut cut.env cut.origin cut.buffers cut.bits env origin buffers cut.bits same)
  obtain ⟨boundary, selectedMode, last, selected⟩ := before.phase.ready_of_length (Or.inl mode)
  have attached := before.materialized
  rw [selected] at attached
  have oldTables : TableBinding h s boundary.L boundary.D := attached.1
  have views : ∀ ref : CodeRef, (Space.get heap ref : Option (Array Code)) = Space.get h ref := by
    intro ref
    cases ref with
    | istate_codes i =>
      by_cases equal : i = zs
      · subst i
        simp only [heap, Space.get, setI_istates_same, cut.env.hs, Option.map_some, state]
      · simp only [heap, Space.get, setI_istates_ne h zs i state equal]
    | st_lenfix | st_distfix => rfl
  have newTables : TableBinding heap state boundary.L boundary.D := oldTables.of_views views
  let phase : SourcePhase4 (sourceLog (callLog base raw cut.used cut.emitted)) (leaveState state l) cut.word :=
    .legacy (.ready boundary (Or.inr rfl) last)
  let facts : CallFacts c entryHeap heap r zs entryZ z state l base raw := {
    cut with
    env := env
    origin := origin
    wrapperOrigins := {
      wrapped := cut.wrapperOrigins.wrapped
      missing := by
        intro impossible
        change LEN = HEAD ∨ LEN = DICTID at impossible
        rcases impossible with bad | bad <;> cases bad
      last := by
        intro impossible
        change LEN = HEAD ∨ LEN = DICTID ∨ LEN = DICT at impossible
        rcases impossible with bad | bad | bad <;> cases bad
    }
    main := main
    buffers := buffers
    window := by
      intro _
      exact WindowHistory.dictionary_transport (cut.window (by rw [mode]; decide)) rfl rfl rfl rfl
        (byte_view_get_setI h zs state)
    physical := by
      intro dest off array pointer get
      apply cut.physical dest off array pointer
      rw [byte_view_get_setI] at get
      exact get
    checksum := by
      intro _ _
      obtain ⟨count, ledger⟩ := cut.checksum (by rw [mode]; decide) (by rw [mode]; decide)
      refine ⟨count, ⟨ledger.count, ledger.checksum, ledger.pending, ?_⟩⟩
      obtain ⟨dest, off, array, pointer, get, start, bound, bytes⟩ := ledger.physical
      exact ⟨dest, off, array, pointer, (byte_view_get_setI h zs state dest).trans get, start, bound, bytes⟩
    registers := {
      inputStart := cut.registers.inputStart
      noHeaderOutput := by
        intro impossible
        change LEN = HEAD ∨ LEN = DICTID ∨ LEN = DICT at impossible
        rcases impossible with bad | bad | bad <;> cases bad
    }
    outputStart := fun _ => cut.outputStart (by rw [mode]; decide)
    normalRet := fun _ => cut.normalRet (by rw [mode]; decide)
  }
  exact ⟨⟨facts, phase, newTables, True.intro⟩, same⟩

#print axioms SourcePhase4.ready_of_length
#print axioms EpochCallCut4.normalize_len_start
end Zlib.Inflate.Proofs.WholeEpoch
