import ZlibF.Proof.«inflate.c.whole-epoch-public-entry»
namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs
set_option autoImplicit false

/-- TYPE has only the nonfinal-next-tag or completed-final-body source
cases. Its actual call-entry normalization activates no installed table. -/
def SourcePhase.type_restart {log : DataLog} {s : InflateState} {wire : List Bool}
    (phase : SourcePhase log s wire) (mode : s.mode = TYPE) (h : Heap) :
    {next : SourcePhase log {s with mode := TYPEDO} wire // next.Materialized h} := by
  cases phase with
  | tag w word _ last context anchor => exact ⟨.tag w word (Or.inr rfl) last context anchor, trivial⟩
  | afterBlocks _ last body => exact ⟨.afterBlocks (Or.inr rfl) last body, trivial⟩
  | memory prior previous _ frame =>
    rw [frame] at mode
    change MEM = TYPE at mode
    exact False.elim ((by decide : MEM ≠ TYPE) mode)
  | _ => simp_all [HEAD, DICTID, DICT, TYPE, TABLE, LENLENS, CODELENS, STORED,
      COPY_, COPY, LEN_, LEN, LENEXT, DIST, DISTEXT, LIT, MATCH, CHECK, LENGTH, DONE, BAD]

/-- The actual entry's TYPE-to-TYPEDO write retains the joint source and
safety state. This function inserts no extra translated instruction. -/
def ScopedInvariant.normalize_type {h : Heap} {r : ZStreamRef} {log : DataLog}
    (before : ScopedInvariant h r log) (mode : before.core.source.point.state.mode = TYPE) :
    ScopedInvariant
      (setI h before.core.source.point.zs {before.core.source.point.state with mode := TYPEDO}) r log := by
  let s := before.core.source.point.state
  let zs := before.core.source.point.zs
  let z := before.core.source.point.z
  let state := {s with mode := TYPEDO}
  let after := setI h zs state
  let old := before.core.origin
  have good : Good after r zs z state := old.good.decode_update rfl
    (by change HEAD ≤ TYPEDO ∧ TYPEDO ≤ SYNC; decide)
  have tables : DataTableInvariant after state := by
    intro active
    change DataTableMode TYPEDO at active
    rcases active with eq | eq | eq | eq | eq | eq | eq <;> contradiction
  have pending : DataPendingInvariant state := by
    apply dataPendingInvariant_idle (s := state) old.pending.sane
    change TYPEDO ≠ LENEXT ∧ TYPEDO ≠ DIST ∧ TYPEDO ≠ DISTEXT ∧ TYPEDO ≠ MATCH
    decide
  have frame : BlockHeaderFrame s state := rfl
  have format := old.toDefaultStateJ.block_format (Or.inl mode)
  have base := old.toDefaultDecodeJ.block_update good tables pending frame
    (Or.inr (Or.inl rfl)) format (byte_view_sizes_setI h zs state) rfl
  have current := old.toDefaultStateJ.config_update base (show DecodeStateFrame s state from rfl).default_config format
  have origin : DefaultOriginState after r zs z state := old.of_fields current rfl rfl rfl
  let attached := before.core.source.phase.type_restart mode after
  let point : CausalInput.AtPublic after r log before.core.source.wire :=
    ⟨zs, z, state, good, before.core.source.point.source⟩
  let source : AtPublic after r log := ⟨before.core.source.wire, point, attached.val⟩
  let core : Invariant after r log := {
    source := source
    origin := origin
    allocator := before.core.allocator
    tables := attached.property
    window := fun _active => WindowHistory.dictionary_transport
      (before.core.window (by rw [mode]; decide)) rfl rfl rfl rfl
      (fun ref => byte_view_get_setI h zs state ref)
    checksum := fun _lower _upper => before.core.checksum (by rw [mode]; decide) (by rw [mode]; decide)
  }
  refine ⟨core, ⟨before.wrapperOrigins.wrapped, ?_, ?_⟩⟩
  · intro selected
    rcases selected with selected | selected <;> change TYPEDO = _ at selected <;> contradiction
  · intro selected
    rcases selected with selected | selected | selected <;> change TYPEDO = _ at selected <;> contradiction

/-- The remaining actual TYPE entry case reaches the same finite local
spine after the single real mode write and LOAD. -/
theorem ScopedInvariant.call_entry_type
    {c : Ctx} {h : Heap} {r : ZStreamRef} {log : DataLog} {raw : List UInt8}
    (before : ScopedInvariant h r log)
    (E : Env c h r before.core.source.point.zs before.core.source.point.z before.core.source.point.state)
    (buffers : StreamBuffers h r) (nonnull : before.core.source.point.z.next_out ≠ .null)
    (input : Bytes h before.core.source.point.z.next_in before.core.source.point.z.avail_in.toNat raw)
    (mode : before.core.source.point.state.mode = TYPE) :
    let zs := before.core.source.point.zs
    let z := before.core.source.point.z
    let state := {before.core.source.point.state with mode := TYPEDO}
    let after := setI h zs state
    Nonempty (FramedCallCut c h after r zs z z state (dispatchRegs z state) log raw) := by
  dsimp only
  let normalized := before.normalize_type mode
  let state := {before.core.source.point.state with mode := TYPEDO}
  let after := setI h before.core.source.point.zs state
  have currentE : Env c after r before.core.source.point.zs before.core.source.point.z state :=
    ⟨E.strm, E.st, normalized.core.origin.good.live.hz, normalized.core.origin.good.live.hs⟩
  have afterBuffers : StreamBuffers after r := by
    obtain ⟨z, get, inputRange, outputRange, separate⟩ := buffers
    have sameZ : z = before.core.source.point.z := Option.some.inj (get.symm.trans before.core.source.point.good.live.hz)
    subst z
    refine ⟨before.core.source.point.z, normalized.core.source.point.good.live.hz, ?_, ?_, separate⟩
    · exact callerRange_transport before.core.source.point.good normalized.core.source.point.good rfl
        (fun ref => byte_view_get_setI h before.core.source.point.zs state ref)
        (fun ref => byte_view_ro_setI h before.core.source.point.zs state ref) inputRange
    · exact callerRange_transport before.core.source.point.good normalized.core.source.point.good rfl
        (fun ref => byte_view_get_setI h before.core.source.point.zs state ref)
        (fun ref => byte_view_ro_setI h before.core.source.point.zs state ref) outputRange
  have afterInput : Bytes after before.core.source.point.z.next_in before.core.source.point.z.avail_in.toNat raw := by
    rcases input with null | ⟨ref, off, array, pointer, get, bound, values⟩
    · exact Or.inl null
    · exact Or.inr ⟨ref, off, array, pointer, by rw [byte_view_get_setI]; exact get, bound, values⟩
  obtain ⟨cut⟩ := normalized.call_entry_not_type currentE afterBuffers nonnull afterInput (by change TYPEDO ≠ TYPE; decide)
  have prefixRun : runX (inflate_run c) IL.init h =
      runX (xwhile (pure true) (inflate_dispatch c)) (dispatchRegs before.core.source.point.z state) after := by
    unfold inflate_run
    rw [runX_bind, runX_rdS E]
    simp only [mode, beq_self_eq_true, ↓reduceIte]
    rw [runX_bind, runX_setMode E]
    simp only []
    rw [runX_bind, LOAD_run currentE]
    simp only []
    rw [runX_bind, runX_modify]
    rfl
  refine ⟨⟨{cut.cut with main := prefixRun}, cut.registers⟩⟩

#print axioms SourcePhase.type_restart
#print axioms ScopedInvariant.normalize_type
#print axioms ScopedInvariant.call_entry_type
end Zlib.Inflate.Proofs.WholeEpoch
