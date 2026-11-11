import ZlibF.Proof.«deflate.c.universal-history»
import ZlibF.Proof.«deflate.c.life.check»
import ZlibF.Spec.Public.Sequences

/-!
# deflate.c: the stream operations keep the invariant (batch A, `operation_step`)

One lemma per operation of `StreamOperation .deflate`, each in the form of `operation_step`: the
call returns, `DInv` holds afterwards, and the buffer frame and the allocation ledger of
`StreamSequenceSafety` hold. This file starts with the operations that leave the heap unchanged
or change only fields of the state record that the invariant does not read.
-/

namespace Zlib.Deflate.Universal
open C ZlibF.Spec ZlibF.Spec.Public Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Engine.Proofs
open Zlib.Deflate.Proofs
set_option autoImplicit false

/-- The conclusion of `operation_step` for one call. -/
def StepOk (h : Heap) (r : ZStreamRef) (call : Call) : Prop :=
  ∃ value after, call.execute default h = .ok ((value, default), after) ∧
    (∃ ds' z' d', DInv after r ds' z' d') ∧
    BufferFrame h after
      (fun b => StreamRoot r b ∨ StreamOwned h r b ∨ StreamHeaderRecord h r call b)
      (StreamWriteRegions h r call) ∧
    LiveChange h after
      (fun b => StreamOwned after r b ∧ ¬ h.live b)
      (fun b => StreamOwned h r b ∧ ¬ StreamOwned after r b)

theorem heapCall_run {α : Type} {program : M α} {h after : Heap} {value : α}
    (run : program h = .ok (value, after)) : heapCall program default h = .ok ((value, default), after) := by
  unfold heapCall; rw [run]

/-- A call that leaves the heap unchanged and writes no caller region. -/
theorem step_unchanged {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    {call : Call} (inv : DInv h r ds z d) (value : call.Result)
    (run : call.execute default h = .ok ((value, default), h))
    (regions : StreamWriteRegions h r call = []) : StepOk h r call := by
  refine ⟨value, h, run, ⟨ds, z, d, inv⟩, ?_, ?_⟩
  · rw [regions]
    refine ⟨⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _, fun b _ _ => ?_⟩, fun _ mem => by cases mem⟩
    simp [restoreRegions]
  · intro b
    constructor
    · intro live; exact Or.inl ⟨live, fun ⟨_, not⟩ => not ‹_›⟩
    · rintro (⟨live, _⟩ | ⟨owned, _⟩)
      · exact live
      · exact owned_live inv.good ((inv.owned b).1 owned)

/-- `deflateUsed` reads the state. -/
theorem step_used {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv h r ds z d) (hasBits : Bool) : StepOk h r (.deflateUsed (some r) hasBits) :=
  step_unchanged inv _ (heapCall_run (deflateUsed_run inv.good.live hasBits)) rfl

/-- `deflatePending` reads the state. -/
theorem step_pending {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv h r ds z d) (hasPending hasBits : Bool) :
    StepOk h r (.deflatePending (some r) hasPending hasBits) :=
  step_unchanged inv _ (heapCall_run (deflatePending_run inv.good.live hasPending hasBits)) rfl

/-- A call that writes only the state record and no caller region. -/
theorem step_setD {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d d' : DeflateState}
    {call : Call} (inv : DInv h r ds z d) (value : call.Result)
    (run : call.execute default h = .ok ((value, default), setD h ds d'))
    (regions : StreamWriteRegions h r call = []) (inv' : DInv (setD h ds d') r ds z d')
    (sameOwned : ∀ b, DeflateOwned ds d b ↔ DeflateOwned ds d' b) :
    StepOk h r call := by
  refine ⟨value, setD h ds d', run, ⟨ds, z, d', inv'⟩, ?_, ?_⟩
  · rw [regions]
    refine ⟨⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _, fun b _ unchanged => ?_⟩, fun _ mem => by cases mem⟩
    have ne : b ≠ ds := by
      rintro rfl
      exact unchanged (Or.inr (Or.inl ((inv.owned b).2 (Or.inl rfl))))
    simp only [restoreRegions, List.foldl]
    exact ⟨rfl, rfl, rfl, rfl, setD_dstates_ne h ds b d' ne, rfl, rfl, rfl⟩
  · have shape := shape_setD inv.good.live.hs d'
    intro b
    rw [shape.live b]
    constructor
    · intro live
      refine Or.inl ⟨live, fun ⟨owned, not⟩ => not ?_⟩
      exact (inv'.owned b).2 ((sameOwned b).1 ((inv.owned b).1 owned))
    · rintro (⟨live, _⟩ | ⟨owned, _⟩)
      · exact live
      · exact owned_live inv.good ((sameOwned b).2 ((inv'.owned b).1 owned))

/-- `deflateTune` writes the four tuning fields, which the invariant does not read. -/
theorem step_tune {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv h r ds z d) (g m n c : Int32) : StepOk h r (.deflateTune (some r) g m n c) := by
  obtain ⟨_, run, rfl, good, _⟩ := deflateTune_safe inv.good g m n c
  refine step_setD inv _ (heapCall_run run) rfl ⟨good, inv.alloc, inv.globals, ?_, ?_, ?_⟩
    (fun b => by simp [DeflateOwned, tuneD])
  · have shape := inv.shape
    cases shape
    constructor <;> assumption
  · have hashing := inv.hashing
    cases hashing
    constructor <;> assumption
  · obtain ⟨⟨xs, ⟨b, a, pbuf, bytes, ledger⟩, near⟩, clear, below⟩ := inv.symbols
    exact ⟨⟨xs, ⟨b, a, pbuf, bytes, ledger.keep rfl rfl rfl rfl⟩, near⟩,
      ⟨clear.bl, clear.opt, clear.fixed⟩, below⟩

end Zlib.Deflate.Universal
