import ZlibF.Proof.«deflate.c.universal-history»
import ZlibF.Proof.«deflate.c.life.check»
import ZlibF.Proof.«deflate.c.life.bound»
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

/-- Every header pointer has the form `GzOk` asks for. -/
theorem gzOk_any (h : Heap) (head : GzHeaderPtr) : GzOk h head := by
  rcases head with _ | ⟨i⟩
  · exact Or.inl rfl
  · cases i with
    | tab i => exact Or.inr ⟨i, rfl⟩

/-- A state update that keeps every field the invariant reads (besides `DGood`) keeps it. -/
theorem DInv.of_fields {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d d' : DeflateState}
    (inv : DInv h r ds z d) (good : DGood (setD h ds d') r ds z d')
    (shape : Shape d → Shape d') (hashing : Hashing h d → Hashing (setD h ds d') d')
    (symbols : Symbols h d → Symbols (setD h ds d') d') : DInv (setD h ds d') r ds z d' :=
  ⟨good, inv.alloc, inv.globals, shape inv.shape, hashing inv.hashing, symbols inv.symbols⟩

/-- `deflateSetHeader` stores the header pointer (gzip) or refuses; the invariant does not read
`gzhead` beyond its pointer form. -/
theorem step_setHeader {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv h r ds z d) (head : GzHeaderPtr) : StepOk h r (.deflateSetHeader (some r) head) := by
  by_cases wrap : d.wrap = 2
  · obtain ⟨_, run, rfl, good, _⟩ := deflateSetHeader_safe inv.good wrap head (gzOk_any h head)
    refine step_setD inv _ (heapCall_run run) rfl (inv.of_fields good ?_ ?_ ?_)
      (fun b => by simp [DeflateOwned, setHeaderD])
    · intro shape; cases shape; constructor <;> assumption
    · intro hashing; cases hashing; constructor <;> assumption
    · rintro ⟨⟨xs, ⟨b, a, pbuf, bytes, ledger⟩, near⟩, clear, below⟩
      exact ⟨⟨xs, ⟨b, a, pbuf, bytes, ledger.keep rfl rfl rfl rfl⟩, near⟩,
        ⟨clear.bl, clear.opt, clear.fixed⟩, below⟩
  · exact step_unchanged inv _ (heapCall_run (deflateSetHeader_run_other inv.good.live wrap head)) rfl

/-- A C string of the public history is a string `deflateBound` can measure. -/
theorem cstring_gzStr {h : Heap} {p : BPtr} {xs : List UInt8} (c : CString h p xs) :
    GzStr h p xs.length := by
  obtain ⟨bytes, nz, lt⟩ := c
  rcases bytes with ⟨_, n0, _⟩ | ⟨r, i, a, rfl, get, fit, eq⟩
  · simp at n0
  · refine ⟨r, i, a, rfl, get, by omega, ?_, ?_, lt⟩
    · have last := congrArg (fun l => l[xs.length]?) eq
      simp only [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero,
        List.getElem?_take, List.getElem?_drop] at last
      simp only [Nat.lt_add_one, if_true] at last
      rw [← Array.getElem?_toList]
      exact last.symm
    · intro k below
      have at_k := congrArg (fun l => l[k]?) eq
      simp only [List.getElem?_append_left below, List.getElem?_take, List.getElem?_drop] at at_k
      simp only [show k < xs.length + 1 by omega, if_true] at at_k
      rw [← Array.getElem?_toList, ← at_k]
      intro zero
      exact nz (List.mem_of_getElem? zero)

/-- A live header (the history's premise of `deflateBound`) gives the strings it measures. -/
theorem hdrStrOk_of_live {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv h r ds z d) (live : DeflateHeaderLive h r) : HdrStrOk h d := by
  obtain ⟨z', get, all⟩ := live
  have same : z' = z := Option.some.inj (get.symm.trans inv.good.live.hz)
  subst same
  rcases all ds d inv.good.live.zst inv.good.live.hs with none | ⟨i, g, head, gh, _, _, name, comment⟩
  · exact Or.inl none
  · refine Or.inr ⟨i, g, head, gh, ?_, ?_⟩
    · by_cases null : g.name = .null
      · exact Or.inl null
      · obtain ⟨xs, c⟩ := name null
        exact Or.inr ⟨xs.length, cstring_gzStr c⟩
    · by_cases null : g.comment = .null
      · exact Or.inl null
      · obtain ⟨xs, c⟩ := comment null
        exact Or.inr ⟨xs.length, cstring_gzStr c⟩

/-- `deflateBound` and `deflateBound_z` read the state and the live header. -/
theorem step_bound {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv h r ds z d) (live : DeflateHeaderLive h r) (n : UInt64) :
    StepOk h r (.deflateBound (some r) n) := by
  obtain ⟨wl, -, run⟩ := deflateBound_safe inv.good (hdrStrOk_of_live inv live) n
  exact step_unchanged inv _ (heapCall_run run) rfl

theorem step_bound_z {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv h r ds z d) (live : DeflateHeaderLive h r) (n : UInt64) :
    StepOk h r (.deflateBound_z (some r) n) := by
  obtain ⟨wl, -, run⟩ := deflateBound_z_safe inv.good (hdrStrOk_of_live inv live) n
  exact step_unchanged inv _ (heapCall_run run) rfl

end Zlib.Deflate.Universal
