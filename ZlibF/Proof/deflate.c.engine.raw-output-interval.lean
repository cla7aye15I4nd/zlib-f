import ZlibF.Proof.«deflate.c.engine.flush-exact-output-frame»

/-! # Exact raw caller output intervals through actual strategy execution -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- An internal effect predicate: output-array size and every byte outside
this actual output interval are preserved. Existence of the caller array
is supplied by StreamBuffers at public call sites. -/
def RawOutputInterval (h g : Heap) (ob offset produced : Nat) : Prop :=
  ∀ before, h.bytes ob = some before →
    ∃ next, g.bytes ob = some next ∧ next.size = before.size ∧
      ∀ j, j < before.size → ¬ (offset ≤ j ∧ j < offset + produced) → next[j]? = before[j]?

/-- A stage that retains the entire caller array has the interval effect for any byte count. -/
theorem RawOutputInterval.of_same {h g : Heap} {ob offset produced : Nat}
    (same : g.bytes ob = h.bytes ob) : RawOutputInterval h g ob offset produced := by
  intro before get
  exact ⟨before, same.trans get, rfl, fun _ _ _ => rfl⟩

/-- Private-only actual effects retain the complete caller array, including shared disjoint caller ranges. -/
theorem RawOutputInterval.of_private_frame {h g : Heap} {r : ZStreamRef} {ds ob offset produced : Nat}
    {z : ZStream} {d : DeflateState} (good : DGood h r ds z d) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) offset)
    (frame : Frame h g (fun b => StreamRoot r b ∨ DeflateOwned ds d b)) :
    RawOutputInterval h g ob offset produced :=
  .of_same (private_frame_raw_output_same good buffers pointer frame).1

/-- Consecutive actual output intervals concatenate at the advanced cursor. -/
theorem RawOutputInterval.trans {h g k : Heap} {ob offset first second : Nat}
    (one : RawOutputInterval h g ob offset first)
    (two : RawOutputInterval g k ob (offset + first) second) :
    RawOutputInterval h k ob offset (first + second) := by
  intro before get
  obtain ⟨middle, getM, sizeM, effectM⟩ := one before get
  obtain ⟨next, getN, sizeN, effectN⟩ := two middle getM
  have effect := raw_output_interval_compose before middle next offset first second sizeM sizeN effectM effectN
  exact ⟨next, getN, effect⟩

/-- Deterministic actual runs identify both the heap and the accounted output interval. -/
theorem RawOutputInterval.identify {α : Type} {program : M α} {h other after : Heap}
    {a b : α} {r : ZStreamRef} {z firstZ finalZ : ZStream} {ob offset firstUsed finalUsed firstOut finalOut : Nat}
    (tested : program h = .ok (a, other)) (run : program h = .ok (b, after))
    (firstLive : r.get other = some firstZ) (finalLive : r.get after = some finalZ)
    (firstAccount : StreamAccounting z firstZ firstUsed firstOut)
    (finalAccount : StreamAccounting z finalZ finalUsed finalOut)
    (effect : RawOutputInterval h other ob offset firstOut) :
    RawOutputInterval h after ob offset finalOut := by
  have heaps := (Prod.mk.inj (Except.ok.inj (tested.symm.trans run))).2
  have streams := actual_run_stream_unique tested run firstLive finalLive
  rw [streams] at firstAccount
  have count := (stream_accounting_counts_unique firstAccount finalAccount).2
  rw [← heaps, ← count]
  exact effect

/-- The interval effect and already established whole-object frame give the exact public BufferFrame. -/
theorem RawOutputInterval.buffer_frame {h after : Heap} {r : ZStreamRef} {ds ob offset used produced : Nat}
    {z z' : ZStream} {d d' : DeflateState}
    (good : DGood h r ds z d) (goodA : DGood after r ds z' d')
    (buffers : StreamBuffers h r) (buffersA : StreamBuffers after r)
    (pointer : z.next_out = .ref (.blk ob) offset) (account : StreamAccounting z z' used produced)
    (shape : Shape h after)
    (frame : Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b ∨ b = ob))
    (effect : RawOutputInterval h after ob offset produced) :
    BufferFrame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) [⟨z.next_out, produced⟩] := by
  obtain ⟨before, getBefore, writable, _bound, _outside⟩ := caller_raw_output good buffers pointer
  have pointerA : z'.next_out = .ref (.blk ob) (offset + produced) := by
    rw [account.2.2.2.2.2.1, pointer]
    rfl
  obtain ⟨_output, _getOutput, writableA, _boundA, _outsideA⟩ := caller_raw_output goodA buffersA pointerA
  obtain ⟨next, getNext, size, untouched⟩ := effect before getBefore
  have fullFrame : Frame h after (fun b => (StreamRoot r b ∨ DeflateOwned ds d b) ∨ b = ob) := by
    apply full_frame_weaken frame
    intro b changed
    rcases changed with root | owned | output
    · exact Or.inl (Or.inl root)
    · exact Or.inl (Or.inr owned)
    · exact Or.inr output
  have readonly : after.ro ob = h.ro ob := writableA.trans writable.symm
  rw [pointer]
  exact raw_buffer_frame_of_interval fullFrame shape good.uniq getBefore getNext readonly size untouched

/-- A null output region restores no array, so its public frame is precisely the private frame. -/
theorem null_output_buffer_frame {h after : Heap} {changed : Nat → Prop} {produced : Nat}
    (frame : Frame h after changed) : BufferFrame h after changed [⟨.null, produced⟩] := by
  constructor
  · simpa only [restoreRegions, List.foldl_cons, List.foldl_nil] using frame
  · intro region member r off a pointer _get
    simp only [List.mem_singleton] at member
    subst region
    cases pointer

end Zlib.Deflate.Engine.Proofs
