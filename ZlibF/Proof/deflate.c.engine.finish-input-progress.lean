import ZlibF.Proof.«deflate.c.engine.public-finish-progress»
import ZlibF.Proof.«deflate.c.engine.public-request-buffer-frame»
import ZlibF.Proof.«deflate.c.engine.caller-input-frame»
import ZlibF.Proof.«deflate.c.engine.input-slices»

/-! # FINISH retries retain the same unread input suffix -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- Advancing a readable snapshot exposes its exact remaining suffix. -/
theorem caller_bytes_drop {h : Heap} {p : BPtr} {n used : Nat} {input : List UInt8}
    (snapshot : Bytes h p n input) (bound : used ≤ n) :
    Bytes h (advance p used) (n - used) (input.drop used) := by
  rcases snapshot with ⟨rfl, rfl, rfl⟩ | ⟨ref, off, a, rfl, get, fit, rfl⟩
  · have zero : used = 0 := by omega
    subst used
    exact Or.inl ⟨rfl, rfl, rfl⟩
  · refine Or.inr ⟨ref, off + used, a, rfl, get, by omega, ?_⟩
    simp only [List.drop_take, List.drop_drop]

/-- Every actual FINISH call preserves the unread suffix of its entry
snapshot. Whole-object frames cover static and embedded byte views; the
exact output interval also covers separated ranges in one raw allocation.
This is a proved execution postcondition, not a new caller restriction. -/
theorem DefaultFinishBoundary.finish_retains_input_suffix
    {h after : Heap} {r : ZStreamRef} {ds ob oo used produced : Nat}
    {z z' : ZStream} {d : DeflateState} {config : EngineConfig} {rc : Int32}
    {input : List UInt8}
    (boundary : DefaultFinishBoundary h r ds z d config) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo)
    (snapshot : Bytes h z.next_in z.avail_in.toNat input)
    (actual : deflate (some r) Z_FINISH h = .ok (rc, after)) (get : r.get after = some z')
    (account : StreamAccounting z z' used produced) :
    Bytes after z'.next_in z'.avail_in.toNat (input.drop used) := by
  have storage := boundary.ordinary_run_full_storage (Or.inr rfl) buffers
    (Or.inr ⟨ob, oo, pointer⟩) actual
  have frame : Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b ∨ b = ob) := by
    simpa only [pointer, ByteRoot] using storage.2.1
  have effect := boundary.finish_run_output_effect buffers pointer actual get account
  have originalBuffers := buffers
  obtain ⟨oldZ, oldGet, range, _output, separate⟩ := buffers
  have same : oldZ = z := Option.some.inj (oldGet.symm.trans boundary.good.live.hz)
  subst oldZ
  have producedBound : produced ≤ z.avail_out.toNat := by have count := account.2.2.2.1; omega
  have separateP : Separate z.next_in z.avail_in.toNat z.next_out produced := by
    rcases separate with empty | empty | separated
    · exact Or.inl empty
    · exact Or.inr (Or.inl (by omega))
    · right; right
      cases p : z.next_in with
      | null => trivial
      | ref ref off =>
        rw [p, pointer] at separated
        rw [pointer]
        rcases separated with different | left | right
        · exact Or.inl different
        · exact Or.inr (Or.inl left)
        · exact Or.inr (Or.inr (by omega))
  have retained := caller_input_bytes_preserved boundary.good originalBuffers pointer range separateP
    (Nat.le_refl _) snapshot frame effect
  have count := account.2.2.1
  have drop := caller_bytes_drop retained (used := used) (by omega)
  have remaining : z'.avail_in.toNat = z.avail_in.toNat - used := by omega
  rw [account.2.2.2.2.1, remaining]
  exact drop

end Zlib.Deflate.Engine.Proofs
