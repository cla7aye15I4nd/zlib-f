import ZlibF.Proof.«public-compress-safe»
import ZlibF.Proof.«public-compress-finished»
import ZlibF.Proof.«public-deflate-safety»

/-!
# compress.c: the `compress*` safety goals under `TinyOverlay`

`Goal.deflate` holds under `TinyOverlay` (`deflate_safety_of_tiny`). `DeflateLoopFacts`, the other
hypothesis of `compress*_safety_of`, follows from the checked deflate call (`deflate_call_full`),
the reachable invariant (`reachable_inv_of`), `finished_new_input`, and two facts about one
`deflate` call that `deflate_call_full` does not state yet:

* `CallProgress`: a `deflate` call that is not refused, with input and output room, before the
  stream is finished, that returns `Z_OK`, reads or writes a byte (the termination of the
  `compress*` loop);
* `CallKeepsGzhead`: `deflate` never changes the `gzhead` field (only `deflateSetHeader` does).
-/

namespace ZlibF.Spec.Public.Proofs.Compress
open C ZlibF.Spec ZlibF.Spec.Public Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Universal
set_option autoImplicit false

/-- A `deflate` call with input and output room, not refused, before `FINISH_STATE`, that
returns `Z_OK` changes `avail_in` or `avail_out`. -/
def CallProgress : Prop :=
  ∀ {h after : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState} {flush rc : Int32},
    DInv h r ds z d → HeaderInv d → CallFacts d → StreamBuffers h r → ActiveHeader h r →
    C.run (Zlib.Deflate.deflate (some r) flush) h = .ok (rc, after) →
    ¬ DeflateRefuses z d flush → z.avail_out ≠ 0 → z.avail_in ≠ 0 → d.status ≠ FINISH_STATE → rc = Z_OK →
    ∀ z', r.get after = some z' → z'.avail_in ≠ z.avail_in ∨ z'.avail_out ≠ z.avail_out

/-- A `deflate` call keeps the `gzhead` field of the state. -/
def CallKeepsGzhead : Prop :=
  ∀ {h after : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState} {flush rc : Int32},
    DInv h r ds z d → HeaderInv d → CallFacts d → StreamBuffers h r → ActiveHeader h r →
    C.run (Zlib.Deflate.deflate (some r) flush) h = .ok (rc, after) →
    ∀ z' d', DGood after r ds z' d' → d'.gzhead = d.gzhead

/-- `DeflateLoopFacts` from `TinyOverlay` and the two call facts. -/
theorem deflate_loop_facts_of_tiny (tiny : Block.TinyOverlay) (progress : CallProgress)
    (gzhead : CallKeepsGzhead) : DeflateLoopFacts := by
  intro h r i z s flush rc after reachable good buffers active run
  obtain ⟨ds, z0, d0, inv, header, calls⟩ := reachable_inv_of (Call.sequence_facts_of tiny) reachable
  obtain ⟨e1, e2, e3⟩ := dgood_unique inv.good good
  subst e1 e2 e3
  obtain ⟨rc', after', z', d', used, out, run', inv', -, -, -, owned, -, -⟩ :=
    Call.deflate_call_full tiny inv header calls buffers active flush
  have same := Except.ok.inj (run'.symm.trans run)
  simp only [Prod.mk.injEq] at same
  obtain ⟨rfl, rfl⟩ := same
  refine ⟨?_, ?_, ?_⟩
  · intro notRef nf ain aout rcOk
    have status : d0.status ≠ FINISH_STATE := by
      intro fs
      apply notRef
      right; right; right; right
      refine ⟨fs, ?_⟩
      rw [nf]; decide
    exact progress inv header calls buffers active run notRef aout ain status rcOk
  · intro notRef fs ain
    exact finished_new_input inv buffers active run notRef fs ain
  · intro z'' s'' good''
    obtain ⟨-, -, es⟩ := dgood_unique good'' inv'.good
    subst es
    exact ⟨gzhead inv header calls buffers active run z'' s'' good'', fun b => (owned b).symm⟩

theorem compress2_z_safety_of_tiny (tiny : Block.TinyOverlay) (progress : CallProgress)
    (gzhead : CallKeepsGzhead) : Goal.compress2_z_safety :=
  compress2_z_safety_of (deflate_safety_of_tiny tiny) (deflate_loop_facts_of_tiny tiny progress gzhead)

theorem compress_z_safety_of_tiny (tiny : Block.TinyOverlay) (progress : CallProgress)
    (gzhead : CallKeepsGzhead) : Goal.compress_z_safety :=
  compress_z_safety_of (deflate_safety_of_tiny tiny) (deflate_loop_facts_of_tiny tiny progress gzhead)

theorem compress2_safety_of_tiny (tiny : Block.TinyOverlay) (progress : CallProgress)
    (gzhead : CallKeepsGzhead) : Goal.compress2_safety :=
  compress2_safety_of (deflate_safety_of_tiny tiny) (deflate_loop_facts_of_tiny tiny progress gzhead)

theorem compress_safety_of_tiny (tiny : Block.TinyOverlay) (progress : CallProgress)
    (gzhead : CallKeepsGzhead) : Goal.compress_safety :=
  compress_safety_of (deflate_safety_of_tiny tiny) (deflate_loop_facts_of_tiny tiny progress gzhead)

#print axioms compress_safety_of_tiny

end ZlibF.Spec.Public.Proofs.Compress
