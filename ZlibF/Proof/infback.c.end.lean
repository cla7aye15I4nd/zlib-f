import ZlibF.Proof.«infback.c.init»

/-!
# infback.c: `inflateBackEnd`

`inflateBackEnd` frees the state record and clears the stream's state pointer. It does not run `inflateStateCheck`, and
it never touches the window, which belongs to the caller.
-/

namespace Zlib.Infback.Spec
open C Zlib.Inflate Zlib.Inflate.Spec

/-- The heap after a successful `inflateBackEnd`: the state record is freed and the stream's state pointer is `NULL`. -/
def backEndHeap (h : Heap) (r : ZStreamRef) (z : ZStream) (zs : Nat) : Heap :=
  r.put (freeIst h zs) { z with state := none }

end Zlib.Infback.Spec

namespace Zlib.Infback.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs Zlib.Infback Zlib.Infback.Spec

/-- A null stream: `Z_STREAM_ERROR`, nothing changes. -/
theorem inflateBackEnd_nullstream (h : Heap) : inflateBackEnd none h = .ok (Z_STREAM_ERROR, h) := by
  simp [inflateBackEnd]

/-- No state, or no `zfree`: `Z_STREAM_ERROR`, nothing changes. -/
theorem inflateBackEnd_refused {h : Heap} {r : ZStreamRef} {z : ZStream} (hz : r.get h = some z)
    (hno : z.state = none ∨ z.zfree = .null) :
    inflateBackEnd (some r) h = .ok (Z_STREAM_ERROR, h) := by
  rcases hno with e | e <;> isimp [inflateBackEnd, hz, e]

/-- **inflateBackEnd, success.** On a stream set up by `inflateBackInit_` it returns `Z_OK` without a fault, frees the
state record, sets the stream's state pointer to `NULL`, and frees nothing else (the window is the caller's). The
blocks the stream owned are the old ones except the state. -/
theorem inflateBackEnd_ok {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {st : InflateState}
    (hG : BackGood h r zs z st) :
    ∃ h', C.run (inflateBackEnd (some r)) h = .ok (Z_OK, h') ∧ h' = backEndHeap h r z zs ∧
      Uniq h' ∧ Fresh h' ∧ r.get h' = some { z with state := none } ∧
      (∀ S, h.Owns S → h'.Owns (fun b => S b ∧ b ≠ zs)) := by
  have hz := hG.hz
  have hs := hG.hs
  have hrun : inflateBackEnd (some r) h = .ok (Z_OK, backEndHeap h r z zs) := by
    unfold inflateBackEnd
    have hz0 : z.zfree ≠ .null := by rw [hG.zfree]; intro c; cases c
    have hs0 : z.state ≠ none := by rw [hG.zst]; intro c; cases c
    isimp [hz, hs0, hz0, hG.zst, hG.zfree, zfrees_run hz hG.zfree hs, backEndHeap]
  have hU1 : Uniq (freeIst h zs) := uniq_freeIst hG.uniq zs
  have hz1 : r.get (freeIst h zs) = some z := by simpa using hz
  refine ⟨_, by rw [C.run]; exact hrun, rfl, ?_, ?_, ?_, ?_⟩
  · exact (shape_put hz1 _).uniq hU1
  · exact (shape_put hz1 _).fresh (by simp [backEndHeap]) (fresh_freeIst hG.fresh zs)
  · simp [backEndHeap, hz]
  · intro S hO
    have hO1 := owns_freeIst hG.uniq hs hO
    exact (shape_put hz1 _).owns hO1

end Zlib.Infback.Proofs
