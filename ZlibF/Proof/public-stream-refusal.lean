import ZlibF.Spec.Public.Refusals
import ZlibF.Proof.«public-inflate-small-queries»
import ZlibF.Proof.«public-deflate-small-queries»
import ZlibF.Proof.«deflate.c.life.getdict»
import ZlibF.Proof.«inflate.c.output-frame-local-cleanup»
import ZlibF.Proof.«inflate.c.sync-default-public»

/-!
# `Goal.inflate_refusal` and `Goal.deflate_refusal`

Every function of the two goals starts with the state check (`inflateStateCheck`,
`deflateStateCheck`), and a refused stream fails it (`notInit_check` from `RefusedInflate` or
`RefusedDeflate`). `inflate` first makes its local four-byte array, so the check runs on that heap.
The refused stream is still refused there, and the array is freed on return (`tmpFreed`).
-/

namespace ZlibF.Spec.Public.RefusalProof
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public
open ZlibF.Spec.Public.InflateQueryProof
set_option autoImplicit false

/-- Making the local array keeps a refused stream refused. -/
theorem refused_syncAlloc {h : Heap} {p : ZStreamPtr} (hr : RefusedInflate h p) :
    RefusedInflate (syncAlloc h) p := by
  rcases hr with hn | ⟨r, z, rfl, hz, bad⟩
  · exact Or.inl hn
  · refine Or.inr ⟨r, z, rfl, ?_, ?_⟩
    · cases r <;> simpa [syncAlloc, ZStreamRef.get] using hz
    · simpa [syncAlloc] using bad

/-- `inflate` refuses a refused stream: it makes and frees its local array and returns. -/
theorem inflate_refused_stream {h : Heap} {p : ZStreamPtr} (fresh : Fresh h) (hr : RefusedInflate h p)
    (flush : Int32) : C.run (inflate p flush) h = .ok (Z_STREAM_ERROR, tmpFreed h) := by
  have hr' := refused_syncAlloc hr
  unfold C.run inflate
  rw [bind_app, allocLocalB_run h fresh]
  simp only []
  rw [bind_app]
  simp only [bind_app, notInit_check (refused_dom hr') (refused_not_initialised hr'), pure_app]
  simp only [bne_iff_ne, ne_eq, show (1 : Int32) ≠ 0 from by decide, not_false_eq_true, ite_true, pure_app]
  dsimp only [syncBuf]
  rw [freeBuf_run (syncAlloc_bytes_buf h) (syncAlloc_ro_buf h)]
  rfl

/-- **Inflate stream refusals.** -/
theorem inflate_refusal : Goal.inflate_refusal := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h p flush fresh hr
    refine ⟨tmpFreed h, inflate_refused_stream fresh hr flush, ?_, ?_⟩
    · have frame := (tmp_freed_buffer_frame fresh (fun _ => False) []).1
      simpa [restoreRegions] using frame
    · intro b
      have := (sync_tmp_freed_shape fresh).live b
      simp only [and_true, or_false, not_false_eq_true]
      exact this
  · intro h p hr
    show inflateEnd p h = _
    unfold inflateEnd
    simp [bind_app, notInit_check (refused_dom hr) (refused_not_initialised hr), pure_app]
  · intro h p hr
    show inflateReset p h = _
    unfold inflateReset
    simp [bind_app, notInit_check (refused_dom hr) (refused_not_initialised hr), pure_app]
  · intro h p w hr
    show inflateReset2 p w h = _
    unfold inflateReset2
    simp [bind_app, notInit_check (refused_dom hr) (refused_not_initialised hr), pure_app]
  · intro h p d l hr
    show inflateGetDictionary p d l h = _
    unfold inflateGetDictionary
    simp [bind_app, notInit_check (refused_dom hr) (refused_not_initialised hr), pure_app]
  · intro h p d l hr
    show inflateSetDictionary p d l h = _
    unfold inflateSetDictionary
    simp [bind_app, notInit_check (refused_dom hr) (refused_not_initialised hr), pure_app]
  · intro h dest oldDest source dget hr
    show inflateCopy (some dest) source h = _
    unfold inflateCopy
    simp [bind_app, notInit_check (refused_dom hr) (refused_not_initialised hr), pure_app, wrZ_eq, dget]

end ZlibF.Spec.Public.RefusalProof

namespace ZlibF.Spec.Public.RefusalProof.Deflate
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Spec.Public.DeflateQueryProof
set_option autoImplicit false

/-- **Deflate stream refusals.** -/
theorem deflate_refusal : Goal.deflate_refusal := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro h p flush hr
    show deflate p flush h = _
    unfold deflate
    rw [bind_app, notInit_check (refused_deflate_dom hr) (refused_deflate_not_init hr)]
    rfl
  · intro h p d l hr
    show deflateSetDictionary p d l h = _
    unfold deflateSetDictionary
    simp [bind_app, notInit_check (refused_deflate_dom hr) (refused_deflate_not_init hr), pure_app]
  · intro h p l s hr
    show deflateParams p l s h = _
    unfold deflateParams
    simp [bind_app, notInit_check (refused_deflate_dom hr) (refused_deflate_not_init hr), pure_app]
  · intro h p d b hr
    exact deflateGetDictionary_reject (refused_deflate_dom hr) (refused_deflate_not_init hr) d b
  · intro h dest oldDest source dget hr
    show deflateCopy (some dest) source h = _
    unfold deflateCopy
    simp [bind_app, notInit_check (refused_deflate_dom hr) (refused_deflate_not_init hr), pure_app,
      zwr_eq, dget]

end ZlibF.Spec.Public.RefusalProof.Deflate

#print axioms ZlibF.Spec.Public.RefusalProof.inflate_refusal
#print axioms ZlibF.Spec.Public.RefusalProof.Deflate.deflate_refusal
