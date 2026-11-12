import ZlibF.Proof.«deflate.c.universal-ops-reset»
import ZlibF.Proof.«deflate.c.engine.full-storage»

/-!
# deflate.c: one direct `deflateResetKeep` call is safe (inflate batch 1)

The deflate sequence domain excludes a direct `deflateResetKeep` call (a deviation set by the
deflate owner): after it the chain heads `strstart - 2`, `strstart - 1` keep keys over bytes the
next call overwrites, so `DInv.Hashing` fails (docs/findings/deflate-resetkeep-stale-hash).
`deflateReset`, which runs `deflateResetKeep` and then `lm_init`, stays in the domain
(`step_reset`). For the direct call this file proves single-call safety only, with no invariant
afterwards:

* `resetKeep_single`: from `DInv`, the call returns `Z_OK` with no fault; the heap after it is
  exactly the old heap with the stream record and the state record replaced (`rkZ`, `rkPost`):
  the counters, `msg`, `data_type`, `adler`; `pending`, `pending_out`, `wrap`, `status`,
  `last_flush`, `gzhead`, the trees and bit buffer of `_tr_init`, `matches`, `block_start`,
  `lookahead` and the match state. Window, `prev`, `head` and `pending_buf` are untouched, no
  block is allocated or freed.
* `resetKeep_refuse`: a stream the check refuses gives `Z_STREAM_ERROR` and the same heap.
-/

namespace Zlib.Deflate.Universal
open C ZlibF.Spec ZlibF.Spec.Public Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Engine.Proofs
open Zlib.Deflate.Proofs
set_option autoImplicit false

/-- **A direct `deflateResetKeep` call from the invariant**: no fault, `Z_OK`, and exactly the
writes of the stream record and of the state record; byte and word blocks unchanged, the same
live blocks, no allocation; `DGood` afterwards. -/
theorem resetKeep_single {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv h r ds z d) :
    ∃ (a1 a2 a3 : Array CtData) (after : Heap),
      C.run (Zlib.Deflate.deflateResetKeep (some r)) h = .ok (Z_OK, after) ∧
      after = setD (r.put h (rkZ z d)) ds (rkPost ds (rkMid d) a1 a2 a3) ∧
      a1.size = 573 ∧ a2.size = 61 ∧ a3.size = 39 ∧
      Frame h after (fun b => StreamRoot r b ∨ b = ds) ∧ Zlib.Deflate.Proofs.Shape h after ∧
      after.bytes = h.bytes ∧ after.words = h.words ∧ after.static = h.static ∧
      after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧
      DGood after r ds (rkZ z d) (rkPost ds (rkMid d) a1 a2 a3) := by
  have good := inv.good
  obtain ⟨a1, a2, a3, after, run, eq, s1, s2, s3, goodA, -⟩ := deflateResetKeep_safe good
  have shapeP : Zlib.Deflate.Proofs.Shape h (r.put h (rkZ z d)) := shape_put good.live.hz _
  have stP : (r.put h (rkZ z d)).dstates ds = some d := by simpa using good.live.hs
  have shapeA : Zlib.Deflate.Proofs.Shape h after := by
    rw [eq]; exact shapeP.trans (shape_setD stP _)
  have frame : Frame h after (fun b => StreamRoot r b ∨ b = ds) := by
    rw [eq]
    exact full_frame_trans_shape
      (full_frame_weaken (stream_store_full_frame h r (rkZ z d)) (fun _ e => Or.inl e))
      (full_frame_weaken (state_store_full_frame (r.put h (rkZ z d)) ds _) (fun _ e => Or.inr e)) shapeP
  have putF : ∀ v : ZStream, (r.put h v).bytes = h.bytes ∧ (r.put h v).words = h.words ∧
      (r.put h v).static = h.static ∧ (r.put h v).nalloc = h.nalloc ∧ (r.put h v).nextBlk = h.nextBlk := by
    intro v
    cases r <;> simp only [ZStreamRef.put] <;> split <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨e1, e2, e3, e4, e5⟩ := putF (rkZ z d)
  subst eq
  exact ⟨a1, a2, a3, _, run, rfl, s1, s2, s3, frame, shapeA, e1, e2, e3, e4, e5,
    full_shape_live_change shapeA, goodA⟩

/-- **The refusal**: a stream `deflateStateCheck` refuses gives `Z_STREAM_ERROR` and leaves the
heap as it is. -/
theorem resetKeep_refuse {h : Heap} {strm : ZStreamPtr} (dom : StreamDom h strm) (not : ¬ DInitialised h strm) :
    C.run (Zlib.Deflate.deflateResetKeep strm) h = .ok (Z_STREAM_ERROR, h) :=
  deflateResetKeep_reject dom not

end Zlib.Deflate.Universal
