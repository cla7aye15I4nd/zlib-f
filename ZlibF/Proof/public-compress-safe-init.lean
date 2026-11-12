import ZlibF.Proof.«public-uncompress-safe»
import ZlibF.Proof.«deflate.c.borrow-stable»
import ZlibF.Proof.«deflate.c.borrow-stable-lifecycle»
import ZlibF.Proof.«deflate.c.borrow-stable-allocation»
import ZlibF.Proof.«public-deflate-init»

/-!
# compress.c: safety, the entry and `deflateInit`

The safety of `compress2_z` (`Goal.compress2_z_safety`) is proved from the public goals of
the three deflate functions it calls (`Goal.deflateInit_`, `Goal.deflate`, `Goal.deflateEnd`),
taken as explicit hypotheses of exactly those types, and from four facts about one `deflate`
call that the public `Goal.deflate` does not state yet (`DeflateLoopFacts`, requested from
the deflate owner). This file: the hypotheses, the heap after the automatic `z_stream` is
made, and the arguments of `deflateInit_`.
-/

namespace ZlibF.Spec.Public.Proofs.Compress
open C ZlibF.Spec ZlibF.Spec.Public Zlib.Compress Zlib.Deflate
set_option autoImplicit false

/-- Four facts about one `deflate` call from a reachable stream, beyond `Goal.deflate`:

* progress without `Z_FINISH`: a call that is not refused, with `Z_NO_FLUSH`, input and output space that returns
  `Z_OK` consumes input or writes output;
* for a call that is not refused, new input after the first `Z_FINISH` gives `Z_BUF_ERROR` or
  writes at least one byte (pending output is flushed before `deflate.c` checks
  `s->status == FINISH_STATE && strm->avail_in != 0`);
* every call, refused or not, keeps the gzip header pointer and the owned blocks. -/
def DeflateLoopFacts : Prop :=
  ∀ h r i z s flush rc after,
    StreamReachable .deflate h r → Zlib.Deflate.Spec.DGood h r i z s →
    StreamBuffers h r → ActiveHeader h r →
    C.run (Zlib.Deflate.deflate (some r) flush) h = .ok (rc, after) →
    (¬ DeflateRefuses z s flush → flush = Z_NO_FLUSH → z.avail_in ≠ 0 → z.avail_out ≠ 0 → rc = Z_OK →
      ∀ z', r.get after = some z' → z'.avail_in ≠ z.avail_in ∨ z'.avail_out ≠ z.avail_out) ∧
    (¬ DeflateRefuses z s flush → s.status = FINISH_STATE → z.avail_in ≠ 0 →
      rc = Z_BUF_ERROR ∨ ∀ z', r.get after = some z' → z'.avail_out ≠ z.avail_out) ∧
    (∀ z' s', Zlib.Deflate.Spec.DGood after r i z' s' →
      s'.gzhead = s.gzhead ∧ ∀ b, DeflateOwned i s' b ↔ DeflateOwned i s b)

private theorem version_index : strIndex ZLIB_VERSION = some 57 := by decide +kernel

/-- `zlibVersion()` returns the static version string and changes nothing. -/
theorem version_run (h : Heap) :
    Zlib.Zutil.zlibVersion h = .ok (.ref (.str 57) 0, h) := by
  simp [Zlib.Zutil.zlibVersion, Zlib.Zutil.strLit, strLitRef, version_index]

/-- The first byte of the version string is `'1'`. -/
theorem version_value (h : Heap) : VersionValue h (.ref (.str 57) 0) (some 49) :=
  ZlibF.Spec.Public.Proofs.Uncompress.version_value h

/-- The automatic `z_stream` after `stream.zalloc = stream.zfree = stream.opaque = 0`. -/
def cStream (h : Heap) : ZStream :=
  { ZStream.garbage (h.garbage h.nalloc) with zalloc := FnPtr.null, zfree := FnPtr.null, «opaque» := .null }

/-- The heap with the automatic `z_stream` at the first free block. -/
def cHeap (h : Heap) : Heap :=
  { h with streams := upd h.streams h.nextBlk (some (cStream h)), nextBlk := h.nextBlk + 1 }

theorem cHeap_live (h : Heap) (b : Nat) : (cHeap h).live b ↔ h.live b ∨ b = h.nextBlk := by
  simp only [cHeap, Heap.live, upd_apply]
  by_cases e : b = h.nextBlk
  · subst e; simp
  · simp [e]

theorem cHeap_fresh {h : Heap} (fresh : Fresh h) : Fresh (cHeap h) := by
  intro b hb live
  rcases (cHeap_live h b).1 live with l | e
  · exact fresh b (by simp [cHeap] at hb; omega) l
  · simp [cHeap] at hb; omega

theorem cHeap_uniq {h : Heap} (fresh : Fresh h) (u : Zlib.Deflate.Spec.Uniq h) :
    Zlib.Deflate.Spec.Uniq (cHeap h) := by
  intro b
  have ub := u b
  simp only [cHeap, upd_apply]
  by_cases e : b = h.nextBlk
  · subst e
    have nl := fresh h.nextBlk (Nat.le_refl _)
    simp only [Heap.live, not_or, ne_eq, Decidable.not_not] at nl
    simp [nl.1, nl.2.1, nl.2.2.2.1, nl.2.2.2.2.1, nl.2.2.2.2.2.1, nl.2.2.2.2.2.2]
  · simpa [e] using ub

theorem cHeap_globals {h : Heap} (g : LibraryGlobals h) : LibraryGlobals (cHeap h) := g

theorem cHeap_get (h : Heap) : (ZStreamRef.tab h.nextBlk).get (cHeap h) = some (cStream h) := by
  simp [cHeap, ZStreamRef.get]

theorem cStream_default (h : Heap) : DefaultOrNull (cStream h) :=
  ⟨Or.inl rfl, Or.inl rfl⟩

open Zlib.Deflate.Spec (Uniq DGood DefAlloc) in
open Zlib.Deflate.Proofs Zlib.Deflate.Proofs.DefaultInit ZlibF.Spec.Public.Proofs.DeflateInit in
/-- `deflateInit(&stream, level)` on the automatic stream: it refuses the level or fails an
allocation and leaves only the stream record changed (`Uniq`, same live blocks, frame of the
root), or it succeeds with five allocations and the initial state. -/
theorem init_cases {h : Heap} (fresh : Fresh h) (uniq : Uniq h) (globals : LibraryGlobals h) (level : Int32) :
    ∃ rc after, deflateInit_ (some (.tab h.nextBlk)) level (.ref (.str 57) 0) 112 (cHeap h) = .ok (rc, after) ∧
      ((rc ≠ Z_OK ∧ Uniq after ∧ (∀ b, after.live b ↔ (cHeap h).live b) ∧
          Frame (cHeap h) after (StreamRoot (.tab h.nextBlk)) ∧
          (∃ z', (ZStreamRef.tab h.nextBlk).get after = some z') ∧
          (rc = Z_MEM_ERROR → AllocationFailed h after)) ∨
       (rc = Z_OK ∧ after.nalloc = h.nalloc + 5 ∧ ∃ p, DeflateInitial (cHeap h) after (.tab h.nextBlk) p)) := by
  let r : ZStreamRef := .tab h.nextBlk
  let H := cHeap h
  have hf : Fresh H := cHeap_fresh fresh
  have hu : Uniq H := cHeap_uniq fresh uniq
  have hg : LibraryGlobals H := cHeap_globals globals
  have hz : r.get H = some (cStream h) := cHeap_get h
  have ha : DefaultOrNull (cStream h) := cStream_default h
  let zp := preparedStream (cStream h)
  let hp := r.put H zp
  let lev := levelValue level
  have hshape := shape_put hz zp
  have hfP : Fresh hp := hshape.fresh (by simp [hp]) hf
  have huP : Uniq hp := hshape.uniq hu
  have hzP : r.get hp = some zp := ZStreamRef.get_put_same hz _
  have haP : DefAlloc zp := prepared_allocators ha
  have entry := entry_run hz (version_value H) level
  have hpLive : ∀ b, hp.live b ↔ H.live b := hshape.live
  have hpN : hp.nalloc = h.nalloc := by simp [H, cHeap, hp]
  have hpA : hp.allocOk = h.allocOk := by simp [hp, H, cHeap]
  by_cases bad : (levelValue level < 0 || levelValue level > 9) = true
  · refine ⟨Z_STREAM_ERROR, hp, ?_, Or.inl ⟨by decide, huP, hpLive, frame_put r zp hf, ⟨zp, hzP⟩,
      fun e => absurd e (by decide)⟩⟩
    simpa only [ite_eq_left bad] using entry
  · have bounds : 0 ≤ lev.toInt ∧ lev.toInt ≤ 9 := by
      have bn := bad
      simp only [Bool.or_eq_true, decide_eq_true_eq, Int32.lt_iff_toInt_lt] at bn
      change ¬ (lev.toInt < 0 ∨ 9 < lev.toInt) at bn
      omega
    have entry' : deflateInit_ (some r) level (.ref (.str 57) 0) 112 H = allocate (some r) lev hp := by
      simpa only [ite_eq_right bad] using entry
    by_cases first : h.allocOk h.nalloc = false
    · have firstH : H.allocOk H.nalloc = false := by simpa [H, cHeap] using first
      refine ⟨Z_MEM_ERROR, { hp with nalloc := hp.nalloc + 1 }, ?_, Or.inl ⟨by decide, ?_, ?_, ?_, ⟨zp, ?_⟩, ?_⟩⟩
      · rw [entry']
        exact allocate_state_fail hzP haP.1 (by simpa [hp] using firstH) lev
      · intro b; exact huP b
      · intro b; exact hpLive b
      · obtain ⟨f1, f2, f3, f4, f5, f6⟩ := frame_put (h := H) r zp hf
        exact ⟨f1, f2, f3, f4, Nat.le_trans f5 (Nat.le_succ _), f6⟩
      · exact hzP
      · intro _
        exact ⟨h.nalloc, Nat.le_refl _, by simp [hpN], first⟩
    · have firstT : H.allocOk H.nalloc = true := by
        cases he : h.allocOk h.nalloc
        · exact absurd he first
        · simpa [H, cHeap] using he
      by_cases all : (List.range 5).all (fun j => H.allocOk (H.nalloc + j)) = true
      · have allok : ∀ j, j < 5 → H.allocOk (H.nalloc + j) = true := by
          simpa only [List.all_eq_true, List.mem_range] using all
        obtain ⟨after, hr, hi⟩ := success_initial hf hu hg hz ha allok lev bounds.1 bounds.2
        have count := allocate_success_count hfP huP hzP haP
          (by simpa [hp] using globals_trees hg) (by simpa [hp] using allok) lev bounds.1 bounds.2 hr
        refine ⟨Z_OK, after, ?_, Or.inr ⟨rfl, ?_, _, hi⟩⟩
        · rw [entry']; exact hr
        · rw [count, hpN]
      · let ph := publishedHeap hp r zp
        have failed : ((bufferPointers ph).1 == .null || (bufferPointers ph).2.1 == .null ||
            (bufferPointers ph).2.2.1 == .null || (bufferPointers ph).2.2.2 == .null) = true := by
          apply Classical.byContradiction
          intro hn
          have hb : ((bufferPointers ph).1 == .null || (bufferPointers ph).2.1 == .null ||
              (bufferPointers ph).2.2.1 == .null || (bufferPointers ph).2.2.2 == .null) = false := by
            cases he : ((bufferPointers ph).1 == .null || (bufferPointers ph).2.1 == .null ||
              (bufferPointers ph).2.2.1 == .null || (bufferPointers ph).2.2.2 == .null) <;> simp_all
          obtain ⟨h0, h1, h2, h3⟩ := (buffers_failed_iff ph).mp hb
          apply all
          rw [List.all_eq_true]
          intro j hj
          have hj5 := List.mem_range.mp hj
          have hn : ph.nalloc = H.nalloc + 1 := by simp [ph, publishedHeap, stateHeap, hp]
          have ao : ph.allocOk = H.allocOk := by simp [ph, publishedHeap, stateHeap, hp]
          rw [ao, hn] at h0 h1 h2 h3
          have cases5 : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by omega
          rcases cases5 with h | h | h | h | h <;> subst j <;>
            simpa only [Nat.add_assoc, Nat.add_zero] using (by assumption)
        obtain ⟨m, hm⟩ := finish_failure hzP haP lev failed
        let after := failureHeap hp r zp m
        have shp := failure_shape hzP hfP m
        refine ⟨Z_MEM_ERROR, after, ?_, Or.inl ⟨by decide, shp.uniq huP, ?_,
          frame_trans r (frame_put r zp hf) (failure_frame r zp m hfP), ⟨_, failure_stream_cleared hzP m⟩, ?_⟩⟩
        · rw [entry', allocate_to_finish hfP hzP haP.1 (by simpa [hp] using firstT)]
          exact hm
        · intro x
          exact (shp.live x).trans (hpLive x)
        · intro _
          have some : ∃ j, j < 5 ∧ H.allocOk (H.nalloc + j) = false := by
            apply Classical.byContradiction
            intro no
            apply all
            rw [List.all_eq_true]
            intro j hj
            cases e : H.allocOk (H.nalloc + j)
            · exact absurd ⟨j, List.mem_range.mp hj, e⟩ no
            · rfl
          obtain ⟨j, hj, e⟩ := some
          refine ⟨h.nalloc + j, Nat.le_add_right _ _, ?_, by simpa [H, cHeap] using e⟩
          have := failure_count hp r zp m
          simp only [after, this, hpN]
          omega

end ZlibF.Spec.Public.Proofs.Compress
