import ZlibF.Proof.«deflate.c.engine.initial»
import ZlibF.Proof.«trees.c.initial-clear»
import ZlibF.Proof.«deflate.c.engine.fill-pending-complete»
import ZlibF.Proof.«deflate.c.engine.block-reset»

/-! # Cleared BL frequencies from the default public entry

These execution siblings retain the BL zeros written by the real initializer.
The final boundary also retains both reset cost counters. The previously registered contracts stay unchanged.
-/

namespace Zlib.Deflate.Engine.Proofs.BlockInit
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open Zlib.Deflate.Proofs.DefaultInit ZlibF.Spec.Public ZlibF.Spec
open ZlibF.Spec.Public.Proofs.DeflateInit Zlib.Deflate.Engine.Proofs
open Zlib.Trees.Proofs.Out (InitialFrequencies TreesBase TreesStatic TreesInvAt ibRec trInitRec)
set_option autoImplicit false

/-- Reset data needed when constructing the next dynamic header. It is
established by actual init/reset and retained through non-flushing frames. -/
structure BlockClear (d : DeflateState) : Prop where
  bl : ∀ k, k < 19 → d.bl_tree[k]!.fc = 0
  opt : d.opt_len = 0
  fixed : d.static_len = 0


theorem rkTail2_bl_zero {H : Heap} {r : ZStreamRef} {ds : Nat} {z' : ZStream} {d3 : DeflateState} {b : Nat} {buf : Array UInt8}
    (hz : r.get H = some z') (hb : Zlib.Trees.Proofs.Out.TreesBase H ds d3 b buf) (v : UInt64) :
    ∃ a1 a2 a3, rkTail2 (some r) (some (.tab ds)) v H =
      .ok (Z_OK, setD (r.put H { z' with adler := v }) ds (rkPost3 ds d3 a1 a2 a3)) ∧
      a1.size = 573 ∧ a2.size = 61 ∧ a3.size = 39 ∧ (∀ k, k < 19 → a3[k]!.fc = 0) := by
  have hd := hb.dstate
  have hb2 : Zlib.Trees.Proofs.Out.TreesBase (setD (r.put H { z' with adler := v }) ds { d3 with last_flush := -2, gzhead := none })
      ds { d3 with last_flush := -2, gzhead := none } b buf :=
    ⟨by simp [setD], hb.wf, by simpa using hb.static, hb.pbuf, by simpa using hb.bytes, by simpa using hb.rw, hb.size,
      hb.psize, hb.sym, hb.lit_lo, hb.lit_hi, hb.sym_end, hb.pending_le⟩
  obtain ⟨a1, a2, a3, d', e, -, hd', s1, s2, s3, frequencies⟩ := Zlib.Trees.Proofs.Out.tr_init_bl_zero hb2
  refine ⟨a1, a2, a3, ?_, s1, s2, s3, frequencies⟩
  rw [trSetD_eq] at e
  unfold rkTail2
  simp only [bind_app, zwr_eq, hz, wrD_eq, rdD_eq, ldD_eq, ZStreamRef.put_dstates, hd, setD_dstates_same, ZStreamRef.get_setD, e, pure_app, setD_setD]
  subst hd'
  simp [rkPost3, setD_setD]

theorem rkTail_bl_zero {H : Heap} {r : ZStreamRef} {ds : Nat} {z' : ZStream} {d2 : DeflateState} {b : Nat} {buf : Array UInt8}
    (hz : r.get H = some z') (hb : Zlib.Trees.Proofs.Out.TreesBase H ds d2 b buf) :
    ∃ a1 a2 a3, rkTail (some r) (some (.tab ds)) H =
      .ok (Z_OK, setD (r.put H { z' with adler := if d2.wrap == 2 then 0 else 1 }) ds (rkPost ds d2 a1 a2 a3)) ∧
      a1.size = 573 ∧ a2.size = 61 ∧ a3.size = 39 ∧ (∀ k, k < 19 → a3[k]!.fc = 0) := by
  have hd := hb.dstate
  have hb3 : Zlib.Trees.Proofs.Out.TreesBase (setD H ds { d2 with status := if d2.wrap == 2 then GZIP_STATE else INIT_STATE })
      ds { d2 with status := if d2.wrap == 2 then GZIP_STATE else INIT_STATE } b buf :=
    ⟨by simp [setD], hb.wf, by simpa using hb.static, hb.pbuf, by simpa using hb.bytes, by simpa using hb.rw, hb.size,
      hb.psize, hb.sym, hb.lit_lo, hb.lit_hi, hb.sym_end, hb.pending_le⟩
  have hz3 : r.get (setD H ds { d2 with status := if d2.wrap == 2 then GZIP_STATE else INIT_STATE }) = some z' := by
    simpa using hz
  obtain ⟨a1, a2, a3, e, s1, s2, s3, frequencies⟩ := rkTail2_bl_zero hz3 hb3 (if d2.wrap == 2 then 0 else 1)
  refine ⟨a1, a2, a3, ?_, s1, s2, s3, frequencies⟩
  unfold rkTail
  by_cases hc : (d2.wrap == 2) = true
  · simp only [hc, ↓reduceIte] at e
    simp only [bind_app, wrD_eq, rdD_eq, hd, setD_dstates_same, hc, ↓reduceIte, crc32_null, pure_app]
    rw [e]
    simp [ZStreamRef.put_setD, setD_setD, rkPost, hc]
  · have hc' : (d2.wrap == 2) = false := by simpa using hc
    simp only [hc', Bool.false_eq_true, ↓reduceIte] at e
    simp only [bind_app, wrD_eq, rdD_eq, hd, setD_dstates_same, hc', Bool.false_eq_true, ↓reduceIte, adler32_null, pure_app]
    rw [e]
    simp [ZStreamRef.put_setD, setD_setD, rkPost, hc]

theorem resetKeep_bl_zero {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState} {b : Nat}
    {buf : Array UInt8} (hL : DLive h r ds z d) (hB : Zlib.Trees.Proofs.Out.TreesBase h ds d b buf)
    (hw1 : -2 ≤ d.wrap.toInt) (hw2 : d.wrap.toInt ≤ 2) :
    ∃ a1 a2 a3, deflateResetKeep (some r) h =
      .ok (Z_OK, setD (r.put h (rkZ z d)) ds (rkPost ds (rkMid d) a1 a2 a3)) ∧
      a1.size = 573 ∧ a2.size = 61 ∧ a3.size = 39 ∧ (∀ k, k < 19 → a3[k]!.fc = 0) := by
  have hbm : Zlib.Trees.Proofs.Out.TreesBase (setD (r.put h { z with total_in := 0, total_out := 0, msg := .null, data_type := Z_UNKNOWN }) ds (rkMid d))
      ds (rkMid d) b buf :=
    ⟨by simp [setD], hB.wf, by simpa using hB.static, hB.pbuf, by simpa using hB.bytes, by simpa using hB.rw, hB.size,
      hB.psize, hB.sym, hB.lit_lo, hB.lit_hi, hB.sym_end, by simp [rkMid]⟩
  have hzm : r.get (setD (r.put h { z with total_in := 0, total_out := 0, msg := .null, data_type := Z_UNKNOWN }) ds (rkMid d)) =
      some { z with total_in := 0, total_out := 0, msg := .null, data_type := Z_UNKNOWN } := by
    simp [ZStreamRef.get_put, hL.hz]
  obtain ⟨a1, a2, a3, e, s1, s2, s3, frequencies⟩ := rkTail_bl_zero hzm hbm
  refine ⟨a1, a2, a3, ?_, s1, s2, s3, frequencies⟩
  rw [deflateResetKeep_eq]
  by_cases hw : d.wrap < 0
  · have hw' : -2 ≤ d.wrap.toInt ∧ d.wrap.toInt < 0 := ⟨hw1, (Int32.lt_iff_toInt_lt.mp hw)⟩
    simp only [bind_app, stateCheck_live hL, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, zwr_eq, hL.hz, zrd_eq,
      ZStreamRef.get_put_same hL.hz, hL.zst, castD, wrD_eq, ZStreamRef.put_dstates, hL.hs, setD_dstates_same, ldD_eq, hw,
      ineg_neg hw'.1 hw'.2, pure_app, setD_setD]
    simp only [rkMid, absWrap, hw, ↓reduceIte, hL.zst] at e
    rw [e]
    simp [rkZ, rkMid, absWrap, hw, ZStreamRef.put_setD, ZStreamRef.put_put, hL.zst]
  · simp only [bind_app, stateCheck_live hL, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, zwr_eq, hL.hz, zrd_eq,
      ZStreamRef.get_put_same hL.hz, hL.zst, castD, wrD_eq, ZStreamRef.put_dstates, hL.hs, setD_dstates_same, ldD_eq, hw,
      pure_app, setD_setD]
    simp only [rkMid, absWrap, hw, ↓reduceIte, hL.zst] at e
    rw [e]
    simp [rkZ, rkMid, absWrap, hw, ZStreamRef.put_setD, ZStreamRef.put_put, hL.zst]

theorem reset_construct_bl_zero {h : Heap} {r : ZStreamRef} {z : ZStream} {ds w p q b : Nat}
    (level : Int32) (hl : DLive h r ds z (readyState r level w p q b))
    (ht : TreesBase h ds (readyState r level w p q b) b
      ((h.bytes b).getD #[]))
    (hb : DBlocks h { readyState r level w p q b with
      pending_out := (readyState r level w p q b).pending_buf } w p q b)
    (hu : Uniq h) (hf : Fresh h) (hl0 : 0 ≤ level.toInt) (hl9 : level.toInt ≤ 9) :
    ∃ (a1 a2 a3 : Array CtData) (qa : Array UInt16),
      a1.size = 573 ∧ a2.size = 61 ∧ a3.size = 39 ∧ (∀ k, k < 19 → a3[k]!.fc = 0) ∧ h.words q = some qa ∧
      let dr := resetState ds r level w p q b a1 a2 a3
      let hr := setD (r.put h (rkZ z (readyState r level w p q b))) ds dr
      let after := setD (setW hr q (clearHead qa 32768)) ds (lmD dr)
      deflateReset (some r) h = .ok (Z_OK, after) ∧
      DGood after r ds (rkZ z (readyState r level w p q b)) (lmD dr) ∧
      (∀ x, after.live x ↔ h.live x) := by
  obtain ⟨a1, a2, a3, hreset, s1, s2, s3, frequencies⟩ := resetKeep_bl_zero hl ht
    (by change (-2 : Int) ≤ (1 : Int32).toInt; decide +kernel)
    (by change (1 : Int32).toInt ≤ (2 : Int); decide +kernel)
  let dr := resetState ds r level w p q b a1 a2 a3
  let zr := rkZ z (readyState r level w p q b)
  let hr := setD (r.put h zr) ds dr
  have hsR : hr.dstates ds = some dr := by simp [hr]
  have hzR : r.get hr = some zr := by simp [hr, ZStreamRef.get_put_same hl.hz]
  have hbR : DBlocks hr dr w p q b := DBlocks.congr (by simp [hr]) (by simp [hr])
    (by simp [hr]) (blocks_reset hb a1 a2 a3)
  obtain ⟨qa, hqa, sizeQ⟩ := hbR.qa
  have qsize : qa.size = 32768 := by simpa [dr, resetState, rkPost, rkPost3, rkMid,
    ibRec, trInitRec, readyState, allocatedState, baseState] using sizeQ
  have level0 : 0 ≤ dr.level.toInt := by simpa [dr, resetState, rkPost, rkPost3, rkMid,
    ibRec, trInitRec, readyState] using hl0
  have level9 : dr.level.toInt ≤ 9 := by simpa [dr, resetState, rkPost, rkPost3, rkMid,
    ibRec, trInitRec, readyState] using hl9
  have hash : dr.hash_size.toNat = 32768 := by
    simp [dr, resetState, rkPost, rkPost3, rkMid, ibRec, trInitRec, readyState, allocatedState, baseState]
  have hlm := lm_init_run hsR hbR hqa level0 level9 (by omega) (by omega)
  rw [hash] at hlm
  let after := setD (setW hr q (clearHead qa 32768)) ds (lmD dr)
  have hbW := hbR.words_set q (clearHead qa 32768) qa hqa (size_clearHead _ _)
  have hbF : DBlocks after (lmD dr) w p q b :=
    blocks_lm (DBlocks.congr (by simp [after, setW]) (by simp [after, setW])
      (by simp [after, setW]) hbW)
  have hI : DStInv after ds (lmD dr) := final_inv ds r level w p q b a1 a2 a3
    s1 s2 s3 hl0 hl9 hbF
  have shapeR : Shape h hr := (shape_put hl.hz zr).trans (shape_setD (by simpa using hl.hs) dr)
  have shapeF : Shape hr after := (shape_setW hqa _).trans (shape_setD (by simpa using hsR) _)
  have shape := shapeR.trans shapeF
  refine ⟨a1, a2, a3, qa, s1, s2, s3, frequencies, by simpa [hr] using hqa, ?_, ?_, fun x => shape.live x⟩
  · unfold deflateReset
    rw [bind_app, hreset]
    simp only [bind_app, beq_self_eq_true, ite_true]
    change (do lm_init (← castDeflateState (← zrd (some r) (·.state))); pure Z_OK) hr = _
    simp only [bind_app, zrd_eq, hzR, zr, rkZ, hl.zst, castD]
    rw [hlm]
    simp only [pure_app]
    simp [after, hr, zr, rkZ, hl.zst, dr]
  · refine ⟨⟨?_, by simp [after], ?_, ?_, ?_, ?_, ?_⟩, hI,
      shape.uniq hu, shape.fresh (by simp [after, hr, setW]) hf, ?_⟩
    · simp only [after, ZStreamRef.get_setD, get_setW, hr, zr,
        ZStreamRef.get_put_same hl.hz]
    · simpa [zr, rkZ] using hl.zst
    · simp [dr, lmD, resetState, rkPost, rkPost3, rkMid, ibRec, trInitRec,
        readyState, allocatedState, baseState]
    · left
      simp [dr, lmD, resetState, rkPost, rkPost3, rkMid, absWrap, ibRec, trInitRec,
        readyState, allocatedState, baseState]
    · simpa [zr, rkZ] using hl.zalloc
    · simpa [zr, rkZ] using hl.zfree
    · refine ⟨lmD dr, b, (h.bytes b).getD #[], ?_, ?_⟩
      · refine ⟨by simp only [after, setD_dstates_same]; rfl, hI.wf, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simpa [after, hr, setW] using ht.static
        · simpa [dr, lmD, resetState, rkPost, rkPost3, rkMid, ibRec, trInitRec] using ht.pbuf
        · simpa [after, hr, setW] using ht.bytes
        · simpa [after, hr, setW] using ht.rw
        · simpa [dr, lmD, resetState, rkPost, rkPost3, rkMid, ibRec, trInitRec] using ht.size
        · simpa [dr, lmD, resetState, rkPost, rkPost3, rkMid, ibRec, trInitRec] using ht.psize
        · simpa [dr, lmD, resetState, rkPost, rkPost3, rkMid, ibRec, trInitRec] using ht.sym
        · simpa [dr, lmD, resetState, rkPost, rkPost3, rkMid, ibRec, trInitRec] using ht.lit_lo
        · simpa [dr, lmD, resetState, rkPost, rkPost3, rkMid, ibRec, trInitRec] using ht.lit_hi
        · simpa [dr, lmD, resetState, rkPost, rkPost3, rkMid, ibRec, trInitRec] using ht.sym_end
        · simp [dr, lmD, resetState, rkPost, rkPost3, rkMid, ibRec, trInitRec]
      · refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩ <;>
          simp [dr, lmD, resetState, rkPost, rkPost3, rkMid, ibRec, trInitRec]

theorem allocate_bl_zero {h : Heap} {r : ZStreamRef} {z : ZStream}
    (hf : Fresh h) (hu : Uniq h) (hz : r.get h = some z) (hd : DefAlloc z)
    (hs : TreesStatic h.static) (ha : ∀ j, j < 5 → h.allocOk (h.nalloc + j) = true)
    (level : Int32) (hl0 : 0 ≤ level.toInt) (hl9 : level.toInt ≤ 9) :
    ∃ (a1 a2 a3 : Array CtData) (qa : Array UInt16),
      (∀ k, k < 19 → a3[k]!.fc = 0) ∧
      allocate (some r) level h = .ok (Z_OK, successHeap h r z level a1 a2 a3 qa) ∧
      DGood (successHeap h r z level a1 a2 a3 qa) r h.nextBlk (resultStream h r z level)
        (resultState h r level a1 a2 a3) ∧
      (∀ x, (successHeap h r z level a1 a2 a3 qa).live x ↔
        h.live x ∨ h.nextBlk ≤ x ∧ x < h.nextBlk + 5) := by
  let ph := publishedHeap h r z
  have ha0 : h.allocOk h.nalloc = true := by simpa using ha 0 (by decide)
  have ha4 : ∀ j, j < 4 → ph.allocOk (ph.nalloc + j) = true := by
    intro j hj
    simpa [ph, publishedHeap, stateHeap, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ha (j + 1) (by omega)
  have hfp := (shape_put hz (stateStream z h.nextBlk)).fresh (by simp) hf
  have hup := (shape_put hz (stateStream z h.nextBlk)).uniq hu
  have hfP : Fresh ph := fresh_stateHeap hfp _
  have huP : Uniq ph := uniq_stateHeap hup hfp _
  have hzP : r.get ph = some (stateStream z h.nextBlk) := by
    simp [ph, publishedHeap, ZStreamRef.get_put_same hz]
  have hdP : DefAlloc (stateStream z h.nextBlk) := hd
  have hsP : ph.dstates h.nextBlk = some (baseState r) := by simp [ph, publishedHeap, stateHeap]
  have hst : TreesStatic ph.static := by simpa [ph, publishedHeap, stateHeap] using hs
  obtain ⟨hlR, htR, hbR, huR, hfR⟩ := ready_storage level hfP huP hzP hsP
    (by simp [ph, publishedHeap, stateHeap]) hdP rfl hst ha4
  obtain ⟨a1, a2, a3, qa, s1, s2, s3, frequencies, hqa, hreset, hG, hLive⟩ :=
    reset_construct_bl_zero level hlR htR hbR huR hfR hl0 hl9
  refine ⟨a1, a2, a3, qa, frequencies, ?_, ?_, ?_⟩
  · rw [allocate_to_finish hf hz hd.1 ha0, finish_to_reset _ _ _ _ ha4, hreset]
    rfl
  · simpa only [successHeap, resultStream, resultState, finalState,
      ph, publishedHeap, stateHeap, ZStreamRef.put_nextBlk, Nat.add_assoc] using hG
  · intro x
    have hc := ready_live hz level ha4 x
    have hr := hLive x
    simpa only [successHeap, resultStream] using hr.trans hc

theorem default_initialization_block_clear {h : Heap} {r : ZStreamRef} {z : ZStream}
    {version : BPtr} {level : Int32} {p : Api.DeflParams}
    (hf : Fresh h) (hu : Uniq h) (hg : LibraryGlobals h) (hz : r.get h = some z)
    (ha : DefaultOrNull z) (hv : VersionValue h version (some 49))
    (params : Api.deflInit? level.toInt 8 15 8 0 = some p)
    (alloc : ∀ j, j < 5 → h.allocOk (h.nalloc + j) = true) :
    ∃ after zf sf, C.run (deflateInit_ (some r) level version 112) h = .ok (Z_OK, after) ∧
      EngineStart after r h.nextBlk zf sf ∧ DeflateInitial h after r p ∧
      StreamReachable .deflate after r ∧ BlockClear sf := by
  obtain ⟨after, hr, hi, reachable⟩ := default_initialization_reachable hf hu hg hz ha hv params alloc
  let zp := preparedStream z
  let hp := r.put h zp
  let lev := levelValue level
  have shape := shape_put hz zp
  have hfP : Fresh hp := shape.fresh (by simp [hp]) hf
  have huP : Uniq hp := shape.uniq hu
  have hzP : r.get hp = some zp := ZStreamRef.get_put_same hz _
  have haP : DefAlloc zp := prepared_allocators ha
  have bad : ¬ (levelValue level < 0 || levelValue level > 9) = true := by
    intro hb
    have parsed := parameters_equiv level
    rw [params] at parsed
    simp only [if_pos hb] at parsed
    cases parsed
  have bounds : 0 ≤ lev.toInt ∧ lev.toInt ≤ 9 := by
    have bn := bad
    simp only [Bool.or_eq_true, decide_eq_true_eq, Int32.lt_iff_toInt_lt] at bn
    change ¬ (lev.toInt < 0 ∨ 9 < lev.toInt) at bn
    omega
  obtain ⟨a1, a2, a3, qa, frequencies, run, good, _⟩ := allocate_bl_zero hfP huP hzP haP
    (by simpa [hp] using globals_trees hg) (by simpa [hp] using alloc) lev bounds.1 bounds.2
  have actual : C.run (deflateInit_ (some r) level version 112) h =
      .ok (Z_OK, successHeap hp r zp lev a1 a2 a3 qa) := by
    rw [C.run, entry_run hz hv level, if_neg bad]
    exact run
  rw [actual] at hr
  cases hr
  refine ⟨_, resultStream hp r zp lev, resultState hp r lev a1 a2 a3, actual, ?_, hi, reachable, ?_⟩
  · have engine := initialized_engine good
    simpa only [hp, ZStreamRef.put_nextBlk] using engine
  · exact ⟨frequencies, rfl, rfl⟩

end Zlib.Deflate.Engine.Proofs.BlockInit
