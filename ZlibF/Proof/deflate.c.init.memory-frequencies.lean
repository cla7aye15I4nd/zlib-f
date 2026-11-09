import ZlibF.Proof.«deflate.c.init.memory-success»
import ZlibF.Proof.«deflate.c.engine.symbol-initial»

namespace Zlib.Deflate.Proofs.MemoryInit
open C Zlib.Deflate Zlib.Deflate.Spec DefaultInit
open Zlib.Trees.Proofs.Out (TreesBase TreesInvAt TreesStatic InitialFrequencies ibRec trInitRec)
open ZlibF.Spec.Public
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 5000000
variable (memory : Nat)

theorem reset_construct_frequencies {h : Heap} {r : ZStreamRef} {z : ZStream} {ds w p q b : Nat}
    (level : Int32) (hl : DLive h r ds z (readyState memory r level w p q b))
    (ht : TreesBase h ds (readyState memory r level w p q b) b
      ((h.bytes b).getD #[]))
    (hb : DBlocks h { readyState memory r level w p q b with
      pending_out := (readyState memory r level w p q b).pending_buf } w p q b)
    (hu : Uniq h) (hf : Fresh h) (hl0 : 0 ≤ level.toInt) (hl9 : level.toInt ≤ 9)
    (memoryLow : 1 ≤ memory) (memoryHigh : memory ≤ 9) :
    ∃ (a1 a2 a3 : Array CtData) (qa : Array UInt16),
      a1.size = 573 ∧ a2.size = 61 ∧ a3.size = 39 ∧ InitialFrequencies a1 a2 ∧ h.words q = some qa ∧
      let dr := resetState memory ds r level w p q b a1 a2 a3
      let hr := setD (r.put h (rkZ z (readyState memory r level w p q b))) ds dr
      let after := setD (setW hr q (clearHead qa (UInt32.ofNat (2 ^ (memory + 7))).toNat)) ds (lmD dr)
      deflateReset (some r) h = .ok (Z_OK, after) ∧
      DGood after r ds (rkZ z (readyState memory r level w p q b)) (lmD dr) ∧
      (∀ x, after.live x ↔ h.live x) := by
  obtain ⟨a1, a2, a3, hreset, s1, s2, s3, frequencies⟩ := Zlib.Deflate.Engine.Proofs.SymbolInit.resetKeep_frequencies hl ht
    (by change (-2 : Int) ≤ (1 : Int32).toInt; decide +kernel)
    (by change (1 : Int32).toInt ≤ (2 : Int); decide +kernel)
  let dr := resetState memory ds r level w p q b a1 a2 a3
  let zr := rkZ z (readyState memory r level w p q b)
  let hr := setD (r.put h zr) ds dr
  have hsR : hr.dstates ds = some dr := by simp [hr]
  have hzR : r.get hr = some zr := by simp [hr, ZStreamRef.get_put_same hl.hz]
  have hbR : DBlocks hr dr w p q b := DBlocks.congr (by simp [hr]) (by simp [hr])
    (by simp [hr]) (blocks_reset hb a1 a2 a3)
  obtain ⟨qa, hqa, sizeQ⟩ := hbR.qa
  have qsize : qa.size = (UInt32.ofNat (2 ^ (memory + 7))).toNat := by simpa [dr, resetState, rkPost, rkPost3, rkMid,
    ibRec, trInitRec, readyState, allocatedState, baseState] using sizeQ
  have level0 : 0 ≤ dr.level.toInt := by simpa [dr, resetState, rkPost, rkPost3, rkMid,
    ibRec, trInitRec, readyState] using hl0
  have level9 : dr.level.toInt ≤ 9 := by simpa [dr, resetState, rkPost, rkPost3, rkMid,
    ibRec, trInitRec, readyState] using hl9
  have hash : dr.hash_size.toNat = (UInt32.ofNat (2 ^ (memory + 7))).toNat := by
    simp [dr, resetState, rkPost, rkPost3, rkMid, ibRec, trInitRec, readyState, allocatedState, baseState]
  have hashCount : (UInt32.ofNat (2 ^ (memory + 7))).toNat = 2 ^ (memory + 7) := by
    rcases ZlibF.Math.DeflateMemLevel.memory_cases memoryLow memoryHigh with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have hashPositive : 1 ≤ (UInt32.ofNat (2 ^ (memory + 7))).toNat := by
    rw [hashCount]
    exact Nat.two_pow_pos _
  have hlm := lm_init_run hsR hbR hqa level0 level9 (by rw [hash]; exact hashPositive) (by omega)
  rw [hash] at hlm
  let after := setD (setW hr q (clearHead qa (UInt32.ofNat (2 ^ (memory + 7))).toNat)) ds (lmD dr)
  have hbW := hbR.words_set q (clearHead qa (UInt32.ofNat (2 ^ (memory + 7))).toNat) qa hqa (size_clearHead _ _)
  have hbF : DBlocks after (lmD dr) w p q b :=
    blocks_lm (DBlocks.congr (by simp [after, setW]) (by simp [after, setW])
      (by simp [after, setW]) hbW)
  have hI : DStInv after ds (lmD dr) := final_inv memory ds r level w p q b a1 a2 a3
    s1 s2 s3 hl0 hl9 memoryLow memoryHigh hbF
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


theorem allocate_success_frequencies {h : Heap} {r : ZStreamRef} {z : ZStream}
    (hf : Fresh h) (hu : Uniq h) (hz : r.get h = some z) (hd : DefAlloc z)
    (hs : TreesStatic h.static) (ha : ∀ j, j < 5 → h.allocOk (h.nalloc + j) = true)
    (level : Int32) (hl0 : 0 ≤ level.toInt) (hl9 : level.toInt ≤ 9)
    (memoryLow : 1 ≤ memory) (memoryHigh : memory ≤ 9) :
    ∃ (a1 a2 a3 : Array CtData) (qa : Array UInt16),
      InitialFrequencies a1 a2 ∧
      allocate (some r) level memory h = .ok (Z_OK, successHeap memory h r z level a1 a2 a3 qa) ∧
      DGood (successHeap memory h r z level a1 a2 a3 qa) r h.nextBlk (resultStream memory h r z level)
        (resultState memory h r level a1 a2 a3) ∧
      (∀ x, (successHeap memory h r z level a1 a2 a3 qa).live x ↔
        h.live x ∨ h.nextBlk ≤ x ∧ x < h.nextBlk + 5) := by
  let ph := publishedHeap h r z memory
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
  have hsP : ph.dstates h.nextBlk = some (baseState r memory) := by simp [ph, publishedHeap, stateHeap]
  have hst : TreesStatic ph.static := by simpa [ph, publishedHeap, stateHeap] using hs
  obtain ⟨hlR, htR, hbR, huR, hfR⟩ := ready_storage memory level memoryLow memoryHigh hfP huP hzP hsP
    (by simp [ph, publishedHeap, stateHeap]) hdP rfl hst ha4
  obtain ⟨a1, a2, a3, qa, s1, s2, s3, frequencies, hqa, hreset, hG, hLive⟩ :=
    reset_construct_frequencies memory level hlR htR hbR huR hfR hl0 hl9 memoryLow memoryHigh
  refine ⟨a1, a2, a3, qa, frequencies, ?_, ?_, ?_⟩
  · rw [allocate_to_finish hf hz hd.1 ha0 level memory, finish_to_reset memory _ _ _ _ memoryLow memoryHigh ha4, hreset]
    rfl
  · simpa only [successHeap, resultStream, resultState, finalState,
      ph, publishedHeap, stateHeap, ZStreamRef.put_nextBlk, Nat.add_assoc] using hG
  · intro x
    have hc := ready_live memory hz level ha4 x
    have hr := hLive x
    simpa only [successHeap, resultStream] using hr.trans hc


open ZlibF.Spec.Public.Proofs.DeflateInit (globals_trees)

theorem public_success_engine_frequencies {h : Heap} {r : ZStreamRef} {z : ZStream} {version : BPtr}
    (fresh : Fresh h) (unique : Uniq h) (globals : LibraryGlobals h)
    (stream : r.get h = some z) (callbacks : DefaultOrNull z)
    (versionValue : VersionValue h version (some 49)) (level : Int32)
    (memoryLow : 1 ≤ memory) (memoryHigh : memory ≤ 9)
    (levelLow : 0 ≤ (levelValue level).toInt) (levelHigh : (levelValue level).toInt ≤ 9)
    (allok : ∀ j, j < 5 → h.allocOk (h.nalloc + j) = true) :
    ∃ after zf sf,
      C.run (deflateInit2_ (some r) level 8 15 (Int32.ofInt memory) 0 version 112) h = .ok (Z_OK, after) ∧
      MemoryInitStart memory after r h.nextBlk zf sf ∧ InitialFrequencies sf.dyn_ltree sf.dyn_dtree ∧ sf.level = levelValue level ∧
      DeflateInitial h after r (settings memory (levelValue level)) ∧
      StreamReachable .deflate after r ∧ after.nalloc = h.nalloc + 5 := by
  let zp := preparedStream z
  let hp := r.put h zp
  have shape := shape_put stream zp
  have freshP : Fresh hp := shape.fresh (by simp [hp]) fresh
  have uniqueP : Uniq hp := shape.uniq unique
  have streamP : r.get hp = some zp := ZStreamRef.get_put_same stream _
  have callbacksP : DefAlloc zp := prepared_allocators callbacks
  have globalsP : TreesStatic hp.static := by simpa [hp] using globals_trees globals
  have allP : ∀ j, j < 5 → hp.allocOk (hp.nalloc + j) = true := by
    intro j below
    simpa [hp] using allok j below
  obtain ⟨a1, a2, a3, qa, frequencies, allocationRun, good, live⟩ :=
    allocate_success_frequencies memory freshP uniqueP streamP callbacksP globalsP allP
      (levelValue level) levelLow levelHigh memoryLow memoryHigh
  let after := successHeap memory hp r zp (levelValue level) a1 a2 a3 qa
  let zf := resultStream memory hp r zp (levelValue level)
  let sf := resultState memory hp r (levelValue level) a1 a2 a3
  have valid : ¬ (levelValue level < 0 || levelValue level > 9) = true := by
    simp only [Bool.or_eq_true, decide_eq_true_eq, Int32.lt_iff_toInt_lt]
    change ¬ ((levelValue level).toInt < 0 ∨ 9 < (levelValue level).toInt)
    omega
  have run : C.run (deflateInit2_ (some r) level 8 15 (Int32.ofInt memory) 0 version 112) h =
      .ok (Z_OK, after) := by
    rw [C.run, entry_run stream versionValue level memory memoryLow memoryHigh, ite_eq_right valid]
    exact allocationRun
  obtain ⟨other, otherRun, initial⟩ := success_initial memory fresh unique globals stream callbacks allok
    (levelValue level) levelLow levelHigh memoryLow memoryHigh
  have heaps : other = after := (Prod.mk.inj (Except.ok.inj (otherRun.symm.trans allocationRun))).2
  rw [heaps] at initial
  have engine : MemoryInitStart memory after r h.nextBlk zf sf := by
    simpa only [hp, ZStreamRef.put_nextBlk] using initialized_memory_engine memory good memoryLow memoryHigh
  have reachable : StreamReachable .deflate after r :=
    StreamReachable.deflateInit fresh unique globals stream callbacks versionValue run
  refine ⟨after, zf, sf, run, engine, frequencies, rfl, initial, reachable, ?_⟩
  simp only [after, successHeap, setD_nalloc, setW, readyHeap, successfulBuffers,
    publishedHeap, stateHeap, ZStreamRef.put_nalloc, hp, Nat.add_assoc]


end Zlib.Deflate.Proofs.MemoryInit

#print axioms Zlib.Deflate.Proofs.MemoryInit.reset_construct_frequencies

#print axioms Zlib.Deflate.Proofs.MemoryInit.allocate_success_frequencies

#print axioms Zlib.Deflate.Proofs.MemoryInit.public_success_engine_frequencies
