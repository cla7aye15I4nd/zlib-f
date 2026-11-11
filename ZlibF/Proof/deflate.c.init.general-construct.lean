import ZlibF.Proof.«deflate.c.init.general-alloc»
import ZlibF.Proof.«deflate.c.init.memory-construct»
import ZlibF.Math.DeflateMemoryBounds
import ZlibF.Proof.«deflate.c.init.construct»
import ZlibF.Proof.«deflate.c.engine.block-initial»
import ZlibF.Proof.«deflate.c.engine.symbol-initial»

namespace Zlib.Deflate.Proofs.GeneralInit
open C Zlib.Deflate Zlib.Deflate.Spec
open DefaultInit
open Zlib.Trees.Proofs.Out (TreesBase TreesInvAt ibRec trInitRec)
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 40000000
variable (wrap : Int32) (wb mem : Nat)

def allocatedState (r : ZStreamRef) (w p q b : Nat) : DeflateState :=
  { baseState r wrap wb mem with
    window := .ref (.blk w) 0, prev := .ref (.blk p) 0, head := .ref (.blk q) 0,
    high_water := 0, lit_bufsize := UInt32.ofNat (2 ^ (mem + 6)), pending_buf := .ref (.blk b) 0,
    pending_buf_size := (UInt32.ofNat (2 ^ (mem + 6))).toUInt64 * 4 }

def readyState (r : ZStreamRef) (level strategy : Int32) (w p q b : Nat) : DeflateState :=
  { allocatedState wrap wb mem r w p q b with
    sym_buf := .ref (.blk b) (2 ^ (mem + 6)), sym_end := (UInt32.ofNat (2 ^ (mem + 6)) - 1) * 3,
    level, strategy, «method» := 8 }

def resetState (ds : Nat) (r : ZStreamRef) (level strategy : Int32) (w p q b : Nat)
    (a1 a2 a3 : Array CtData) : DeflateState :=
  rkPost ds (rkMid (readyState wrap wb mem r level strategy w p q b)) a1 a2 a3

def finalState (ds : Nat) (r : ZStreamRef) (level strategy : Int32) (w p q b : Nat)
    (a1 a2 a3 : Array CtData) : DeflateState :=
  lmD (resetState wrap wb mem ds r level strategy w p q b a1 a2 a3)

theorem absWrap_nonneg {w : Int32} (h0 : 0 ≤ w.toInt) : absWrap w = w := by
  have : ¬ w < 0 := by rw [Int32.lt_iff_toInt_lt]; simp; omega
  simp [absWrap, this]

/-- All representation fields after the actual reset and match initializer.
Only the arbitrary legal compression level and the actual constructor's
array extents remain symbolic. -/
theorem final_inv {h : Heap} (ds : Nat) (r : ZStreamRef) (level strategy : Int32) (w p q b : Nat)
    (a1 a2 a3 : Array CtData) (s1 : a1.size = 573) (s2 : a2.size = 61) (s3 : a3.size = 39)
    (hl0 : 0 ≤ level.toInt) (hl9 : level.toInt ≤ 9) (hs0 : 0 ≤ strategy.toInt) (hs4 : strategy.toInt ≤ 4)
    (hw0 : 0 ≤ wrap.toInt) (hw2 : wrap.toInt ≤ 2)
    (wbLow : 9 ≤ wb) (wbHigh : wb ≤ 15) (memoryLow : 1 ≤ mem) (memoryHigh : mem ≤ 9)
    (hb : DBlocks h (finalState wrap wb mem ds r level strategy w p q b a1 a2 a3) w p q b) :
    DStInv h ds (finalState wrap wb mem ds r level strategy w p q b a1 a2 a3) := by
  have hw := absWrap_nonneg hw0
  have wcases : wb = 9 ∨ wb = 10 ∨ wb = 11 ∨ wb = 12 ∨ wb = 13 ∨ wb = 14 ∨ wb = 15 := by omega
  rcases ZlibF.Math.DeflateMemLevel.memory_cases memoryLow memoryHigh with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  rcases wcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals constructor
  all_goals first
    | exact ⟨w, p, q, b, hb⟩
    | simpa [finalState, resetState, lmD, rkPost, rkPost3, rkMid, ibRec, trInitRec,
        readyState, allocatedState, baseState] using hl0
    | simpa [finalState, resetState, lmD, rkPost, rkPost3, rkMid, ibRec, trInitRec,
        readyState, allocatedState, baseState] using hl9
    | simpa [finalState, resetState, lmD, rkPost, rkPost3, rkMid, ibRec, trInitRec,
        readyState, allocatedState, baseState] using hs0
    | simpa [finalState, resetState, lmD, rkPost, rkPost3, rkMid, ibRec, trInitRec,
        readyState, allocatedState, baseState] using hs4
    | (simp [finalState, resetState, lmD, rkPost, rkPost3, rkMid, hw, ibRec, trInitRec,
        readyState, allocatedState, baseState]; omega)
    | simp [finalState, resetState, lmD, rkPost, rkPost3, rkMid, hw, ibRec, trInitRec,
        readyState, allocatedState, baseState, DeflateState.WellFormed, DeflateState.zeroed,
        DeflateState.garbage, s1, s2, s3, GzOk]

/-- `deflateResetKeep` with the facts of `init_block` that the universal invariant needs: the
bit-length frequencies are zero and the literal and distance frequencies are the initial ones. -/
theorem resetKeep_initial {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState} {b : Nat}
    {buf : Array UInt8} (hL : DLive h r ds z d) (hB : TreesBase h ds d b buf)
    (hw1 : -2 ≤ d.wrap.toInt) (hw2 : d.wrap.toInt ≤ 2) :
    ∃ a1 a2 a3, deflateResetKeep (some r) h =
      .ok (Z_OK, setD (r.put h (rkZ z d)) ds (rkPost ds (rkMid d) a1 a2 a3)) ∧
      a1.size = 573 ∧ a2.size = 61 ∧ a3.size = 39 ∧ (∀ k, k < 19 → a3[k]!.fc = 0) ∧
      Zlib.Trees.Proofs.Out.InitialFrequencies a1 a2 := by
  obtain ⟨a1, a2, a3, e1, s1, s2, s3, bl⟩ := Zlib.Deflate.Engine.Proofs.BlockInit.resetKeep_bl_zero hL hB hw1 hw2
  obtain ⟨b1, b2, b3, e2, -, -, -, freq⟩ := Zlib.Deflate.Engine.Proofs.SymbolInit.resetKeep_frequencies hL hB hw1 hw2
  have same := e1.symm.trans e2
  simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at same
  have states := congrArg (fun g : Heap => g.dstates ds) same
  simp only [setD_dstates_same, Option.some.injEq] at states
  have l1 : a1 = b1 := by
    have := congrArg DeflateState.dyn_ltree states
    simpa [rkPost, rkPost3, Zlib.Trees.Proofs.Out.ibRec] using this
  have l2 : a2 = b2 := by
    have := congrArg DeflateState.dyn_dtree states
    simpa [rkPost, rkPost3, Zlib.Trees.Proofs.Out.ibRec] using this
  subst l1; subst l2
  exact ⟨a1, a2, a3, e1, s1, s2, s3, bl, freq⟩

/-- The actual reset establishes DGood from the construction storage.
Neither DGood nor any reset execution contract is a premise. The caller
has not yet written pending_out or window_size; the reset writes both. -/
theorem reset_construct {h : Heap} {r : ZStreamRef} {z : ZStream} {ds w p q b : Nat}
    (level strategy : Int32) (hl : DLive h r ds z (readyState wrap wb mem r level strategy w p q b))
    (ht : TreesBase h ds (readyState wrap wb mem r level strategy w p q b) b
      ((h.bytes b).getD #[]))
    (hb : DBlocks h { readyState wrap wb mem r level strategy w p q b with
      pending_out := (readyState wrap wb mem r level strategy w p q b).pending_buf } w p q b)
    (hu : Uniq h) (hf : Fresh h) (hl0 : 0 ≤ level.toInt) (hl9 : level.toInt ≤ 9)
    (hs0 : 0 ≤ strategy.toInt) (hs4 : strategy.toInt ≤ 4) (hw0 : 0 ≤ wrap.toInt) (hw2 : wrap.toInt ≤ 2)
    (wbLow : 9 ≤ wb) (wbHigh : wb ≤ 15) (memoryLow : 1 ≤ mem) (memoryHigh : mem ≤ 9) :
    ∃ (a1 a2 a3 : Array CtData) (qa : Array UInt16),
      a1.size = 573 ∧ a2.size = 61 ∧ a3.size = 39 ∧ (∀ k, k < 19 → a3[k]!.fc = 0) ∧
      Zlib.Trees.Proofs.Out.InitialFrequencies a1 a2 ∧ h.words q = some qa ∧
      let dr := resetState wrap wb mem ds r level strategy w p q b a1 a2 a3
      let hr := setD (r.put h (rkZ z (readyState wrap wb mem r level strategy w p q b))) ds dr
      let after := setD (setW hr q (clearHead qa (UInt32.ofNat (2 ^ (mem + 7))).toNat)) ds (lmD dr)
      deflateReset (some r) h = .ok (Z_OK, after) ∧
      DGood after r ds (rkZ z (readyState wrap wb mem r level strategy w p q b)) (lmD dr) ∧
      (∀ x, after.live x ↔ h.live x) := by
  obtain ⟨a1, a2, a3, hreset, s1, s2, s3, bl, freq⟩ := resetKeep_initial hl ht
    (by simp [readyState, allocatedState, baseState]; omega)
    (by simp [readyState, allocatedState, baseState]; omega)
  let dr := resetState wrap wb mem ds r level strategy w p q b a1 a2 a3
  let zr := rkZ z (readyState wrap wb mem r level strategy w p q b)
  let hr := setD (r.put h zr) ds dr
  have hsR : hr.dstates ds = some dr := by simp [hr]
  have hzR : r.get hr = some zr := by simp [hr, ZStreamRef.get_put_same hl.hz]
  have hbR : DBlocks hr dr w p q b := DBlocks.congr (by simp [hr]) (by simp [hr])
    (by simp [hr]) (blocks_reset hb a1 a2 a3)
  obtain ⟨qa, hqa, sizeQ⟩ := hbR.qa
  have qsize : qa.size = (UInt32.ofNat (2 ^ (mem + 7))).toNat := by simpa [dr, resetState, rkPost, rkPost3, rkMid,
    ibRec, trInitRec, readyState, allocatedState, baseState] using sizeQ
  have level0 : 0 ≤ dr.level.toInt := by simpa [dr, resetState, rkPost, rkPost3, rkMid,
    ibRec, trInitRec, readyState] using hl0
  have level9 : dr.level.toInt ≤ 9 := by simpa [dr, resetState, rkPost, rkPost3, rkMid,
    ibRec, trInitRec, readyState] using hl9
  have hash : dr.hash_size.toNat = (UInt32.ofNat (2 ^ (mem + 7))).toNat := by
    simp [dr, resetState, rkPost, rkPost3, rkMid, ibRec, trInitRec, readyState, allocatedState, baseState]
  have hashCount : (UInt32.ofNat (2 ^ (mem + 7))).toNat = 2 ^ (mem + 7) := by
    rcases ZlibF.Math.DeflateMemLevel.memory_cases memoryLow memoryHigh with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have hashPositive : 1 ≤ (UInt32.ofNat (2 ^ (mem + 7))).toNat := by
    rw [hashCount]
    exact Nat.two_pow_pos _
  have hlm := lm_init_run hsR hbR hqa level0 level9 (by rw [hash]; exact hashPositive) (by omega)
  rw [hash] at hlm
  let after := setD (setW hr q (clearHead qa (UInt32.ofNat (2 ^ (mem + 7))).toNat)) ds (lmD dr)
  have hbW := hbR.words_set q (clearHead qa (UInt32.ofNat (2 ^ (mem + 7))).toNat) qa hqa (size_clearHead _ _)
  have hbF : DBlocks after (lmD dr) w p q b :=
    blocks_lm (DBlocks.congr (by simp [after, setW]) (by simp [after, setW])
      (by simp [after, setW]) hbW)
  have hI : DStInv after ds (lmD dr) := final_inv wrap wb mem ds r level strategy w p q b a1 a2 a3
    s1 s2 s3 hl0 hl9 hs0 hs4 hw0 hw2 wbLow wbHigh memoryLow memoryHigh hbF
  have shapeR : Shape h hr := (shape_put hl.hz zr).trans (shape_setD (by simpa using hl.hs) dr)
  have shapeF : Shape hr after := (shape_setW hqa _).trans (shape_setD (by simpa using hsR) _)
  have shape := shapeR.trans shapeF
  refine ⟨a1, a2, a3, qa, s1, s2, s3, bl, freq, by simpa [hr] using hqa, ?_, ?_, fun x => shape.live x⟩
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
    · have hw := absWrap_nonneg hw0
      by_cases two : wrap = 2
      · right; left
        subst two
        simp [dr, lmD, resetState, rkPost, rkPost3, rkMid, show absWrap (2 : Int32) = 2 from by decide,
          ibRec, trInitRec, readyState, allocatedState, baseState]
      · left
        simp [dr, lmD, resetState, rkPost, rkPost3, rkMid, hw, two, ibRec, trInitRec,
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

end Zlib.Deflate.Proofs.GeneralInit


#print axioms Zlib.Deflate.Proofs.GeneralInit.final_inv
#print axioms Zlib.Deflate.Proofs.GeneralInit.reset_construct
