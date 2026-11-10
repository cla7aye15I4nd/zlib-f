import ZlibF.Proof.«deflate.c.gzip-init-allocation»
import ZlibF.Proof.«deflate.c.init.construct»

namespace Zlib.Deflate.Proofs.DefaultGzipInit
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open Zlib.Deflate.Proofs.DefaultInit (blocks_lm blocks_reset get_setW)
open Zlib.Trees.Proofs.Out (TreesBase TreesInvAt ibRec trInitRec)
set_option autoImplicit false

def allocatedState (r : ZStreamRef) (w p q b : Nat) : DeflateState :=
  { baseState r with
    window := .ref (.blk w) 0, prev := .ref (.blk p) 0, head := .ref (.blk q) 0,
    high_water := 0, lit_bufsize := 16384, pending_buf := .ref (.blk b) 0,
    pending_buf_size := 65536 }

def readyState (r : ZStreamRef) (level : Int32) (w p q b : Nat) : DeflateState :=
  { allocatedState r w p q b with
    sym_buf := .ref (.blk b) 16384, sym_end := 49149,
    level, strategy := 0, «method» := 8 }

def resetState (ds : Nat) (r : ZStreamRef) (level : Int32) (w p q b : Nat)
    (a1 a2 a3 : Array CtData) : DeflateState :=
  rkPost ds (rkMid (readyState r level w p q b)) a1 a2 a3

def finalState (ds : Nat) (r : ZStreamRef) (level : Int32) (w p q b : Nat)
    (a1 a2 a3 : Array CtData) : DeflateState :=
  lmD (resetState ds r level w p q b a1 a2 a3)

/-- All representation fields after the actual reset and match initializer.
Only the arbitrary legal compression level and the actual constructor's
array extents remain symbolic. -/
theorem final_inv {h : Heap} (ds : Nat) (r : ZStreamRef) (level : Int32) (w p q b : Nat)
    (a1 a2 a3 : Array CtData) (s1 : a1.size = 573) (s2 : a2.size = 61) (s3 : a3.size = 39)
    (hl0 : 0 ≤ level.toInt) (hl9 : level.toInt ≤ 9)
    (hb : DBlocks h (finalState ds r level w p q b a1 a2 a3) w p q b) :
    DStInv h ds (finalState ds r level w p q b a1 a2 a3) := by
  constructor
  all_goals first
    | exact ⟨w, p, q, b, hb⟩
    | simpa [finalState, resetState, lmD, rkPost, rkPost3, rkMid, ibRec, trInitRec,
        readyState, allocatedState, baseState] using hl0
    | simpa [finalState, resetState, lmD, rkPost, rkPost3, rkMid, ibRec, trInitRec,
        readyState, allocatedState, baseState] using hl9
    | simp [finalState, resetState, lmD, rkPost, rkPost3, rkMid, absWrap, ibRec, trInitRec,
        readyState, allocatedState, baseState, DeflateState.WellFormed, DeflateState.zeroed,
        DeflateState.garbage, s1, s2, s3, GzOk]

/-- The actual reset establishes DGood from the construction storage.
Neither DGood nor any reset execution contract is a premise. The caller
has not yet written pending_out or window_size; the reset writes both. -/
theorem reset_construct {h : Heap} {r : ZStreamRef} {z : ZStream} {ds w p q b : Nat}
    (level : Int32) (hl : DLive h r ds z (readyState r level w p q b))
    (ht : TreesBase h ds (readyState r level w p q b) b
      ((h.bytes b).getD #[]))
    (hb : DBlocks h { readyState r level w p q b with
      pending_out := (readyState r level w p q b).pending_buf } w p q b)
    (hu : Uniq h) (hf : Fresh h) (hl0 : 0 ≤ level.toInt) (hl9 : level.toInt ≤ 9) :
    ∃ (a1 a2 a3 : Array CtData) (qa : Array UInt16),
      a1.size = 573 ∧ a2.size = 61 ∧ a3.size = 39 ∧ h.words q = some qa ∧
      let dr := resetState ds r level w p q b a1 a2 a3
      let hr := setD (r.put h (rkZ z (readyState r level w p q b))) ds dr
      let after := setD (setW hr q (clearHead qa 32768)) ds (lmD dr)
      deflateReset (some r) h = .ok (Z_OK, after) ∧
      DGood after r ds (rkZ z (readyState r level w p q b)) (lmD dr) ∧
      (∀ x, after.live x ↔ h.live x) := by
  obtain ⟨a1, a2, a3, hreset, s1, s2, s3⟩ := resetKeep_run' hl ht
    (by change (-2 : Int) ≤ (2 : Int32).toInt; decide +kernel)
    (by change (2 : Int32).toInt ≤ (2 : Int); decide +kernel)
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
  refine ⟨a1, a2, a3, qa, s1, s2, s3, by simpa [hr] using hqa, ?_, ?_, fun x => shape.live x⟩
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
    · right; left
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

end Zlib.Deflate.Proofs.DefaultGzipInit
