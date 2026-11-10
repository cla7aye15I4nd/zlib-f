import ZlibF.Proof.«compress.c.shadow-kinds»

/-! # Actual successful default init without old caller uniqueness

Only the real initialization prefix is considered. The existing typed
construction/reset source lemmas suffice; no engine contract is assumed.
-/
namespace ZlibF.Spec.Public.Proofs.CompressShadow
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open Zlib.Deflate.Proofs.DefaultInit
open ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesBase TreesStatic ibRec trInitRec)
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

theorem ready_objects {h : Heap} {r : ZStreamRef} {z : ZStream} {ds : Nat}
    (level : Int32) (hz : r.get h = some z)
    (hs : h.dstates ds = some (baseState r)) (hds : ds < h.nextBlk)
    (halloc : DefAlloc z) (hzs : z.state = some (.deflate ds))
    (hstatic : TreesStatic h.static)
    (ha : ∀ j, j < 4 → h.allocOk (h.nalloc + j) = true) :
    let d := readyState r level h.nextBlk (h.nextBlk + 1) (h.nextBlk + 2) (h.nextBlk + 3)
    let g := readyHeap h ds r level
    DLive g r ds z d ∧ TreesBase g ds d (h.nextBlk + 3) ((g.bytes (h.nextBlk + 3)).getD #[]) ∧
      DBlocks g { d with pending_out := d.pending_buf }
        h.nextBlk (h.nextBlk + 1) (h.nextBlk + 2) (h.nextBlk + 3) := by
  let d := readyState r level h.nextBlk (h.nextBlk + 1) (h.nextBlk + 2) (h.nextBlk + 3)
  let g := readyHeap h ds r level
  have slots := (buffers_success h ha).1
  have hgZ : r.get g = some z := by
    change r.get (setD (successfulBuffers h) ds d) = some z
    rw [ZStreamRef.get_setD, ← slots, get_buffersHeap]
    exact hz
  have wf : d.WellFormed := by
    simp [d, readyState, allocatedState, baseState, DeflateState.WellFormed,
      DeflateState.zeroed, DeflateState.garbage]
  have hb : DBlocks g { d with pending_out := d.pending_buf }
      h.nextBlk (h.nextBlk + 1) (h.nextBlk + 2) (h.nextBlk + 3) := by
    refine ⟨rfl, rfl, rfl, rfl,
      ⟨byteGarbage h 0, ?_, ?_⟩, ?_, ⟨wordGarbage h 1, ?_, ?_⟩,
      ⟨wordGarbage h 2, ?_, ?_⟩, ⟨byteGarbage h 3, ?_, ?_⟩,
      ?_, ?_, by omega, by omega, 0, rfl, ?_⟩
    all_goals simp [g, readyHeap, successfulBuffers, d, readyState, allocatedState, baseState,
      byteGarbage, wordGarbage, DeflateState.zeroed, DeflateState.garbage, Junk.of]
  refine ⟨⟨hgZ, by simp [g, readyHeap], hzs, rfl, Or.inl rfl,
    by rw [halloc.1]; decide, by rw [halloc.2]; decide⟩,
    ?_, hb⟩
  refine ⟨by simp [g, readyHeap], wf, ?_, rfl, ?_, hb.bro, ?_, ?_, rfl,
    by change 128 ≤ (16384 : UInt32).toNat; decide +kernel,
    by change (16384 : UInt32).toNat ≤ 32768; decide +kernel,
    by change (49149 : UInt32).toNat = 3 * ((16384 : UInt32).toNat - 1); decide +kernel, ?_⟩
  · simpa [g, readyHeap, successfulBuffers] using hstatic
  · simp [g, readyHeap, successfulBuffers]
  · simp [g, readyHeap, successfulBuffers, d, readyState, allocatedState,
      byteGarbage]
  · simp [g, readyHeap, successfulBuffers, d, readyState, allocatedState, byteGarbage]
  · simp [d, readyState, allocatedState, baseState, DeflateState.zeroed, DeflateState.garbage, Junk.of]


theorem reset_run {h : Heap} {r : ZStreamRef} {z : ZStream} {ds w p q b : Nat}
    (level : Int32) (hl : DLive h r ds z (readyState r level w p q b))
    (ht : TreesBase h ds (readyState r level w p q b) b
      ((h.bytes b).getD #[]))
    (hb : DBlocks h { readyState r level w p q b with
      pending_out := (readyState r level w p q b).pending_buf } w p q b)
    (hl0 : 0 ≤ level.toInt) (hl9 : level.toInt ≤ 9) :
    ∃ (a1 a2 a3 : Array CtData) (qa : Array UInt16),
      a1.size = 573 ∧ a2.size = 61 ∧ a3.size = 39 ∧ h.words q = some qa ∧
      let dr := resetState ds r level w p q b a1 a2 a3
      let hr := setD (r.put h (rkZ z (readyState r level w p q b))) ds dr
      let after := setD (setW hr q (clearHead qa 32768)) ds (lmD dr)
      deflateReset (some r) h = .ok (Z_OK, after) := by
  obtain ⟨a1, a2, a3, hreset, s1, s2, s3⟩ := resetKeep_run' hl ht
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
  refine ⟨a1,a2,a3,qa,s1,s2,s3,by simpa [hr] using hqa,?_⟩
  unfold deflateReset
  rw [bind_app, hreset]
  simp only [bind_app, beq_self_eq_true, ite_true]
  change (do lm_init (← castDeflateState (← zrd (some r) (·.state))); pure Z_OK) hr = _
  simp only [bind_app, zrd_eq, hzR, zr, rkZ, hl.zst, castD]
  rw [hlm]
  simp only [pure_app]
  simp [after, hr, zr, rkZ, hl.zst, dr]


end ZlibF.Spec.Public.Proofs.CompressShadow
