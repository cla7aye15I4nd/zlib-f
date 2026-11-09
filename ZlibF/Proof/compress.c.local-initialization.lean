import ZlibF.Proof.«compress.c.local-uniqueness»

/-! # Actual default initialization with local private representation

The internal local state is produced by the actual initialization writes.
It has no global Uniq field and does not change DGood, Rebuffer or the
public utility goal. Ordinary engine reuse remains a separate dependency.
-/
namespace ZlibF.Spec.Public.Proofs.CompressLocalInit
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open Zlib.Deflate.Proofs.DefaultInit ZlibF.Spec.Public
open ZlibF.Spec.Public.Proofs.CompressLocal
open ZlibF.Spec.Public.Proofs.DeflateInit (resultState)
open Zlib.Trees.Proofs.Out (TreesBase TreesStatic TreesInv ibRec trInitRec)
set_option autoImplicit false
set_option maxRecDepth 100000

/-- Internal representation on the same actual heap; only newly allocated
identities are constrained by type uniqueness. This is not a caller premise. -/
structure LocalState (h : Heap) (cutoff : Nat) (r : ZStreamRef) (ds : Nat) (z : ZStream) (d : DeflateState) : Prop where
  live : DLive h r ds z d
  inv : DStInv h ds d
  newUnique : UniqueFrom h cutoff
  fresh : Fresh h
  trees : TreesInv h ds

theorem ready_storage_local {h : Heap} {r : ZStreamRef} {z : ZStream} {ds cutoff : Nat}
    (level : Int32) (hf : Fresh h) (hu : UniqueFrom h cutoff) (hz : r.get h = some z)
    (hs : h.dstates ds = some (baseState r)) (hds : ds < h.nextBlk)
    (halloc : DefAlloc z) (hzs : z.state = some (.deflate ds))
    (hstatic : TreesStatic h.static)
    (ha : ∀ j, j < 4 → h.allocOk (h.nalloc + j) = true) :
    let d := readyState r level h.nextBlk (h.nextBlk + 1) (h.nextBlk + 2) (h.nextBlk + 3)
    let g := readyHeap h ds r level
    DLive g r ds z d ∧ TreesBase g ds d (h.nextBlk + 3) ((g.bytes (h.nextBlk + 3)).getD #[]) ∧
      DBlocks g { d with pending_out := d.pending_buf }
        h.nextBlk (h.nextBlk + 1) (h.nextBlk + 2) (h.nextBlk + 3) ∧ UniqueFrom g cutoff ∧ Fresh g := by
  let d := readyState r level h.nextBlk (h.nextBlk + 1) (h.nextBlk + 2) (h.nextBlk + 3)
  let g := readyHeap h ds r level
  have slots := (buffers_success h ha).1
  have hsf : (successfulBuffers h).dstates ds = some (baseState r) := by simpa [successfulBuffers] using hs
  have hsh := shape_setD hsf d
  have huB : UniqueFrom (successfulBuffers h) cutoff := by rw [← slots]; exact hu.buffers hf
  have hfB : Fresh (successfulBuffers h) := by rw [← slots]; exact buffers_fresh hf
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
    ?_, hb, huB.shape hsh, hsh.fresh (by rfl) hfB⟩
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

theorem reset_construct_local {h : Heap} {r : ZStreamRef} {z : ZStream} {ds w p q b cutoff : Nat}
    (level : Int32) (hl : DLive h r ds z (readyState r level w p q b))
    (ht : TreesBase h ds (readyState r level w p q b) b
      ((h.bytes b).getD #[]))
    (hb : DBlocks h { readyState r level w p q b with
      pending_out := (readyState r level w p q b).pending_buf } w p q b)
    (hu : UniqueFrom h cutoff) (hf : Fresh h) (hl0 : 0 ≤ level.toInt) (hl9 : level.toInt ≤ 9) :
    ∃ (a1 a2 a3 : Array CtData) (qa : Array UInt16),
      a1.size = 573 ∧ a2.size = 61 ∧ a3.size = 39 ∧ h.words q = some qa ∧
      let dr := resetState ds r level w p q b a1 a2 a3
      let hr := setD (r.put h (rkZ z (readyState r level w p q b))) ds dr
      let after := setD (setW hr q (clearHead qa 32768)) ds (lmD dr)
      deflateReset (some r) h = .ok (Z_OK, after) ∧
      LocalState after cutoff r ds (rkZ z (readyState r level w p q b)) (lmD dr) ∧
      (∀ x, after.live x ↔ h.live x) := by
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
      hu.shape shape, shape.fresh (by simp [after, hr, setW]) hf, ?_⟩
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

theorem allocate_success_local {h : Heap} {r : ZStreamRef} {z : ZStream} {cutoff : Nat}
    (hf : Fresh h) (hu : UniqueFrom h cutoff) (hz : r.get h = some z) (hd : DefAlloc z)
    (hs : TreesStatic h.static) (ha : ∀ j, j < 5 → h.allocOk (h.nalloc + j) = true)
    (level : Int32) (hl0 : 0 ≤ level.toInt) (hl9 : level.toInt ≤ 9) :
    ∃ (a1 a2 a3 : Array CtData) (qa : Array UInt16),
      allocate (some r) level h = .ok (Z_OK, successHeap h r z level a1 a2 a3 qa) ∧
      LocalState (successHeap h r z level a1 a2 a3 qa) cutoff r h.nextBlk (resultStream h r z level)
        (resultState h r level a1 a2 a3) ∧
      (∀ x, (successHeap h r z level a1 a2 a3 qa).live x ↔
        h.live x ∨ h.nextBlk ≤ x ∧ x < h.nextBlk + 5) := by
  let ph := publishedHeap h r z
  have ha0 : h.allocOk h.nalloc = true := by simpa using ha 0 (by decide)
  have ha4 : ∀ j, j < 4 → ph.allocOk (ph.nalloc + j) = true := by
    intro j hj
    simpa [ph, publishedHeap, stateHeap, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ha (j + 1) (by omega)
  have hfp := (shape_put hz (stateStream z h.nextBlk)).fresh (by simp) hf
  have hup := hu.shape (shape_put hz (stateStream z h.nextBlk))
  have hfP : Fresh ph := fresh_stateHeap hfp _
  have huP : UniqueFrom ph cutoff := hup.state hfp _
  have hzP : r.get ph = some (stateStream z h.nextBlk) := by
    simp [ph, publishedHeap, ZStreamRef.get_put_same hz]
  have hdP : DefAlloc (stateStream z h.nextBlk) := hd
  have hsP : ph.dstates h.nextBlk = some (baseState r) := by simp [ph, publishedHeap, stateHeap]
  have hst : TreesStatic ph.static := by simpa [ph, publishedHeap, stateHeap] using hs
  obtain ⟨hlR, htR, hbR, huR, hfR⟩ := ready_storage_local level hfP huP hzP hsP
    (by simp [ph, publishedHeap, stateHeap]) hdP rfl hst ha4
  obtain ⟨a1, a2, a3, qa, s1, s2, s3, hqa, hreset, hG, hLive⟩ :=
    reset_construct_local level hlR htR hbR huR hfR hl0 hl9
  refine ⟨a1, a2, a3, qa, ?_, ?_, ?_⟩
  · rw [allocate_to_finish hf hz hd.1 ha0, finish_to_reset _ _ _ _ ha4, hreset]
    rfl
  · simpa only [successHeap, resultStream, resultState, finalState,
      ph, publishedHeap, stateHeap, ZStreamRef.put_nextBlk, Nat.add_assoc] using hG
  · intro x
    have hc := ready_live hz level ha4 x
    have hr := hLive x
    simpa only [successHeap, resultStream] using hr.trans hc


/-- A Fresh original heap and actual successful allocator choices produce
the complete default local invariant through the real automatic stream,
real initializer, reset and hash initialization. Global Uniq is neither
assumed nor concluded. This is the successful-initialization branch; the
ordinary data-loop extension is not claimed here. -/
theorem fresh_utility_initialization {h : Heap} (fresh : Fresh h) (globals : LibraryGlobals h)
    (allocations : ∀ j, j < 5 → h.allocOk (h.nalloc+j) = true) :
    ∃ after z d,
      C.run (deflateInit_ (some (.tab h.nextBlk)) Z_DEFAULT_COMPRESSION (.ref (.str 57) 0) 112)
        (ZlibF.Spec.Public.Proofs.CompressCaller.localHeap h) = .ok (Z_OK,after) ∧
      LocalState after h.nextBlk (.tab h.nextBlk) (h.nextBlk+1) z d ∧
      Frame h after (fun _ => False) ∧
      (∀ x, after.live x ↔ h.live x ∨ h.nextBlk ≤ x ∧ x < h.nextBlk+6) := by
  let root := ZStreamRef.tab h.nextBlk
  let automatic := ZlibF.Spec.Public.Proofs.CompressCaller.localHeap h
  let old := ZlibF.Spec.Public.Proofs.CompressCaller.localStream h
  let z := ZlibF.Spec.Public.preparedStream old
  let prepared := root.put automatic z
  have get : root.get automatic = some old := by
    simp [root,automatic,ZlibF.Spec.Public.Proofs.CompressCaller.localHeap,ZStreamRef.get,old]
  obtain ⟨freshA,uniqueA⟩ := automatic_stream_local fresh
  have controls := shape_put get z
  have freshP : Fresh prepared := controls.fresh (by simp) freshA
  have uniqueP : UniqueFrom prepared h.nextBlk := uniqueA.shape controls
  have getP : root.get prepared = some z := ZStreamRef.get_put_same get _
  have allocator : DefAlloc z := by
    simp [DefAlloc,z,ZlibF.Spec.Public.preparedStream,old,ZlibF.Spec.Public.Proofs.CompressCaller.localStream]
  have static : TreesStatic prepared.static := by
    simpa [prepared,automatic,ZlibF.Spec.Public.Proofs.CompressCaller.localHeap] using
      ZlibF.Spec.Public.Proofs.DeflateInit.globals_trees globals
  have requests : ∀ j, j < 5 → prepared.allocOk (prepared.nalloc+j) = true := by
    intro j bound
    simpa [prepared,automatic,ZlibF.Spec.Public.Proofs.CompressCaller.localHeap] using allocations j bound
  obtain ⟨a1,a2,a3,qa,run,state,live⟩ := allocate_success_local freshP uniqueP getP allocator static requests 6 (by decide) (by decide)
  let after := successHeap prepared root z 6 a1 a2 a3 qa
  have version : VersionValue automatic (.ref (.str 57) 0) (some 49) :=
    Or.inr ⟨49,rfl,Or.inr ⟨.str 57,0,strBytes ZLIB_VERSION,rfl,rfl,by decide +kernel,by decide +kernel⟩⟩
  have init := entry_run get version Z_DEFAULT_COMPRESSION
  have normalize : levelValue Z_DEFAULT_COMPRESSION = 6 := by decide +kernel
  rw [normalize,show ((6 : Int32) < 0 || (6 : Int32) > 9) = false from by decide +kernel] at init
  change deflateInit_ (some root) Z_DEFAULT_COMPRESSION (.ref (.str 57) 0) 112 automatic = allocate (some root) 6 prepared at init
  have next : prepared.nextBlk = h.nextBlk+1 := by simp [prepared,automatic,ZlibF.Spec.Public.Proofs.CompressCaller.localHeap]
  have originalFrame : Frame h prepared (fun _ => False) := by
    simp only [prepared,root,automatic,ZlibF.Spec.Public.Proofs.CompressCaller.localHeap,ZStreamRef.put,upd_same]
    refine ⟨rfl,rfl,rfl,by change h.nextBlk ≤ h.nextBlk+1;omega,Nat.le_refl _,?_⟩
    intro x live _outside
    have different : x ≠ h.nextBlk := by have low := fresh.lt live;omega
    simp [SlotSame,upd_ne _ _ _ _ different]
  have finalFrame := success_frame (h := prepared) root z 6 a1 a2 a3 qa freshP
  have allFrame : Frame h after (fun _ => False) := by
    refine ⟨originalFrame.1.trans finalFrame.1,originalFrame.2.1.trans finalFrame.2.1,
      originalFrame.2.2.1.trans finalFrame.2.2.1,Nat.le_trans originalFrame.2.2.2.1 finalFrame.2.2.2.1,
      Nat.le_trans originalFrame.2.2.2.2.1 finalFrame.2.2.2.2.1,?_⟩
    intro x oldLive _outside
    have first : SlotSame h prepared x := originalFrame.2.2.2.2.2 x oldLive (by simp)
    apply first.trans
    apply finalFrame.2.2.2.2.2 x (first.live.mpr oldLive)
    change x ≠ h.nextBlk
    have low := fresh.lt oldLive
    omega
  refine ⟨after,resultStream prepared root z 6,resultState prepared root 6 a1 a2 a3,init.trans run,?_,allFrame,?_⟩
  · simpa only [next] using state
  · intro x
    have automaticLive : automatic.live x ↔ h.live x ∨ x = h.nextBlk := by
      by_cases same : x = h.nextBlk
      · subst x;simp [automatic,ZlibF.Spec.Public.Proofs.CompressCaller.localHeap,Heap.live]
      · simp [automatic,ZlibF.Spec.Public.Proofs.CompressCaller.localHeap,Heap.live,upd_ne _ _ _ _ same,same]
    have current := live x
    rw [controls.live x,automaticLive,next] at current
    change after.live x ↔ _ at current
    have union : ((h.live x ∨ x = h.nextBlk) ∨ h.nextBlk+1 ≤ x ∧ x < h.nextBlk+1+5) ↔
        (h.live x ∨ h.nextBlk ≤ x ∧ x < h.nextBlk+6) := by
      by_cases oldLive : h.live x <;>simp only [oldLive,true_or,false_or] <;>omega
    exact current.trans union


private def collidingCaller : Heap :=
  let base := ZlibF.Spec.Public.Proofs.DeflateInit.witnessHeap
  {base with bytes := upd base.bytes 0 (some #[1]),words := upd base.words 0 (some #[2])}

/-- Non-vacuity on a concrete Fresh caller with old typed collisions.
The real complete default initializer still establishes its local state;
this does not assert that such a heap can satisfy the old global DGood. -/
theorem fresh_nonunique_initialization_witness :
    ∃ h after z d, Fresh h ∧ ¬Uniq h ∧
      C.run (deflateInit_ (some (.tab h.nextBlk)) Z_DEFAULT_COMPRESSION (.ref (.str 57) 0) 112)
        (ZlibF.Spec.Public.Proofs.CompressCaller.localHeap h) = .ok (Z_OK,after) ∧
      LocalState after h.nextBlk (.tab h.nextBlk) (h.nextBlk+1) z d ∧ ¬Uniq after := by
  have fresh : Fresh collidingCaller := by
    intro b bound live
    have different : b ≠ 0 := by change 2 ≤ b at bound;omega
    apply ZlibF.Spec.Public.Proofs.DeflateInit.witness_fresh b bound
    simpa only [collidingCaller,Heap.live,upd_ne _ _ _ _ different] using live
  have collision : ¬Uniq collidingCaller := by
    intro unique
    have counts := unique 0
    simp [collidingCaller,ZlibF.Spec.Public.Proofs.DeflateInit.witnessHeap,Heap.empty,cnt] at counts
  have globals : LibraryGlobals collidingCaller := rfl
  obtain ⟨after,z,d,actual,state,frame,_live⟩ := fresh_utility_initialization fresh globals (by intro j _bound;rfl)
  have retainedCollision : ¬Uniq after := by
    intro unique
    have live : collidingCaller.live 0 := by simp [collidingCaller,Heap.live]
    have slots := frame.2.2.2.2.2 0 live (by simp)
    have count := unique 0
    rw [slots.1,slots.2.1] at count
    simp [collidingCaller,cnt] at count
    omega
  exact ⟨collidingCaller,after,z,d,fresh,collision,actual,state,retainedCollision⟩

end ZlibF.Spec.Public.Proofs.CompressLocalInit
