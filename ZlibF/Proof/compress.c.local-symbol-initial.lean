import ZlibF.Proof.«compress.c.local-literal»

/-! # Actual local initialization establishes the symbol ledger

The real reset tree writes produce exact initial leaf frequencies. This
strengthens the local execution result; it does not assume a callee contract
or exclude old caller cross-table collisions.
-/
namespace ZlibF.Spec.Public.Proofs.CompressLocalSymbols
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open Zlib.Deflate.Engine.Proofs Zlib.Deflate.Engine.Proofs.SymbolInit
open Zlib.Deflate.Proofs.DefaultInit ZlibF.Spec.Public
open ZlibF.Spec.Public.Proofs.DeflateInit
open ZlibF.Spec.Public.Proofs.CompressLocal ZlibF.Spec.Public.Proofs.CompressLocalInit
open ZlibF.Spec.Public.Proofs.CompressLocalLiteral
open Zlib.Trees.Proofs.Out (TreesBase TreesStatic InitialFrequencies ibRec trInitRec)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false
set_option maxRecDepth 100000

theorem local_reset_frequencies {h : Heap} {r : ZStreamRef} {z : ZStream} {cutoff ds w p q b : Nat}
    (level : Int32) (hl : DLive h r ds z (readyState r level w p q b))
    (ht : TreesBase h ds (readyState r level w p q b) b
      ((h.bytes b).getD #[]))
    (hb : DBlocks h { readyState r level w p q b with
      pending_out := (readyState r level w p q b).pending_buf } w p q b)
    (hu : UniqueFrom h cutoff) (hf : Fresh h) (hl0 : 0 ≤ level.toInt) (hl9 : level.toInt ≤ 9) :
    ∃ (a1 a2 a3 : Array CtData) (qa : Array UInt16),
      a1.size = 573 ∧ a2.size = 61 ∧ a3.size = 39 ∧ InitialFrequencies a1 a2 ∧ h.words q = some qa ∧
      let dr := resetState ds r level w p q b a1 a2 a3
      let hr := setD (r.put h (rkZ z (readyState r level w p q b))) ds dr
      let after := setD (setW hr q (clearHead qa 32768)) ds (lmD dr)
      deflateReset (some r) h = .ok (Z_OK, after) ∧
      LocalState after cutoff r ds (rkZ z (readyState r level w p q b)) (lmD dr) ∧
      (∀ x, after.live x ↔ h.live x) := by
  obtain ⟨a1, a2, a3, hreset, s1, s2, s3, frequencies⟩ := resetKeep_frequencies hl ht
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

theorem local_allocate_frequencies {h : Heap} {r : ZStreamRef} {z : ZStream} {cutoff : Nat}
    (hf : Fresh h) (hu : UniqueFrom h cutoff) (hz : r.get h = some z) (hd : DefAlloc z)
    (hs : TreesStatic h.static) (ha : ∀ j, j < 5 → h.allocOk (h.nalloc + j) = true)
    (level : Int32) (hl0 : 0 ≤ level.toInt) (hl9 : level.toInt ≤ 9) :
    ∃ (a1 a2 a3 : Array CtData) (qa : Array UInt16),
      InitialFrequencies a1 a2 ∧
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
  obtain ⟨a1, a2, a3, qa, s1, s2, s3, frequencies, hqa, hreset, hG, hLive⟩ :=
    local_reset_frequencies level hlR htR hbR huR hfR hl0 hl9
  refine ⟨a1, a2, a3, qa, frequencies, ?_, ?_, ?_⟩
  · rw [allocate_to_finish hf hz hd.1 ha0, finish_to_reset _ _ _ _ ha4, hreset]
    rfl
  · simpa only [successHeap, resultStream, resultState, finalState,
      ph, publishedHeap, stateHeap, ZStreamRef.put_nextBlk, Nat.add_assoc] using hG
  · intro x
    have hc := ready_live hz level ha4 x
    have hr := hLive x
    simpa only [successHeap, resultStream] using hr.trans hc

/-- A same-run observer of actual default initialization produces the
complete empty symbol representation on arbitrary original Fresh heaps. -/
def InitialDataControls (cutoff : Nat) (d : DeflateState) : Prop :=
  d.sym_next = 0 ∧ d.strstart = 0 ∧ d.block_start = 0 ∧ d.match_available = 0 ∧
  d.match_length = 2 ∧ d.window = .ref (.blk (cutoff+2)) 0 ∧
  d.prev = .ref (.blk (cutoff+3)) 0 ∧ d.head = .ref (.blk (cutoff+4)) 0 ∧
  d.pending_buf = .ref (.blk (cutoff+5)) 0

theorem initialized_symbol_boundary {h after : Heap} {z : ZStream} {d : DeflateState}
    (fresh : Fresh h) (globals : LibraryGlobals h)
    (allocations : ∀ j, j < 5 → h.allocOk (h.nalloc+j) = true)
    (actualInit : C.run (deflateInit_ (some (.tab h.nextBlk)) Z_DEFAULT_COMPRESSION (.ref (.str 57) 0) 112)
      (ZlibF.Spec.Public.Proofs.CompressCaller.localHeap h) = .ok (Z_OK,after))
    (localState : LocalState after h.nextBlk (.tab h.nextBlk) (h.nextBlk+1) z d) :
    SymbolBoundary after (h.nextBlk+1) d [] ∧ InitialFrequencies d.dyn_ltree d.dyn_dtree ∧
      InitialDataControls h.nextBlk d := by
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
  have static : Zlib.Trees.Proofs.Out.TreesStatic prepared.static := by
    simpa [prepared,automatic,ZlibF.Spec.Public.Proofs.CompressCaller.localHeap] using
      ZlibF.Spec.Public.Proofs.DeflateInit.globals_trees globals
  have requests : ∀ j, j < 5 → prepared.allocOk (prepared.nalloc+j) = true := by
    intro j bound
    simpa [prepared,automatic,ZlibF.Spec.Public.Proofs.CompressCaller.localHeap] using allocations j bound
  obtain ⟨a1,a2,a3,qa,frequencies,run,stateA,_⟩ := local_allocate_frequencies freshP uniqueP getP allocator static requests 6 (by decide +kernel) (by decide +kernel)
  let after := successHeap prepared root z 6 a1 a2 a3 qa
  have version : VersionValue automatic (.ref (.str 57) 0) (some 49) :=
    Or.inr ⟨49,rfl,Or.inr ⟨.str 57,0,strBytes ZLIB_VERSION,rfl,rfl,by decide +kernel,by decide +kernel⟩⟩
  have init := entry_run get version Z_DEFAULT_COMPRESSION
  have normalize : levelValue Z_DEFAULT_COMPRESSION = 6 := by decide +kernel
  rw [normalize,show ((6 : Int32) < 0 || (6 : Int32) > 9) = false from by decide +kernel] at init
  change deflateInit_ (some root) Z_DEFAULT_COMPRESSION (.ref (.str 57) 0) 112 automatic = allocate (some root) 6 prepared at init
  have computed : C.run (deflateInit_ (some root) Z_DEFAULT_COMPRESSION (.ref (.str 57) 0) 112) automatic =
      .ok (Z_OK,successHeap prepared root z 6 a1 a2 a3 qa) := init.trans run
  have heaps := (Prod.mk.inj (Except.ok.inj (computed.symm.trans actualInit))).2
  have known := stateA.live.hs
  have next : prepared.nextBlk = h.nextBlk+1 := by
    simp [prepared,automatic,ZlibF.Spec.Public.Proofs.CompressCaller.localHeap]
  rw [heaps,next] at known
  have sameD : resultState prepared root 6 a1 a2 a3 = d := Option.some.inj (known.symm.trans localState.live.hs)
  have frequencyD : InitialFrequencies d.dyn_ltree d.dyn_dtree := by
    rw [←sameD]
    exact frequencies
  have fields : d.sym_next = 0 ∧ d.strstart = 0 ∧ d.block_start = 0 ∧ d.match_available = 0 := by
    rw [←sameD]
    exact ⟨rfl,rfl,rfl,rfl⟩
  obtain ⟨d0,b,buf,trees⟩ := localState.trees
  have actualState : d0 = d := Option.some.inj (trees.base.dstate.symm.trans localState.live.hs)
  subst d0
  have ledger : SymbolLedger buf d [] := empty_symbol_ledger fields.1 frequencyD
  have balance : BlockBalance d [] (deferredCredit d) := by
    simp [BlockBalance,deferredCredit,fields.2.1,fields.2.2.1,fields.2.2.2,represented]
  have controls : InitialDataControls h.nextBlk d := by
    rw [←sameD]
    simp [InitialDataControls,resultState,finalState,lmD,resetState,rkPost,rkPost3,rkMid,
      ibRec,trInitRec,readyState,allocatedState,baseState,next,Nat.add_assoc,initial_match_length]
  exact ⟨⟨b,buf,trees,ledger,balance⟩,frequencyD,controls⟩


end ZlibF.Spec.Public.Proofs.CompressLocalSymbols
