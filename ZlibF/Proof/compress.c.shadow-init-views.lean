import ZlibF.Proof.«compress.c.shadow-init-run»

/-! # Initialized private views at original and shadow identifiers

These are observations of the explicit heaps returned by the actual
initialization producer. No equality of global live-ID predicates or of
unrelated caller pointer graphs is asserted.
-/
namespace ZlibF.Spec.Public.Proofs.CompressShadow
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open Zlib.Deflate.Proofs.DefaultInit Zlib.Deflate.Engine.Proofs
open ZlibF.Spec.Public
open ZlibF.Spec.Public.Proofs.DeflateInit (resultState)
open Zlib.Trees.Proofs.Out (ibRec trInitRec)
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000
@[simp] theorem state_put_byteBase (h : Heap) (ds : Nat) (d : DeflateState) :
    (setD h ds d).byteBase = h.byteBase := rfl

@[simp] theorem state_put_borrow (h : Heap) (ds : Nat) (d : DeflateState) :
    (setD h ds d).libcErrorBorrow = h.libcErrorBorrow := rfl

@[simp] theorem stream_put_byteBase (h : Heap) (r : ZStreamRef) (z : ZStream) :
    (r.put h z).byteBase = h.byteBase := by
  cases r <;> simp only [ZStreamRef.put] <;> split <;> rfl

@[simp] theorem stream_put_borrow (h : Heap) (r : ZStreamRef) (z : ZStream) :
    (r.put h z).libcErrorBorrow = h.libcErrorBorrow := by
  cases r <;> simp only [ZStreamRef.put] <;> split <;> rfl

def seedStream (h : Heap) : ZStream :=
  resultStream (seedPrepared h) (.tab h.nextBlk) (preparedStream (CompressCaller.localStream h)) 6

def seedState (h : Heap) (a1 a2 a3 : Array CtData) : DeflateState :=
  resultState (seedPrepared h) (.tab h.nextBlk) 6 a1 a2 a3

theorem seedPrepared_eq (h : Heap) :
    seedPrepared h = {h with
      streams := upd h.streams h.nextBlk (some (preparedStream (CompressCaller.localStream h)))
      nextBlk := h.nextBlk+1} := by
  simp [seedPrepared,CompressCaller.localHeap,ZStreamRef.put,upd_upd]

theorem seed_result_metadata (h : Heap) (a1 a2 a3 : Array CtData) (qa : Array UInt16) :
    (seedResult h a1 a2 a3 qa).nextBlk = h.nextBlk+6 ∧
    (seedResult h a1 a2 a3 qa).nalloc = h.nalloc+5 ∧
    (seedResult h a1 a2 a3 qa).allocOk = h.allocOk ∧
    (seedResult h a1 a2 a3 qa).garbage = h.garbage ∧
    (seedResult h a1 a2 a3 qa).static = h.static ∧
    (seedResult h a1 a2 a3 qa).byteBase = h.byteBase ∧
    (seedResult h a1 a2 a3 qa).libcErrorBorrow = h.libcErrorBorrow := by
  simp [seedResult,successHeap,seedPrepared,readyHeap,successfulBuffers,publishedHeap,stateHeap,
    CompressCaller.localHeap,setW,Nat.add_assoc]

theorem seed_result_objects (h : Heap) (a1 a2 a3 : Array CtData) (qa : Array UInt16) :
    (seedResult h a1 a2 a3 qa).streams h.nextBlk = some (seedStream h) ∧
    (seedResult h a1 a2 a3 qa).dstates (h.nextBlk+1) = some (seedState h a1 a2 a3) ∧
    (seedResult h a1 a2 a3 qa).bytes (h.nextBlk+2) = some (byteGarbage h 1) ∧
    (seedResult h a1 a2 a3 qa).words (h.nextBlk+3) = some (wordGarbage h 2) ∧
    (seedResult h a1 a2 a3 qa).words (h.nextBlk+4) = some (clearHead qa 32768) ∧
    (seedResult h a1 a2 a3 qa).bytes (h.nextBlk+5) = some (byteGarbage h 4) ∧
    (seedResult h a1 a2 a3 qa).ro (h.nextBlk+2) = false ∧
    (seedResult h a1 a2 a3 qa).ro (h.nextBlk+5) = false := by
  simp [seedResult,seedStream,seedState,resultState,finalState,successHeap,seedPrepared_eq,readyHeap,
    successfulBuffers,publishedHeap,stateHeap,CompressCaller.localHeap,ZStreamRef.put,setW,
    byteGarbage,wordGarbage,Nat.add_assoc]

theorem seed_state_parameters (h : Heap) (a1 a2 a3 : Array CtData) :
    let d := seedState h a1 a2 a3
    d.strm = some (.tab h.nextBlk) ∧ d.window = .ref (.blk (h.nextBlk+2)) 0 ∧
    d.prev = .ref (.blk (h.nextBlk+3)) 0 ∧ d.head = .ref (.blk (h.nextBlk+4)) 0 ∧
    d.pending_buf = .ref (.blk (h.nextBlk+5)) 0 ∧ d.pending_out = d.pending_buf ∧
    d.sym_buf = .ref (.blk (h.nextBlk+5)) 16384 ∧
    d.l_desc.dyn_tree = .ref (.dstate_dyn_ltree (h.nextBlk+1)) 0 ∧
    d.d_desc.dyn_tree = .ref (.dstate_dyn_dtree (h.nextBlk+1)) 0 ∧
    d.bl_desc.dyn_tree = .ref (.dstate_bl_tree (h.nextBlk+1)) 0 ∧
    d.level = 6 ∧ d.strategy = 0 ∧ d.w_bits = 15 ∧ d.hash_bits = 15 ∧
    d.window_size = 65536 ∧ d.lit_bufsize = 16384 ∧
    d.depth = DeflateState.zeroed.depth := by
  simp [seedState,resultState,finalState,lmD,resetState,rkPost,rkPost3,rkMid,
    ibRec,trInitRec,readyState,allocatedState,baseState,seedPrepared,
    CompressCaller.localHeap,Nat.add_assoc]

theorem seed_result_old {h : Heap} {b : Nat} (old : b < h.nextBlk)
    (a1 a2 a3 : Array CtData) (qa : Array UInt16) :
    SlotSame h (seedResult h a1 a2 a3 qa) b := by
  let pre := seedPrepared h
  let r := ZStreamRef.tab h.nextBlk
  let z := preparedStream (CompressCaller.localStream h)
  let ph := publishedHeap pre r z
  let rd := readyState r 6 ph.nextBlk (ph.nextBlk+1) (ph.nextBlk+2) (ph.nextBlk+3)
  let dr := resetState pre.nextBlk r 6 ph.nextBlk (ph.nextBlk+1) (ph.nextBlk+2) (ph.nextBlk+3) a1 a2 a3
  have npre : pre.nextBlk = h.nextBlk+1 := by simp [pre,seedPrepared,CompressCaller.localHeap]
  have nph : ph.nextBlk = h.nextBlk+2 := by simp [ph,publishedHeap,stateHeap,npre]
  have outside : ¬StreamRoot r b := by change b ≠ h.nextBlk;omega
  have prep : SlotSame h pre b := by simp [SlotSame,pre,seedPrepared_eq,upd_ne _ _ _ _ (by omega : b ≠ h.nextBlk)]
  have first : SlotSame pre ph b :=
    (slot_put_except pre r (stateStream z pre.nextBlk) b outside).trans
      (slot_stateHeap_old _ (baseState r) b (by simp only [ZStreamRef.put_nextBlk,npre];omega))
  have keep := (prep.trans first).trans (slot_successfulBuffers_old ph b (by omega))
  have keep := keep.trans (slot_setD_except _ pre.nextBlk rd b (by omega))
  have keep := keep.trans (slot_put_except _ r (resultStream pre r z 6) b outside)
  have keep := keep.trans (slot_setD_except _ pre.nextBlk dr b (by omega))
  have keep := keep.trans (slot_setW_except _ (ph.nextBlk+2) (clearHead qa 32768) b (by omega))
  exact keep.trans (slot_setD_except _ pre.nextBlk (lmD dr) b (by omega))

theorem seed_qa_shadow (h : Heap) :
    wordGarbage (publishedHeap (seedPrepared (seedShadow h)) (.tab (7*h.nextBlk))
      (preparedStream (CompressCaller.localStream (seedShadow h)))) 2 =
    wordGarbage (publishedHeap (seedPrepared h) (.tab h.nextBlk)
      (preparedStream (CompressCaller.localStream h))) 2 := by
  simp [wordGarbage,publishedHeap,stateHeap,seedPrepared,seedShadow,CompressCaller.localHeap]

#print axioms seed_result_objects
#print axioms seed_state_parameters
end ZlibF.Spec.Public.Proofs.CompressShadow
