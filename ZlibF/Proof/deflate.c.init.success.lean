import ZlibF.Proof.«deflate.c.init.construct»
import ZlibF.Proof.«deflate.c.init.storage»

/-! # deflate.c: successful default buffer construction -/

namespace Zlib.Deflate.Proofs.DefaultInit
open C Zlib.Deflate Zlib.Deflate.Spec
open Zlib.Trees.Proofs.Out (TreesBase TreesStatic)
set_option autoImplicit false

def readyHeap (h : Heap) (ds : Nat) (r : ZStreamRef) (level : Int32) : Heap :=
  setD (successfulBuffers h) ds
    (readyState r level h.nextBlk (h.nextBlk + 1) (h.nextBlk + 2) (h.nextBlk + 3))

theorem buffer_state_success (h : Heap) (r : ZStreamRef)
    (ha : ∀ j, j < 4 → h.allocOk (h.nalloc + j) = true) :
    bufferState h (baseState r) =
      allocatedState r h.nextBlk (h.nextBlk + 1) (h.nextBlk + 2) (h.nextBlk + 3) := by
  have ps := (buffers_success h ha).2
  have w := congrArg (fun x : BPtr × WPtr × WPtr × BPtr => x.1) ps
  have p := congrArg (fun x : BPtr × WPtr × WPtr × BPtr => x.2.1) ps
  have q := congrArg (fun x : BPtr × WPtr × WPtr × BPtr => x.2.2.1) ps
  have b := congrArg (fun x : BPtr × WPtr × WPtr × BPtr => x.2.2.2) ps
  dsimp only [bufferPointers] at w p q b
  simp only [bufferState, allocatedState, w, p, q, b]

/-- The real pointer addition and final stores reach the constructed
default state before the actual reset call. -/
theorem finish_to_reset (h : Heap) (ds : Nat) (r : ZStreamRef) (level : Int32)
    (ha : ∀ j, j < 4 → h.allocOk (h.nalloc + j) = true) :
    finish (some r) (some (.tab ds)) level (bufferPointers h)
        (setD (buffersHeap h) ds (bufferState h (baseState r))) =
      deflateReset (some r) (readyHeap h ds r level) := by
  have he := (buffers_success h ha).1
  have hp := (buffers_success h ha).2
  rw [he, buffer_state_success h r ha, hp]
  let d := allocatedState r h.nextBlk (h.nextBlk + 1) (h.nextBlk + 2) (h.nextBlk + 3)
  let g := setD (successfulBuffers h) ds d
  have hb : g.bytes (h.nextBlk + 3) = some (byteGarbage h 3) := by
    simp [g, successfulBuffers]
  have padd_run : padd (.ref (.blk (h.nextBlk + 3)) 0 : BPtr) 16384 g =
      .ok (.ref (.blk (h.nextBlk + 3)) 16384, g) := by
    have hget : Space.get g (BRef.blk (h.nextBlk + 3)) = some (byteGarbage h 3) := hb
    have add := Ptr.add_nat_ok (off := 0) (n := 16384) hget (by simp [byteGarbage])
    simpa only [OkOn, padd, Nat.zero_add] using add
  unfold finish
  simp only [bind_app, Bool.or_false, Bool.false_or]
  change (do
    let sym_buf ← padd (.ref (.blk (h.nextBlk + 3)) 0 : BPtr) 16384
    wr (some (.tab ds)) (fun d => { d with sym_buf, sym_end := 49149 })
    wr (some (.tab ds)) (fun d => { d with level, strategy := 0, «method» := 8 })
    deflateReset (some r)) g = _
  rw [bind_app, padd_run]
  simp only [bind_app, wrD_eq, g, setD_dstates_same, setD_setD]
  rfl

/-- All buffer geometry and tree storage follow from the actual successful
requests. pending_out and window_size are deliberately left for reset. -/
theorem ready_storage {h : Heap} {r : ZStreamRef} {z : ZStream} {ds : Nat}
    (level : Int32) (hf : Fresh h) (hu : Uniq h) (hz : r.get h = some z)
    (hs : h.dstates ds = some (baseState r)) (hds : ds < h.nextBlk)
    (halloc : DefAlloc z) (hzs : z.state = some (.deflate ds))
    (hstatic : TreesStatic h.static)
    (ha : ∀ j, j < 4 → h.allocOk (h.nalloc + j) = true) :
    let d := readyState r level h.nextBlk (h.nextBlk + 1) (h.nextBlk + 2) (h.nextBlk + 3)
    let g := readyHeap h ds r level
    DLive g r ds z d ∧ TreesBase g ds d (h.nextBlk + 3) ((g.bytes (h.nextBlk + 3)).getD #[]) ∧
      DBlocks g { d with pending_out := d.pending_buf }
        h.nextBlk (h.nextBlk + 1) (h.nextBlk + 2) (h.nextBlk + 3) ∧ Uniq g ∧ Fresh g := by
  let d := readyState r level h.nextBlk (h.nextBlk + 1) (h.nextBlk + 2) (h.nextBlk + 3)
  let g := readyHeap h ds r level
  have slots := (buffers_success h ha).1
  have hsf : (successfulBuffers h).dstates ds = some (baseState r) := by simpa [successfulBuffers] using hs
  have hsh := shape_setD hsf d
  have huB : Uniq (successfulBuffers h) := by rw [← slots]; exact buffers_uniq hu hf
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
    ?_, hb, hsh.uniq huB, hsh.fresh (by rfl) hfB⟩
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

end Zlib.Deflate.Proofs.DefaultInit
