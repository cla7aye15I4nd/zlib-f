import ZlibF.Proof.«deflate.c.engine.output-state»
import ZlibF.Proof.«deflate.c.engine.header-caller»

/-! # Actual pending-copy results retain ownership and caller extents -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

def pendingCopyHeap (h : Heap) (r : ZStreamRef) (ds pb po ob oo : Nat)
    (z : ZStream) (d : DeflateState) (pending output : Array UInt8) (n : UInt32) : Heap :=
  let copied := { h with bytes := upd h.bytes ob (some (copyRange output pending oo po n.toNat)) }
  setD (r.put copied (pendingStream z (.ref (.blk ob) (oo + n.toNat)) n)) ds
    (pendingState d (.ref (.blk pb) (po + n.toNat)) n)

/-- The natural copy count gives exact non-wrapping subtractions. -/
theorem pending_copy_counts (pending : UInt64) (available : UInt32) :
    let n := pendingLen pending available
    (pending - n.toUInt64).toNat + n.toNat = pending.toNat ∧
      (available - n).toNat + n.toNat = available.toNat := by
  let n := pendingLen pending available
  change (pending - n.toUInt64).toNat + n.toNat = pending.toNat ∧
    (available - n).toNat + n.toNat = available.toNat
  have count : n.toNat = min pending.toNat available.toNat := pendingLen_value _ _
  have pin : n.toUInt64 ≤ pending := by rw [UInt64.le_iff_toNat_le, UInt32.toNat_toUInt64]; omega
  have pout : n ≤ available := by rw [UInt32.le_iff_toNat_le]; omega
  rw [UInt64.toNat_sub_of_le _ _ pin, UInt32.toNat_toUInt64, UInt32.toNat_sub_of_le _ _ pout]
  constructor <;> omega

theorem pending_copy_accounting {z : ZStream} {d : DeflateState} {ob oo : Nat}
    (pointer : z.next_out = .ref (.blk ob) oo) :
    let n := pendingLen d.pending z.avail_out
    StreamAccounting z (pendingStream z (.ref (.blk ob) (oo + n.toNat)) n) 0 n.toNat := by
  let n := pendingLen d.pending z.avail_out
  change StreamAccounting z (pendingStream z (.ref (.blk ob) (oo + n.toNat)) n) 0 n.toNat
  have count : n.toNat = min d.pending.toNat z.avail_out.toNat := pendingLen_value _ _
  dsimp only [pendingStream]
  refine ⟨by omega, by omega, by simp, (pending_copy_counts d.pending z.avail_out).2,
    (advance_zero _).symm, ?_, rfl, rfl, rfl, rfl, rfl⟩
  simp only [pointer, advance]

theorem pending_copy_good {h : Heap} {r : ZStreamRef} {ds pb po ob oo : Nat}
    {z : ZStream} {d : DeflateState} {pending output : Array UInt8}
    (good : DGood h r ds z d) (buffer : d.pending_buf = .ref (.blk pb) 0)
    (cursor : d.pending_out = .ref (.blk pb) po) (outGet : h.bytes ob = some output) :
    let n := pendingLen d.pending z.avail_out
    DGood (pendingCopyHeap h r ds pb po ob oo z d pending output n) r ds
      (pendingStream z (.ref (.blk ob) (oo + n.toNat)) n)
      (pendingState d (.ref (.blk pb) (po + n.toNat)) n) := by
  let n := pendingLen d.pending z.avail_out
  let copied := { h with bytes := upd h.bytes ob (some (copyRange output pending oo po n.toNat)) }
  let result := pendingState d (.ref (.blk pb) (po + n.toNat)) n
  have goodC : DGood copied r ds z d := good.bytes_set ob _ output outGet (size_copyRange _ _ _ _ _)
  obtain ⟨w, p, q, b, blocks⟩ := goodC.inv.blocks
  have bid : b = pb := by simpa only [buffer, Ptr.ref.injEq, BRef.blk.injEq, and_true] using blocks.pbuf.symm
  subst b
  obtain ⟨off, oldPtr, bound⟩ := blocks.pout
  have same : off = po := by simpa only [cursor, Ptr.ref.injEq, true_and] using oldPtr.symm
  subst off
  have count := (pending_copy_counts d.pending z.avail_out).1
  have blocksA : DBlocks copied result w p q pb := by
    refine { blocks with pout := ?_ }
    unfold result pendingState
    by_cases empty : (d.pending - n.toUInt64 == 0) = true
    · refine ⟨0, by simp only [empty, ite_true, buffer], ?_⟩
      change 0 + (d.pending - n.toUInt64).toNat ≤ d.pending_buf_size.toNat
      dsimp only [n] at *
      omega
    · refine ⟨po + n.toNat, by simp [empty], ?_⟩
      change po + n.toNat + (d.pending - n.toUInt64).toNat ≤ d.pending_buf_size.toNat
      dsimp only [n] at *
      omega
  have inv : DStInv copied ds result := { goodC.inv with blocks := ⟨w, p, q, pb, blocksA⟩ }
  exact goodC.setZD (z' := pendingStream z (.ref (.blk ob) (oo + n.toNat)) n) (d' := result)
    rfl good.live.zalloc good.live.zfree rfl good.live.status inv (by trkeep)

theorem pending_copy_sizes {h : Heap} {r : ZStreamRef} {ds pb po ob oo : Nat}
    {z : ZStream} {d : DeflateState} {pending output : Array UInt8} (n : UInt32)
    (state : h.dstates ds = some d) (outGet : h.bytes ob = some output) :
    ByteSizes h (pendingCopyHeap h r ds pb po ob oo z d pending output n) := by
  let copied := { h with bytes := upd h.bytes ob (some (copyRange output pending oo po n.toNat)) }
  have stateC : copied.dstates ds = some d := state
  have view : ∀ ref : BRef,
      Space.get (pendingCopyHeap h r ds pb po ob oo z d pending output n) ref = Space.get copied ref := by
    intro ref
    rw [pendingCopyHeap, byte_view_setD_depth (d := d) (result := pendingState d (.ref (.blk pb) (po + n.toNat)) n) (by simpa using stateC) rfl, byte_get_stream_put]
  refine ⟨?_, ?_⟩
  · intro ref a get
    obtain ⟨next, getA, size⟩ := byte_view_write_size (new := copyRange output pending oo po n.toNat)
      get outGet (size_copyRange _ _ _ _ _)
    exact ⟨next, (view ref).trans getA, size⟩
  · intro ref
    cases ref <;> simp [Space.ro, pendingCopyHeap]

theorem ByteSizes.trans {h g j : Heap} (first : ByteSizes h g) (second : ByteSizes g j) : ByteSizes h j := by
  refine ⟨?_, fun ref => (second.ro ref).trans (first.ro ref)⟩
  intro ref a get
  obtain ⟨middle, getM, sizeM⟩ := first.get ref a get
  obtain ⟨next, getA, sizeA⟩ := second.get ref middle getM
  exact ⟨next, getA, sizeA.trans sizeM⟩

theorem output_bits_sizes {h : Heap} {r : ZStreamRef} {ds pb : Nat}
    {z : ZStream} {d result : DeflateState} {buf next : Array UInt8}
    (good : DGood h r ds z d) (get : h.bytes pb = some buf) (size : next.size = buf.size)
    (fields : Zlib.Trees.Proofs.Out.BitsDiff d result) :
    ByteSizes h (setD (Zlib.Trees.Proofs.Out.setB h pb next) ds result) := by
  have depth : result.depth = d.depth := by obtain ⟨_, _, _, _, rfl⟩ := fields; rfl
  have view : ∀ ref : BRef, Space.get (setD (Zlib.Trees.Proofs.Out.setB h pb next) ds result) ref =
      Space.get (Zlib.Trees.Proofs.Out.setB h pb next) ref := by
    intro ref
    exact byte_view_setD_depth (h := Zlib.Trees.Proofs.Out.setB h pb next) good.live.hs depth ref
  refine ⟨?_, ?_⟩
  · intro ref a old
    obtain ⟨a', getA, sizeA⟩ := byte_view_write_size (new := next) old get size
    exact ⟨a', (view ref).trans getA, sizeA⟩
  · intro ref
    cases ref <;> rfl

/-- The real bit-writer heap keeps public caller ranges. The represented
bit-state update and its already established TreesInvAt give DGood here. -/
theorem output_bits_buffers {h : Heap} {r : ZStreamRef} {ds pb : Nat}
    {z : ZStream} {d result : DeflateState} {buf next : Array UInt8}
    (good : DGood h r ds z d) (buffers : StreamBuffers h r) (cursor : d.pending_out = d.pending_buf)
    (get : h.bytes pb = some buf) (size : next.size = buf.size)
    (fields : Zlib.Trees.Proofs.Out.BitsDiff d result)
    (trees : Zlib.Trees.Proofs.Out.TreesInvAt (setD (Zlib.Trees.Proofs.Out.setB h pb next) ds result) ds result pb next) :
    StreamBuffers (setD (Zlib.Trees.Proofs.Out.setB h pb next) ds result) r := by
  have goodA := output_bits_good good cursor get size fields trees
  have keys : ∀ b, DeflateOwned ds result b ↔ DeflateOwned ds d b := by
    obtain ⟨_, _, _, _, rfl⟩ := fields
    intro b
    rfl
  have owned : ∀ b, StreamOwned (setD (Zlib.Trees.Proofs.Out.setB h pb next) ds result) r b ↔ StreamOwned h r b := by
    intro b
    rw [stream_owned_deflate goodA, stream_owned_deflate good, keys]
  exact stream_buffers_sizes good.live.hz goodA.live.hz buffers (output_bits_sizes good get size fields)
    owned (stream_accounting_zero z)

/-- The tree writer's byte prefix is exactly the independent format's
least-significant-bit-first byte interpretation. -/
theorem bytes_bits_format (buf : Array UInt8) (n : Nat) (bound : n ≤ buf.size) :
    Zlib.Trees.Proofs.Out.bytesBits buf n = ZlibF.Spec.bytesToBits (buf.toList.take n) := by
  have seq := seg_eq_take_drop buf 0 n (by omega)
  simp only [List.drop_zero] at seq
  rw [← seq]
  unfold Zlib.Adler32.Proofs.seg ZlibF.Spec.bytesToBits Zlib.Trees.Proofs.Out.bytesBits
  rw [List.flatMap_map]
  congr 1
  funext i
  change Zlib.Trees.Proofs.Out.natBits (buf.getD i 0).toNat 8 = ZlibF.Spec.byteBits buf[0 + i]!
  rw [Nat.zero_add, Array.getElem!_eq_getD]
  rfl

/-- The bit buffer in the existing public PendingBits relation agrees
with the tree writer's bit vocabulary. -/
theorem pending_word_bits (d : DeflateState) :
    Zlib.Trees.Proofs.Out.natBits d.bi_buf.toNat d.bi_valid.toInt.toNat =
      (List.range d.bi_valid.toInt.toNat).map (fun j => decide (d.bi_buf.toNat / 2 ^ j % 2 = 1)) := by
  simp only [Zlib.Trees.Proofs.Out.natBits, Nat.testBit_eq_decide_div_mod_eq]

end Zlib.Deflate.Engine.Proofs
