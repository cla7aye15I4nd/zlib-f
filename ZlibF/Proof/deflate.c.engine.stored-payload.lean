import ZlibF.Proof.«deflate.c.engine.stored-window»
import ZlibF.Proof.«deflate.c.engine.fixed-header»

/-! # The real stored writer extends the accepted input on the engine heap -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt BitsDiff sourceBytes storedTag storedBodyBits)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- The initialized engine owns distinct pending and window allocations. -/
theorem stored_window_separate {h : Heap} {r : ZStreamRef} {ds pb w : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (win : d.window = .ref (.blk w) 0) : pb ≠ w := by
  obtain ⟨w0, p, q, b0, blocks⟩ := good.inv.blocks
  have windowId : w0 = w := by simpa only [win, Ptr.ref.injEq, BRef.blk.injEq, and_true] using blocks.win.symm
  have pendingId : b0 = pb := by simpa only [trees.base.pbuf, Ptr.ref.injEq, BRef.blk.injEq, and_true] using blocks.pbuf.symm
  subst w0
  subst b0
  exact Ne.symm blocks.wb

/-- `void ZLIB_INTERNAL _tr_stored_block(deflate_state *s, charf *buf, ulg stored_len, int last)`.
The actual engine call writes the real window slice and independently
decodes to exactly the next accepted input prefix. Ownership, caller
buffers and object accounting survive the write. The selected branch's
derived size bound is explicit here; full flush must supply it on this
same constructed state and compose the common reset/publication tail. -/
theorem stored_payload_engine {h : Heap} {r : ZStreamRef} {ds pb ob w origin base : Nat}
    {z : ZStream} {d : DeflateState} {buf window : Array UInt8} {xs : List Symbol} {input : Nat → UInt8}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (cursor : d.pending_out = d.pending_buf) (memory : d.lit_bufsize.toNat = 16384)
    (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7)
    (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some window)
    (range : fillEnd d ≤ d.window_size.toNat) (nonnegative : 0 ≤ d.block_start.toInt)
    (balance : BlockBalance d xs 0) (accounted : base + represented xs = origin + d.strstart.toNat)
    (view : ∀ i, i < fillEnd d → bfn window i = input (origin + i))
    (selectedRoom : represented xs + 6 ≤ 63488) (last : Bool) :
    ∃ next result,
      let after := setD (Zlib.Trees.Proofs.Out.setB h pb next) ds result
      Zlib.Trees.«_tr_stored_block» (some (.tab ds)) (.ref (.blk w) d.block_start.toInt.toNat)
        (UInt64.ofNat (represented xs)) (if last then 1 else 0) h = .ok ((), after) ∧
      DGood after r ds z result ∧ TreesInvAt after ds result pb next ∧ StreamBuffers after r ∧
      ByteSizes h after ∧ OutputStorage h after r ds pb ob ∧ BitsDiff d result ∧
      next.size = 65536 ∧ result.pending_out = result.pending_buf ∧
      result.bi_valid.toInt = 0 ∧ result.pending.toNat ≤ 63488 ∧
      Zlib.Trees.Proofs.Out.outBits next result = Zlib.Trees.Proofs.Out.outBits buf d ++
        (storedTag last ++ storedBodyBits ((8 - (d.bi_valid.toInt.toNat + 3) % 8) % 8)
          (sourceBytes window d.block_start.toInt.toNat (represented xs))) ∧
      ∀ suffix : List Bool, suffix.length % 8 = 0 →
        ZlibF.Spec.Body [] 0 (inputPrefix input base)
          (storedBodyBits ((8 - (d.bi_valid.toInt.toNat + 3) % 8) % 8)
            (sourceBytes window d.block_start.toInt.toNat (represented xs)) ++ suffix)
          suffix (inputPrefix input (base + represented xs)) := by
  have length : (UInt64.ofNat (represented xs)).toNat = represented xs := by
    rw [UInt64.toNat_ofNat']
    exact Nat.mod_eq_of_lt (by omega)
  have inputBound := stored_window_readable good win get range balance nonnegative
  have inputPrefixEq := stored_window_prefix balance accounted nonnegative view
  obtain ⟨next, result, run, treesA, output, size, aligned, roomA, diff, decode⟩ :=
    Zlib.Trees.Proofs.Out.stored_block_format trees get (stored_window_separate good trees win)
      bits (UInt64.ofNat (represented xs)) (by rw [length]; omega)
      (by rw [length]; exact inputBound)
      (by rw [length, pending, trees.base.size, memory]; change 0 + represented xs + 6 ≤ 4 * 16384; omega) last
  rw [length] at output decode roomA
  have goodA := output_bits_good good cursor trees.base.bytes size diff treesA
  have buffersA := output_bits_buffers good buffers cursor trees.base.bytes size diff treesA
  have sizes := output_bits_sizes good trees.base.bytes size diff
  have storage := output_bits_storage (r := r) (ob := ob) (result := result) (next := next)
    good.live.hs trees.base.bytes
  have sizeA : next.size = 65536 := by rw [size, trees.base.size, memory]
  have cursorA : result.pending_out = result.pending_buf := by
    obtain ⟨_, _, _, _, fields⟩ := diff
    rw [fields]
    exact cursor
  refine ⟨next, result, run, goodA, treesA, buffersA, sizes, storage, diff,
    sizeA, cursorA, aligned, ?_, output, ?_⟩
  · rw [pending] at roomA
    change result.pending.toNat ≤ 0 + represented xs + 6 at roomA
    omega
  · intro suffix suffixAligned
    have body := decode (inputPrefix input base) suffix suffixAligned
    rw [inputPrefixEq] at body
    exact body

end Zlib.Deflate.Engine.Proofs
