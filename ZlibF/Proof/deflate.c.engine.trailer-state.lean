import ZlibF.Proof.«deflate.c.engine.block-reset»
import ZlibF.Math.DeflateZlibTrailer

/-! # Actual default zlib trailer writes on the initialized heap -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt BitsDiff)
set_option autoImplicit false

/-- The two source calls in the zlib trailer branch. -/
def zlibTrailer (strm : ZStreamPtr) (s : DeflateStatePtr) : M Unit := do
  let a ← zrd strm (·.adler)
  putShortMSB s (a >>> 16).toUInt32
  putShortMSB s (a &&& 0xffff).toUInt32

def zlibTrailerBuffer (buf : Array UInt8) (a : UInt64) : Array UInt8 :=
  (((buf.set! 0 ((a >>> 16).toUInt32 >>> 8).toUInt8).set! 1
    ((a >>> 16).toUInt32 &&& 0xff).toUInt8).set! 2
    ((a &&& 0xffff).toUInt32 >>> 8).toUInt8).set! 3
    ((a &&& 0xffff).toUInt32 &&& 0xff).toUInt8

/-- `int ZEXPORT deflate(z_streamp strm, int flush)` (zlib trailer stores).
The two actual putShortMSB calls fill four bytes after the final block
has drained. Real initialized storage supplies room; no allocator or
callee contract is assumed. All other record fields are unchanged. -/
theorem zlib_trailer_write {h : Heap} {r : ZStreamRef} {ds pb ob : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (pending : d.pending = 0) (cursor : d.pending_out = d.pending_buf) :
    let next := zlibTrailerBuffer buf z.adler
    let result := { d with pending := 4 }
    let after := setD (Zlib.Trees.Proofs.Out.setB h pb next) ds result
    zlibTrailer (some r) (some (.tab ds)) h = .ok ((), after) ∧
    DGood after r ds z result ∧ TreesInvAt after ds result pb next ∧ StreamBuffers after r ∧
    ByteSizes h after ∧ OutputStorage h after r ds pb ob ∧
    next.toList.take 4 = zlibTrailerWord z.adler := by
  let next := zlibTrailerBuffer buf z.adler
  let result := { d with pending := 4 }
  let after := setD (Zlib.Trees.Proofs.Out.setB h pb next) ds result
  have room : 4 ≤ buf.size := by have size := trees.base.size; have lo := trees.base.lit_lo; omega
  let half := (buf.set! 0 ((z.adler >>> 16).toUInt32 >>> 8).toUInt8).set! 1
    ((z.adler >>> 16).toUInt32 &&& 0xff).toUInt8
  let h1 := setD (Zlib.Trees.Proofs.Out.setB h pb half) ds { d with pending := 2 }
  have first : putShortMSB (some (.tab ds)) (z.adler >>> 16).toUInt32 h = .ok ((), h1) := by
    simpa only [pending, UInt64.toNat_zero, Nat.add_zero, Nat.zero_add, UInt64.zero_add,
      h1, half, setD, Zlib.Trees.Proofs.Out.setB] using
      putShortMSB_ok (z.adler >>> 16).toUInt32 good.live.hs trees.base.pbuf trees.base.bytes trees.base.rw
        (by rw [pending]; change 0 + 0 + 1 < buf.size; omega) (by rw [pending]; decide)
  have second : putShortMSB (some (.tab ds)) (z.adler &&& 0xffff).toUInt32 h1 = .ok ((), after) := by
    simpa only [h1, half, after, result, next, zlibTrailerBuffer, setD, Zlib.Trees.Proofs.Out.setB,
      upd_same, upd_upd, Nat.zero_add, show (2 : UInt64).toNat = 2 from rfl,
      show (2 : UInt64) + 2 = 4 from rfl] using
      putShortMSB_ok (h := h1) (sr := ds) (b := pb) (off := 0) (d := { d with pending := 2 }) (a := half)
        (z.adler &&& 0xffff).toUInt32 (by simp [h1]) trees.base.pbuf (by simp [h1]) trees.base.rw
        (by simp [half]; omega) (by change 2 + 2 < 2 ^ 64; decide)
  have size : next.size = buf.size := by simp [next, zlibTrailerBuffer]
  have treeA : TreesInvAt after ds result pb next := by
    refine ⟨⟨by simp [after], trees.base.wf, trees.base.static, trees.base.pbuf,
      by simp [after], trees.base.rw, size.trans trees.base.size,
      trees.base.psize.trans size.symm, trees.base.sym, trees.base.lit_lo,
      trees.base.lit_hi, trees.base.sym_end, ?_⟩,
      ⟨trees.run.ldyn, trees.run.lstat, trees.run.ddyn, trees.run.dstat,
       trees.run.bldyn, trees.run.blstat, trees.run.bi_lo, trees.run.bi_hi,
       trees.run.bi_buf, trees.run.sym_next_le, trees.run.sym_next_mod⟩⟩
    change 4 ≤ d.pending_buf_size.toNat
    rw [trees.base.psize]
    exact room
  have fields : BitsDiff d result := ⟨4, d.bi_buf, d.bi_valid, d.bi_used, rfl⟩
  have goodA := output_bits_good good cursor trees.base.bytes size fields treeA
  have sizes := output_bits_sizes good trees.base.bytes size fields
  have storage := output_bits_storage (r := r) (ob := ob) (result := result) (next := next)
    good.live.hs trees.base.bytes
  have owned := stream_owned_keys good goodA rfl rfl rfl rfl
  have buffersA := stream_buffers_sizes good.live.hz goodA.live.hz buffers sizes owned (stream_accounting_zero z)
  refine ⟨?_, goodA, treeA, buffersA, sizes, storage, ?_⟩
  · simp only [zlibTrailer, bind_app, zrd_eq, good.live.hz, first, second]
    rfl
  · change next.toList.take 4 = zlibTrailerWord z.adler
    apply List.ext_getElem
    · simp only [List.length_take, Array.length_toList, size, zlibTrailerWord, List.length_cons, List.length_nil]
      omega
    · intro i hleft hright
      have range : i < 4 := by simpa [zlibTrailerWord] using hright
      have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
      rcases cases with rfl | rfl | rfl | rfl <;>
        simp [next, zlibTrailerBuffer, zlibTrailerWord, room, Array.set!_eq_setIfInBounds]

end Zlib.Deflate.Engine.Proofs
