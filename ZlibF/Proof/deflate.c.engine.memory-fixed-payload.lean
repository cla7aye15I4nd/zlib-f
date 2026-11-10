import ZlibF.Proof.«deflate.c.engine.fixed-payload»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
open Zlib.Trees.Proofs.Out (TreesInvAt)
set_option autoImplicit false

/-- The actual fixed writer fits every legal symbol allocation, using its
real size. Its derived two-byte margin supports the common final tail. -/
theorem memory_fixed_payload_ready_fields {h : Heap} {r : ZStreamRef} {ds pb ob : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8} {xs : List Symbol}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (cursor : d.pending_out = d.pending_buf)
    (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 10)
    (count : d.sym_next.toNat = 3 * xs.length) (packed : PackedSymbols buf d.lit_bufsize.toNat xs)
    (valid : ∀ s ∈ xs, s.Valid) :
    ∃ next result,
      let ready := setD (Zlib.Trees.Proofs.Out.setB h pb next) ds result
      Zlib.Trees.compress_block (some (.tab ds)) (.ref .st_static_ltree 0) (.ref .st_static_dtree 0) h = .ok ((), ready) ∧
      DGood ready r ds z result ∧ TreesInvAt ready ds result pb next ∧ StreamBuffers ready r ∧
      ByteSizes h ready ∧ OutputStorage h ready r ds pb ob ∧ Zlib.Trees.Proofs.Out.BitsDiff d result ∧
      next.size = buf.size ∧ result.pending.toNat + 2 ≤ next.size ∧ result.pending_out = result.pending_buf ∧
      8 * result.pending.toNat + result.bi_valid.toInt.toNat ≤ 8 * next.size ∧
      Zlib.Trees.Proofs.Out.outBits next result = Zlib.Trees.Proofs.Out.outBits buf d ++
        (xs.flatMap (fun s => Zlib.Trees.Proofs.Out.payloadSymBits
          Zlib.Trees.Proofs.fixedLiteralWords Zlib.Trees.Proofs.fixedDistanceWords (s.distance, s.value)) ++
          Zlib.Trees.Proofs.Out.codeBits Zlib.Trees.Proofs.fixedLiteralWords 256) := by
  have legal := packed_payload_legal packed valid
  obtain ⟨next, result, run, treesA, output, size, _frame, _lower, _upper, fields⟩ :=
    Zlib.Trees.Proofs.compress_block_fixed_emit trees pending bits xs.length count legal
  have goodA := output_bits_good good cursor trees.base.bytes size fields treesA
  have buffersA := output_bits_buffers good buffers cursor trees.base.bytes size fields treesA
  have sizes := output_bits_sizes good trees.base.bytes size fields
  have storage := output_bits_storage (r := r) (ob := ob) (result := result) (next := next)
    good.live.hs trees.base.bytes
  have capacity := trees.run.sym_next_le
  rw [count, trees.base.sym_end] at capacity
  have capacityMin := trees.base.lit_lo
  have length := Zlib.Trees.Proofs.fixedPayloadPrefix_length buf d.lit_bufsize.toNat xs.length legal
  have bitCount := congrArg List.length output
  simp only [Zlib.Trees.Proofs.Out.outBits_length, List.length_append, Zlib.Trees.Proofs.Out.codeBits,
    Zlib.Trees.Proofs.fixed_literal_end, Zlib.Trees.Proofs.Out.natBits_length,
    show (7 : UInt16).toNat = 7 from rfl, pending, UInt64.toNat_zero] at bitCount
  have pendingBound : result.pending.toNat + 2 ≤ next.size := by rw [size, trees.base.size]; omega
  have sizeA : next.size = buf.size := size
  have cursorA : result.pending_out = result.pending_buf := by
    obtain ⟨_, _, _, _, equal⟩ := fields
    rw [equal]
    exact cursor
  have validA := treesA.run.bi_hi
  have room : 8 * result.pending.toNat + result.bi_valid.toInt.toNat ≤ 8 * next.size := by omega
  rw [packed_fixed_payload_bits packed valid] at output
  exact ⟨next, result, run, goodA, treesA, buffersA, sizes, storage, fields, sizeA, pendingBound, cursorA, room, output⟩

end Zlib.Deflate.Engine.Proofs
#print axioms Zlib.Deflate.Engine.Proofs.memory_fixed_payload_ready_fields
