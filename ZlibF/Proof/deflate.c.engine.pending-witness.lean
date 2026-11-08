import ZlibF.Proof.«deflate.c.engine.pending-block-output»
import ZlibF.Proof.«deflate.c.engine.loop-entry»
import ZlibF.Math.InflatePrefixes

/-! # Default initialization and real bit writers reach pending publication -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt BitsDiff)
open ZlibF.Spec.Public.Proofs.DeflateInit
set_option autoImplicit false

/-- Actual fitting send_bits execution establishes a publishing state.
The bit room for a following flush will be derived from these counters. -/
theorem buffered_bits_publish_state {h : Heap} {r : ZStreamRef} {ds pb : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (cursor : d.pending_out = d.pending_buf) (value len : Int32)
    (lengthLo : 0 ≤ len.toInt) (lengthHi : len.toInt ≤ 15)
    (fits : Zlib.Trees.Proofs.Out.v16 value < 2 ^ len.toInt.toNat)
    (buffered : d.bi_valid.toInt + len.toInt ≤ 16) :
    ∃ result,
      Zlib.Trees.send_bits (some (.tab ds)) value len h = .ok ((), setD h ds result) ∧
      DGood (setD h ds result) r ds z result ∧ TreesInvAt (setD h ds result) ds result pb buf ∧
      StreamBuffers (setD h ds result) r ∧ result.pending = d.pending ∧
      result.bi_valid.toInt = d.bi_valid.toInt + len.toInt ∧ result.pending_out = result.pending_buf ∧
      Zlib.Trees.Proofs.Out.outBits buf result = Zlib.Trees.Proofs.Out.outBits buf d ++
        Zlib.Trees.Proofs.Out.natBits (Zlib.Trees.Proofs.Out.v16 value) len.toInt.toNat := by
  obtain ⟨result, run, treesA, bits, pending, word, valid, fields⟩ :=
    Zlib.Trees.Proofs.Out.send_bits_spec_B trees value len lengthLo lengthHi fits buffered
  have diff : BitsDiff d result := by rw [fields]; exact ⟨d.pending, word, valid, d.bi_used, rfl⟩
  have treesB : TreesInvAt (setD (Zlib.Trees.Proofs.Out.setB h pb buf) ds result) ds result pb buf := by
    rw [Zlib.Trees.Proofs.Out.setB_self trees.base.bytes]
    exact treesA
  have goodA := output_bits_good good cursor trees.base.bytes rfl diff treesB
  have bufferA := output_bits_buffers good buffers cursor trees.base.bytes rfl diff treesB
  rw [Zlib.Trees.Proofs.Out.setB_self trees.base.bytes] at goodA bufferA
  have count := congrArg List.length bits
  simp only [Zlib.Trees.Proofs.Out.outBits_length, List.length_append,
    Zlib.Trees.Proofs.Out.natBits_length, pending] at count
  have lo := treesA.run.bi_lo
  have oldLo := trees.run.bi_lo
  refine ⟨result, run, goodA, treesA, bufferA, pending, by omega, ?_, bits⟩
  rw [fields]
  exact cursor

/-- The existing concrete nonempty default caller is actually initialized
with a two-byte raw output view. No engine invariant is caller-supplied. -/
theorem default_pending_output_entry :
    ∃ initialized z d,
      C.run (deflateInit_ (some (.tab 0)) Z_DEFAULT_COMPRESSION (.ref (.blk 1) 0) 112)
        loopWitnessHeap = .ok (Z_OK, initialized) ∧ EngineStart initialized (.tab 0) 2 z d ∧
      StreamBuffers initialized (.tab 0) ∧ z.next_out = .ref (.blk 1) 0 ∧ z.avail_out = 2 := by
  obtain ⟨initialized, z, d, _used, _after, _zf, _result, _ys, _input, _origin, initRun, _count,
    buffers, start, _rest⟩ := default_slow_loop_witness
  have oldGet : (ZStreamRef.tab 0).get witnessHeap = some (default : ZStream) := by simp [ZStreamRef.get, witnessHeap]
  have shape := shape_put oldGet loopWitnessStream
  have fresh : Fresh loopWitnessHeap := shape.fresh (by simp [loopWitnessHeap]) witness_fresh
  have uniq : Uniq loopWitnessHeap := shape.uniq witness_uniq
  have get : (ZStreamRef.tab 0).get loopWitnessHeap = some loopWitnessStream := ZStreamRef.get_put_same oldGet _
  have version : VersionValue loopWitnessHeap (.ref (.blk 1) 0) (some 49) := by
    right
    refine ⟨49, rfl, Or.inr ⟨.blk 1, 0, #[49, 0], rfl, ?_, by decide, rfl⟩⟩
    simp [Space.get, loopWitnessHeap, witnessHeap, Heap.empty]
  obtain ⟨other, otherZ, otherD, otherRun, otherStart, _initial, _reachable, _inputPtr, _inputCount, outPtr, outCount⟩ :=
    default_initialization_engine_bindings (h := loopWitnessHeap) (r := .tab 0) (z := loopWitnessStream)
      (version := .ref (.blk 1) 0) (level := Z_DEFAULT_COMPRESSION) (p := settings 6)
      fresh uniq (by rfl) get ⟨Or.inl rfl, Or.inl rfl⟩ version (by decide +kernel) (by intro _ _; rfl)
  have same : other = initialized := congrArg Prod.snd (Except.ok.inj (otherRun.symm.trans initRun))
  subst other
  have sameZ : otherZ = z := Option.some.inj (otherStart.good.live.hz.symm.trans start.good.live.hz)
  subst otherZ
  exact ⟨initialized, z, d, initRun, start, buffers, outPtr, outCount⟩

/-- Actual default initialization, two real eight-bit sends and the real
flush_pending publish two known bytes. This witnesses the full 16-bit
branch and the publishing premises from execution, not assignments. -/
theorem default_pending_word_witness :
    ∃ initialized after z' result,
      (∃ z d, C.run (deflateInit_ (some (.tab 0)) Z_DEFAULT_COMPRESSION (.ref (.blk 1) 0) 112)
        loopWitnessHeap = .ok (Z_OK, initialized) ∧ EngineStart initialized (.tab 0) 2 z d) ∧
      (do Zlib.Trees.send_bits (some (.tab 2)) 0xa5 8
          Zlib.Trees.send_bits (some (.tab 2)) 0x3c 8
          flush_pending (some (.tab 0))) initialized = .ok ((), after) ∧
      DGood after (.tab 0) 2 z' result ∧ StreamBuffers after (.tab 0) ∧
      Bytes after (.ref (.blk 1) 0) 2 [0xa5, 0x3c] ∧ result.pending.toNat = 0 ∧ result.bi_valid.toInt.toNat = 0 := by
  obtain ⟨initialized, z, d, initRun, start, buffers, pointer, available⟩ := default_pending_output_entry
  obtain ⟨oldD, pb, buf, trees⟩ := start.good.trees
  have stateEq : oldD = d := Option.some.inj (trees.base.dstate.symm.trans start.good.live.hs)
  subst oldD
  obtain ⟨one, run1, good1, tree1, buffers1, pending1, valid1, cursor1, bits1⟩ :=
    buffered_bits_publish_state start.good trees buffers start.pendingOut 0xa5 8
      (by decide) (by decide) (by decide +kernel) (by rw [start.bits]; decide)
  have bit8 : one.bi_valid.toInt = 8 := by rw [start.bits] at valid1; exact valid1
  obtain ⟨two, run2, good2, tree2, buffers2, pending2, valid2, cursor2, bits2⟩ :=
    buffered_bits_publish_state good1 tree1 buffers1 cursor1 0x3c 8
      (by decide) (by decide) (by decide +kernel) (by rw [bit8]; decide)
  have bit16 : two.bi_valid.toInt = 16 := by rw [bit8] at valid2; exact valid2
  have noPending : two.pending = 0 := pending2.trans (pending1.trans start.pending)
  have room : 8 * two.pending.toNat + two.bi_valid.toInt.toNat ≤ 8 * buf.size := by
    rw [noPending, bit16]
    change 16 ≤ 8 * buf.size
    have lo := tree2.base.lit_lo
    have size := tree2.base.size
    omega
  obtain ⟨produced, after, z', result, written, remaining, run, goodA, buffersA, _account, _sizes, _storage,
    copied, count, _low, valid, _fields, bytes, pendingBits, bits⟩ :=
    flush_pending_raw_bits good2 tree2 buffers2 pointer cursor2 room
  have amount : produced = 2 := by rw [noPending, bit16, available] at copied; exact copied
  have emptyPending : result.pending.toNat = 0 := by
    rw [noPending, bit16, amount] at count
    change result.pending.toNat + 2 = 2 at count
    omega
  have emptyValid : result.bi_valid.toInt.toNat = 0 := by rw [bit16] at valid; exact valid
  have noRemaining : remaining = [] := pending_bits_empty pendingBits emptyPending emptyValid
  have before : Zlib.Trees.Proofs.Out.outBits buf d = [] := by
    simp [Zlib.Trees.Proofs.Out.outBits, Zlib.Trees.Proofs.Out.bytesBits, Zlib.Trees.Proofs.Out.natBits,
      start.pending, start.bits]
  have emitted : ZlibF.Spec.bytesToBits written = ZlibF.Spec.bytesToBits [0xa5, 0x3c] := by
    rw [noRemaining, List.append_nil, bits2, bits1, before] at bits
    simp only [List.nil_append] at bits
    have concrete : Zlib.Trees.Proofs.Out.natBits (Zlib.Trees.Proofs.Out.v16 0xa5) (8 : Int32).toInt.toNat ++
        Zlib.Trees.Proofs.Out.natBits (Zlib.Trees.Proofs.Out.v16 0x3c) (8 : Int32).toInt.toNat =
        ZlibF.Spec.bytesToBits [0xa5, 0x3c] := by decide +kernel
    exact bits.trans concrete
  have actualBytes : written = [0xa5, 0x3c] := by
    have left : written <+: [0xa5, 0x3c] := by
      apply ZlibF.Spec.Api.Proofs.bytesToBits_prefix_reflect
      rw [emitted]
      exact List.prefix_refl _
    have right : [0xa5, 0x3c] <+: written := by
      apply ZlibF.Spec.Api.Proofs.bytesToBits_prefix_reflect
      rw [emitted]
      exact List.prefix_refl _
    exact left.eq_of_length_le right.length_le
  refine ⟨initialized, after, z', result, ⟨z, d, initRun, start⟩, ?_, goodA, buffersA, ?_, emptyPending, emptyValid⟩
  · simp only [bind_app, run1, run2, run]
  · rw [amount, actualBytes, pointer] at bytes
    exact bytes

/-- A real eight-bit send reaches the middle-byte branch of bi_flush.
The caller receives one byte and retains one byte of output capacity. -/
theorem default_pending_byte_witness :
    ∃ initialized after z' result,
      (∃ z d, C.run (deflateInit_ (some (.tab 0)) Z_DEFAULT_COMPRESSION (.ref (.blk 1) 0) 112)
        loopWitnessHeap = .ok (Z_OK, initialized) ∧ EngineStart initialized (.tab 0) 2 z d) ∧
      (do Zlib.Trees.send_bits (some (.tab 2)) 0xa5 8
          flush_pending (some (.tab 0))) initialized = .ok ((), after) ∧
      DGood after (.tab 0) 2 z' result ∧ StreamBuffers after (.tab 0) ∧
      Bytes after (.ref (.blk 1) 0) 1 [0xa5] ∧ result.pending.toNat = 0 ∧ result.bi_valid.toInt.toNat = 0 := by
  obtain ⟨initialized, z, d, initRun, start, buffers, pointer, available⟩ := default_pending_output_entry
  obtain ⟨oldD, pb, buf, trees⟩ := start.good.trees
  have stateEq : oldD = d := Option.some.inj (trees.base.dstate.symm.trans start.good.live.hs)
  subst oldD
  obtain ⟨one, run1, good1, tree1, buffers1, pending1, valid1, cursor1, bits1⟩ :=
    buffered_bits_publish_state start.good trees buffers start.pendingOut 0xa5 8
      (by decide) (by decide) (by decide +kernel) (by rw [start.bits]; decide)
  have bit8 : one.bi_valid.toInt = 8 := by rw [start.bits] at valid1; exact valid1
  have noPending : one.pending = 0 := pending1.trans start.pending
  have room : 8 * one.pending.toNat + one.bi_valid.toInt.toNat ≤ 8 * buf.size := by
    rw [noPending, bit8]
    change 8 ≤ 8 * buf.size
    have lo := tree1.base.lit_lo
    have size := tree1.base.size
    omega
  obtain ⟨produced, after, z', result, written, remaining, run, goodA, buffersA, _account, _sizes, _storage,
    copied, count, _low, valid, _fields, bytes, pendingBits, bits⟩ :=
    flush_pending_raw_bits good1 tree1 buffers1 pointer cursor1 room
  have amount : produced = 1 := by rw [noPending, bit8, available] at copied; exact copied
  have emptyPending : result.pending.toNat = 0 := by
    rw [noPending, bit8, amount] at count
    change result.pending.toNat + 1 = 1 at count
    omega
  have emptyValid : result.bi_valid.toInt.toNat = 0 := by rw [bit8] at valid; exact valid
  have noRemaining : remaining = [] := pending_bits_empty pendingBits emptyPending emptyValid
  have before : Zlib.Trees.Proofs.Out.outBits buf d = [] := by
    simp [Zlib.Trees.Proofs.Out.outBits, Zlib.Trees.Proofs.Out.bytesBits, Zlib.Trees.Proofs.Out.natBits,
      start.pending, start.bits]
  have emitted : ZlibF.Spec.bytesToBits written = ZlibF.Spec.bytesToBits [0xa5] := by
    rw [noRemaining, List.append_nil, bits1, before] at bits
    simp only [List.nil_append] at bits
    have concrete : Zlib.Trees.Proofs.Out.natBits (Zlib.Trees.Proofs.Out.v16 0xa5) (8 : Int32).toInt.toNat =
        ZlibF.Spec.bytesToBits [0xa5] := by decide +kernel
    exact bits.trans concrete
  have actualBytes : written = [0xa5] := by
    have left : written <+: [0xa5] := by
      apply ZlibF.Spec.Api.Proofs.bytesToBits_prefix_reflect
      rw [emitted]
      exact List.prefix_refl _
    have right : [0xa5] <+: written := by
      apply ZlibF.Spec.Api.Proofs.bytesToBits_prefix_reflect
      rw [emitted]
      exact List.prefix_refl _
    exact left.eq_of_length_le right.length_le
  refine ⟨initialized, after, z', result, ⟨z, d, initRun, start⟩, ?_, goodA, buffersA, ?_, emptyPending, emptyValid⟩
  · simp only [bind_app, run1, run]
  · rw [amount, actualBytes, pointer] at bytes
    exact bytes

end Zlib.Deflate.Engine.Proofs
