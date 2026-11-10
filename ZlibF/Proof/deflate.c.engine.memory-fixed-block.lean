import ZlibF.Proof.«deflate.c.engine.memory-fixed-payload»
import ZlibF.Proof.«deflate.c.engine.fixed-block»
import ZlibF.Proof.«deflate.c.engine.block-clear-preserve»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
open Zlib.Trees.Proofs.Out (TreesInvAt fixedTag)
set_option autoImplicit false

/-- Actual fixed emission, init_block and optional final windup preserve
all logical output and reset data using the actual allocation extent. -/
theorem memory_fixed_block_ready_frame {h : Heap} {r : ZStreamRef} {ds pb ob base : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8} {xs : List Symbol} {input : Nat → UInt8}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (cursor : d.pending_out = d.pending_buf)
    (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7)
    (count : d.sym_next.toNat = 3 * xs.length) (packed : PackedSymbols buf d.lit_bufsize.toNat xs)
    (valid : ∀ s ∈ xs, s.Valid) (trace : Trace input base xs) (last : Bool) :
    ∃ after result next payload padding,
      (do Zlib.Trees.Proofs.fixedBlockPayload (some (.tab ds)) (if last then 1 else 0)
          Zlib.Trees.Proofs.flushBlockTail (some (.tab ds)) (if last then 1 else 0)) h = .ok ((), after) ∧
      DGood after r ds z result ∧ TreesInvAt after ds result pb next ∧ StreamBuffers after r ∧
      ByteSizes h after ∧ OutputStorage h after r ds pb ob ∧ SymbolLedger next result [] ∧ BlockInit.BlockClear result ∧ BlockOutputFrame d result ∧
      next.size = buf.size ∧ result.pending.toNat ≤ next.size ∧
      (last = false → result.pending.toNat + 2 ≤ next.size) ∧ result.pending_out = result.pending_buf ∧
      8 * result.pending.toNat + result.bi_valid.toInt.toNat ≤ 8 * next.size ∧
      (last = true → result.bi_valid.toInt = 0 ∧ result.bi_buf = 0) ∧
      padding.length < 8 ∧ (last = false → padding = []) ∧
      Zlib.Trees.Proofs.Out.outBits next result = Zlib.Trees.Proofs.Out.outBits buf d ++
        (fixedTag last ++ payload ++ padding) ∧
      ∀ suffix, ZlibF.Spec.Body [] 1 (inputPrefix input base) (payload ++ suffix) suffix
        (inputPrefix input (base + represented xs)) := by
  obtain ⟨tagged, headerRun, goodH, treesH, buffersH, sizesH, storageH, diffH,
    pendingH, bitsH, cursorH, outputH⟩ := fixed_header_engine (ob := ob) good trees buffers cursor pending bits last
  obtain ⟨_p, _a, _v, _u, fieldsH⟩ := diffH
  obtain ⟨emittedBuf, emitted, payloadRun, goodE, treesE, buffersE, sizesE, storageE,
    fieldsE, sizeE, pendingE, cursorE, roomE, outputE⟩ :=
    memory_fixed_payload_ready_fields (ob := ob) goodH treesH buffersH cursorH
      pendingH bitsH
      (by rw [fieldsH]; exact count) (by rw [fieldsH]; exact packed) valid
  let payload := xs.flatMap (fun s => Zlib.Trees.Proofs.Out.payloadSymBits
      Zlib.Trees.Proofs.fixedLiteralWords Zlib.Trees.Proofs.fixedDistanceWords (s.distance, s.value)) ++
    Zlib.Trees.Proofs.Out.codeBits Zlib.Trees.Proofs.fixedLiteralWords 256
  have emittedBits : Zlib.Trees.Proofs.Out.outBits emittedBuf emitted =
      Zlib.Trees.Proofs.Out.outBits buf d ++ (fixedTag last ++ payload) := by
    rw [outputE, outputH, List.append_assoc]
  obtain ⟨a1, a2, a3, reset, resetRun, goodR, treesR, buffersR, sizesR, storageR, resetFields, ledgerR, resetBits⟩ :=
    init_block_engine (ob := ob) goodE treesE buffersE
  obtain ⟨clearState, clearRun, _clearGood, _clearTrees, _clearBuffers, _clearSizes,
      _clearStorage, _clearLedger, clear, _clearBits⟩ := init_block_clear_engine (ob := ob) goodE treesE buffersE
  have same : clearState = reset := Zlib.Trees.Proofs.same_record_of_runs clearRun resetRun
  have clearR : BlockInit.BlockClear reset := same ▸ clear
  have frameR : BlockOutputFrame d reset := by
    obtain ⟨_, _, _, _, emittedFields⟩ := fieldsE
    unfold BlockOutputFrame
    rw [resetFields, emittedFields, fieldsH]
    rfl
  have pendingR : reset.pending.toNat + 2 ≤ emittedBuf.size := by rw [resetFields]; exact pendingE
  have cursorR : reset.pending_out = reset.pending_buf := by rw [resetFields]; exact cursorE
  have bitsR : Zlib.Trees.Proofs.Out.outBits emittedBuf reset =
      Zlib.Trees.Proofs.Out.outBits buf d ++ (fixedTag last ++ payload) := resetBits.trans emittedBits
  have highR := treesR.run.bi_hi
  have roomR : 8 * reset.pending.toNat + reset.bi_valid.toInt.toNat ≤ 8 * emittedBuf.size := by
    omega
  have sizes := (sizesH.trans sizesE).trans sizesR
  have storage := (storageH.trans storageE).trans storageR
  have grammar : ∀ suffix, ZlibF.Spec.Body [] 1 (inputPrefix input base) (payload ++ suffix) suffix
      (inputPrefix input (base + represented xs)) := by
    intro suffix
    exact ZlibF.Spec.Body.fixed (Zlib.Trees.Proofs.Out.fixed_payload_grammar trace suffix)
  cases last with
  | false =>
    change Zlib.Trees.Proofs.fixedBlockHeader (some (.tab ds)) 0 h = .ok ((), setD h ds tagged) at headerRun
    refine ⟨_, reset, emittedBuf, payload, [], ?_, goodR, treesR, buffersR, sizes, storage, ledgerR, clearR, frameR,
      sizeE, by omega, (by intro _; exact pendingR), cursorR, roomR, by simp, by decide, by simp, ?_, grammar⟩
    · unfold Zlib.Trees.Proofs.fixedBlockPayload Zlib.Trees.Proofs.flushBlockTail
      simp only [bind_app, headerRun, payloadRun, resetRun,
        show ((0 : Int32) != 0) = false from rfl, Bool.false_eq_true, ite_false, pure_app]
    · simpa only [List.append_nil] using bitsR
  | true =>
    change Zlib.Trees.Proofs.fixedBlockHeader (some (.tab ds)) 1 h = .ok ((), setD h ds tagged) at headerRun
    obtain ⟨next, result, windupRun, goodA, treesA, buffersA, sizesA, storageA, fieldsA,
      sizeA, pendingA, zeroA, wordA, cursorA, outputA⟩ :=
      windup_engine (ob := ob) goodR treesR buffersR cursorR roomR
    let padding := List.replicate ((8 - reset.bi_valid.toInt.toNat % 8) % 8) false
    have size : next.size = buf.size := sizeA.trans sizeE
    have upper : result.pending.toNat ≤ next.size := by omega
    have room : 8 * result.pending.toNat + result.bi_valid.toInt.toNat ≤ 8 * next.size := by
      rw [zeroA]
      change 8 * result.pending.toNat ≤ 8 * next.size
      omega
    refine ⟨_, result, next, payload, padding, ?_, goodA, treesA, buffersA, sizes.trans sizesA,
      storage.trans storageA, empty_ledger_bits ledgerR fieldsA, clearR.bits fieldsA, frameR.bits fieldsA, size, upper, (by simp), cursorA, room,
      by intro _; exact ⟨zeroA, wordA⟩, ?_, by simp, ?_, grammar⟩
    · unfold Zlib.Trees.Proofs.fixedBlockPayload Zlib.Trees.Proofs.flushBlockTail
      simp only [bind_app, headerRun, payloadRun, resetRun,
        show ((1 : Int32) != 0) = true from rfl, ite_true, windupRun]
    · simpa only [padding, List.length_replicate] using Nat.mod_lt (8 - reset.bi_valid.toInt.toNat % 8) (by decide : 0 < 8)
    · rw [outputA, bitsR]
      simp only [List.append_assoc, padding]

end Zlib.Deflate.Engine.Proofs
#print axioms Zlib.Deflate.Engine.Proofs.memory_fixed_block_ready_frame
