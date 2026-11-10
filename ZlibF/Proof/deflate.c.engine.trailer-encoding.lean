import ZlibF.Proof.«deflate.c.engine.trailer-output»
import ZlibF.Proof.«deflate.c.engine.pending-checksum»
import ZlibF.Proof.«deflate.c.engine.input-slices»
import ZlibF.Math.DeflateZlibEncoding

/-! # Actual trailer publication has exact byte meaning -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt)
set_option autoImplicit false

/-- The actual zlib trailer stores, pending copy and wrapper negation
compose on the same heap. Arbitrary raw output capacity includes zero
and partial trailers. Written bytes plus remaining PendingBits are exactly
the independent big-endian checksum bytes. The final block's pending bytes
and residual bits must have drained; strategy completion is separate. -/
theorem zlib_trailer_publish_encoding {h : Heap} {r : ZStreamRef} {ds pb ob oo : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo) (wrap : d.wrap = 1)
    (pending : d.pending = 0) (cursor : d.pending_out = d.pending_buf) (bits : d.bi_valid.toInt = 0) :
    ∃ produced after z' result written remaining,
      publicFinishTail (some r) (some (.tab ds)) Z_FINISH h =
        .ok ((if result.pending != 0 then Z_OK else Z_STREAM_END), after) ∧
      DGood after r ds z' result ∧ StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧
      ByteSizes h after ∧ OutputStorage h after r ds pb ob ∧
      produced = min 4 z.avail_out.toNat ∧ result.pending.toNat + produced = 4 ∧
      result.wrap = -1 ∧ result.bi_valid.toInt = 0 ∧
      result = { d with pending := result.pending, pending_out := result.pending_out, wrap := -1 } ∧
      Bytes after z.next_out produced written ∧ PendingBits after result remaining ∧
      ZlibF.Spec.bytesToBits written ++ remaining = ZlibF.Spec.bytesToBits (ZlibF.Spec.be32 z.adler.toNat) ∧
      z'.adler = z.adler ∧ ∃ tailBytes,
        Bytes after result.pending_out result.pending.toNat tailBytes ∧
        written ++ tailBytes = ZlibF.Spec.be32 z.adler.toNat ∧
        (result.pending = 0 → written = ZlibF.Spec.be32 z.adler.toNat) := by
  let next := zlibTrailerBuffer buf z.adler
  let emitted := { d with pending := 4 }
  let ready := setD (Zlib.Trees.Proofs.Out.setB h pb next) ds emitted
  obtain ⟨write, goodE, treesE, buffersE, sizesE, storageE, values⟩ :=
    zlib_trailer_write (ob := ob) good trees buffers pending cursor
  obtain ⟨output, getOutput, writable, outputBound, outside⟩ := caller_raw_output goodE buffersE pointer
  have separate : ob ≠ pb := by
    intro same
    subst ob
    exact outside (Or.inr (Or.inr (Or.inr (Or.inr treesE.base.pbuf))))
  obtain ⟨produced, middle, z', result, written, remaining, flush, goodM, account, sizesM,
    amount, left, fields, bytesM, pendingM, outputM, storageM⟩ :=
    flush_pending_low_raw_bits_storage goodE treesE (by change d.bi_valid.toInt < 8; omega)
      cursor pointer getOutput writable separate outputBound
  have adlerM := flush_pending_low_run_adler goodE buffersE pointer
    (by change d.bi_valid.toInt < 8; omega) flush goodM.live.hz account
  have wrapM : result.wrap = 1 := by rw [fields]; exact wrap
  have bitsM : result.bi_valid.toInt = 0 := by rw [fields]; exact bits
  let final := setD middle ds { result with wrap := -1 }
  have goodF := trailer_wrap_good goodM wrapM
  have sizesF := block_record_sizes (result := { result with wrap := -1 }) goodM.live.hs rfl
  have owned := stream_owned_keys goodM goodF rfl rfl rfl rfl
  have buffersM := stream_buffers_sizes goodE.live.hz goodM.live.hz buffersE sizesM
    (stream_owned_keys goodE goodM (by rw [fields]) (by rw [fields]) (by rw [fields]) (by rw [fields])) account
  have buffersF := stream_buffers_sizes goodM.live.hz goodF.live.hz buffersM sizesF owned (stream_accounting_zero z')
  obtain ⟨w, p, q, b, blocks⟩ := goodM.inv.blocks
  have key : b = pb := by
    have base : result.pending_buf = .ref (.blk pb) 0 := by rw [fields]; exact treesE.base.pbuf
    simpa only [base, Ptr.ref.injEq, BRef.blk.injEq, and_true] using blocks.pbuf.symm
  subst b
  obtain ⟨bufM, getM, _sizeM⟩ := blocks.ba
  have storageF := output_bits_storage (r := r) (ob := ob) (result := { result with wrap := -1 })
    (next := bufM) goodM.live.hs getM
  rw [Zlib.Trees.Proofs.Out.setB_self getM] at storageF
  have bytesF := trailer_wrap_bytes goodM.live.hs bytesM
  have pendingF : PendingBits final { result with wrap := -1 } remaining := by
    obtain ⟨data, read, equal⟩ := pendingM
    exact ⟨data, trailer_wrap_bytes goodM.live.hs read, equal⟩
  have fieldsF : { result with wrap := -1 } =
      { d with pending := result.pending, pending_out := result.pending_out, wrap := -1 } := by rw [fields]
  have size : next.size = buf.size := by simp [next, zlibTrailerBuffer]
  have room : 4 ≤ next.size := by have sz := trees.base.size; have lo := trees.base.lit_lo; omega
  have word : Zlib.Trees.Proofs.Out.outBits next emitted =
      ZlibF.Spec.bytesToBits (ZlibF.Spec.be32 z.adler.toNat) := by
    unfold Zlib.Trees.Proofs.Out.outBits
    change Zlib.Trees.Proofs.Out.bytesBits next 4 ++
      Zlib.Trees.Proofs.Out.natBits d.bi_buf.toNat d.bi_valid.toInt.toNat = _
    rw [bytes_bits_format next 4 room]
    change ZlibF.Spec.bytesToBits (next.toList.take 4) ++
      Zlib.Trees.Proofs.Out.natBits d.bi_buf.toNat d.bi_valid.toInt.toNat = _
    rw [values, zlib_trailer_word, bits]
    rfl
  have run : publicFinishTail (some r) (some (.tab ds)) Z_FINISH h =
      .ok ((if result.pending != 0 then Z_OK else Z_STREAM_END), final) := by
    have getW : rd (some (.tab ds)) (·.wrap) h = .ok (1, h) := by
      simp only [rdD_eq, good.live.hs, wrap]
    have getWM : rd (some (.tab ds)) (·.wrap) middle = .ok (1, middle) := by
      simp only [rdD_eq, goodM.live.hs, wrapM]
    have negative : ineg (1 : Int32) = pure (-1) := by rfl
    unfold publicFinishTail
    simp only [bind_app, pure_app, show (Z_FINISH != Z_FINISH) = false from rfl,
      Bool.false_eq_true, ite_false, getW,
      show ¬ (1 : Int32) ≤ 0 from by decide, show ((1 : Int32) == 2) = false from rfl,
      write, flush, getWM, show (1 : Int32) > 0 from by decide,
      ite_true, negative, wrD_eq, goodM.live.hs]
    simp only [bind_app, pure_app, rdD_eq, setD_dstates_same]
    rfl
  have wire := outputM.trans word
  have pendingCopy := pendingF
  obtain ⟨tailBytes, tailData, tailEq⟩ := pendingCopy
  have remainingEq : remaining = ZlibF.Spec.bytesToBits tailBytes := by
    simpa only [bitsM, Int.toNat_zero, List.range_zero, List.map_nil, List.append_nil] using tailEq
  have splitBytes : written ++ tailBytes = ZlibF.Spec.be32 z.adler.toNat := by
    apply ZlibF.Math.DeflateEncoding.encoded_bytes_injective
    simpa only [ZlibF.Spec.bytesToBits, List.flatMap_append, remainingEq] using wire
  have completed : result.pending = 0 → written = ZlibF.Spec.be32 z.adler.toNat := by
    intro empty
    have length := caller_bytes_length tailData
    have nil : tailBytes = [] := List.eq_nil_iff_length_eq_zero.mpr (by simpa only [empty, UInt64.toNat_zero] using length)
    simpa only [nil, List.append_nil] using splitBytes
  exact ⟨produced, final, z', { result with wrap := -1 }, written, remaining, run,
    goodF, buffersF, account, (sizesE.trans sizesM).trans sizesF,
    (storageE.trans storageM).trans storageF, amount, left, rfl, bitsM, fieldsF,
    bytesF, pendingF, wire, adlerM, tailBytes, tailData, splitBytes, completed⟩

/-- Actual trailer stores and arbitrary partial publication retain a
complete independent zlib stream in the published bytes plus the exact
pending suffix. When pending is empty, the published bytes alone are that
stream. Raw validity and checksum meaning are mathematical history facts
about the same accepted input, not assumptions about a C callee. -/
theorem zlib_trailer_publish_valid {h : Heap} {r : ZStreamRef} {ds pb ob oo : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8} {accepted raw : List UInt8}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo) (wrap : d.wrap = 1)
    (pending : d.pending = 0) (cursor : d.pending_out = d.pending_buf) (bits : d.bi_valid.toInt = 0)
    (checksum : z.adler = (ZlibF.Spec.adler32 accepted).toUInt64)
    (rawMeaning : ZlibF.Spec.Deflate.Valid accepted raw) :
    ∃ produced after z' result written tailBytes,
      publicFinishTail (some r) (some (.tab ds)) Z_FINISH h =
        .ok ((if result.pending != 0 then Z_OK else Z_STREAM_END), after) ∧
      DGood after r ds z' result ∧ StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧
      OutputStorage h after r ds pb ob ∧ result.wrap = -1 ∧ result.bi_valid.toInt = 0 ∧
      Bytes after z.next_out produced written ∧ Bytes after result.pending_out result.pending.toNat tailBytes ∧
      written ++ tailBytes = ZlibF.Spec.be32 (ZlibF.Spec.adler32 accepted).toNat ∧
      z'.adler = (ZlibF.Spec.adler32 accepted).toUInt64 ∧
      ZlibF.Spec.Zlib.Valid accepted ([120,156] ++ raw ++ written ++ tailBytes) ∧
      (result.pending = 0 → ZlibF.Spec.Zlib.Valid accepted ([120,156] ++ raw ++ written)) := by
  obtain ⟨produced, after, z', result, written, _remaining, run, goodA, buffersA, accountA,
      _sizes, storageA, _amount, _left, wrapA, bitsA, _fields, bytesA, _pendingA, _wire,
      adlerA, tailBytes, tailData, splitBytes, completed⟩ :=
    zlib_trailer_publish_encoding good trees buffers pointer wrap pending cursor bits
  have trailer : ZlibF.Spec.be32 z.adler.toNat = ZlibF.Spec.be32 (ZlibF.Spec.adler32 accepted).toNat := by
    simp only [checksum, UInt32.toNat_toUInt64]
  have valid := ZlibF.Math.DeflateEncoding.raw_valid_zlib_grammar rawMeaning
  refine ⟨produced, after, z', result, written, tailBytes, run, goodA, buffersA, accountA,
    storageA, wrapA, bitsA, bytesA, tailData, splitBytes.trans trailer, adlerA.trans checksum, ?_, ?_⟩
  · simpa only [List.append_assoc, splitBytes, trailer] using valid
  · intro empty
    rw [completed empty, trailer]
    exact valid

end Zlib.Deflate.Engine.Proofs
