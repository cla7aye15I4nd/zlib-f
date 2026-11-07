import ZlibF.Proof.«deflate.c.engine.trailer-state»
import ZlibF.Proof.«deflate.c.engine.public-pending-idle»

/-! # Default zlib trailer publication and its one-time wrapper transition -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt)
set_option autoImplicit false

/-- The final source statements, retaining all wrapper and return branches. -/
def publicFinishTail (strm : ZStreamPtr) (s : DeflateStatePtr) (flush : Int32) : M Int32 := do
  -- if (flush != Z_FINISH) return Z_OK; if (s->wrap <= 0) return Z_STREAM_END;
  if flush != Z_FINISH then return Z_OK
  if (← rd s (·.wrap)) ≤ 0 then return Z_STREAM_END
  -- Write the trailer
  if (← rd s (·.wrap)) == 2 then
    let a ← zrd strm (·.adler)
    put_byte s (a &&& 0xff).toUInt8
    put_byte s ((a >>> 8) &&& 0xff).toUInt8
    put_byte s ((a >>> 16) &&& 0xff).toUInt8
    put_byte s ((a >>> 24) &&& 0xff).toUInt8
    let t ← zrd strm (·.total_in)
    put_byte s (t &&& 0xff).toUInt8
    put_byte s ((t >>> 8) &&& 0xff).toUInt8
    put_byte s ((t >>> 16) &&& 0xff).toUInt8
    put_byte s ((t >>> 24) &&& 0xff).toUInt8
  else
    zlibTrailer strm s
  flush_pending strm
  -- if (s->wrap > 0) s->wrap = -s->wrap; /* write the trailer only once! */
  let w ← rd s (·.wrap)
  if w > 0 then
    let nw ← ineg w
    wr s (fun d => { d with wrap := nw })
  -- return s->pending != 0 ? Z_OK : Z_STREAM_END;
  return if (← rd s (·.pending)) != 0 then Z_OK else Z_STREAM_END

/-- The actual post-header source reaches its finish tail after the strategy
has completed. No block-compressor contract is an assumption. -/
theorem public_finish_source {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (hz : r.get h = some z) (hd : h.dstates ds = some d)
    (status : d.status = FINISH_STATE) (empty : z.avail_in = 0) (look : d.lookahead = 0) :
    publicDataTail (some r) (some (.tab ds)) Z_FINISH h =
      publicFinishTail (some r) (some (.tab ds)) Z_FINISH h := by
  unfold publicDataTail publicFinishTail zlibTrailer
  simp only [bind_app, pure_app, rdD_eq, hd, status,
    show (FINISH_STATE == GZIP_STATE) = false from rfl,
    show (FINISH_STATE == EXTRA_STATE) = false from rfl,
    show (FINISH_STATE == NAME_STATE) = false from rfl,
    show (FINISH_STATE == COMMENT_STATE) = false from rfl,
    show (FINISH_STATE == HCRC_STATE) = false from rfl,
    Bool.false_eq_true, ite_false, ldDeflateState_tab hd, zrd_eq, hz,
    empty, look, show ((0 : UInt32) != 0) = false from rfl, BEq.rfl, Bool.not_true,
    show (FINISH_STATE != FINISH_STATE) = false from rfl,
    show (Z_FINISH != Z_FINISH) = false from rfl, Bool.and_false, Bool.false_or]
  simp only [M_bind_assoc, M_pure_bind, Zlib.Trees.Proofs.merge_ite_bind, bind_app, pure_app, rdD_eq, hd]

/-- After the real trailer is queued, the wrapper changes from 1 to -1.
Its record update retains every representation and caller-buffer fact. -/
theorem trailer_wrap_good {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (good : DGood h r ds z d) (wrap : d.wrap = 1) :
    DGood (setD h ds { d with wrap := -1 }) r ds z { d with wrap := -1 } := by
  have inv : DStInv h ds { d with wrap := -1 } :=
    { good.inv with
      wrap_lo := by change -2 ≤ (-1 : Int32).toInt; decide
      wrap_hi := by change (-1 : Int32).toInt ≤ 2; decide
      blocks := good.inv.blocks_keys rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl }
  exact good.setD' rfl good.live.status inv (by trkeep)

/-- The one-time wrapper flag update retains every readable byte view. -/
theorem trailer_wrap_bytes {h : Heap} {ds : Nat} {d : DeflateState}
    {ptr : BPtr} {n : Nat} {xs : List UInt8} (state : h.dstates ds = some d)
    (bytes : Bytes h ptr n xs) : Bytes (setD h ds { d with wrap := -1 }) ptr n xs := by
  rcases bytes with null | ⟨ref, off, array, pointer, get, bound, value⟩
  · exact Or.inl null
  · exact Or.inr ⟨ref, off, array, pointer,
      (byte_view_setD_depth (result := { d with wrap := -1 }) state rfl ref).trans get, bound, value⟩

/-- The actual zlib trailer stores, pending copy and wrapper negation
compose on the same heap. Arbitrary raw output capacity includes zero
and partial trailers. Written bytes plus remaining PendingBits are exactly
the independent big-endian checksum bytes. The final block's pending bytes
and residual bits must have drained; strategy completion is separate. -/
theorem zlib_trailer_publish {h : Heap} {r : ZStreamRef} {ds pb ob oo : Nat}
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
      ZlibF.Spec.bytesToBits written ++ remaining = ZlibF.Spec.bytesToBits (ZlibF.Spec.be32 z.adler.toNat) := by
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
  exact ⟨produced, final, z', { result with wrap := -1 }, written, remaining, run,
    goodF, buffersF, account, (sizesE.trans sizesM).trans sizesF,
    (storageE.trans storageM).trans storageF, amount, left, rfl, bitsM, fieldsF,
    bytesF, pendingF, outputM.trans word⟩

end Zlib.Deflate.Engine.Proofs
