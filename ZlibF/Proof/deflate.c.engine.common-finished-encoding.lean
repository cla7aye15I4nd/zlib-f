import ZlibF.Proof.«deflate.c.engine.pending-complete-encoding»
import ZlibF.Proof.«deflate.c.engine.common-header-encoding»
import ZlibF.Proof.«deflate.c.engine.input-snapshot-controls»
import ZlibF.Proof.«deflate.c.engine.public-finishing-phase»

/-! # Completed raw and wrapped meaning across finishing calls -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- After the final block, published bytes and the exact pending suffix
already form a complete stream. Wrapper 1 still needs the zlib trailer;
wrapper -1 already includes it. The ordinary initialization invariant has
its separate working/header alternatives. Actual completion establishes
this finishing alternative; it is not a callee contract. -/
structure CommonFinishedEncoding (h : Heap) (d : DeflateState) (headerLevel : Int32) (accepted published : List UInt8) : Prop where
  bits : d.bi_valid.toInt = 0
  data : ∃ tailBytes, Bytes h d.pending_out d.pending.toNat tailBytes ∧
    ((d.wrap = 1 ∧ ZlibF.Spec.Deflate.Valid accepted (published ++ tailBytes)) ∨
     (d.wrap = -1 ∧ ZlibF.Spec.Zlib.Valid accepted (levelHeaderPrefix headerLevel ++ published ++ tailBytes)))

/-- Recording the next request or exhausted-output marker retains exact
completed bytes and their independent meaning. -/
theorem CommonFinishedEncoding.last_flush {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState} {headerLevel : Int32} {accepted published : List UInt8}
    (encoding : CommonFinishedEncoding h d headerLevel accepted published) (good : DGood h r ds z d) (flush : Int32) :
    CommonFinishedEncoding (setD h ds { d with last_flush := flush }) { d with last_flush := flush } headerLevel accepted published := by
  obtain ⟨tailBytes, data, meaning⟩ := encoding.data
  exact ⟨encoding.bits, tailBytes,
    caller_bytes_setD_depth (result := { d with last_flush := flush }) good.live.hs rfl data, meaning⟩

/-- Legal caller replacement preserves the exact private completed suffix;
previous output remains mathematical history even when its array is reused. -/
theorem CommonFinishedEncoding.rebuffer {h g : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState} {headerLevel : Int32} {accepted published : List UInt8}
    (encoding : CommonFinishedEncoding h d headerLevel accepted published) (good : DGood h r ds z d)
    (edit : Rebuffer h g r) : CommonFinishedEncoding g d headerLevel accepted published := by
  obtain ⟨tailBytes, data, meaning⟩ := encoding.data
  have pending : PendingBits h d (ZlibF.Spec.bytesToBits tailBytes) :=
    ⟨tailBytes, data, by simp only [encoding.bits, Int.toNat_zero, List.range_zero, List.map_nil, List.append_nil]⟩
  obtain ⟨nextBytes, dataA, same⟩ := rebuffer_pending_bits good edit pending
  have wire : ZlibF.Spec.bytesToBits tailBytes = ZlibF.Spec.bytesToBits nextBytes := by
    simpa only [encoding.bits, Int.toNat_zero, List.range_zero, List.map_nil, List.append_nil] using same
  have equal := ZlibF.Math.DeflateEncoding.encoded_bytes_injective wire
  rw [← equal] at dataA
  exact ⟨encoding.bits, tailBytes, dataA, meaning⟩

/-- Once the actual completed wrapper's pending count reaches zero, all
published bytes already satisfy independent zlib validity. -/
theorem CommonFinishedEncoding.drained {h : Heap} {d : DeflateState} {headerLevel : Int32} {accepted published : List UInt8}
    (encoding : CommonFinishedEncoding h d headerLevel accepted published) (wrap : d.wrap = -1) (empty : d.pending = 0) :
    ZlibF.Spec.Zlib.Valid accepted (levelHeaderPrefix headerLevel ++ published) := by
  obtain ⟨tailBytes, data, meaning⟩ := encoding.data
  have length := caller_bytes_length data
  have nil : tailBytes = [] := List.eq_nil_iff_length_eq_zero.mpr (by simpa only [empty, UInt64.toNat_zero] using length)
  rcases meaning with ⟨impossible, _raw⟩ | ⟨_wrap, valid⟩
  · rw [wrap] at impossible
    cases (show (-1 : Int32) ≠ 1 from by decide) impossible
  · simpa only [nil, List.append_nil] using valid

/-- Every actual pending copy retains completed raw or wrapper meaning,
including partial output, zero capacity and advanced pending cursors. -/
theorem flush_pending_common_finished_encoding {h : Heap} {r : ZStreamRef} {ds ob oo : Nat}
    {z : ZStream} {d : DeflateState} {headerLevel : Int32} {accepted published : List UInt8}
    (good : DGood h r ds z d) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo) (encoding : CommonFinishedEncoding h d headerLevel accepted published) :
    ∃ pb produced after z' result written,
      d.pending_buf = .ref (.blk pb) 0 ∧
      flush_pending (some r) h = .ok ((), after) ∧ DGood after r ds z' result ∧ StreamBuffers after r ∧
      StreamAccounting z z' 0 produced ∧ OutputStorage h after r ds pb ob ∧
      produced = min d.pending.toNat z.avail_out.toNat ∧ result.pending.toNat + produced = d.pending.toNat ∧
      result = { d with pending := result.pending, pending_out := result.pending_out } ∧
      (0 < produced → result.pending.toNat = 0 → result.pending_out = result.pending_buf) ∧
      Bytes after z.next_out produced written ∧ CommonFinishedEncoding after result headerLevel accepted (published ++ written) ∧
      z'.adler = z.adler := by
  obtain ⟨tailBytes, data, meaning⟩ := encoding.data
  obtain ⟨pb, produced, after, z', result, written, remaining, base, run, goodA, buffersA, account,
      storage, amount, count, fields, reset, bytesA, pendingA, splitBytes, adlerA⟩ :=
    flush_pending_complete_bytes good buffers pointer encoding.bits data
  have encodingA : CommonFinishedEncoding after result headerLevel accepted (published ++ written) := by
    refine ⟨by rw [fields]; exact encoding.bits, remaining, pendingA, ?_⟩
    rcases meaning with ⟨wrap, valid⟩ | ⟨wrap, valid⟩
    · exact Or.inl ⟨by rw [fields]; exact wrap, by simpa only [List.append_assoc, splitBytes] using valid⟩
    · exact Or.inr ⟨by rw [fields]; exact wrap, by simpa only [List.append_assoc, splitBytes] using valid⟩
  exact ⟨pb, produced, after, z', result, written, base, run, goodA, buffersA, account, storage,
    amount, count, fields, reset, bytesA, encodingA, adlerA⟩

end Zlib.Deflate.Engine.Proofs
