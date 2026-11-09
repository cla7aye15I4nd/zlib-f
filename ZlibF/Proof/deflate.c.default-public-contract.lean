import ZlibF.Proof.«deflate.c.engine.generic-basic-history-full-contract»
import ZlibF.Proof.«deflate.c.engine.generic-completion-lifetime»
import ZlibF.Proof.«deflate.c.default-core»

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Spec.Public.Proofs
set_option autoImplicit false

/-- `int deflate(z_streamp strm, int flush)`.
The original public Goal.deflate conclusion holds on actual basic default
request histories: successful default Init, legal caller rebuffering and
actual returning deflate calls with every signed flush. The only domain
replacement is GenericDefaultRequestTrace for StreamReachable. The original
DGood, public-buffer and ActiveHeader premises are retained unchanged.
There is no readable-input, raw-output, positive-capacity, invariant or
called-function premise added by this bridge. Other configurations and
advanced API histories are outside this milestone; this is not Goal.deflate. -/
theorem generic_default_public_contract :
  ∀ h r i z s flush,
    GenericDefaultRequestTrace r h → DGood h r i z s →
    StreamBuffers h r → ActiveHeader h r →
    ∃ rc after z' s' used out,
      C.run (deflate (some r) flush) h = .ok (rc, after) ∧
      DGood after r i z' s' ∧ StreamAccounting z z' used out.length ∧
      Bytes after z.next_out out.length out ∧
      z'.total_in = z.total_in + UInt64.ofNat used ∧
      z'.total_out = z.total_out + UInt64.ofNat out.length ∧
      (rc = Z_OK ∨ rc = Z_STREAM_END ∨ rc = Z_STREAM_ERROR ∨ rc = Z_BUF_ERROR) ∧
      (rc = Z_STREAM_ERROR ↔
        flush.toInt < 0 ∨ 5 < flush.toInt ∨ z.next_out = .null ∨
        (z.next_in = .null ∧ z.avail_in ≠ 0) ∨
        (s.status = FINISH_STATE ∧ flush ≠ Z_FINISH)) ∧
      (flush.toInt < 0 ∨ 5 < flush.toInt → rc = Z_STREAM_ERROR ∧ after = h) ∧
      (rc = Z_STREAM_END → flush = Z_FINISH ∧ s'.status = FINISH_STATE ∧
        z'.avail_in = 0 ∧ s'.pending = 0 ∧ s'.bi_valid = 0) ∧
      BufferFrame h after (fun b => StreamRoot r b ∨ DeflateOwned i s b) [⟨z.next_out, out.length⟩] ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧ after.nalloc = h.nalloc := by
  intro h r i z s flush history good buffers _header
  obtain ⟨ds, stream, state, config, accepted, observed, encoding, _allocators, next⟩ :=
    history.full_next_request_contract
  have streams : stream = z :=
    Option.some.inj (encoding.protocol.good.live.hz.symm.trans good.live.hz)
  subst stream
  have keys : ds = i := by
    injection encoding.protocol.good.live.zst.symm.trans good.live.zst with tagged
    injection tagged
  subst ds
  have states : state = s :=
    Option.some.inj (encoding.protocol.good.live.hs.symm.trans good.live.hs)
  subst state
  obtain ⟨used, rc, after, z', s', out, _consumed, run, _encodingA, goodA, _buffersA,
      account, bytes, _length, _original, _adler, totalIn, totalOut, allowed, errors,
      invalid, terminal, _validity, _shape, frame, live, nalloc, _nextBlk⟩ :=
    next flush buffers
  exact ⟨rc, after, z', s', used, out, run, goodA, account, bytes, totalIn, totalOut,
    allowed, errors, invalid, terminal, frame, live, nalloc⟩

/-- The restricted basic-default domain is inhabited by an actual successful
translated default initialization. The caller-domain witness is concrete;
no initialized representation or allocator-success oracle is manufactured. -/
theorem generic_default_request_trace_witness :
    ∃ after, GenericDefaultRequestTrace (.tab 0) after := by
  obtain ⟨after, actual, _initial⟩ := DeflateInit.default_init_witness
  have domain : InitDomain DeflateInit.witnessHeap (.tab 0) (.ref (.blk 1) 0) := by
    refine ⟨DeflateInit.witness_fresh, DeflateInit.witness_uniq, rfl,
      DeflateInit.witness_version, default, ?_, ⟨Or.inl rfl, Or.inl rfl⟩, rfl⟩
    simp [ZStreamRef.get, DeflateInit.witnessHeap]
  exact ⟨after, GenericDefaultRequestTrace.init domain actual⟩

end Zlib.Deflate.Engine.Proofs
#print axioms Zlib.Deflate.Engine.Proofs.generic_default_public_contract
#print axioms Zlib.Deflate.Engine.Proofs.generic_default_request_trace_witness
