import ZlibF.Proof.«inflate.c.origin-history-memory-contract»
import ZlibF.Proof.«inflate.c.output-frame-footprint-compose»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The exact public Goal.inflate contract on the explicitly selected
actual default history domain. The sole type change is replacing public
StreamReachable with DefaultOriginHistory. Every other caller premise and
result clause is retained verbatim. This does not prove the unrestricted
original goal or the separate sequence/format/completion targets. -/
theorem inflate_default_history_goal :
  ∀ h r i z s flush,
    DefaultOriginHistory h r → Zlib.Inflate.Spec.Good h r i z s →
    ZlibF.PlatformMemory.ByteObjectsFit h →
    Zlib.Inflate.Spec.DefAlloc z → StreamBuffers h r → ActiveHeader h r →
    ∃ rc after z' s' used out,
      C.run (Zlib.Inflate.inflate (some r) flush) h = .ok (rc, after) ∧
      Zlib.Inflate.Spec.Good after r i z' s' ∧ StreamAccounting z z' used out.length ∧
      Bytes after z.next_out out.length out ∧
      (rc = Z_OK ∨ rc = Z_STREAM_END ∨ rc = Z_NEED_DICT ∨ rc = Z_STREAM_ERROR ∨
       rc = Z_DATA_ERROR ∨ rc = Z_MEM_ERROR ∨ rc = Z_BUF_ERROR) ∧
      (rc = Z_OK → (used ≠ 0 ∨ out ≠ []) ∧ flush ≠ Z_FINISH) ∧
      (rc = Z_STREAM_END → s'.mode = DONE) ∧
      (rc = Z_NEED_DICT → s'.mode = DICT) ∧
      (rc = Z_DATA_ERROR → s'.mode = BAD) ∧
      (rc = Z_MEM_ERROR → s'.mode = MEM ∧ z'.total_in = z.total_in ∧ z'.total_out = z.total_out) ∧
      (rc = Z_OK ∨ rc = Z_STREAM_END ∨ rc = Z_DATA_ERROR ∨ rc = Z_BUF_ERROR →
        z'.total_in = z.total_in + UInt64.ofNat used ∧
        z'.total_out = z.total_out + UInt64.ofNat out.length) ∧
      BufferFrame h after
        (fun b => StreamRoot r b ∨ InflateOwned i s b ∨ s.head = some (.tab b))
        (⟨z.next_out, out.length⟩ :: HeaderRegions h s.head) ∧
      LiveChange h after (fun b => InflateOwned i s' b ∧ ¬ h.live b) (fun _ => False) := by
  intro h r i z s flush history good _platform allocator buffers _header
  obtain ⟨⟨zs, originalStream, originalState, before, _historyAllocator⟩, _reachable⟩ := history.sound
  have sameStream : originalStream = z :=
    Option.some.inj (before.good.live.hz.symm.trans good.live.hz)
  subst originalStream
  have sameIndex : zs = i := by
    have same := before.good.live.zst.symm.trans good.live.zst
    cases same
    rfl
  subst zs
  have sameState : originalState = s :=
    Option.some.inj (before.good.live.hs.symm.trans good.live.hs)
  subst originalState
  obtain ⟨rc, after, stream, state, used, output, run, current, _finalAllocator,
    _freed, accounting, bytes, totals, progress, codes, memoryTotals, modes, frame, ledger⟩ :=
    inflate_default_origin_public_memory_contract before allocator buffers flush
  refine ⟨rc, after, stream, state, used, output, run, current.good, accounting, bytes,
    codes, progress, modes.1, modes.2.1, modes.2.2.1, ?_, totals, ?_, ledger⟩
  · intro memory
    exact ⟨modes.2.2.2 memory, memoryTotals memory⟩
  · simpa only [before.header, HeaderRegions, reduceCtorEq, or_false] using frame

/-- Real initialization and the existing legal caller-buffer witness
satisfy every retained premise of the selected exact public contract.
This witnesses the domain and a real returning call; it makes no successful
format-decoding claim. -/
theorem inflate_default_history_goal_domain_witness :
    ∃ initialized h z s rc after,
      C.run (inflateInit_ (some (.tab 0)) (.ref (.blk 1) 0) 112) witnessHeap =
        .ok (Z_OK, initialized) ∧
      Rebuffer initialized h (.tab 0) ∧ DefaultOriginHistory h (.tab 0) ∧
      Good h (.tab 0) witnessHeap.nextBlk z s ∧
      ZlibF.PlatformMemory.ByteObjectsFit h ∧ DefAlloc z ∧
      StreamBuffers h (.tab 0) ∧ ActiveHeader h (.tab 0) ∧
      C.run (inflate (some (.tab 0)) Z_FINISH) h = .ok (rc, after) := by
  obtain ⟨initialized, _initialStream, s, h, z, rc, after, _finalStream, _finalState,
    _used, _output, initRun, _initial, edit, _reachable, current, allocator, buffers,
    run, _rest⟩ := inflate_default_public_memory_witness
  have initial := DefaultOriginHistory.init
    ZlibF.Spec.Public.Proofs.InflateInit.public_witness_domain inflate_default_witness_platform rfl initRun
  have history := DefaultOriginHistory.rebuffer initial edit current.platform
  exact ⟨initialized, h, z, s, rc, after, initRun, edit, history,
    current.good, current.platform, allocator, buffers, current.active_header, run⟩

#print axioms inflate_default_history_goal
#print axioms inflate_default_history_goal_domain_witness
end Zlib.Inflate.Proofs
