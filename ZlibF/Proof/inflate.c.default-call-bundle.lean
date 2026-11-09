import ZlibF.Proof.«inflate.c.default-record-resources»
import ZlibF.Proof.«inflate.c.default-public-frame»
import ZlibF.Proof.«inflate.c.old-owned»
import ZlibF.Proof.«inflate.c.default-setdict-resources»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The complete actual default inflate call returns from the original
public buffers with both initialized origins and the exact public ledger. -/
theorem inflate_default_origin_public_sequence_contract
    {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (before : DefaultOriginState h r zs z s) (allocator : DefAlloc z)
    (buffers : StreamBuffers h r) (flush : Int32) :
    ∃ rc after stream state, C.run (inflate (some r) flush) h = .ok (rc, after) ∧
      DefaultOriginState after r zs stream state ∧ DefAlloc stream ∧
      BufferFrame h after
        (fun b => StreamRoot r b ∨ StreamOwned h r b ∨ StreamHeaderRecord h r (.inflate (some r) flush) b)
        (StreamWriteRegions h r (.inflate (some r) flush)) ∧
      LiveChange h after
        (fun b => StreamOwned after r b ∧ ¬ h.live b)
        (fun b => StreamOwned h r b ∧ ¬ StreamOwned after r b) := by
  obtain ⟨rc, after, stream, state, _used, _output, run, current, finalAllocator,
    accounting, _bytes, frame, _window, _retained, ledger⟩ :=
    inflate_default_origin_old_owned_resources before allocator buffers flush
  exact ⟨rc, after, stream, state, run, current, finalAllocator,
    inflate_default_public_buffer_frame before flush frame accounting.2.1, ledger⟩

/-- All thirteen registered default-history call shapes return from the
original public arguments and satisfy the exact public memory and allocation
clauses. Reset2 here is the registered fifteen-bit request; Sync and Copy
have separate contracts. No next-call run or callee contract is assumed. -/
theorem DefaultHistoryCall.total_origin_public_contract
    {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState} {call : Call}
    (before : DefaultOriginState h r zs z s) (allocator : DefAlloc z)
    (selected : DefaultHistoryCall r call) (arguments : StreamArguments h r call) :
    ∃ value after stream state, call.execute default h = .ok ((value, default), after) ∧
      DefaultOriginState after r zs stream state ∧ DefAlloc stream ∧
      BufferFrame h after
        (fun b => StreamRoot r b ∨ StreamOwned h r b ∨ StreamHeaderRecord h r call b)
        (StreamWriteRegions h r call) ∧
      LiveChange h after
        (fun b => StreamOwned after r b ∧ ¬ h.live b)
        (fun b => StreamOwned h r b ∧ ¬ StreamOwned after r b) := by
  cases selected with
  | inflate flush =>
    obtain ⟨rc, after, stream, state, run, current, finalAllocator, frame, ledger⟩ :=
      inflate_default_origin_public_sequence_contract before allocator arguments.1 flush
    exact ⟨rc, after, stream, state, heapCall_of_actual_run run default,
      current, finalAllocator, frame, ledger⟩
  | resetKeep =>
    obtain ⟨after, run, current⟩ := inflateResetKeep_default_origin before.toDefaultStateJ
    have resources := inflateResetKeep_default_public_resources before current run
    exact ⟨Z_OK, after, _, _, heapCall_of_actual_run run default, current, allocator, resources⟩
  | reset =>
    obtain ⟨after, run, current⟩ := inflateReset_default_origin before.toDefaultStateJ allocator.2
    have resources := inflateReset_default_public_resources before allocator current run
    exact ⟨Z_OK, after, _, _, heapCall_of_actual_run run default, current, allocator, resources⟩
  | reset2 =>
    obtain ⟨after, run, current⟩ := inflateReset2_15_default_origin before.toDefaultStateJ allocator.2
    have resources := inflateReset2_15_default_public_resources before allocator current run
    exact ⟨Z_OK, after, _, _, heapCall_of_actual_run run default, current, allocator, resources⟩
  | prime bits requested =>
    obtain ⟨rc, after, state, run, current, _codes⟩ := inflatePrime_default_origin before bits requested
    have resources := inflatePrime_default_public_resources before bits requested current run
    exact ⟨rc, after, z, state, heapCall_of_actual_run run default, current, allocator, resources⟩
  | validate check =>
    obtain ⟨after, state, run, current⟩ := inflateValidate_default_origin before check
    have resources := inflateValidate_default_public_resources before check current run
    exact ⟨Z_OK, after, z, state, heapCall_of_actual_run run default, current, allocator, resources⟩
  | getHeader head =>
    have run := (inflateGetHeader_default_origin before head).1
    have resources := default_record_public_resources before.good before.good
      (RecordFrame.refl r (some (.tab zs)) h) rfl (.inflateGetHeader (some r) head)
    exact ⟨Z_STREAM_ERROR, h, z, s, heapCall_of_actual_run run default, before, allocator, resources⟩
  | undermine subvert =>
    have run := (inflateUndermine_default_origin before subvert).1
    have resources := default_record_public_resources before.good before.good
      (RecordFrame.refl r (some (.tab zs)) h) rfl (.inflateUndermine (some r) subvert)
    exact ⟨Z_DATA_ERROR, h, z, s, heapCall_of_actual_run run default, before, allocator, resources⟩
  | setDictionary source len =>
    obtain ⟨rc, after, state, run, current, frame, ledger⟩ :=
      inflateSetDictionary_default_public_contract before allocator source len arguments
    exact ⟨rc, after, z, state, heapCall_of_actual_run run default, current, allocator, frame, ledger⟩
  | getDictionary dest dl =>
    obtain ⟨stream, index, state, streamGet, pointer, stateGet, range⟩ := arguments
    have sameStream : stream = z := Option.some.inj (streamGet.symm.trans before.good.live.hz)
    subst stream
    have sameIndex : index = zs := by
      rw [before.good.live.zst] at pointer
      cases pointer
      rfl
    subst index
    have sameState : state = s := Option.some.inj (stateGet.symm.trans before.good.live.hs)
    subst state
    obtain ⟨after, run, current, frame, ledger⟩ :=
      inflateGetDictionary_default_public_contract before dest dl range
    exact ⟨_, after, z, s, heapCall_of_actual_run run default, current, allocator, frame, ledger⟩
  | syncPoint =>
    have run := (inflateSyncPoint_default_state before.toDefaultStateJ).1
    have resources := default_record_public_resources before.good before.good
      (RecordFrame.refl r (some (.tab zs)) h) rfl (.inflateSyncPoint (some r))
    exact ⟨_, h, z, s, heapCall_of_actual_run run default, before, allocator, resources⟩
  | mark =>
    obtain ⟨value, run, _meaning, _next⟩ := inflateMark_default_state before.toDefaultStateJ
    have resources := default_record_public_resources before.good before.good
      (RecordFrame.refl r (some (.tab zs)) h) rfl (.inflateMark (some r))
    exact ⟨value, h, z, s, heapCall_of_actual_run run default, before, allocator, resources⟩
  | codesUsed =>
    obtain ⟨offset, _bounded, _pointer, run, _next⟩ := inflateCodesUsed_default_state before.toDefaultStateJ
    have resources := default_record_public_resources before.good before.good
      (RecordFrame.refl r (some (.tab zs)) h) rfl (.inflateCodesUsed (some r))
    exact ⟨_, h, z, s, heapCall_of_actual_run run default, before, allocator, resources⟩

#print axioms DefaultHistoryCall.total_origin_public_contract

#print axioms inflate_default_origin_public_sequence_contract
end Zlib.Inflate.Proofs
