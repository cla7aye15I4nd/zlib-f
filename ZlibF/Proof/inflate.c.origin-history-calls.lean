import ZlibF.Proof.«inflate.c.origin-fields-memory-contract»
import ZlibF.Proof.«inflate.c.dictionary-install-origin»
import ZlibF.Proof.«inflate.c.default-history-calls»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- A selected actual call preserves the full initialized decoder relation.
The arguments are the original public history arguments; no callee contract
or desired state property is supplied by the caller. -/
theorem DefaultHistoryCall.preserve_origin {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {call : Call} {value : call.Result}
    (invariant : DefaultOriginState h r zs z s) (allocator : DefAlloc z)
    (selected : DefaultHistoryCall r call) (arguments : StreamArguments h r call)
    (actual : call.execute default h = .ok ((value, default), after)) :
    ∃ stream state, DefaultOriginState after r zs stream state ∧ DefAlloc stream := by
  cases selected with
  | inflate flush =>
    obtain ⟨code, computed, stream, state, _used, _output, run, next, nextAllocator, _⟩ :=
      inflate_default_origin_public_memory_contract invariant allocator arguments.1 flush
    have same := Except.ok.inj ((heapCall_of_actual_run run default).symm.trans actual)
    cases same
    exact ⟨stream, state, next, nextAllocator⟩
  | resetKeep =>
    obtain ⟨computed, run, next⟩ := inflateResetKeep_default_origin invariant.toDefaultStateJ
    have same := Except.ok.inj ((heapCall_of_actual_run run default).symm.trans actual)
    cases same
    exact ⟨_, _, next, allocator⟩
  | reset =>
    obtain ⟨computed, run, next⟩ := inflateReset_default_origin invariant.toDefaultStateJ allocator.2
    have same := Except.ok.inj ((heapCall_of_actual_run run default).symm.trans actual)
    cases same
    exact ⟨_, _, next, allocator⟩
  | reset2 =>
    obtain ⟨computed, run, next⟩ := inflateReset2_15_default_origin invariant.toDefaultStateJ allocator.2
    have same := Except.ok.inj ((heapCall_of_actual_run run default).symm.trans actual)
    cases same
    exact ⟨_, _, next, allocator⟩
  | prime bits requested =>
    obtain ⟨code, computed, state, run, next, _⟩ := inflatePrime_default_origin invariant bits requested
    have same := Except.ok.inj ((heapCall_of_actual_run run default).symm.trans actual)
    cases same
    exact ⟨z, state, next, allocator⟩
  | validate check =>
    obtain ⟨computed, state, run, next⟩ := inflateValidate_default_origin invariant check
    have same := Except.ok.inj ((heapCall_of_actual_run run default).symm.trans actual)
    cases same
    exact ⟨z, state, next, allocator⟩
  | getHeader head =>
    have run := (inflateGetHeader_default_J invariant.toDefaultDecodeJ head).1
    have same := Except.ok.inj ((heapCall_of_actual_run run default).symm.trans actual)
    cases same
    exact ⟨z, s, invariant, allocator⟩
  | undermine subvert =>
    have run := (inflateUndermine_default_J invariant.toDefaultDecodeJ subvert).1
    have same := Except.ok.inj ((heapCall_of_actual_run run default).symm.trans actual)
    cases same
    exact ⟨z, s, invariant, allocator⟩
  | setDictionary source len =>
    obtain ⟨code, computed, state, run, next, _codes⟩ :=
      inflateSetDictionary_default_origin invariant allocator source len arguments
    have same := Except.ok.inj ((heapCall_of_actual_run run default).symm.trans actual)
    cases same
    exact ⟨z, state, next, allocator⟩
  | getDictionary dest dl =>
    obtain ⟨stream, index, state, streamGet, pointer, stateGet, range⟩ := arguments
    have sameStream : stream = z := Option.some.inj (streamGet.symm.trans invariant.good.live.hz)
    subst stream
    have sameIndex : index = zs := by
      rw [invariant.good.live.zst] at pointer
      cases pointer
      rfl
    subst index
    have sameState : state = s := Option.some.inj (stateGet.symm.trans invariant.good.live.hs)
    subst state
    obtain ⟨computed, run, next⟩ := inflateGetDictionary_default_origin invariant dest dl range
    have same := Except.ok.inj ((heapCall_of_actual_run run default).symm.trans actual)
    cases same
    exact ⟨z, s, next, allocator⟩
  | syncPoint =>
    have run := (inflateSyncPoint_default_state invariant.toDefaultStateJ).1
    have same := Except.ok.inj ((heapCall_of_actual_run run default).symm.trans actual)
    cases same
    exact ⟨z, s, invariant, allocator⟩
  | mark =>
    obtain ⟨mark, run, _meaning, _next⟩ := inflateMark_default_state invariant.toDefaultStateJ
    have same := Except.ok.inj ((heapCall_of_actual_run run default).symm.trans actual)
    cases same
    exact ⟨z, s, invariant, allocator⟩
  | codesUsed =>
    obtain ⟨offset, _bounded, _pointer, run, _next⟩ := inflateCodesUsed_default_state invariant.toDefaultStateJ
    have same := Except.ok.inj ((heapCall_of_actual_run run default).symm.trans actual)
    cases same
    exact ⟨z, s, invariant, allocator⟩

#print axioms DefaultHistoryCall.preserve_origin
end Zlib.Inflate.Proofs
