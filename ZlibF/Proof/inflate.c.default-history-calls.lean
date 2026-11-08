import ZlibF.Proof.«inflate.c.default-readonly-controls»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The selected default calls. Reset2 selects fifteen bits. Synchronization
recovery and copy require additional history facts and are not included. -/
inductive DefaultHistoryCall (r : ZStreamRef) : Call → Prop where
  | inflate (flush : Int32) : DefaultHistoryCall r (.inflate (some r) flush)
  | resetKeep : DefaultHistoryCall r (.inflateResetKeep (some r))
  | reset : DefaultHistoryCall r (.inflateReset (some r))
  | reset2 : DefaultHistoryCall r (.inflateReset2 (some r) 15)
  | prime (bits value : Int32) : DefaultHistoryCall r (.inflatePrime (some r) bits value)
  | validate (check : Int32) : DefaultHistoryCall r (.inflateValidate (some r) check)
  | getHeader (head : GzHeaderPtr) : DefaultHistoryCall r (.inflateGetHeader (some r) head)
  | undermine (subvert : Int32) : DefaultHistoryCall r (.inflateUndermine (some r) subvert)
  | setDictionary (source : BPtr) (len : UInt32) :
      DefaultHistoryCall r (.inflateSetDictionary (some r) source len)
  | getDictionary (dest : BPtr) (dl : Option UInt32) :
      DefaultHistoryCall r (.inflateGetDictionary (some r) dest dl)
  | syncPoint : DefaultHistoryCall r (.inflateSyncPoint (some r))
  | mark : DefaultHistoryCall r (.inflateMark (some r))
  | codesUsed : DefaultHistoryCall r (.inflateCodesUsed (some r))

/-- Every selected call is one of the original public stream operations. -/
theorem DefaultHistoryCall.public_operation {r : ZStreamRef} {call : Call}
    (selected : DefaultHistoryCall r call) : StreamOperation .inflate r call := by
  cases selected <;> exact ⟨rfl, rfl⟩

/-- A selected actual call preserves the full initialized decoder relation.
The arguments are the original public history arguments; no callee contract
or desired state property is supplied by the caller. -/
theorem DefaultHistoryCall.preserve {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {call : Call} {value : call.Result}
    (invariant : DefaultStateJ h r zs z s) (allocator : DefAlloc z)
    (selected : DefaultHistoryCall r call) (arguments : StreamArguments h r call)
    (actual : call.execute default h = .ok ((value, default), after)) :
    ∃ stream state, DefaultStateJ after r zs stream state ∧ DefAlloc stream := by
  cases selected with
  | inflate flush =>
    obtain ⟨code, computed, stream, state, _used, _output, run, next, nextAllocator, _⟩ :=
      inflate_default_view_public_memory_contract invariant allocator arguments.1 flush
    have same := Except.ok.inj ((heapCall_of_actual_run run default).symm.trans actual)
    cases same
    exact ⟨stream, state, next, nextAllocator⟩
  | resetKeep =>
    obtain ⟨computed, run, _, next, _⟩ := inflateResetKeep_default_state invariant
    have same := Except.ok.inj ((heapCall_of_actual_run run default).symm.trans actual)
    cases same
    exact ⟨_, _, next, allocator⟩
  | reset =>
    obtain ⟨computed, run, next, _⟩ := inflateReset_default_state invariant allocator.2
    have same := Except.ok.inj ((heapCall_of_actual_run run default).symm.trans actual)
    cases same
    exact ⟨_, _, next, allocator⟩
  | reset2 =>
    obtain ⟨computed, run, next, _⟩ := inflateReset2_15_default_state invariant allocator.2
    have same := Except.ok.inj ((heapCall_of_actual_run run default).symm.trans actual)
    cases same
    exact ⟨_, _, next, allocator⟩
  | prime bits requested =>
    obtain ⟨code, computed, state, run, next, _⟩ := inflatePrime_default_state invariant bits requested
    have same := Except.ok.inj ((heapCall_of_actual_run run default).symm.trans actual)
    cases same
    exact ⟨z, state, next, allocator⟩
  | validate check =>
    obtain ⟨computed, state, run, _, _, next⟩ := inflateValidate_default_state invariant check
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
      inflateSetDictionary_default_state invariant allocator source len arguments
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
    obtain ⟨computed, run, next⟩ := inflateGetDictionary_default_state invariant dest dl range
    have same := Except.ok.inj ((heapCall_of_actual_run run default).symm.trans actual)
    cases same
    exact ⟨z, s, next, allocator⟩
  | syncPoint =>
    have run := (inflateSyncPoint_default_state invariant).1
    have same := Except.ok.inj ((heapCall_of_actual_run run default).symm.trans actual)
    cases same
    exact ⟨z, s, invariant, allocator⟩
  | mark =>
    obtain ⟨mark, run, _meaning, _next⟩ := inflateMark_default_state invariant
    have same := Except.ok.inj ((heapCall_of_actual_run run default).symm.trans actual)
    cases same
    exact ⟨z, s, invariant, allocator⟩
  | codesUsed =>
    obtain ⟨offset, _bounded, _pointer, run, _next⟩ := inflateCodesUsed_default_state invariant
    have same := Except.ok.inj ((heapCall_of_actual_run run default).symm.trans actual)
    cases same
    exact ⟨z, s, invariant, allocator⟩

#print axioms DefaultHistoryCall.preserve
end Zlib.Inflate.Proofs
