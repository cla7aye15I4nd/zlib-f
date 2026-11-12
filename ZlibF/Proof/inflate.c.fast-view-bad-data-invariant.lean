import ZlibF.Proof.«inflate.c.fast-view-dodist-leaf-invariant»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The translated fast error write preserves caller byte views and enters
the BAD state of the default decoder relation for any source literal. -/
theorem FastInputPacket.badData_default_state
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow bs l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow bs)
    (streamPtr : c.strm = some r)
    (statePtr : c.state = some (.tab zs))
    (message : String) (literal : message ∈ strTable) :
    ∃ i after,
      C.run (Zlib.Inffast.badData c message) h = .ok ((), after) ∧
      after = badHeap h r zs z s i ∧
      FastInputPacket after slow bs l ∧
      DefaultStateJ after r zs
        { z with msg := .ref (.str i) 0 } { s with mode := BAD } ∧
      DispatchBuffers after r slow bs ∧
      ByteViewSizes h after := by
  obtain ⟨i, litRun, _⟩ :=
    strLitRef_of_mem (h := h) (s := message) literal
  let updatedStream : ZStream :=
    { z with msg := .ref (.str i) 0 }
  let heap1 : Heap := r.put h updatedStream
  let updatedState : InflateState := { s with mode := BAD }
  let after : Heap := setI heap1 zs updatedState
  have afterEq : after = badHeap h r zs z s i := rfl
  have streamLoad : ldZStream c.strm h = .ok (z, h) := by
    rw [streamPtr]
    exact ldZStream_ok invariant.good.live.hz
  have streamStore : stZStream c.strm updatedStream h =
      .ok ((), heap1) := by
    rw [streamPtr]
    exact stZStream_ok invariant.good.live.hz
      (by cases r <;> rfl)
  have stateGet1 : heap1.istates zs = some s := by
    simpa only [heap1, ZStreamRef.put_istates]
      using invariant.good.live.hs
  have stateLoad1 : ldInflateState c.state heap1 =
      .ok (s, heap1) := by
    rw [statePtr]
    exact ldInflateState_ok stateGet1
  have stateStore1 : stInflateState c.state updatedState heap1 =
      .ok ((), after) := by
    rw [statePtr]
    have store := stInflateState_ok
      (r := InflateStateRef.tab zs) stateGet1 rfl
      (v' := updatedState)
    rw [InflateStateRef.put_tab stateGet1 updatedState] at store
    exact store
  have run : Zlib.Inffast.badData c message h =
      .ok ((), after) := by
    unfold Zlib.Inffast.badData Zlib.Zutil.strLit
    rw [bind_ok litRun, bind_ok streamLoad,
      bind_ok streamStore, bind_ok stateLoad1]
    exact stateStore1
  have summary := head_bad_packet invariant.good
    invariant.pending buffers buffers.bits
    (by rfl : HeadRegFrame slow slow) i
  rcases summary with ⟨nextGood, nextTables, nextPending,
    nextBuffers, sizes, static⟩
  have views : ∀ ref : BRef,
      (Space.get after ref : Option (Array UInt8)) =
        Space.get h ref := by
    intro ref
    dsimp [after, badHeap]
    rw [byte_view_get_setI, byte_view_get_stream_put]
  have nextPacket : FastInputPacket after slow bs l :=
    ⟨packet.source.byte_views views, packet.cursor,
      packet.hold, packet.bits⟩
  have nextInvariant : DefaultStateJ after r zs
      updatedStream updatedState := by
    rw [afterEq]
    refine ⟨⟨nextGood, nextTables, nextPending, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
    · intro active
      have impossible : BAD = CODELENS := by simpa using active
      exact False.elim ((by decide : BAD ≠ CODELENS) impossible)
    · intro active
      have impossible : BAD = LENLENS := by simpa using active
      exact False.elim ((by decide : BAD ≠ LENLENS) impossible)
    · exact invariant.held
    · exact invariant.window
    · exact invariant.wrapper
    · exact invariant.header
    · right; left
      change DICTID ≤ BAD ∧ BAD ≤ SYNC
      decide
    · intro active
      rcases active with check | length
      · have impossible : BAD = CHECK := by simpa using check
        exact False.elim ((by decide : BAD ≠ CHECK) impossible)
      · have impossible : BAD = LENGTH := by simpa using length
        exact False.elim ((by decide : BAD ≠ LENGTH) impossible)
    · change (badHeap h r zs z s i).static = _
      rw [static]
      exact invariant.globals
    · exact sizes.platform invariant.platform
    · exact invariant.requestedBits
    · exact invariant.requestedWrap
    · exact Or.inr (Or.inl rfl)
  exact ⟨i, after, run, afterEq, nextPacket,
    nextInvariant,
    by rw [afterEq]; exact nextBuffers,
    by rw [afterEq]; exact sizes⟩

end Zlib.Inflate.Proofs
