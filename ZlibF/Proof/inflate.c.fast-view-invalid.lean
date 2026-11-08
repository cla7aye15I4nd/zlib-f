import ZlibF.Proof.«inflate.c.fast-view-match-cases»
import ZlibF.Proof.«inflate.c.fast-buffers»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- A distance beyond available history takes the actual BAD branch of
translated `copyMatch`. Its record writes leave all byte views untouched. -/
theorem FastInputPacket.copyMatch_invalid_view
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {s : InflateState}
    (packet : FastInputPacket h slow bs l)
    (good : Good h r zs z s)
    (streamPtr : c.strm = some r)
    (statePtr : c.state = some (.tab zs))
    (sane : s.sane ≠ 0)
    (windowBranch : l.dist > l.op)
    (invalidBack : l.dist - l.op > c.whave)
    {dest : BRef} {output : Array UInt8}
    (outputGet : Space.get h dest = some output)
    (outputWrite : Space.ro h dest = false) :
    ∃ i after,
      C.run (Zlib.Inffast.copyMatch c l) h =
        .ok ({ l with op := l.dist - l.op, broke := true }, after) ∧
      after = setI
        (r.put h { z with msg := .ref (.str i) 0 }) zs
        { s with mode := BAD } ∧
      FastInputPacket after slow bs
        { l with op := l.dist - l.op, broke := true } ∧
      Space.get after dest = some output ∧
      Space.ro after dest = false := by
  obtain ⟨i, litRun, _⟩ :=
    strLitRef_of_mem (h := h) (s := "invalid distance too far back")
      (by decide +kernel)
  let updatedStream : ZStream :=
    { z with msg := .ref (.str i) 0 }
  let heap1 : Heap := r.put h updatedStream
  let updatedState : InflateState := { s with mode := BAD }
  let after : Heap := setI heap1 zs updatedState
  have streamLoad : ldZStream c.strm h = .ok (z, h) := by
    rw [streamPtr]
    exact ldZStream_ok good.live.hz
  have streamStore : stZStream c.strm updatedStream h =
      .ok ((), heap1) := by
    rw [streamPtr]
    exact stZStream_ok good.live.hz (by cases r <;> rfl)
  have stateGet1 : heap1.istates zs = some s := by
    simpa only [heap1, ZStreamRef.put_istates] using good.live.hs
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
  have stateLoad : ldInflateState c.state h = .ok (s, h) := by
    rw [statePtr]
    exact ldInflateState_ok good.live.hs
  have badRun : Zlib.Inffast.badData c
      "invalid distance too far back" h = .ok ((), after) := by
    unfold Zlib.Inffast.badData Zlib.Zutil.strLit
    rw [bind_ok litRun, bind_ok streamLoad,
      bind_ok streamStore, bind_ok stateLoad1]
    exact stateStore1
  have run : Zlib.Inffast.copyMatch c l h =
      .ok ({ l with op := l.dist - l.op, broke := true }, after) := by
    have saneBool : (s.sane != 0) = true := by
      simpa only [bne_iff_ne] using sane
    unfold Zlib.Inffast.copyMatch
    simp only [windowBranch, ite_true, invalidBack]
    rw [bind_ok stateLoad]
    simp only [saneBool, ite_true]
    simp only [bind_app, badRun]
    rfl
  have views : ∀ ref : BRef,
      (Space.get after ref : Option (Array UInt8)) =
        Space.get h ref := by
    intro ref
    dsimp [after, heap1]
    rw [byte_view_get_setI, byte_view_get_stream_put]
  have packetAfter : FastInputPacket after slow bs
      { l with op := l.dist - l.op, broke := true } :=
    ⟨packet.source.byte_views views, packet.cursor,
      packet.hold, packet.bits⟩
  refine ⟨i, after, run, rfl, packetAfter, ?_, ?_⟩
  · rw [views]
    exact outputGet
  · dsimp [after, heap1]
    rw [byte_view_ro_setI, byte_view_ro_stream_put]
    exact outputWrite

end Zlib.Inflate.Proofs
