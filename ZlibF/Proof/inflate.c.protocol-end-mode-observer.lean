import ZlibF.Proof.«inflate.c.global-functional-epoch»

namespace Zlib.Inflate.Proofs.ProtocolWindow
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs
set_option autoImplicit false

private theorem good_mode_unique
    {h : Heap} {r : ZStreamRef} {first second : Nat}
    {z stream : ZStream} {s state : InflateState}
    (before : Good h r first z s) (after : Good h r second stream state) :
    s.mode = state.mode := by
  have sameStream : z = stream := Option.some.inj (before.live.hz.symm.trans after.live.hz)
  subst stream
  have sameIndex : first = second := by simpa using before.live.zst.symm.trans after.live.zst
  subst second
  have sameState : s = state := Option.some.inj (before.live.hs.symm.trans after.live.hs)
  exact congrArg InflateState.mode sameState

/-- END in the actual default protocol log still denotes the real DONE
state after arbitrary caller edits and dictionary requests. Other return
codes are deliberately not projected through setters, which retain the
previous data-call result in the log. -/
theorem protocol_result_end_mode
    {r : ZStreamRef} {h : Heap} {log : DataLog} {pending : Bool}
    (trace : InflateProtocolTrace 15 r h log pending) (scope : PlatformScope trace) :
    ∀ zs z s, Good h r zs z s → log.result = Z_STREAM_END → s.mode = DONE := by
  induction scope with
  | @init before after version domain actual platform =>
    intro zs z s _good ended
    change Z_OK = Z_STREAM_END at ended
    exact False.elim ((by decide : Z_OK ≠ Z_STREAM_END) ended)
  | @caller before after log pending prior edit earlier _platform ih =>
    intro zs z s good ended
    obtain ⟨_physical, _history, _exact, index, oldZ, oldS, current, _allocator, _token, _empty⟩ :=
      exact_physical_history prior earlier
    obtain ⟨stream, _fields, final⟩ := rebuffer_inflate_good current.good edit
    have sameMode := good_mode_unique final good
    exact sameMode.symm.trans (ih index oldZ oldS current.good ended)
  | @step before after log pending flush rc input output used prior actual earlier _ih =>
    intro zs z s good ended
    obtain ⟨index, stream, state, current, _allocator, modes⟩ :=
      FunctionalEpoch.dataStep_observed_modes prior earlier actual
    have sameMode := good_mode_unique current.good good
    exact sameMode.symm.trans (modes.1 ended)
  | @dictionary before after log pending source n bytes rc prior _arguments _input actual _allowed earlier ih =>
    intro zs z s good ended
    change log.result = Z_STREAM_END at ended
    obtain ⟨_physical, history, _exact, index, oldZ, oldS, current, _allocator, _token, _empty⟩ :=
      exact_physical_history prior earlier
    have doneBefore := ih index oldZ oldS current.good ended
    have wrapped : oldS.wrap = 5 := (history_header_fields history current).1
    have refused := inflateSetDictionary_refused_any current.good.live source n
      (Or.inr ⟨by rw [wrapped]; decide, by rw [doneBefore]; decide⟩)
    have pair := Except.ok.inj (actual.symm.trans refused)
    have sameHeap : after = before := congrArg Prod.snd pair
    subst after
    have sameMode := good_mode_unique current.good good
    exact sameMode.symm.trans doneBefore

#print axioms protocol_result_end_mode
end Zlib.Inflate.Proofs.ProtocolWindow
