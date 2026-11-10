import ZlibF.Proof.«inflate.c.whole-slow-matching-dispatch-v4»

namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs
set_option autoImplicit false

/-- Every actual slow data dispatcher trip advances or really stops the
finite whole-call source invariant. The ordinary fast guard is selected
internally; no valid compressed future or desired return is assumed. -/
 theorem EpochCallCut4.slow_payload_dispatch
    {c : Ctx} {entryHeap h : Heap} {r : ZStreamRef} {zs : Nat} {entryZ z : ZStream}
    {s : InflateState} {l : IL} {base : DataLog} {raw : List UInt8}
    (before : EpochCallCut4 c entryHeap h r zs entryZ z s l base raw)
    (dataMode : DataTableMode s.mode)
    (slow : s.mode = LEN_ ∨ s.mode = LEN → ¬ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    Nonempty (DispatchResult4 before) := by
  change DataTableMode (leaveState s l).mode at dataMode
  cases selected : before.phase with
  | legacy previous =>
    cases previous with
    | ready boundary mode last => exact before.ready_slow_dispatch boundary mode last selected (slow mode)
    | reading modes data => exact before.reading_slow_dispatch modes data selected
    | matching mode data => exact before.matching_slow_dispatch mode data selected
    | head mode _wire _output _dictionary _bits => rw [mode] at dataMode; exact ((by unfold DataTableMode; decide : ¬ DataTableMode HEAD) dataMode).elim
    | dictid _cmf _flg mode _valid _flag _wire _output _dictionary _bits => rw [mode] at dataMode; exact ((by unfold DataTableMode; decide : ¬ DataTableMode DICTID) dataMode).elim
    | dictionary _wrapper _id mode _flag _wire _output _bits _check _dict => rw [mode] at dataMode; exact ((by unfold DataTableMode; decide : ¬ DataTableMode DICT) dataMode).elim
    | tag _wrapper _word modes _last _context _anchor =>
      rcases modes with mode | mode <;> rw [mode] at dataMode
      · exact ((by unfold DataTableMode; decide : ¬ DataTableMode TYPE) dataMode).elim
      · exact ((by unfold DataTableMode; decide : ¬ DataTableMode TYPEDO) dataMode).elim
    | table _block mode _dynamic _last _anchor _output => rw [mode] at dataMode; exact ((by unfold DataTableMode; decide : ¬ DataTableMode TABLE) dataMode).elim
    | alphabet mode _data => rw [mode] at dataMode; exact ((by unfold DataTableMode; decide : ¬ DataTableMode LENLENS) dataMode).elim
    | codes mode _data => rw [mode] at dataMode; exact ((by unfold DataTableMode; decide : ¬ DataTableMode CODELENS) dataMode).elim
    | emptyCodes mode _data => rw [mode] at dataMode; exact ((by unfold DataTableMode; decide : ¬ DataTableMode CODELENS) dataMode).elim
    | stored _block _padding mode _kind _short _bits _last _anchor _output => rw [mode] at dataMode; exact ((by unfold DataTableMode; decide : ¬ DataTableMode STORED) dataMode).elim
    | copying modes _data =>
      rcases modes with mode | mode <;> rw [mode] at dataMode
      · exact ((by unfold DataTableMode; decide : ¬ DataTableMode COPY_) dataMode).elim
      · exact ((by unfold DataTableMode; decide : ¬ DataTableMode COPY) dataMode).elim
    | afterBlocks modes _last _data =>
      rcases modes with mode | mode <;> rw [mode] at dataMode
      · exact ((by unfold DataTableMode; decide : ¬ DataTableMode TYPE) dataMode).elim
      · exact ((by unfold DataTableMode; decide : ¬ DataTableMode TYPEDO) dataMode).elim
    | trailer modes _last _bits _data _check _length =>
      rcases modes with mode | mode <;> rw [mode] at dataMode
      · exact ((by unfold DataTableMode; decide : ¬ DataTableMode CHECK) dataMode).elim
      · exact ((by unfold DataTableMode; decide : ¬ DataTableMode LENGTH) dataMode).elim
    | done mode _bits _data => rw [mode] at dataMode; exact ((by unfold DataTableMode; decide : ¬ DataTableMode DONE) dataMode).elim
    | rejected mode _reason => rw [mode] at dataMode; exact ((by unfold DataTableMode; decide : ¬ DataTableMode BAD) dataMode).elim
    | memory _prior _phase _notMemory frame =>
      rw [frame] at dataMode
      exact ((by unfold DataTableMode; decide : ¬ DataTableMode MEM) dataMode).elim
  | rawStored _block mode _kind _last _anchor _output =>
    rw [mode] at dataMode
    exact ((by unfold DataTableMode; decide : ¬ DataTableMode STORED) dataMode).elim
  | uncheckedMatch mode data => exact before.unchecked_match_dispatch mode data selected
  | memory _prior _phase _notMemory frame =>
    rw [frame] at dataMode
    exact ((by unfold DataTableMode; decide : ¬ DataTableMode MEM) dataMode).elim

#print axioms EpochCallCut4.slow_payload_dispatch
end Zlib.Inflate.Proofs.WholeEpoch
