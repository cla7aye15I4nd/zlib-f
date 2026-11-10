import ZlibF.Proof.«inflate.c.whole-wrapper-word32»
namespace Zlib.Inflate.Proofs.WholeWrapper
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.WholeEpoch
set_option autoImplicit false
set_option maxHeartbeats 1800000

def readLog (log : DataLog) (raw : List UInt8) (used : Nat) : DataLog :=
  {log with input := log.input ++ raw.take used}

/-- Partial DICTID pulls credit actual bytes but commit no identifier bits.
This works after arbitrarily many earlier partial calls. -/
theorem dictid_wait_phase
    {h : Heap} {s : InflateState} {l : IL} {bs : List UInt8} {log : DataLog} {cmf flg : UInt8}
    (mode : s.mode = DICTID) (valid : Zlib.HeaderOK cmf flg) (flag : flg.toNat / 32 % 2 = 1)
    (empty : log.output = []) (dictionary : log.dictionary = [])
    (event : ByteWordRead h l bs log.input (bytesBits [cmf, flg]) 32)
    (waiting : event.outcome = .error Ex.leave) :
    Nonempty (SourcePhase (sourceLog (readLog log bs event.used)) (leaveState s event.regs) (bytesBits [cmf, flg])) := by
  refine ⟨SourcePhase.dictid (log := sourceLog (readLog log bs event.used)) cmf flg (by exact mode) valid flag rfl empty dictionary ?_⟩
  exact (event.wait waiting).2.2

/-- A completed cumulative actual DICTID read derives the identifier and
its entire credited wire. The real subsequent DICT check uses this scalar. -/
theorem dictid_complete_phase
    {h : Heap} {s : InflateState} {l : IL} {bs : List UInt8} {log : DataLog} {cmf flg : UInt8}
    (valid : Zlib.HeaderOK cmf flg) (flag : flg.toNat / 32 % 2 = 1)
    (empty : log.output = []) (missing : s.havedict = 0)
    (event : ByteWordRead h l bs log.input (bytesBits [cmf, flg]) 32)
    (normal : event.outcome = .ok ()) :
    ∃ identifier : UInt32,
      ZSWAP32 event.regs.hold = identifier.toUInt64 ∧
      natBits event.regs.bits.toNat event.regs.hold.toNat = bytesBits (be32 identifier.toNat) ∧
      CausalInput.Credited (readLog log bs event.used).input
        (bytesBits ([cmf, flg] ++ be32 identifier.toNat)) 0 0 ∧
      Nonempty (SourcePhase (sourceLog (readLog log bs event.used))
        (leaveState {s with check := identifier.toUInt64, mode := DICT} {event.regs with hold := 0, bits := 0})
        (bytesBits ([cmf, flg] ++ be32 identifier.toNat))) := by
  obtain ⟨identifier, swap, word⟩ := actual_be32_word (event.normal normal)
  have credited := event.credited
  change bytesBits (log.input ++ bs.take event.used) = bytesBits [cmf, flg] ++ natBits event.regs.bits.toNat event.regs.hold.toNat at credited
  rw [word, ← bytesBits_append] at credited
  let w : Wrapper (sourceLog (readLog log bs event.used)).dictionary :=
    ⟨cmf, flg, valid, fun no => False.elim (by omega)⟩
  refine ⟨identifier, swap, word, ?_, ?_⟩
  · simpa only [CausalInput.Credited, readLog, UInt32.toNat_zero, natBits, List.append_nil] using credited
  · refine ⟨SourcePhase.dictionary (log := sourceLog (readLog log bs event.used)) w identifier rfl flag rfl empty rfl rfl ?_⟩
    intro installed
    exact False.elim (installed missing)

#print axioms dictid_wait_phase
#print axioms dictid_complete_phase
end Zlib.Inflate.Proofs.WholeWrapper
