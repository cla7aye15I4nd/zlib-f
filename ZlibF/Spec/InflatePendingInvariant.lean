import ZlibF.Zlib.«inflate.c»

namespace Zlib.Inflate.Spec
open C

/-- The signed back counter at an extra-bit or distance boundary. -/
def BackBound (s : InflateState) (bound : Nat) : Prop :=
  ∃ used, used ≤ bound ∧ s.back = Int32.ofNat used

/-- Preconditions of the actual LENEXT suffix, established by a length leaf. -/
def LengthExtraSafe (s : InflateState) : Prop :=
  s.extra.toNat ≤ 5 ∧ 3 ≤ s.length.toNat ∧
    s.length.toNat + 2 ^ s.extra.toNat ≤ 259 ∧ BackBound s 15

/-- A complete length has been retained while the distance is read. -/
def PendingLengthSafe (s : InflateState) : Prop :=
  3 ≤ s.length.toNat ∧ s.length.toNat ≤ 258 ∧ s.was = s.length

def DistanceSafe (s : InflateState) : Prop :=
  PendingLengthSafe s ∧ BackBound s 20

/-- Preconditions of the actual DISTEXT suffix, established by a distance leaf.
The coarse distance budget is sufficient for safety; it does not assert
canonical-symbol meaning or the independent format's maximum distance. -/
def DistanceExtraSafe (s : InflateState) : Prop :=
  PendingLengthSafe s ∧ s.extra.toNat ≤ 13 ∧ 1 ≤ s.offset.toNat ∧
    s.offset.toNat + 2 ^ s.extra.toNat ≤ 73727 ∧ BackBound s 35

/-- A partially emitted match retains its original length and positive distance. -/
def MatchSafe (s : InflateState) : Prop :=
  0 < s.length.toNat ∧ s.length.toNat ≤ s.was.toNat ∧
    s.was.toNat ≤ 258 ∧ 0 < s.offset.toNat

/-- Guarded scalar clauses for the default-build data decoder. These are
internal stream-state facts. They do not constrain caller arguments or
replace the separate table, buffer and construction clauses of J. -/
structure DataPendingInvariant (s : InflateState) : Prop where
  sane : s.sane = 1
  lenext : s.mode = LENEXT → LengthExtraSafe s
  dist : s.mode = DIST → DistanceSafe s
  distext : s.mode = DISTEXT → DistanceExtraSafe s
  matching : s.mode = MATCH → MatchSafe s

end Zlib.Inflate.Spec
