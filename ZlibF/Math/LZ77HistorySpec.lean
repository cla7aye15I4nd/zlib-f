import ZlibF.Spec.Format.Deflate

/-!
# Retained windows and complete independent output history

The decoder retains only a suffix of earlier bytes. A match reaching no
farther than that suffix must agree with copying against the full history.
These are list statements, independent of the heap representation.
-/

namespace ZlibF.Math.LZ77History
open ZlibF.Spec

/-- Copying only appends bytes, exactly one for each requested byte. -/
def Goal.copy_back_extends_history : Prop :=
  ∀ (dict history : List UInt8) (dist n : Nat),
    history <+: copyBack dict dist n history ∧
    (copyBack dict dist n history).length = history.length + n

/-- Physical chunks compose to the same independent bytewise match. -/
def Goal.copy_back_compose : Prop :=
  ∀ (dict history : List UInt8) (dist n m : Nat),
    copyBack dict dist (n + m) history =
      copyBack dict dist m (copyBack dict dist n history)

/-- When a distance reaches only retained bytes, forgetting older history
does not change the new output. The suffix relation must be established
from actual window updates by the enclosing decoder proof. -/
def Goal.retained_history_agrees : Prop :=
  ∀ (dict past current saved : List UInt8) (dist n : Nat),
    saved <:+ (dict ++ past) →
    0 < dist → dist ≤ saved.length + current.length →
    copyBack dict dist n (past ++ current) =
      past ++ copyBack saved dist n current

/-- For a distance within the configured capacity, retaining the complete
window loses no usable history. A too-far check on the retained bytes is
then exactly the independent check on the entire preceding history. -/
def Goal.window_distance_check_agrees : Prop :=
  ∀ (dict past current : List UInt8) (capacity dist : Nat),
    dist ≤ capacity →
    ((((dict ++ past).drop ((dict ++ past).length - capacity)) ++ current).length < dist ↔
      (dict ++ past ++ current).length < dist)

end ZlibF.Math.LZ77History
