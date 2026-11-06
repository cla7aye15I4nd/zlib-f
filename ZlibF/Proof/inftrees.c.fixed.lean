import ZlibF.Proof.«inflate.c.base»
import ZlibF.Zlib.«inftrees.c»

/-!
# inftrees.c: `inflate_fixed`

`inflate_fixed` does not build a table. It points the state at the two static tables (`lenfix`, `distfix`) and sets
their root widths. The tables themselves are static data of the heap (installed by `initStatics`).
-/

namespace Zlib.Inftrees.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs

/-- The state record after `inflate_fixed`. -/
def fixedState (st : InflateState) : InflateState :=
  { st with lencode := .ref .st_lenfix 0, lenbits := 9, distcode := .ref .st_distfix 0, distbits := 5 }

/-- **inflate_fixed.** On a live inflate state `zs` the call does not fault and changes exactly four fields of that
record: `lencode` is the static `lenfix`, `lenbits` is 9, `distcode` is the static `distfix`, `distbits` is 5. No other
table entry of the heap changes, and nothing is allocated or freed. -/
theorem inflate_fixed_ok {h : Heap} {zs : Nat} {st : InflateState} (hs : h.istates zs = some st) :
    C.run (inflate_fixed (some (.tab zs))) h = .ok ((), setI h zs (fixedState st)) := by
  rw [C.run]
  simp [inflate_fixed, bind_app, ldI_eq, stI_eq, hs, fixedState, setI, upd_upd]

end Zlib.Inftrees.Proofs
