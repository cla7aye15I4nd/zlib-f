import ZlibF.Proof.«inflate.c.dictionary-install-origin»
import ZlibF.Proof.«inflate.c.copy-both-J»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The actual copy's pointer relocation keeps the dynamic-base or paired
fixed-table origin, now relative to the new decoder record. -/
theorem CopyTableOrigin.relocated {old : Nat} {s : InflateState}
    (origin : CopyTableOrigin old s) (dest : ZStreamRef) (fresh nextOff distOff : Nat)
    (window : BPtr) : CopyTableOrigin fresh (copiedGeneric dest old fresh nextOff distOff window s) := by
  rcases origin with dynamic | fixed
  · exact Or.inl (by simp only [copiedGeneric, dynamic, ↓reduceIte])
  · have different : s.lencode ≠ .ref (.istate_codes old) 0 := by
      rw [fixed.1]
      intro impossible
      cases impossible
    exact Or.inr (by simpa only [copiedGeneric, different, ↓reduceIte] using fixed)

/-- A copied source record retains its header sentinel and repaired table
origins. The incoming J here is an actual copied-state conclusion, not a
callee contract required of a public caller. -/
theorem DefaultOriginState.copied_state {h after : Heap} {source dest : ZStreamRef}
    {old fresh nextOff distOff : Nat} {z : ZStream} {s : InflateState} {window : BPtr}
    (before : DefaultOriginState h source old z s)
    (current : DefaultStateJ after dest fresh { z with state := some (.inflate fresh) }
      (copiedGeneric dest old fresh nextOff distOff window s)) :
    DefaultOriginState after dest fresh { z with state := some (.inflate fresh) }
      (copiedGeneric dest old fresh nextOff distOff window s) :=
  ⟨current, before.flagsOrigin, before.tableOrigin.relocated dest fresh nextOff distOff window⟩

end Zlib.Inflate.Proofs
