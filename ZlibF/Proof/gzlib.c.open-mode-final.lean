import ZlibF.Proof.«gzlib.c.open-supplied-io»
import ZlibF.Proof.«gzlib.c.open-copy-stage»

/-!
# gzlib.c: final parser guards on the actual live handle

The source rejects absent modes and forbidden direct combinations before path
allocation. Accepted reads write direct one exactly when its old value is zero.
-/

namespace Zlib.Gzlib.Proofs
open C Zlib.GzFs Zlib.Gzguts Zlib.Gzlib.Spec ZlibF.Spec.Public.OffsetProof
open ZlibF.Math.GzModeParser

/-- The source's sole accepted-mode field normalization. -/
def checkedModeRecord (s : GzState) (mode : ZlibF.Spec.Api.GzMode) : GzState :=
  if mode = .read ∧ s.direct = 0 then { s with direct := 1 } else s

/-- Exact heap after the accepted mode guards, before path allocation. -/
def checkedModeHeap (h : Heap) (i : Nat) (s : GzState) (mode : ZlibF.Spec.Api.GzMode) : Heap :=
  if mode = .read ∧ s.direct = 0 then setS h i { s with direct := 1 } else h

/-- An absent source mode releases the actual handle without touching path or
file-system state, even when the other parsed settings are arbitrary. -/
theorem openAfterMode_absent (h : Heap) (fs : Fs) (i : Nat) (s : GzState)
    (path : BPtr) (fd : Int32) (ml : ModeLoop)
    (hs : h.gzstates i = some s) (hm : s.mode = GZ_NONE) (hdone : ml.done = false) :
    openAfterMode (some (.tab i)) path fd ml fs h =
      .ok ((none, fs), { h with gzstates := upd h.gzstates i none }) := by
  rw [openAfterMode_copy_cut]
  offsetsimp [hs, hm, hdone, freeGzState]

/-- Both forbidden direct combinations take their real release branch. -/
theorem openAfterMode_forbidden (h : Heap) (fs : Fs) (i : Nat) (s : GzState)
    (path : BPtr) (fd : Int32) (ml : ModeLoop) (mode : ZlibF.Spec.Api.GzMode)
    (hs : h.gzstates i = some s) (hm : s.mode = modeCode (some mode))
    (hbad : (mode = .read ∧ s.direct = 1) ∨ (mode ≠ .read ∧ s.direct = -1))
    (hdone : ml.done = false) :
    openAfterMode (some (.tab i)) path fd ml fs h =
      .ok ((none, fs), { h with gzstates := upd h.gzstates i none }) := by
  rw [openAfterMode_copy_cut]
  cases mode <;> simp at hbad
  all_goals offsetsimp [hs, hm, hdone, hbad, modeCode, GZ_READ, GZ_WRITE, GZ_APPEND,
    GZ_NONE, freeGzState]

/-- Every accepted source mode reaches the common real copy stage, with the
exact single normalization write. No level, strategy or flag is fixed. -/
theorem openAfterMode_accepted (h : Heap) (fs : Fs) (i : Nat) (s : GzState)
    (path : BPtr) (fd : Int32) (ml : ModeLoop) (mode : ZlibF.Spec.Api.GzMode)
    (hs : h.gzstates i = some s) (hm : s.mode = modeCode (some mode))
    (hread : mode = .read → s.direct ≠ 1)
    (hwrite : mode ≠ .read → s.direct ≠ -1) (hdone : ml.done = false) :
    openAfterMode (some (.tab i)) path fd ml fs h =
      openCopyPath (some (.tab i)) path fd ml fs (checkedModeHeap h i s mode) := by
  rw [openAfterMode_copy_cut]
  cases mode with
  | read =>
    have hn := hread rfl
    by_cases hz : s.direct = 0 <;>
      offsetsimp [hs, hm, hdone, hn, hz, checkedModeHeap, modeCode, GZ_NONE,
        GZ_READ, GZ_WRITE, GZ_APPEND, setS]
  | write =>
    have hn := hwrite (by decide)
    offsetsimp [hs, hm, hdone, hn, checkedModeHeap, modeCode, GZ_NONE,
      GZ_READ, GZ_WRITE, GZ_APPEND]
  | append =>
    have hn := hwrite (by decide)
    offsetsimp [hs, hm, hdone, hn, checkedModeHeap, modeCode, GZ_NONE,
      GZ_READ, GZ_WRITE, GZ_APPEND]

/-- The actual checked heap contains the exact normalized record. -/
theorem checkedMode_state (h : Heap) (i : Nat) (s : GzState) (mode : ZlibF.Spec.Api.GzMode)
    (hs : h.gzstates i = some s) :
    (checkedModeHeap h i s mode).gzstates i = some (checkedModeRecord s mode) := by
  by_cases hc : mode = .read ∧ s.direct = 0 <;>
    simp [checkedModeHeap, checkedModeRecord, hc, setS, hs]

/-- The normalization preserves object kinds and all caller byte views. -/
theorem checkedMode_invariants (h : Heap) (i : Nat) (s : GzState)
    (mode : ZlibF.Spec.Api.GzMode) (hs : h.gzstates i = some s) (hf : Fresh h) (hu : Uniq h) :
    Fresh (checkedModeHeap h i s mode) ∧ Uniq (checkedModeHeap h i s mode) := by
  by_cases hc : mode = .read ∧ s.direct = 0
  · simp only [checkedModeHeap, hc, ite_true]
    exact ⟨Shape.fresh (shape_setS hs _) rfl hf, Shape.uniq (shape_setS hs _) hu⟩
  · simp [checkedModeHeap, hc, hf, hu]

theorem checkedMode_cstring (h : Heap) (i : Nat) (s : GzState)
    (mode : ZlibF.Spec.Api.GzMode) (p : BPtr) (bs : List UInt8)
    (hc : ZlibF.Spec.Public.CString h p bs) :
    ZlibF.Spec.Public.CString (checkedModeHeap h i s mode) p bs := by
  by_cases he : mode = .read ∧ s.direct = 0
  · simp only [checkedModeHeap, he, ite_true]
    exact openCString_setS h i _ p bs hc
  · simpa [checkedModeHeap, he] using hc

/-- No allocation counter or oracle changes during the real mode guards. -/
theorem checkedMode_counts (h : Heap) (i : Nat) (s : GzState) (mode : ZlibF.Spec.Api.GzMode) :
    (checkedModeHeap h i s mode).nextBlk = h.nextBlk ∧
    (checkedModeHeap h i s mode).nalloc = h.nalloc ∧
    (checkedModeHeap h i s mode).allocOk = h.allocOk := by
  by_cases he : mode = .read ∧ s.direct = 0 <;> simp [checkedModeHeap, he, setS]

/-- The public finish checks and source checks reject exactly the same direct
combinations. These are equalities to the original API parser's final stage. -/
theorem finish_some_iff (mode : ZlibF.Spec.Api.GzMode) (level : Int) (strategy : Nat)
    (direct : Int) :
    finish (some mode, level, strategy, direct, false) = some (mode, level, strategy, direct) ↔
      (mode = .read → direct ≠ 1) ∧ (mode ≠ .read → direct ≠ -1) := by
  by_cases hr : mode = .read ∧ direct = 1 <;>
    by_cases hw : mode ≠ .read ∧ direct = -1 <;> simp [finish, hr, hw]
  exact ⟨fun h₁ h₂ => hr ⟨h₁, h₂⟩, fun h₁ h₂ => hw ⟨h₁, h₂⟩⟩

#print axioms openAfterMode_absent
#print axioms openAfterMode_forbidden
#print axioms openAfterMode_accepted
#print axioms checkedMode_state
#print axioms checkedMode_invariants
#print axioms checkedMode_cstring
#print axioms checkedMode_counts
#print axioms finish_some_iff
end Zlib.Gzlib.Proofs
