import ZlibF.Proof.«gzlib.c.seek»

/-!
# gz: `gzseek64` in the raw area needs `GzReadInv.posHave`

In the raw area (`how == COPY`) `gzseek64` computes `pos - state->x.pos - state->x.have` in `z_off64_t`. That
expression overflows when `x.pos + x.have` is above `GZ_OFF_MAX` and the target is small. `GzReadInv.posHave`
(`x.pos + x.have ≤ GZ_OFF_MAX`) excludes this; without the clause, `gzseek64_step` would be false.

The record below has `x.pos = GZ_OFF_MAX` and two buffered bytes, so it breaks `posHave` and only that clause of the
seek's hypotheses. `gzseek64(file, 0, SEEK_SET)` on it faults with a signed overflow. The state is constructed, not
reached by a public history: the point is that the clause is needed, not that the state is reachable.
-/

namespace GzSeekPosHaveRegression
open C Zlib.GzFs Zlib.Gzguts Zlib.Gzlib Zlib.Gzlib.Spec Zlib.Gzlib.Proofs

/-- A reader in the raw area at `x.pos = GZ_OFF_MAX` with two bytes buffered. -/
def badState : GzState :=
  { GzState.zeroed with
    mode := GZ_READ, how := GZ_COPY, err := Z_OK, skip := 0, past := 0, msg := .null
    x := { GzFile.zeroed with «have» := 2, pos := GZ_OFF_MAX } }

/-- The heap holding only that record, as handle 0. -/
def badHeap : Heap := setS Heap.empty 0 badState

/-- The record breaks `GzReadInv.posHave`. -/
theorem badState_breaks_posHave :
    ¬ (badState.x.pos.toInt + badState.x.«have».toNat ≤ 9223372036854775807) := by
  show ¬ (GZ_OFF_MAX.toInt + ((2 : UInt32).toNat : Int) ≤ 9223372036854775807)
  rw [GZ_OFF_MAX_toInt, OffMax_val]
  decide

/-- `gzseek64(file, 0, SEEK_SET)` on the record faults: `pos - x.pos - x.have` overflows. -/
theorem seek_faults (fs : Fs) :
    gzseek64 (hnd 0) 0 SEEK_SET fs badHeap = .error (.ub "signed overflow (long)") := by
  have hpos : badState.x.pos.toInt = 9223372036854775807 := by
    show GZ_OFF_MAX.toInt = _
    rw [GZ_OFF_MAX_toInt, OffMax_val]
  have hhv : (badState.x.«have».toNat : Int) = 2 := rfl
  have hskip : badState.skip.toInt = 0 := rfl
  have hG : SeekGood badHeap 0 badState :=
    ⟨setS_gz_same _ _ _, Or.inl rfl, Or.inl rfl, fun _ => rfl⟩
  have htp : tellPos badState = 9223372036854775807 := by
    unfold tellPos tellSkip
    rw [ite_eq_right (by decide), hskip, hpos]
    rfl
  have hP : PosInv badState := ⟨by rw [hskip]; decide, by rw [htp]; decide, by rw [htp]; decide⟩
  have hT : seekT badState 0 SEEK_SET = 0 := by
    simp [seekT, seekBase]
  have hok : SeekOkAt badState 0 := ⟨⟨Int.le_refl _, by rw [OffMax_val]; decide⟩, fun h => by omega⟩
  rw [gzseek64_head_any hG hP (Or.inl rfl) (Or.inl rfl) (fun h => absurd h (by decide)) 0 fs, hT, ite_eq_left hok]
  exact seekTail_copy_ub hG rfl rfl (by omega) ⟨Int.le_refl _, by rw [OffMax_val]; decide⟩ (by omega) fs

#print axioms badState_breaks_posHave
#print axioms seek_faults

end GzSeekPosHaveRegression
