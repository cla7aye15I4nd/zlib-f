import ZlibF.Proof.«inflate.c.origin-fields-primitives»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

theorem decoderOriginFields_setI {h : Heap} {zs : Nat} {old state : InflateState}
    (get : h.istates zs = some old) (window : originStateFields state = originStateFields old) :
    decoderOriginFields (setI h zs state) = decoderOriginFields h := by
  funext b
  by_cases same : b = zs
  · subst b
    simp only [decoderOriginFields, setI_istates_same, get, Option.map_some, window]
  · simp only [decoderOriginFields, setI_istates_ne h zs b state same]

theorem decoderOriginFields_byte_put (h : Heap) (ref : BRef) (array : Array UInt8) :
    decoderOriginFields (Space.put h ref array) = decoderOriginFields h := by
  cases ref <;> simp only [Space.put]
  all_goals repeat' first | rfl | split

theorem decoderOriginFields_word_put (h : Heap) (ref : WRef) (array : Array UInt16) :
    decoderOriginFields (Space.put h ref array) = decoderOriginFields h := by
  cases ref with
  | blk b => rfl
  | dstate_bl_count b => cases get : h.dstates b <;> simp only [Space.put, get] <;> rfl
  | istate_lens b =>
    cases get : h.istates b with
    | none => simp only [Space.put, get]
    | some state =>
      simp only [Space.put, get]
      exact decoderOriginFields_setI (state := { state with lens := array }) get rfl
  | istate_work b =>
    cases get : h.istates b with
    | none => simp only [Space.put, get]
    | some state =>
      simp only [Space.put, get]
      exact decoderOriginFields_setI (state := { state with work := array }) get rfl

theorem decoderOriginFields_code_put (h : Heap) (ref : CodeRef) (array : Array Code) :
    decoderOriginFields (Space.put h ref array) = decoderOriginFields h := by
  cases ref with
  | st_lenfix => rfl
  | st_distfix => rfl
  | istate_codes b =>
    cases get : h.istates b with
    | none => simp only [Space.put, get]
    | some state =>
      simp only [Space.put, get]
      exact decoderOriginFields_setI (state := { state with codes := array }) get rfl

/-- A state-field store preserves every decoder window whenever its
actual field update preserves the previous pointer. -/
theorem originFieldFrameM_wrS (r : ZStreamRef) (owner : InflateStatePtr)
    (update : InflateState → InflateState) (window : ∀ s, originStateFields (update s) = originStateFields s) :
    OriginFieldFrameM r owner (wrS owner update) := by
  intro h value after run
  cases owner with
  | none => cases run
  | some pointer =>
    cases pointer with
    | tab zs =>
      rw [wrI_eq] at run
      cases get : h.istates zs with
      | none => rw [get] at run; cases run
      | some state =>
        rw [get] at run
        cases run
        exact decoderOriginFields_setI get (window state)

theorem originFieldFrameM_wrZ (r : ZStreamRef) (owner : InflateStatePtr) (update : ZStream → ZStream) :
    OriginFieldFrameM r owner (wrZ (some r) update) := by
  intro h value after run
  rw [wrZ_eq] at run
  cases get : r.get h with
  | none => rw [get] at run; cases run
  | some stream =>
    rw [get] at run
    cases run
    funext b
    simp only [decoderOriginFields, ZStreamRef.put_istates]

section pointers
variable {R T : Type} [Space Heap R T]

theorem originFieldFrameM_ptr_store (r : ZStreamRef) (owner : InflateStatePtr) (p : Ptr R) (value : T)
    (writes : ∀ (h : Heap) (ref : R) (array : Array T), decoderOriginFields (Space.put h ref array) = decoderOriginFields h) :
    OriginFieldFrameM r owner (p.store value) := by
  intro h result after run
  cases p with
  | null => cases run
  | ref ref off =>
    cases get : Space.get h ref with
    | none => simp only [Ptr.store, get] at run; cases run
    | some array =>
      simp only [Ptr.store, get] at run
      split at run
      · cases run
      · split at run
        · rw [Space.modify_eq h ref array _ get] at run
          cases run
          exact writes h ref _
        · cases run
end pointers

theorem originFieldFrameM_store8 (r : ZStreamRef) (owner : InflateStatePtr) (p : BPtr) (value : UInt8) :
    OriginFieldFrameM r owner (store8 p value) := originFieldFrameM_ptr_store r owner p value decoderOriginFields_byte_put

theorem originFieldFrameM_store16 (r : ZStreamRef) (owner : InflateStatePtr) (p : WPtr) (value : UInt16) :
    OriginFieldFrameM r owner (p.store value) := originFieldFrameM_ptr_store r owner p value decoderOriginFields_word_put

theorem originFieldFrameM_storeCode (r : ZStreamRef) (owner : InflateStatePtr) (p : CodePtr) (value : Code) :
    OriginFieldFrameM r owner (p.store value) := originFieldFrameM_ptr_store r owner p value decoderOriginFields_code_put

/-- Every successful actual memcpy changes a byte view, which cannot
change a decoder window field. -/
theorem originFieldFrameM_memcpyB (r : ZStreamRef) (owner : InflateStatePtr) (destination source : BPtr) (count : Nat) :
    OriginFieldFrameM r owner (memcpyB destination source count) := by
  intro h value after run
  cases destination with
  | null => cases run
  | ref dest off =>
    cases source with
    | null => cases run
    | ref src srcOff =>
      cases destGet : (Space.get h dest : Option (Array UInt8)) <;>
        cases srcGet : (Space.get h src : Option (Array UInt8))
      all_goals simp only [memcpyB, Ptr.memcpy, destGet, srcGet] at run
      all_goals first | cases run | skip
      rename_i array sourceArray
      rw [Space.modify_eq h dest array _ destGet] at run
      repeat' first | split at run | (cases run <;> exact decoderOriginFields_byte_put h dest _)

end Zlib.Inflate.Proofs
