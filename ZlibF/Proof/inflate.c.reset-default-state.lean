import ZlibF.Proof.«inflate.c.default-foundation»
import ZlibF.Proof.«inflate.c.reset»
import ZlibF.Proof.«inflate.c.block-type»
import ZlibF.Proof.«inflate.c.init»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The translated reset-keep call returns the stream to HEAD while
retaining the initialized default configuration and window. -/
theorem inflateResetKeep_default_state
    {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (invariant : DefaultStateJ h r zs z s) :
    ∃ after,
      C.run (inflateResetKeep (some r)) h = .ok (Z_OK, after) ∧
      after = setI (r.put h (resetKeepStream z s)) zs (resetKeepState zs s) ∧
      DefaultStateJ after r zs (resetKeepStream z s) (resetKeepState zs s) ∧
      (∀ b, after.live b ↔ h.live b) := by
  obtain ⟨after, run, exactHeap, good, live⟩ :=
    inflateResetKeep_safe invariant.good
  subst after
  let stream := resetKeepStream z s
  let state := resetKeepState zs s
  have stateMode : state.mode = HEAD := rfl
  have sizes : ByteViewSizes h (setI (r.put h stream) zs state) :=
    (byte_view_sizes_stream_put h r stream).trans (byte_view_sizes_setI _ zs state)
  have pending : DataPendingInvariant state :=
    dataPendingInvariant_head (by rfl) stateMode
  have table : DataTableInvariant (setI (r.put h stream) zs state) state :=
    dataTableInvariant_inactive (by rw [stateMode]; unfold DataTableMode; decide)
  have result : DefaultStateJ (setI (r.put h stream) zs state) r zs stream state := by
    refine ⟨⟨good, table, pending, ?_, ?_, ?_, ?_, ?_, ?_, Or.inl stateMode,
      ?_, ?_, sizes.platform invariant.platform⟩, ?_, ?_, Or.inl stateMode⟩
    · intro active
      rw [stateMode] at active
      contradiction
    · intro active
      rw [stateMode] at active
      contradiction
    · change (0 : UInt64).toNat < 2 ^ (0 : UInt32).toNat
      decide
    · exact invariant.window
    · exact invariant.wrapper
    · rfl
    · rintro (active | active) <;> rw [stateMode] at active <;> contradiction
    · simpa only [LibraryGlobals, setI, ZStreamRef.put_static] using invariant.globals
    · exact invariant.requestedBits
    · exact invariant.requestedWrap
  exact ⟨_, run, rfl, result, live⟩

#print axioms inflateResetKeep_default_state

/-- The standard default reset returns to HEAD without freeing a window:
the requested and active window widths are both fifteen. The free callback
fact is carried by the initialized default allocator history. -/
theorem inflateReset_default_state
    {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (invariant : DefaultStateJ h r zs z s)
    (free : z.zfree = .fn "zcfree") :
    ∃ after,
      C.run (inflateReset (some r)) h = .ok (Z_OK, after) ∧
      DefaultStateJ after r zs
        (resetKeepStream z (resetPre s)) (resetKeepState zs (resetPre s)) ∧
      (∀ b, after.live b ↔ h.live b) := by
  have sameBits : s.wbits = s.reqbits := invariant.requestedBits.symm
  obtain ⟨after, run, exactHeap, good, _⟩ :=
    inflateReset_safe invariant.good free
  subst after
  have resetHeapEq : resetHeap h s = h := by
    simp [resetHeap, sameBits]
  rw [resetHeapEq] at run good
  let stream := resetKeepStream z (resetPre s)
  let state := resetKeepState zs (resetPre s)
  have stateMode : state.mode = HEAD := rfl
  have sizes : ByteViewSizes h (setI (r.put h stream) zs state) :=
    (byte_view_sizes_stream_put h r stream).trans (byte_view_sizes_setI _ zs state)
  have pending : DataPendingInvariant state :=
    dataPendingInvariant_head (by rfl) stateMode
  have table : DataTableInvariant (setI (r.put h stream) zs state) state :=
    dataTableInvariant_inactive (by rw [stateMode]; unfold DataTableMode; decide)
  have window : 8 ≤ state.wbits.toNat ∧ state.wbits.toNat ≤ 15 := by
    simpa [state, resetKeepState, resetPre, sameBits] using invariant.window
  have wrapper : state.wrap = 0 ∨ state.wrap = 1 ∨ state.wrap = 5 := by
    simpa [state, resetKeepState, resetPre, sameBits] using
      (invariant.requestedWrap : s.reqwrap = 0 ∨ s.reqwrap = 1 ∨ s.reqwrap = 5)
  have result : DefaultStateJ (setI (r.put h stream) zs state) r zs stream state := by
    refine ⟨⟨good, table, pending, ?_, ?_, ?_, window, wrapper, ?_, Or.inl stateMode,
      ?_, ?_, sizes.platform invariant.platform⟩, ?_, ?_, Or.inl stateMode⟩
    · intro active
      rw [stateMode] at active
      contradiction
    · intro active
      rw [stateMode] at active
      contradiction
    · change (0 : UInt64).toNat < 2 ^ (0 : UInt32).toNat
      decide
    · rfl
    · rintro (active | active) <;> rw [stateMode] at active <;> contradiction
    · simpa only [LibraryGlobals, setI, ZStreamRef.put_static] using invariant.globals
    · simpa [state, resetKeepState, resetPre, sameBits] using invariant.requestedBits
    · simpa [state, resetKeepState, resetPre, sameBits] using invariant.requestedWrap
  have shape : Shape h (setI (r.put h stream) zs state) :=
    (shape_put invariant.good.live.hz stream).trans
      (shape_setI (by simpa using invariant.good.live.hs) state)
  exact ⟨_, run, result, fun b => shape.live b⟩

#print axioms inflateReset_default_state

/-- Freeing the window (or nothing) cannot create an oversized byte view. -/
theorem platform_freeWin {h : Heap} (platform : ZlibF.PlatformMemory.ByteObjectsFit h) (p : BPtr) :
    ZlibF.PlatformMemory.ByteObjectsFit (freeWin h p) := by
  intro ref array get
  unfold freeWin at get
  split at get
  · rename_i block
    cases ref with
    | blk b =>
      by_cases same : b = block
      · subst b
        simp only [Space.get, upd_same] at get
        cases get
      · have old : h.bytes b = some array := by
          simpa only [Space.get, upd_ne _ _ _ _ same] using get
        exact platform (BRef.blk b) array old
    | str index => exact platform (.str index) array get
    | dstate_depth index => exact platform (.dstate_depth index) array get
    | st_dist_code => exact platform .st_dist_code array get
    | st_length_code => exact platform .st_length_code array get
  · exact platform ref array get

theorem platform_reset2Heap {h : Heap} (platform : ZlibF.PlatformMemory.ByteObjectsFit h)
    (wb : Int32) (s : InflateState) : ZlibF.PlatformMemory.ByteObjectsFit (reset2Heap h wb s) := by
  unfold reset2Heap
  split
  · exact platform_freeWin platform s.window
  · exact platform

theorem reset2Heap_static (h : Heap) (wb : Int32) (s : InflateState) :
    (reset2Heap h wb s).static = h.static := by
  unfold reset2Heap freeWin
  split
  · split <;> rfl
  · rfl

/-- Reset2 with a zlib window request of 8 to 15 bits retains J. If the
requested width differs from the current one, the actual call frees the old
window first; that heap change is part of the returned state. -/
theorem inflateReset2_zlib_default_state
    {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (invariant : DefaultStateJ h r zs z s)
    (free : z.zfree = .fn "zcfree") (wb : Int32) (low : 8 ≤ wb.toInt) (high : wb.toInt ≤ 15) :
    ∃ after,
      C.run (inflateReset2 (some r) wb) h = .ok (Z_OK, after) ∧
      DefaultStateJ after r zs
        (resetKeepStream z (resetPre (reset2Pre 5 wb s)))
        (resetKeepState zs (resetPre (reset2Pre 5 wb s))) := by
  obtain ⟨rc, after, run, result⟩ :=
    inflateReset2_safe invariant.good free wb
  have value : ∀ v : Int, wb.toInt = v → wb = Int32.ofInt v := fun v e => by
    rw [← e, Int32.ofInt_toInt]
  have cases : wb.toInt = 8 ∨ wb.toInt = 9 ∨ wb.toInt = 10 ∨ wb.toInt = 11 ∨
      wb.toInt = 12 ∨ wb.toInt = 13 ∨ wb.toInt = 14 ∨ wb.toInt = 15 := by omega
  have params : reset2Params wb = some (5, wb) := by
    rcases cases with e | e | e | e | e | e | e | e <;> rw [value _ e] <;> decide
  have bitsVal : 8 ≤ (i2u wb).toNat ∧ (i2u wb).toNat ≤ 15 := by
    rcases cases with e | e | e | e | e | e | e | e <;> rw [value _ e] <;> decide
  rw [params] at result
  obtain ⟨rcEq, exactHeap, good, _⟩ := result
  subst rc
  subst after
  let H := reset2Heap h wb s
  let stream := resetKeepStream z (resetPre (reset2Pre 5 wb s))
  let state := resetKeepState zs (resetPre (reset2Pre 5 wb s))
  have stateMode : state.mode = HEAD := rfl
  have sizes : ByteViewSizes H (setI (r.put H stream) zs state) :=
    (byte_view_sizes_stream_put H r stream).trans (byte_view_sizes_setI _ zs state)
  have pending : DataPendingInvariant state :=
    dataPendingInvariant_head (by rfl) stateMode
  have table : DataTableInvariant (setI (r.put H stream) zs state) state :=
    dataTableInvariant_inactive (by rw [stateMode]; unfold DataTableMode; decide)
  have stateBits : state.wbits = i2u wb := by
    simp [state, resetKeepState, resetPre, reset2Pre]
  have stateReq : state.reqbits = i2u wb := by
    simp [state, resetKeepState, resetPre, reset2Pre]
  have stateWrap : state.wrap = 5 := by
    simp [state, resetKeepState, resetPre, reset2Pre]
  have stateReqWrap : state.reqwrap = 5 := by
    simp [state, resetKeepState, resetPre, reset2Pre]
  have window : 8 ≤ state.wbits.toNat ∧ state.wbits.toNat ≤ 15 := by
    rw [stateBits]
    exact bitsVal
  have resultJ : DefaultStateJ (setI (r.put H stream) zs state) r zs stream state := by
    refine ⟨⟨good, table, pending, ?_, ?_, ?_, window, Or.inr (Or.inr stateWrap), ?_, Or.inl stateMode,
      ?_, ?_, sizes.platform (platform_reset2Heap invariant.platform wb s)⟩,
      stateReq.trans stateBits.symm, Or.inr (Or.inr stateReqWrap), Or.inl stateMode⟩
    · intro active
      rw [stateMode] at active
      contradiction
    · intro active
      rw [stateMode] at active
      contradiction
    · change (0 : UInt64).toNat < 2 ^ (0 : UInt32).toNat
      decide
    · rfl
    · rintro (active | active) <;> rw [stateMode] at active <;> contradiction
    · change (setI (r.put H stream) zs state).static = _
      simp only [setI, ZStreamRef.put_static]
      rw [reset2Heap_static]
      exact invariant.globals
  exact ⟨_, run, resultJ⟩

#print axioms inflateReset2_zlib_default_state

/-- The default-window Reset2 call retains J, for every current window width. -/
theorem inflateReset2_15_default_state
    {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (invariant : DefaultStateJ h r zs z s)
    (free : z.zfree = .fn "zcfree") :
    ∃ after,
      C.run (inflateReset2 (some r) 15) h = .ok (Z_OK, after) ∧
      DefaultStateJ after r zs
        (resetKeepStream z (resetPre (reset2Pre 5 15 s)))
        (resetKeepState zs (resetPre (reset2Pre 5 15 s))) ∧ True := by
  obtain ⟨after, run, next⟩ :=
    inflateReset2_zlib_default_state invariant free 15 (by decide) (by decide)
  exact ⟨after, run, next, trivial⟩

#print axioms inflateReset2_15_default_state
end Zlib.Inflate.Proofs
