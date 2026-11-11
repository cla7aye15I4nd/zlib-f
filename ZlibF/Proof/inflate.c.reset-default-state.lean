import ZlibF.Proof.«inflate.c.default-foundation»
import ZlibF.Proof.«inflate.c.reset»
import ZlibF.Proof.«inflate.c.block-type»
import ZlibF.Proof.«inflate.c.init»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

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

theorem platform_resetHeap {h : Heap} (platform : ZlibF.PlatformMemory.ByteObjectsFit h)
    (s : InflateState) : ZlibF.PlatformMemory.ByteObjectsFit (resetHeap h s) := by
  unfold resetHeap
  split
  · exact platform_freeWin platform s.window
  · exact platform

theorem resetHeap_static (h : Heap) (s : InflateState) :
    (resetHeap h s).static = h.static := by
  unfold resetHeap freeWin
  split
  · split <;> rfl
  · rfl

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
    · rcases invariant.window with range | ⟨zero, null, _⟩
      · exact Or.inl range
      · exact Or.inr ⟨zero, null, Or.inl stateMode⟩
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
        (resetKeepStream z (resetPre s)) (resetKeepState zs (resetPre s)) ∧ True := by
  obtain ⟨after, run, exactHeap, good, _⟩ :=
    inflateReset_safe invariant.good free
  subst after
  let H := resetHeap h s
  let stream := resetKeepStream z (resetPre s)
  let state := resetKeepState zs (resetPre s)
  have stateMode : state.mode = HEAD := rfl
  have sizes : ByteViewSizes H (setI (r.put H stream) zs state) :=
    (byte_view_sizes_stream_put H r stream).trans (byte_view_sizes_setI _ zs state)
  have pending : DataPendingInvariant state :=
    dataPendingInvariant_head (by rfl) stateMode
  have table : DataTableInvariant (setI (r.put H stream) zs state) state :=
    dataTableInvariant_inactive (by rw [stateMode]; unfold DataTableMode; decide)
  have stateBits : state.wbits = s.reqbits := by
    simp only [state, resetKeepState, resetPre]
    split <;> simp_all
  have stateReq : state.reqbits = s.reqbits := by
    simp only [state, resetKeepState, resetPre]
    try ((try split) <;> rfl)
  have window : (8 ≤ state.wbits.toNat ∧ state.wbits.toNat ≤ 15) ∨
      (state.wbits = 0 ∧ state.window = .null ∧
        (state.mode = HEAD ∨ state.mode = BAD ∨ state.mode = SYNC)) := by
    by_cases same : s.wbits = s.reqbits
    · have keep : state.window = s.window := by
        simp only [state, resetKeepState, resetPre, same, bne_self_eq_false, Bool.false_eq_true,
          ↓reduceIte]
      rw [stateBits, ← same, keep]
      rcases invariant.window with range | ⟨zero, null, _⟩
      · exact Or.inl range
      · exact Or.inr ⟨zero, null, Or.inl stateMode⟩
    · rcases invariant.requestedBits with equal | ⟨zero, _⟩
      · exact False.elim (same equal.symm)
      · have cleared : state.window = .null := by
          have differ : (s.wbits != s.reqbits) = true := by simpa using same
          simp only [state, resetKeepState, resetPre, differ, ↓reduceIte]
        exact Or.inr ⟨stateBits.trans zero, cleared, Or.inl stateMode⟩
  have wrapper : state.wrap = 0 ∨ state.wrap = 1 ∨ state.wrap = 5 := by
    have wrapEq : state.wrap = s.reqwrap := by
      simp only [state, resetKeepState, resetPre]
      try ((try split) <;> rfl)
    rw [wrapEq]
    exact invariant.requestedWrap
  have result : DefaultStateJ (setI (r.put H stream) zs state) r zs stream state := by
    refine ⟨⟨good, table, pending, ?_, ?_, ?_, window, wrapper, ?_, Or.inl stateMode,
      ?_, ?_, sizes.platform (platform_resetHeap invariant.platform s)⟩,
      Or.inl (stateReq.trans stateBits.symm), ?_, Or.inl stateMode⟩
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
      rw [resetHeap_static]
      exact invariant.globals
    · have reqwrapEq : state.reqwrap = s.reqwrap := by
        simp only [state, resetKeepState, resetPre]
        try ((try split) <;> rfl)
      rw [reqwrapEq]
      exact invariant.requestedWrap
  exact ⟨_, run, result, trivial⟩

#print axioms inflateReset_default_state

/-- Reset2 with a zlib window request of 8 to 15 bits retains J. If the
requested width differs from the current one, the actual call frees the old
window first; that heap change is part of the returned state. -/
theorem inflateReset2_default_state_of_params
    {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (invariant : DefaultStateJ h r zs z s)
    (free : z.zfree = .fn "zcfree") (wb : Int32) {code width : Int32}
    (params : reset2Params wb = some (code, width)) (kind : code = 0 ∨ code = 5)
    (bitsVal : 8 ≤ (i2u width).toNat ∧ (i2u width).toNat ≤ 15) :
    ∃ after,
      C.run (inflateReset2 (some r) wb) h = .ok (Z_OK, after) ∧
      DefaultStateJ after r zs
        (resetKeepStream z (resetPre (reset2Pre code width s)))
        (resetKeepState zs (resetPre (reset2Pre code width s))) := by
  obtain ⟨rc, after, run, result⟩ :=
    inflateReset2_safe invariant.good free wb
  rw [params] at result
  obtain ⟨rcEq, exactHeap, good, _⟩ := result
  subst rc
  subst after
  let H := reset2Heap h width s
  let stream := resetKeepStream z (resetPre (reset2Pre code width s))
  let state := resetKeepState zs (resetPre (reset2Pre code width s))
  have stateMode : state.mode = HEAD := rfl
  have sizes : ByteViewSizes H (setI (r.put H stream) zs state) :=
    (byte_view_sizes_stream_put H r stream).trans (byte_view_sizes_setI _ zs state)
  have pending : DataPendingInvariant state :=
    dataPendingInvariant_head (by rfl) stateMode
  have table : DataTableInvariant (setI (r.put H stream) zs state) state :=
    dataTableInvariant_inactive (by rw [stateMode]; unfold DataTableMode; decide)
  have stateBits : state.wbits = i2u width := by
    simp [state, resetKeepState, resetPre, reset2Pre]
  have stateReq : state.reqbits = i2u width := by
    simp [state, resetKeepState, resetPre, reset2Pre]
  have stateWrap : state.wrap = code := by
    simp [state, resetKeepState, resetPre, reset2Pre]
  have stateReqWrap : state.reqwrap = code := by
    simp [state, resetKeepState, resetPre, reset2Pre]
  have window : 8 ≤ state.wbits.toNat ∧ state.wbits.toNat ≤ 15 := by
    rw [stateBits]
    exact bitsVal
  have resultJ : DefaultStateJ (setI (r.put H stream) zs state) r zs stream state := by
    refine ⟨⟨good, table, pending, ?_, ?_, ?_, Or.inl window, (by rcases kind with k | k <;> rw [stateWrap, k] <;> simp), ?_, Or.inl stateMode,
      ?_, ?_, sizes.platform (platform_reset2Heap invariant.platform width s)⟩,
      Or.inl (stateReq.trans stateBits.symm), (by rcases kind with k | k <;> rw [stateReqWrap, k] <;> simp), Or.inl stateMode⟩
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

#print axioms inflateReset2_default_state_of_params

theorem inflateReset2_zlib_default_state
    {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (invariant : DefaultStateJ h r zs z s)
    (free : z.zfree = .fn "zcfree") (wb : Int32) (low : 8 ≤ wb.toInt) (high : wb.toInt ≤ 15) :
    ∃ after,
      C.run (inflateReset2 (some r) wb) h = .ok (Z_OK, after) ∧
      DefaultStateJ after r zs
        (resetKeepStream z (resetPre (reset2Pre 5 wb s)))
        (resetKeepState zs (resetPre (reset2Pre 5 wb s))) := by
  have value : ∀ v : Int, wb.toInt = v → wb = Int32.ofInt v := fun v e => by
    rw [← e, Int32.ofInt_toInt]
  have cases : wb.toInt = 8 ∨ wb.toInt = 9 ∨ wb.toInt = 10 ∨ wb.toInt = 11 ∨
      wb.toInt = 12 ∨ wb.toInt = 13 ∨ wb.toInt = 14 ∨ wb.toInt = 15 := by omega
  have params : reset2Params wb = some (5, wb) := by
    rcases cases with e | e | e | e | e | e | e | e <;> rw [value _ e] <;> decide
  have bitsVal : 8 ≤ (i2u wb).toNat ∧ (i2u wb).toNat ≤ 15 := by
    rcases cases with e | e | e | e | e | e | e | e <;> rw [value _ e] <;> decide
  exact inflateReset2_default_state_of_params invariant free wb params (Or.inr rfl) bitsVal

/-- Reset2 with a raw window request of 8 to 15 bits (`windowBits` -8..-15) retains J. -/
theorem inflateReset2_raw_default_state
    {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (invariant : DefaultStateJ h r zs z s)
    (free : z.zfree = .fn "zcfree") (wb : Int32) (low : -15 ≤ wb.toInt) (high : wb.toInt ≤ -8) :
    ∃ after,
      C.run (inflateReset2 (some r) wb) h = .ok (Z_OK, after) ∧
      DefaultStateJ after r zs
        (resetKeepStream z (resetPre (reset2Pre 0 (-wb) s)))
        (resetKeepState zs (resetPre (reset2Pre 0 (-wb) s))) := by
  have value : ∀ v : Int, wb.toInt = v → wb = Int32.ofInt v := fun v e => by
    rw [← e, Int32.ofInt_toInt]
  have cases : wb.toInt = -8 ∨ wb.toInt = -9 ∨ wb.toInt = -10 ∨ wb.toInt = -11 ∨
      wb.toInt = -12 ∨ wb.toInt = -13 ∨ wb.toInt = -14 ∨ wb.toInt = -15 := by omega
  have params : reset2Params wb = some (0, -wb) := by
    rcases cases with e | e | e | e | e | e | e | e <;> rw [value _ e] <;> decide
  have bitsVal : 8 ≤ (i2u (-wb)).toNat ∧ (i2u (-wb)).toNat ≤ 15 := by
    rcases cases with e | e | e | e | e | e | e | e <;> rw [value _ e] <;> decide
  exact inflateReset2_default_state_of_params invariant free wb params (Or.inl rfl) bitsVal

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
