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
  have sameBits : s.wbits = s.reqbits := by
    rw [invariant.window, invariant.requestedBits]
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
  have window : state.wbits = 15 := by
    simpa [state, resetKeepState, resetPre, sameBits] using invariant.requestedBits
  have wrapper : state.wrap = 0 ∨ state.wrap = 1 ∨ state.wrap = 5 := by
    simpa [state, resetKeepState, resetPre, sameBits] using
      (Or.inr invariant.requestedWrap : s.reqwrap = 0 ∨ s.reqwrap = 1 ∨ s.reqwrap = 5)
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

/-- The default-window Reset2 call retains J. This theorem covers only
`windowBits = 15`; other legal Reset2 configurations need their own history
relation. The current default window width is already fifteen, so this
call does not free it. -/
theorem inflateReset2_15_default_state
    {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (invariant : DefaultStateJ h r zs z s)
    (free : z.zfree = .fn "zcfree") :
    ∃ after,
      C.run (inflateReset2 (some r) 15) h = .ok (Z_OK, after) ∧
      DefaultStateJ after r zs
        (resetKeepStream z (resetPre (reset2Pre 5 15 s)))
        (resetKeepState zs (resetPre (reset2Pre 5 15 s))) ∧
      (∀ b, after.live b ↔ h.live b) := by
  have bits : s.wbits = 15 := invariant.window
  have bit15 : i2u (15 : Int32) = (15 : UInt32) := by decide
  have heapEq : reset2Heap h 15 s = h := by
    simp [reset2Heap, bits, bit15]
  obtain ⟨rc, after, run, result⟩ :=
    inflateReset2_safe invariant.good free 15
  have params : reset2Params 15 = some (5, 15) := by decide
  rw [params] at result
  obtain ⟨rcEq, exactHeap, good, _⟩ := result
  subst rc
  subst after
  rw [heapEq] at run good
  let stream := resetKeepStream z (resetPre (reset2Pre 5 15 s))
  let state := resetKeepState zs (resetPre (reset2Pre 5 15 s))
  have stateMode : state.mode = HEAD := rfl
  have sizes : ByteViewSizes h (setI (r.put h stream) zs state) :=
    (byte_view_sizes_stream_put h r stream).trans (byte_view_sizes_setI _ zs state)
  have pending : DataPendingInvariant state :=
    dataPendingInvariant_head (by rfl) stateMode
  have table : DataTableInvariant (setI (r.put h stream) zs state) state :=
    dataTableInvariant_inactive (by rw [stateMode]; unfold DataTableMode; decide)
  have window : state.wbits = 15 := by
    simp [state, resetKeepState, resetPre, reset2Pre, bits, bit15]
  have wrapper : state.wrap = 0 ∨ state.wrap = 1 ∨ state.wrap = 5 := by
    simp [state, resetKeepState, resetPre, reset2Pre, bits, bit15]
  have resultJ : DefaultStateJ (setI (r.put h stream) zs state) r zs stream state := by
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
    · simp [state, resetKeepState, resetPre, reset2Pre, bits, bit15]
    · simp [state, resetKeepState, resetPre, reset2Pre, bits, bit15]
  have shape : Shape h (setI (r.put h stream) zs state) :=
    (shape_put invariant.good.live.hz stream).trans
      (shape_setI (by simpa using invariant.good.live.hs) state)
  exact ⟨_, run, resultJ, fun b => shape.live b⟩

#print axioms inflateReset2_15_default_state
end Zlib.Inflate.Proofs
