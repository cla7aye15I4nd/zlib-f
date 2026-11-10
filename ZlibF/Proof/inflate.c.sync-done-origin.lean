import ZlibF.Proof.«inflate.c.sync-search-heap»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The real recovery reset establishes TYPE with canonical table origins.
The retained default flag origin discharges the raw-or-zlib phase clause.
The requested fifteen-bit window prevents either recovery window free. -/
theorem syncDone_default_origin_run {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (before : DefaultOriginState h r zs z s)
    (free : z.zfree = .fn "zcfree") :
    C.run (syncDone (some r) (some (.tab zs))) h = .ok (Z_OK, syncOkHeap h r zs z s) ∧
      DefaultOriginState (syncOkHeap h r zs z s) r zs (syncOkStream z s) (syncOkState zs s) := by
  let state := syncOkState zs s
  let stream := syncOkStream z s
  have form : state = { syncC zs s with mode := TYPE } :=
    syncOkState_ne0 (by
      rw [before.requestedBits]
      intro zero
      have low := before.window.1
      rw [zero] at low
      simp at low)
  have mode : state.mode = TYPE := rfl
  have bits : (syncC zs s).wbits ≠ 0 := by
    rw [(syncC_field zs s).1, before.requestedBits]
    intro zero
    have low := before.window.1
    rw [zero] at low
    simp at low
  have unchanged : resetHeap h s = h := by
    simp [resetHeap, before.window, before.requestedBits]
  have heap : syncOkHeap h r zs z s = setI (r.put h stream) zs state := by
    simp [syncOkHeap, unchanged, bits, stream, state]
  have good := (syncDone_good before.good).1
  have tables : DataTableInvariant (syncOkHeap h r zs z s) state :=
    dataTableInvariant_inactive (by rw [mode]; unfold DataTableMode; decide)
  have sane : state.sane = 1 := by
    rw [form]
    unfold syncC
    split <;> rfl
  have pending : DataPendingInvariant state := dataPendingInvariant_idle sane (by rw [mode]; decide)
  have sizes := (byte_view_sizes_stream_put h r stream).trans
    (byte_view_sizes_setI (r.put h stream) zs state)
  have platform : ZlibF.PlatformMemory.ByteObjectsFit (syncOkHeap h r zs z s) := by
    rw [heap]
    exact sizes.platform before.platform
  have flags : state.flags = s.flags := by
    rw [form]
    unfold syncC
    split <;> rfl
  have wrapper : state.wrap = 0 ∨ state.wrap = 1 ∨ state.wrap = 5 := by
    rw [form]
    rcases before.flagsOrigin with flag | flag
    all_goals rcases before.requestedWrap with request | request
    all_goals simp [syncC, resetKeepState, resetPre, before.window, before.requestedBits, flag, request]
    all_goals decide
  have phase : state.wrap = 0 ∨ state.flags = 0 := by
    rcases before.flagsOrigin with flag | flag
    · left
      rw [form]
      simp [syncC, flag]
    · exact Or.inr (flags.trans flag)
  have current : DefaultStateJ (syncOkHeap h r zs z s) r zs stream state := by
    refine ⟨⟨good, tables, pending, ?_, ?_, ?_, ?_, wrapper, ?_, Or.inr ?_, ?_, ?_, platform⟩,
      ?_, ?_, Or.inr (Or.inr (Or.inr (Or.inr phase)))⟩
    · intro active
      rw [mode] at active
      contradiction
    · intro active
      rw [mode] at active
      contradiction
    · rw [form]
      unfold syncC
      split <;> change (0 : UInt64).toNat < 2 ^ (0 : UInt32).toNat <;> decide
    · rw [form]
      simpa [syncC_field] using (show 8 ≤ (syncC zs s).wbits.toNat ∧ (syncC zs s).wbits.toNat ≤ 15 by
        rw [(syncC_field zs s).1, before.requestedBits]
        exact before.window)
    · rw [form]
      unfold syncC
      split <;> rfl
    · rw [mode]
      decide
    · rintro (active | active) <;> rw [mode] at active <;> contradiction
    · change (syncOkHeap h r zs z s).static = _
      rw [heap]
      simpa only [LibraryGlobals, setI, ZStreamRef.put_static] using before.globals
    · rw [form]
      unfold syncC
      split <;> simpa [resetKeepState, resetPre, before.window, before.requestedBits] using before.requestedBits
    · rw [form]
      unfold syncC
      split <;> simpa [resetKeepState, resetPre, before.window, before.requestedBits] using before.requestedWrap
  refine ⟨syncDone_run before.good free, ⟨current, ?_, ?_⟩⟩
  · rw [flags]
    exact before.flagsOrigin
  · change CopyTableOrigin zs state
    rw [form]
    unfold CopyTableOrigin syncC
    split <;> exact Or.inl rfl

#print axioms syncDone_default_origin_run
end Zlib.Inflate.Proofs
