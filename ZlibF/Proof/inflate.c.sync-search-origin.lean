import ZlibF.Proof.«inflate.c.sync-done-origin»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The sync input-search state write changes only its scalar search count
and stream cursors. The exact pointer value comes from actual arithmetic;
it need not be supplied as a callee safety contract. -/
theorem default_origin_sync_search_state {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (before : DefaultOriginState h r zs z s)
    (mode : s.mode = SYNC) (used found : UInt32) (next : BPtr) :
    let stream := { z with avail_in := z.avail_in - used, next_in := next, total_in := z.total_in + used.toUInt64 }
    DefaultOriginState (setI (r.put h stream) zs (syncHave s found)) r zs stream (syncHave s found) := by
  dsimp only
  let stream := { z with avail_in := z.avail_in - used, next_in := next, total_in := z.total_in + used.toUInt64 }
  let state := syncHave s found
  have currentMode : state.mode = SYNC := mode
  have inv : StInv h zs state := before.good.inv.of_fields rfl rfl rfl rfl rfl rfl rfl rfl rfl
    before.good.inv.bits rfl rfl rfl
  have good : Good (setI (r.put h stream) zs state) r zs stream state :=
    before.good.setZI rfl before.good.live.zalloc before.good.live.zfree rfl before.good.live.mode inv
  have tables : DataTableInvariant (setI (r.put h stream) zs state) state :=
    dataTableInvariant_inactive (by rw [currentMode]; unfold DataTableMode; decide)
  have pending : DataPendingInvariant state :=
    dataPendingInvariant_idle before.pending.sane (by rw [currentMode]; decide)
  have sizes := (byte_view_sizes_stream_put h r stream).trans
    (byte_view_sizes_setI (r.put h stream) zs state)
  have current : DefaultStateJ (setI (r.put h stream) zs state) r zs stream state := by
    refine ⟨⟨good, tables, pending, ?_, ?_, before.held, before.window, before.wrapper,
      before.header, Or.inr ?_, ?_, ?_, sizes.platform before.platform⟩,
      before.requestedBits, before.requestedWrap, Or.inr (Or.inr (Or.inr (Or.inl currentMode)))⟩
    · intro active
      change state.mode = CODELENS at active
      rw [currentMode] at active
      contradiction
    · intro active
      change state.mode = LENLENS at active
      rw [currentMode] at active
      contradiction
    · rw [currentMode]
      decide
    · rintro (active | active) <;> rw [currentMode] at active <;> contradiction
    · simpa only [LibraryGlobals, setI, ZStreamRef.put_static] using before.globals
  exact ⟨current, before.flagsOrigin, before.tableOrigin⟩

#print axioms default_origin_sync_search_state
end Zlib.Inflate.Proofs
