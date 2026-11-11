import ZlibF.Proof.«inflate.c.sync-held-origin»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The real local four-byte allocation retains both source origins. -/
theorem default_origin_syncAlloc {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (before : DefaultOriginState h r zs z s) :
    DefaultOriginState (syncAlloc h) r zs z s :=
  ⟨default_state_syncAlloc before.toDefaultStateJ, before.tableOrigin⟩

/-- The exact sync-restore heap establishes the empty bit buffer and
retains every default clause, including origins. Its scratch byte block
is distinct from the private window; the public wrapper supplies it by
actual fresh local allocation. -/
theorem default_origin_syncFirstHeap {h : Heap} {r : ZStreamRef} {zs nb : Nat}
    {z : ZStream} {s : InflateState} {array : Array UInt8}
    (before : DefaultOriginState h r zs z s) (get : h.bytes nb = some array)
    (size : array.size = 4) (separate : ∀ w, s.window = .ref (.blk w) 0 → w ≠ nb) :
    DefaultOriginState (syncFirstHeap h zs nb s array) r zs z (syncFirstState s) := by
  have good := good_firstState before.good get separate
  have tables : DataTableInvariant (syncFirstHeap h zs nb s array) (syncFirstState s) :=
    dataTableInvariant_inactive (by change ¬ DataTableMode SYNC; unfold DataTableMode; decide)
  have pending : DataPendingInvariant (syncFirstState s) :=
    dataPendingInvariant_idle before.pending.sane (by
      change SYNC ≠ LENEXT ∧ SYNC ≠ DIST ∧ SYNC ≠ DISTEXT ∧ SYNC ≠ MATCH
      decide)
  have bounded : (fillBuf array (syncHold0 s) (syncNB s)).size < ZlibF.PlatformMemory.byteObjectLimit := by
    rw [fillBuf_size, size]
    change 4 < 2 ^ 63
    decide
  have platform := (before.platform.with_bytes (block := nb) bounded).with_istates
    (upd h.istates zs (some (syncFirstState s)))
  have current : DefaultStateJ (syncFirstHeap h zs nb s array) r zs z (syncFirstState s) := by
    refine ⟨⟨good, tables, pending, ?_, ?_, ?_, before.window, before.wrapper,
      before.header, Or.inr ?_, ?_, ?_, platform⟩,
      before.requestedBits, before.requestedWrap, Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩
    · intro active
      exact False.elim ((by decide : SYNC ≠ CODELENS) active)
    · intro active
      exact False.elim ((by decide : SYNC ≠ LENLENS) active)
    · change (syncFirstState s).hold.toNat < 2 ^ (0 : UInt32).toNat
      rw [syncFirstState_hold_zero before.held]
      decide
    · left
      change DICTID ≤ SYNC ∧ SYNC ≤ SYNC
      decide
    · rintro (active | active)
      · exact False.elim ((by decide : SYNC ≠ CHECK) active)
      · exact False.elim ((by decide : SYNC ≠ LENGTH) active)
    · exact before.globals
  exact ⟨current, before.tableOrigin⟩

/-- The actual translated restore-and-search prefix terminates and
establishes the strengthened state. The scratch block's actual four-byte
shape and writable flag discharge its source reads and stores. -/
theorem syncFirst_default_origin_run {h : Heap} {r : ZStreamRef} {zs nb : Nat}
    {z : ZStream} {s : InflateState} {array : Array UInt8}
    (before : DefaultOriginState h r zs z s) (get : h.bytes nb = some array)
    (size : array.size = 4) (write : h.ro nb = false)
    (separate : ∀ w, s.window = .ref (.blk w) 0 → w ≠ nb) :
    C.run (syncFirst (some (.tab zs)) (.ref (.blk nb) 0) s) h =
      .ok ((), syncFirstHeap h zs nb s array) ∧
      DefaultOriginState (syncFirstHeap h zs nb s array) r zs z (syncFirstState s) :=
  ⟨syncFirst_run before.good.live.hs get size write before.good.inv.bits,
    default_origin_syncFirstHeap before get size separate⟩

/-- The actual local allocation supplies every scratch-buffer premise of
the sync restore prefix. No scratch-memory or callee contract is assumed. -/
theorem syncFirst_default_local_origin_run {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (before : DefaultOriginState h r zs z s) :
    C.run (do
      let buffer ← allocLocalB 4
      syncFirst (some (.tab zs)) buffer s) h =
        .ok ((), syncFirstHeap (syncAlloc h) zs h.nextBlk s (syncJunk h)) ∧
      DefaultOriginState (syncFirstHeap (syncAlloc h) zs h.nextBlk s (syncJunk h))
        r zs z (syncFirstState s) := by
  have current := default_origin_syncAlloc before
  have separate := win_ne_buf before.good.fresh before.good.inv.win
  obtain ⟨run, next⟩ := syncFirst_default_origin_run current
    (syncAlloc_bytes_buf h) (by simp [syncJunk]) (syncAlloc_ro_buf h) separate
  refine ⟨?_, next⟩
  change (do
    let buffer ← allocLocalB 4
    syncFirst (some (.tab zs)) buffer s) h = _
  rw [bind_app, allocLocalB_run h before.good.fresh]
  exact run

#print axioms default_origin_syncAlloc
#print axioms default_origin_syncFirstHeap
#print axioms syncFirst_default_origin_run
#print axioms syncFirst_default_local_origin_run
end Zlib.Inflate.Proofs
