import ZlibF.Proof.«inflate.c.local-window-run»

/-! Exact actual allocation origin, counters, frame and live ledger for
all returning window branches under the local decoder representation. -/
namespace Zlib.Inflate.Local
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- The very same returned window heap retains allocation origin and all
resource effects. The new-window root is exactly the old next identity; no
lower bound on caller uniqueness or synthetic global Good is used. -/
theorem updatewindow_local_effects {h after : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s state : InflateState} {eo : Nat} {source : BRef}
    {bytes : Array UInt8} {copy : UInt32} {rc : Int32}
    (good : LocalGood h cutoff r zs z s) (allocator : z.zalloc = .fn "zcalloc")
    (get : Space.get h source = some bytes) (count : copy.toNat ≤ eo) (bound : eo ≤ bytes.size)
    (separate : Separate (.ref source (eo - copy.toNat)) copy.toNat s.window (2 ^ s.wbits.toNat))
    (run : updatewindow (some r) (.ref source eo) copy h = .ok (rc, after))
    (stored : after.istates zs = some state) :
    Frame h after (fun b => StreamRoot r b ∨ InflateOwned zs s b) ∧
    LiveChange h after (fun b => s.window = .null ∧ h.allocOk h.nalloc = true ∧ b = h.nextBlk) (fun _ => False) ∧
    after.nextBlk = h.nextBlk + (if s.window = .null ∧ h.allocOk h.nalloc = true then 1 else 0) ∧
    after.nalloc = h.nalloc + (if s.window = .null then 1 else 0) ∧
    (state.window = s.window ∨ (s.window = .null ∧ state.window = .ref (.blk h.nextBlk) 0)) := by
  rcases good.inv.win.block with window | ⟨w, a, window, array, ro, size⟩
  · by_cases alloc : h.allocOk h.nalloc = true
    · have actual := uw_new_local_exact good allocator window alloc get count bound
      have heaps : after = localWindowNewHeap h zs s bytes eo copy :=
        congrArg Prod.snd (Except.ok.inj (run.symm.trans actual))
      subst after
      have states : state = localWindowNewState h s bytes eo copy := by
        simp only [localWindowNewHeap, setI_istates_same] at stored
        exact (Option.some.inj stored).symm
      refine ⟨localWindowNewHeap_frame good.fresh bytes eo copy, ?_, ?_, ?_, Or.inr ⟨window, ?_⟩⟩
      · simpa [window, alloc] using localWindowNewHeap_live good.live.hs bytes eo copy
      · simpa [window, alloc] using (localWindowNewHeap_counts h zs s bytes eo copy).1
      · simpa [window] using (localWindowNewHeap_counts h zs s bytes eo copy).2.1
      · rw [states]
        exact localWindowNewState_origin h s bytes eo copy
    · have actual := uw_alloc_fail good.live allocator good.inv.win.wbits window alloc (.ref source eo) copy
      have heaps : after = setI {h with nalloc := h.nalloc + 1} zs s :=
        congrArg Prod.snd (Except.ok.inj (run.symm.trans actual))
      have self : setI {h with nalloc := h.nalloc + 1} zs s = {h with nalloc := h.nalloc + 1} :=
        tcSetI_same good.live.hs
      rw [heaps, self] at stored ⊢
      have states : state = s := (Option.some.inj (stored.symm.trans good.live.hs))
      refine ⟨?_, ?_, by simp [window, alloc], by simp [window], Or.inl (by rw [states])⟩
      · refine ⟨rfl, rfl, rfl, Nat.le_refl _, by simp, ?_⟩
        intro b _ _
        exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      · intro b
        simp [window, alloc, Heap.live]
  · have nonnull : s.window ≠ .null := by rw [window]; simp
    obtain ⟨result, nextState, actual, heapEq, value, nextGood, sameWindow,
        _, _, _, live, next⟩ := uw_post_local good window array ro size get count bound separate
    have heaps : after = result := congrArg Prod.snd (Except.ok.inj (run.symm.trans actual))
    rw [heaps] at stored ⊢
    have states : state = nextState := Option.some.inj (stored.symm.trans nextGood.live.hs)
    refine ⟨?_, ?_, ?_, ?_, Or.inl (states ▸ sameWindow)⟩
    · rw [heapEq]
      exact uw_existing_frame window
    · intro b
      simpa [nonnull] using live b
    · simpa [nonnull] using next
    · rw [heapEq]
      simp [setI, nonnull]

#print axioms updatewindow_local_effects
end Zlib.Inflate.Local
