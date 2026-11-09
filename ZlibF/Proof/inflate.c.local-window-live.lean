import ZlibF.Proof.«inflate.c.local-window-j»

namespace Zlib.Inflate.Local
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

theorem local_inflate_owned_live {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (good : LocalGood h cutoff r zs z s) {b : Nat}
    (owned : InflateOwned zs s b) : h.live b := by
  rcases owned with same | window
  · subst b
    simp [Heap.live, good.live.hs]
  · rcases good.inv.win.block with null | ⟨w, a, ptr, get, _, _⟩
    · rw [null] at window
      cases window
    · rw [ptr] at window
      cases window
      simp [Heap.live, get]

theorem updatewindow_local_live {h after : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s state : InflateState} {eo : Nat} {source : BRef}
    {bytes : Array UInt8} {copy : UInt32} {rc : Int32}
    (good : LocalGood h cutoff r zs z s) (allocator : z.zalloc = .fn "zcalloc")
    (get : Space.get h source = some bytes) (count : copy.toNat ≤ eo) (bound : eo ≤ bytes.size)
    (separate : Separate (.ref source (eo - copy.toNat)) copy.toNat s.window (2 ^ s.wbits.toNat))
    (run : updatewindow (some r) (.ref source eo) copy h = .ok (rc, after))
    (final : LocalGood after cutoff r zs z state) :
    LiveChange h after (fun b => InflateOwned zs state b ∧ ¬ h.live b) (fun _ => False) := by
  obtain ⟨_, ledger, _, _, _⟩ := updatewindow_local_effects good allocator get count bound separate run final.live.hs
  have ownedNew : ∀ b, s.window = .null ∧ h.allocOk h.nalloc = true ∧ b = h.nextBlk → InflateOwned zs state b := by
    rintro b ⟨null, ok, same⟩
    subst b
    have actual := uw_new_local_exact good allocator null ok get count bound
    have heaps : after = localWindowNewHeap h zs s bytes eo copy :=
      congrArg Prod.snd (Except.ok.inj (run.symm.trans actual))
    have stored := final.live.hs
    rw [heaps] at stored
    have states : state = localWindowNewState h s bytes eo copy := by
      simp only [localWindowNewHeap, setI_istates_same] at stored
      exact (Option.some.inj stored).symm
    exact Or.inr (by rw [states, localWindowNewState_origin])
  intro b
  constructor
  · intro live
    rcases (ledger b).mp live with old | fresh
    · exact Or.inl old
    · exact Or.inr ⟨ownedNew b fresh, fun old => Nat.not_lt_of_ge (Nat.le_refl _) (good.fresh.lt (fresh.2.2 ▸ old))⟩
  · rintro (old | ⟨owned, fresh⟩)
    · exact (ledger b).mpr (Or.inl old)
    · exact local_inflate_owned_live final owned

#print axioms updatewindow_local_live
end Zlib.Inflate.Local
