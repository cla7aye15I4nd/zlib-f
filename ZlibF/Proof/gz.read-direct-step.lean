import ZlibF.Proof.«gz.read-getc-step»

/-!
# gz read side: `gzdirect` is safe

`gzdirect(file)` on a reader in LOOK mode with nothing buffered calls `gz_look` and then `gz_skip_have`, and returns
`state->direct == 1`. `gz_look` may buffer output (COPY) while a skip is pending; patch 0004 bounds that output by the
room left before `GZ_OFF_MAX`, so the record is in the invariant up to the pending skip, and `gz_skip_have` consumes
the skip or the buffered output, which gives `GzInv` back. `gzdirect` has no reading loop, so its termination needs no
read budget (`NeedsReadBound` is false for it).

`gzdirect_step` has the skeleton statement and no premise.
-/

namespace ZlibF.Spec.Public.GzRead
open C Zlib.GzFs Zlib.Gzguts Zlib.Gzlib.Spec Zlib.Gzlib.Proofs ZlibF.Spec.Public
open ZlibF.Spec.Public.GetcUngetc (EffI Eff good_skip good_inv)
set_option autoImplicit false

theorem gzdirect_eq (i : Nat) : Zlib.Gzread.gzdirect (some (.in_gzstate_x i)) = (do
    let s ← ldS (some (.tab i))
    if s.mode == GZ_READ && s.how == LOOK && s.x.«have» == 0 then
      let _ ← Zlib.Gzread.gz_look (some (.tab i))
      Zlib.Gzread.gz_skip_have (some (.tab i))
    return if (← ldS (some (.tab i))).direct == 1 then 1 else 0 : G Int32) := rfl

/-- The tail of `gzdirect`: one load of the record and the result. -/
theorem direct_tail {i : Nat} {h0 : Heap} {s0 : GzState} {fs0 fs : Fs} {h : Heap} {fin : Prop}
    (e : Eff i h0 s0 fs0 fs h) :
    RunSafe (do return if (← ldS (some (.tab i))).direct == 1 then (1 : Int32) else 0 : G Int32) fs h fin
      (fun _ fs' after => Eff i h0 s0 fs0 fs' after) := by
  obtain ⟨_, _, s1, inv1, _⟩ := id e
  refine GetcUngetc.RunSafe.bind_lift (ldS_run inv1.common.record) ?_
  exact GetcUngetc.RunSafe.pure' e

/-- **The run of `gzdirect`** from `LookFacts`. -/
theorem gzdirect_run (look : LookFacts) (i : Nat) (h : Heap) (fs : Fs) (s : GzState) (inv : GzInv h i s)
    (hfs : FileSystem fs) :
    RunSafe (Zlib.Gzread.gzdirect (some (.in_gzstate_x i))) fs h True
      (fun _ fs' after => Eff i h s fs fs' after) := by
  rw [gzdirect_eq]
  refine GetcUngetc.RunSafe.bind_lift (ldS_run inv.common.record) ?_
  refine GetcUngetc.RunSafe.ite (fun hc => ?_) (fun _ => direct_tail (GetcUngetc.Eff.refl inv hfs))
  have hm : s.mode = GZ_READ := by simp at hc; exact hc.1.1
  have hlk : s.how = LOOK := by simp at hc; exact hc.1.2
  have h0 : s.x.have = 0 := by simp at hc; exact hc.2
  refine GetcUngetc.RunSafe.bind (look i h fs s inv hfs hm h0 hlk) ?_
  rintro r fs1 h1 ⟨_, k1, post1, _, _⟩
  have e1 : EffI GzInvUpToSkip i h s fs fs1 h1 := ⟨k1, post1⟩
  obtain ⟨hfs1, s1, u1, m1, f1, _⟩ := post1
  obtain ⟨hr, inv2, -, -, -, -⟩ := gz_skip_have_run' u1
  refine GetcUngetc.RunSafe.bind_lift hr ?_
  have p2 := post_put_any (I := GzInv) (fs := fs1) u1.cur (fun b hb => u1.live hb) inv2
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl hfs1
  exact direct_tail (GetcUngetc.EffI.trans good_skip good_inv e1 u1.cur p2 (fun _ => Iff.rfl))

/-- **`gzdirect_step`** (skeleton statement) from `LookFacts`. -/
theorem gzdirect_step_of' (look : LookFacts) (i : Nat) : GzCallSafe i (.gzdirect (some (.in_gzstate_x i))) := by
  intro h fs s inv hfs _
  have R := gzdirect_run look i h fs s inv hfs
  exact ⟨R.1, fun _ => R.2.1 trivial, fun v fs' after he => GetcUngetc.Eff.post rfl (R.2.2 v fs' after he)⟩

/-- **`gzdirect_step`**, the skeleton statement. -/
theorem gzdirect_step (i : Nat) : GzCallSafe i (.gzdirect (some (.in_gzstate_x i))) :=
  gzdirect_step_of' (lookFacts_of readInvFacts_holds.msgLit gzLookFailEmpty_holds) i

end ZlibF.Spec.Public.GzRead
