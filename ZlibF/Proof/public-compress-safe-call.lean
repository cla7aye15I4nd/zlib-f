import ZlibF.Proof.«public-compress-safe-tiny»

/-!
# compress.c: the two call facts of `compress*` from `deflate_call_full`

`CallProgress` and `CallKeepsGzhead` (`public-compress-safe-tiny`) are clauses of
`deflate_call_full`: the progress clause comes from the strategy returns (`StratMeaning.stop`, and
`dispatch_stored_progress` at level 0), the header phase's full output and the entry flush; `gzhead`
is kept by every state write of the call (`KeepRel.gz`). So the `compress*` goals hold under
`TinyOverlay` alone.
-/

namespace ZlibF.Spec.Public.Proofs.Compress
open C ZlibF.Spec ZlibF.Spec.Public Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Universal
set_option autoImplicit false

/-- `CallProgress` from `deflate_call_full`. -/
theorem call_progress_of (tiny : Block.TinyOverlay) : CallProgress := by
  intro h after r ds z d flush rc inv header calls buffers active run notRef aout ain status _ z' get
  obtain ⟨rc', after', z1, d1, _, _, run', inv', _, _, _, _, prog, _⟩ :=
    Call.deflate_call_full inv (Block.TinyOverlay.at tiny _) header calls buffers active flush
  have same := Except.ok.inj (run'.symm.trans run)
  simp only [Prod.mk.injEq] at same
  obtain ⟨rfl, rfl⟩ := same
  have e : z' = z1 := Option.some.inj (get.symm.trans inv'.good.live.hz)
  subst e
  exact prog notRef aout ain status

/-- `CallKeepsGzhead` from `deflate_call_full`. -/
theorem call_keeps_gzhead_of (tiny : Block.TinyOverlay) : CallKeepsGzhead := by
  intro h after r ds z d flush rc inv header calls buffers active run z' d' good
  obtain ⟨rc', after', z1, d1, _, _, run', inv', _, _, _, _, _, gz⟩ :=
    Call.deflate_call_full inv (Block.TinyOverlay.at tiny _) header calls buffers active flush
  have same := Except.ok.inj (run'.symm.trans run)
  simp only [Prod.mk.injEq] at same
  obtain ⟨rfl, rfl⟩ := same
  obtain ⟨_, _, rfl⟩ := inv'.unique good
  exact gz

/-- **`Goal.compress2_z_safety`** under `TinyOverlay` alone. -/
theorem compress2_z_safety_tiny (tiny : Block.TinyOverlay) : Goal.compress2_z_safety :=
  compress2_z_safety_of_tiny tiny (call_progress_of tiny) (call_keeps_gzhead_of tiny)

/-- **`Goal.compress_z_safety`** under `TinyOverlay` alone. -/
theorem compress_z_safety_tiny (tiny : Block.TinyOverlay) : Goal.compress_z_safety :=
  compress_z_safety_of_tiny tiny (call_progress_of tiny) (call_keeps_gzhead_of tiny)

/-- **`Goal.compress2_safety`** under `TinyOverlay` alone. -/
theorem compress2_safety_tiny (tiny : Block.TinyOverlay) : Goal.compress2_safety :=
  compress2_safety_of_tiny tiny (call_progress_of tiny) (call_keeps_gzhead_of tiny)

/-- **`Goal.compress_safety`** under `TinyOverlay` alone. -/
theorem compress_safety_tiny (tiny : Block.TinyOverlay) : Goal.compress_safety :=
  compress_safety_of_tiny tiny (call_progress_of tiny) (call_keeps_gzhead_of tiny)

end ZlibF.Spec.Public.Proofs.Compress
