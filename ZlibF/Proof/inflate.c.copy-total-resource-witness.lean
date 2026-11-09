import ZlibF.Proof.«inflate.c.copy-total-resource»
namespace Zlib.Inflate.Proofs.CopyResource
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- The selected copy contract has an actual initialized source and a
separate caller-supplied destination. No copy execution is assumed. -/
theorem default_copy_total_domain_witness :
    ∃ h zs z s dest oldDest rc after,
      DefaultOriginHistory h (.tab 0) ∧ Good h (.tab 0) zs z s ∧ DefAlloc z ∧
      (ZStreamRef.tab 0) ≠ dest ∧ dest.get h = some oldDest ∧
      C.run (inflateCopy (some dest) (some (.tab 0))) h = .ok (rc, after) ∧
      CopyResult h after (.tab 0) dest zs z oldDest s rc := by
  obtain ⟨initial, history⟩ := default_origin_history_initial_witness
  obtain ⟨⟨zs, z, s, current, allocator⟩, _reachable⟩ := history.sound
  let withDest : Heap := {initial with
    streams := upd initial.streams initial.nextBlk (some (default : ZStream))
    nextBlk := initial.nextBlk + 1}
  have initialRoot : initial.live 0 := by
    have streamGet : initial.streams 0 = some z := current.good.live.hz
    exact Or.inr (Or.inr (Or.inl (by rw [streamGet]; exact Option.some_ne_none z)))
  have rootOld : (0 : Nat) ≠ initial.nextBlk := by
    intro equal
    exact current.good.fresh 0 (by omega) initialRoot
  have fresh : Fresh withDest := by
    intro b bound
    have different : b ≠ initial.nextBlk := by dsimp [withDest] at bound; omega
    have empty := current.good.fresh b (by dsimp [withDest] at bound; omega)
    simpa [withDest, Heap.live, upd_ne _ _ _ _ different] using empty
  have uniq : Uniq withDest := by
    intro b
    by_cases equal : b = initial.nextBlk
    · subst b
      obtain ⟨bytes, words, streams, headers, deflates, inflates, gzstates⟩ :=
        fresh_dead current.good.fresh (Nat.le_refl _)
      simp [withDest, bytes, words, headers, deflates, inflates, gzstates]
    · simpa [withDest, upd_ne _ _ _ _ equal] using current.good.uniq b
  have sourceGet : (ZStreamRef.tab 0).get withDest = some z := by
    simpa [withDest, ZStreamRef.get, upd_ne _ _ _ _ rootOld] using current.good.live.hz
  have callerFrame : Frame initial withDest (fun b => ¬ StreamOwned initial (.tab 0) b) := by
    refine ⟨rfl, rfl, rfl, by simp [withDest], by simp [withDest], ?_⟩
    intro b live _outside
    have different : b ≠ initial.nextBlk := fun equal => current.good.fresh b (by omega) live
    simp [withDest, upd_ne _ _ _ _ different]
  have rebound : Rebuffer initial withDest (.tab 0) :=
    ⟨fresh, uniq, current.globals, callerFrame, z, z, current.good.live.hz, sourceGet, rfl⟩
  have platform : ZlibF.PlatformMemory.ByteObjectsFit withDest :=
    current.platform.of_storage_eq rfl rfl rfl
  have admitted : DefaultOriginHistory withDest (.tab 0) := .rebuffer history rebound platform
  obtain ⟨⟨index, stream, state, before, alloc⟩, _reachable⟩ := admitted.sound
  have destGet : (ZStreamRef.tab initial.nextBlk).get withDest = some (default : ZStream) := by
    simp [withDest, ZStreamRef.get]
  have different : (ZStreamRef.tab 0) ≠ .tab initial.nextBlk := by
    intro equal
    exact rootOld (ZStreamRef.tab.inj equal)
  obtain ⟨rc, after, run, result, _origins⟩ := inflateCopy_default_origin_total before alloc destGet different
  exact ⟨withDest, index, stream, state, .tab initial.nextBlk, default, rc, after,
    admitted, before.good, alloc, different, destGet, run, result⟩

#print axioms default_copy_total_domain_witness
end Zlib.Inflate.Proofs.CopyResource
