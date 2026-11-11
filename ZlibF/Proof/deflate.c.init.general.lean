import ZlibF.Proof.«deflate.c.init.default»

/-! # deflate.c: `deflateInit2_` for every argument tuple

The entry checks of `deflateInit2_` before any allocation: the version and stream-size refusal
and the `NULL` stream refusal hold for every level, method, window, memory level and strategy.
These are lemmas `init2_version` and `init2_null` of the deflate skeleton
(`docs/progress.md`, Core proof skeletons).
-/

namespace Zlib.Deflate.Proofs.GeneralInit
open C Zlib.Deflate Zlib.Deflate.Spec
open ZlibF.Spec.Public Zlib.Deflate.Proofs.DefaultInit
set_option autoImplicit false

/-- Version and size refusal occurs before any stream access or allocation, for every argument. -/
theorem init2_version (level method wb mem strategy : Int32) :
    ∀ h p version head size, VersionValue h version head → (head ≠ some 49 ∨ size ≠ 112) →
      C.run (deflateInit2_ p level method wb mem strategy version size) h = .ok (Z_VERSION_ERROR, h) := by
  intro h p version head size hv hbad
  rw [C.run]
  unfold deflateInit2_
  cases head with
  | none =>
    rcases hv with ⟨rfl, _⟩ | ⟨b, hb, _⟩
    · simp
    · cases hb
  | some byte =>
    obtain ⟨hn, read⟩ := version_load hv
    by_cases hb : byte = 49
    · subst byte
      have hs : size ≠ 112 := by simpa using hbad
      simp [hn, bind_app, read, sizeof_z_stream, hs]
    · simp [hn, bind_app, read, hb]

/-- A `NULL` stream is refused after the successful version read, for every argument. -/
theorem init2_null (level method wb mem strategy : Int32) :
    ∀ h version, VersionValue h version (some 49) →
      C.run (deflateInit2_ none level method wb mem strategy version 112) h = .ok (Z_STREAM_ERROR, h) := by
  intro h version hv
  obtain ⟨hn, read⟩ := version_load hv
  rw [C.run]
  unfold deflateInit2_
  simp [hn, bind_app, read, sizeof_z_stream]

end Zlib.Deflate.Proofs.GeneralInit
