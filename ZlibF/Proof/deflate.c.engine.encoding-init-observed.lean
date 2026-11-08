import ZlibF.Proof.«deflate.c.engine.encoded-state-initial»

/-! # Actual successful init observations supply every allocation premise -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- A real successful default-entry initialization implies that all five
actual allocations succeeded. This derives the producer premise from the
observed C run rather than adding it to a successful data epoch. The
registered fixed-parameter init proof is used; universal Init2 correctness
is not a premise or a dependency. -/
theorem default_init_success_allocations {h after : Heap} {r : ZStreamRef} {z : ZStream} {version : BPtr}
    (hf : Fresh h) (hu : Uniq h) (hg : LibraryGlobals h) (hz : r.get h = some z)
    (ha : DefaultOrNull z) (hv : VersionValue h version (some 49))
    (run : C.run (deflateInit_ (some r) Z_DEFAULT_COMPRESSION version 112) h = .ok (Z_OK, after)) :
    ∀ j, j < 5 → h.allocOk (h.nalloc + j) = true := by
  obtain ⟨rc, computed, actual, properties⟩ :=
    (ZlibF.Spec.Public.Proofs.DeflateInit.deflateInit_proof Z_DEFAULT_COMPRESSION).2.2
      h r z version hf hu hg hz ha hv
  have code : rc = Z_OK := (Prod.mk.inj (Except.ok.inj (actual.symm.trans run))).1
  by_cases first : h.allocOk h.nalloc = false
  · simp only [ite_eq_left first] at properties
    have impossible : Z_OK = Z_MEM_ERROR := code.symm.trans properties.1
    exact False.elim ((by decide : Z_OK ≠ Z_MEM_ERROR) impossible)
  · simp only [ite_eq_right first] at properties
    by_cases all : (List.range 5).all (fun j => h.allocOk (h.nalloc + j)) = true
    · simpa only [List.all_eq_true, List.mem_range] using all
    · simp only [ite_eq_right all] at properties
      have impossible : Z_OK = Z_MEM_ERROR := code.symm.trans properties.2.1
      exact False.elim ((by decide : Z_OK ≠ Z_MEM_ERROR) impossible)

/-- Every observed successful actual default init establishes encoding
for empty observed input/output on that exact returned heap. Allocation
success and the invariant are conclusions of the actual execution. -/
theorem observed_default_init_encoding_state {h after : Heap} {r : ZStreamRef} {z : ZStream} {version : BPtr}
    (hf : Fresh h) (hu : Uniq h) (hg : LibraryGlobals h) (hz : r.get h = some z)
    (ha : DefaultOrNull z) (hv : VersionValue h version (some 49))
    (run : C.run (deflateInit_ (some r) Z_DEFAULT_COMPRESSION version 112) h = .ok (Z_OK, after)) :
    ∃ zf sf, DefaultEncodingState after r h.nextBlk zf sf (engineConfig sf) [] [] := by
  have alloc := default_init_success_allocations hf hu hg hz ha hv run
  obtain ⟨other, zf, sf, actual, state⟩ := default_initialization_encoding_state hf hu hg hz ha hv alloc
  have heaps : other = after := (Prod.mk.inj (Except.ok.inj (actual.symm.trans run))).2
  subst other
  exact ⟨zf, sf, state⟩

end Zlib.Deflate.Engine.Proofs
