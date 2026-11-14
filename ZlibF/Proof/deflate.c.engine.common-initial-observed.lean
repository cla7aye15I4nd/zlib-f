import ZlibF.Proof.«deflate.c.engine.common-initial-valid-protocol»
import ZlibF.Proof.«deflate.c.engine.encoding-init-observed»
import ZlibF.Spec.Public.Domains
import ZlibF.Spec.Functional.Api.Compress

/-! # Successful observed standard initialization establishes common-level phases -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- Allocation success follows from the actual successful translated init
at every admitted level; it is not a caller assumption. -/
theorem common_init_success_allocations {h after : Heap} {r : ZStreamRef} {z : ZStream}
    {version : BPtr} {level : Int32} {p : ZlibF.Spec.Api.DeflParams}
    (hf : Fresh h) (hu : Uniq h) (hg : LibraryGlobals h) (hz : r.get h = some z)
    (ha : DefaultOrNull z) (hv : VersionValue h version (some 49))
    (params : ZlibF.Spec.Api.deflInit? level.toInt 8 15 8 0 = some p)
    (run : C.run (deflateInit_ (some r) level version 112) h = .ok (Z_OK, after)) :
    ∀ j, j < 5 → h.allocOk (h.nalloc + j) = true := by
  obtain ⟨rc, computed, actual, properties⟩ :=
    (ZlibF.Spec.Public.Proofs.DeflateInit.deflateInit_proof level).2.2
      h r z version hf hu hg hz ha hv
  simp only [show (8 : Int32).toInt = (8 : Int) from rfl,
    show (15 : Int32).toInt = (15 : Int) from rfl,
    show (0 : Int32).toInt = (0 : Int) from rfl, params] at properties
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


/-- An observed successful init at a common slow level supplies the same
actual returned heap and all later first-header obligations. No allocation
success, representation invariant or init execution contract is assumed. -/
theorem common_observed_initialization_protocol {before initialized : Heap}
    {r : ZStreamRef} {version : BPtr} {level : Int32} {p : ZlibF.Spec.Api.DeflParams}
    (domain : InitDomain before r version)
    (params : ZlibF.Spec.Api.deflInit? level.toInt 8 15 8 0 = some p)
    (low : 4 ≤ p.level) (high : p.level ≤ 9)
    (actual : C.run (deflateInit_ (some r) level version 112) before = .ok (Z_OK, initialized)) :
    ∃ zf sf, EngineStart initialized r before.nextBlk zf sf ∧
      DeflateInitial before initialized r p ∧
      ∀ g, Rebuffer initialized g r → ∃ zg, r.get g = some zg ∧
        ∀ ob oo, zg.next_out = .ref (.blk ob) oo → zg.avail_out = 1 → StreamBuffers g r →
          (zg.avail_in ≠ 0 → zg.next_in ≠ .null) →
          ∀ flush : Int32, 0 ≤ flush.toInt → flush.toInt ≤ 5 →
            ∃ after z' result,
              C.run (deflate (some r) flush) g = .ok (Z_OK, after) ∧
              CommonSlowFinishBoundary after r before.nextBlk z' result (engineConfig sf) ∧
              StreamBuffers after r ∧ StreamAccounting zg z' 0 1 := by
  obtain ⟨fresh, unique, globals, versionValue, z, getZ, allocators, _state⟩ := domain
  have allocation := common_init_success_allocations fresh unique globals getZ allocators versionValue params actual
  obtain ⟨computed, zf, sf, run, start, initial, first⟩ :=
    common_initialization_valid_split_boundary fresh unique globals getZ allocators versionValue
      params low high allocation
  have heaps : computed = initialized := (Prod.mk.inj (Except.ok.inj (run.symm.trans actual))).2
  subst computed
  exact ⟨zf, sf, start, initial, first⟩

end Zlib.Deflate.Engine.Proofs
