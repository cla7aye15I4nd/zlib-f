import ZlibF.Proof.«gzlib.c.error-inv»
import ZlibF.Proof.«gzread.c.skip-gets»
import ZlibF.Proof.«gzread.c.getc-ungetc»
import ZlibF.Proof.«gzwrite.c.init»

/-!
# gz safety: the facts on `gz_error` that other modules take as premises

`GzInv.gz_error` is the skeleton's interface lemma, and `GzInv.gz_error_own` is the no-grab fact. Both follow from
`GzInv.gz_error_full` (`gzlib.c.error-inv`). The premises `GzErrorSpec` and `GzErrorOwn` of `gzwrite.c.init`,
`gzread.c.getc-ungetc` and `gzread.c.skip-gets` restate them; each is proved here, so the results stated over those
premises hold without them.
-/

namespace ZlibF.Spec.Public
open C Zlib.GzFs
set_option autoImplicit false

/-- **Interface: `gz_error` keeps the invariant** (the skeleton statement `GzInv.gz_error`). -/
theorem GzInv.gz_error {h : Heap} {i : Nat} {s : GzState} (inv : GzInv h i s) (err : Int32) (msg : BPtr)
    (hmsg : msg = .null ∨ ∃ t, CString h msg t ∧ ∀ b, ByteRoot msg b → ¬ GzOwned h i s b) :
    ∃ after s', C.run (Zlib.Gzlib.gz_error (gzSt i) err msg) h = .ok ((), after) ∧ GzInv after i s' ∧
      s' = { s with err := s'.err, msg := s'.msg } ∧ (s'.err = err ∨ (s'.err = Z_MEM_ERROR ∧ s'.msg = .null)) ∧
      Frame h after (fun b => b = i ∨ blkOf s.msg = some b) ∧
      LiveChange h after (fun b => blkOf s'.msg = some b ∧ ¬ h.live b) (fun b => blkOf s.msg = some b) := by
  obtain ⟨after, s', run, inv', eq, herr, fr, lc, -, -, -, -⟩ := inv.gz_error_full err msg hmsg
  exact ⟨after, s', run, inv', eq, herr, fr, lc⟩

/-- **No grab**: a block the handle owns after `gz_error` and that was live before was owned before. -/
theorem GzInv.gz_error_own {h : Heap} {i : Nat} {s : GzState} (inv : GzInv h i s) (err : Int32) (msg : BPtr)
    (hmsg : msg = .null ∨ ∃ t, CString h msg t ∧ ∀ b, ByteRoot msg b → ¬ GzOwned h i s b) {after : Heap}
    (run : C.run (Zlib.Gzlib.gz_error (gzSt i) err msg) h = .ok ((), after)) :
    ∀ s', after.gzstates i = some s' → ∀ b, GzOwned after i s' b → h.live b → GzOwned h i s b := by
  obtain ⟨a', s'', run', -, -, -, -, -, -, hrec, hown, -⟩ := inv.gz_error_full err msg hmsg
  rw [run'] at run
  cases run
  intro s' hs' b ho hl
  rw [hrec] at hs'
  cases hs'
  rcases hown b ho with e | e
  · exact e
  · exact absurd hl e

/-- The premise `GzErrorSpec` of `gzread.c.skip-gets` holds. -/
theorem gzErrorSpec_holds : GzErrorSpec := fun inv err msg hmsg => inv.gz_error err msg hmsg

/-- The premise `GzErrorOwn` of `gzread.c.skip-gets` holds. -/
theorem gzErrorOwn_holds : GzErrorOwn := fun _ _ _ err msg _ inv hmsg run => inv.gz_error_own err msg hmsg run

/-- The premise `GzErrorSpec` of `gzread.c.getc-ungetc` holds. -/
theorem GetcUngetc.gzErrorSpec_holds : GetcUngetc.GzErrorSpec := fun inv err msg hmsg => inv.gz_error err msg hmsg

/-- The premise `GzErrorOwn` of `gzread.c.getc-ungetc` holds. -/
theorem GetcUngetc.gzErrorOwn_holds : GetcUngetc.GzErrorOwn :=
  fun _ _ _ err msg _ inv hmsg run => inv.gz_error_own err msg hmsg run

/-- The premise `GzErrorSpec` of `gzwrite.c.init` holds. -/
theorem gzwrite_gzErrorSpec_holds : Zlib.Gzwrite.SafeInit.GzErrorSpec :=
  fun inv err msg hmsg => inv.gz_error err msg hmsg

/-- The premise `GzErrorOwn` of `gzwrite.c.init` holds. -/
theorem gzwrite_gzErrorOwn_holds : Zlib.Gzwrite.SafeInit.GzErrorOwn :=
  fun _ _ _ err msg _ inv hmsg run => inv.gz_error_own err msg hmsg run

#print axioms GzInv.gz_error_full
#print axioms GzInv.gz_error
#print axioms GzInv.gz_error_own
#print axioms gzErrorSpec_holds
#print axioms gzErrorOwn_holds
#print axioms GetcUngetc.gzErrorSpec_holds
#print axioms GetcUngetc.gzErrorOwn_holds
#print axioms gzwrite_gzErrorSpec_holds
#print axioms gzwrite_gzErrorOwn_holds

end ZlibF.Spec.Public
