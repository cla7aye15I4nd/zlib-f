import ZlibF.Proof.«trees.c.block»

/-! # Leaf frequencies established by the actual tree initializer -/

namespace Zlib.Trees.Proofs.Out
open C Zlib.Trees
set_option autoImplicit false

/-- The empty symbol block has one end marker and no distance symbols.
The unused internal nodes and the length halves remain unrestricted. -/
structure InitialFrequencies (l d : Array CtData) : Prop where
  literal : ∀ n, n < 286 → (l[n]!).fc.toNat = if n = 256 then 1 else 0
  distance : ∀ n, n < 30 → (d[n]!).fc.toNat = 0

/-- `_tr_init` establishes the frequencies as well as the representation
invariant. No initialized frequencies are supplied as a premise. -/
theorem tr_init_frequencies {h : Heap} {id : Nat} {d : DeflateState} {b : Nat} {buf : Array UInt8}
    (hb : TreesBase h id d b buf) :
    ∃ a1 a2 a3 d', «_tr_init» (some (.tab id)) h = .ok ((), setD h id d') ∧
      TreesInvAt (setD h id d') id d' b buf ∧ d' = ibRec (trInitRec id d) a1 a2 a3 ∧
      a1.size = 573 ∧ a2.size = 61 ∧ a3.size = 39 ∧ InitialFrequencies a1 a2 := by
  obtain ⟨hb6, hr6⟩ := trInitRec_inv hb
  obtain ⟨a1, a2, a3, d', e, hi, hd, s1, s2, s3, zeros, last, distances, _⟩ :=
    init_block_spec0 hb6 hr6
  simp only [setD_setD] at e hi
  refine ⟨a1, a2, a3, d', ?_, hi, hd, s1, s2, s3, ?_, ?_⟩
  · have hrd : rdD h id = d := by simp [rdD, hb.dstate]
    unfold «_tr_init»
    simp (disch := simp [hb.dstate]) only [tr_static_init, bind_app, pure_app,
      sid_run hb.dstate, md_run', rdD_setD_same, setD_setD, hrd]
    exact e
  · intro n bound
    by_cases endMarker : n = 256
    · subst n
      simp [last]
    · simp [endMarker, zeros n bound endMarker]
  · intro n bound
    simp [distances n bound]

end Zlib.Trees.Proofs.Out
