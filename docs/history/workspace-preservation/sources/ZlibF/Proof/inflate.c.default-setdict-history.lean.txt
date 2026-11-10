import ZlibF.Proof.«inflate.c.dictionary-state-history»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- A public caller dictionary range cannot alias the decoder's owned
window. The public ownership condition supplies the internal separation
needed by the actual copy proof. -/
theorem callerRange_dictionary_window_separate {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {source : BPtr} {n : Nat}
    (good : Good h r zs z s) (range : CallerRange h r source n false) :
    Separate source n s.window (2 ^ s.wbits.toNat) := by
  rcases range with null | ⟨_, _, unowned⟩
  · simp [Separate, null]
  rcases good.inv.win.block with windowNull | ⟨w, _, window, _, _, _⟩
  · simp [Separate, windowNull]
  cases source with
  | null => simp [Separate]
  | ref ref off =>
    have distinct : ref ≠ .blk w := by
      intro same
      subst ref
      have root : ByteRoot (.ref (.blk w) off) w := by simp [ByteRoot]
      have owned : StreamOwned h r w :=
        (good.streamOwned_iff w).mpr (Or.inr window)
      exact unowned w root owned
    simp [Separate, window, distinct]

/-- Every admissible default-history dictionary argument has a checked
translated call. Its result retains the decoder relation, allocator and
actual public reachability on acceptance, refusal and allocation failure. -/
theorem inflateSetDictionary_default_history {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (reachable : StreamReachable .inflate h r)
    (invariant : DefaultStateJ h r zs z s) (allocator : DefAlloc z)
    (source : BPtr) (n : UInt32)
    (arguments : StreamArguments h r (.inflateSetDictionary (some r) source n)) :
    ∃ rc after state, C.run (inflateSetDictionary (some r) source n) h = .ok (rc, after) ∧
      DefaultStateJ after r zs z state ∧ DefAlloc z ∧
      StreamReachable .inflate after r := by
  have range : CallerRange h r source n.toNat false := arguments
  obtain ⟨xs, readable⟩ : ∃ xs, source ≠ .null → Bytes h source n.toNat xs := by
    rcases range with null | ⟨⟨xs, bytes⟩, _, _⟩
    · exact ⟨[], by intro nonnull; exact False.elim (nonnull null)⟩
    · exact ⟨xs, by intro _; exact bytes⟩
  have separate := callerRange_dictionary_window_separate invariant.good range
  obtain ⟨rc, after, state, run, current, finalAllocator, _⟩ :=
    inflateSetDictionary_default_state invariant allocator source n xs readable separate
  have executed : (Call.inflateSetDictionary (some r) source n).execute default h =
      .ok ((rc, default), after) := by
    change inflateSetDictionary (some r) source n h = _ at run
    simp only [Call.execute, heapCall, run]
  have operation : StreamOperation .inflate r (.inflateSetDictionary (some r) source n) := by
    simp [StreamOperation]
  exact ⟨rc, after, state, run, current, finalAllocator,
    StreamReachable.step reachable operation arguments executed⟩

end Zlib.Inflate.Proofs
