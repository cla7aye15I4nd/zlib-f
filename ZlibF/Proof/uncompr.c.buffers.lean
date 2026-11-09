import ZlibF.Proof.«uncompr.c.loop»

/-!
# Caller ranges at uncompress refills

Complete outer remainder ranges establish the exact UInt32 input/output views.
Ownership and separation are preserved when the actual stream is refilled.
The resulting iteration theorem invokes the checked inflate implementation theorem.
-/

namespace Zlib.Uncompr.Proof.Buffers
open C ZlibF.Spec.Public Zlib.Uncompr.Proof.Loop

/-- Availability refill does not change any byte object, static view, or byte read-only flag. -/
theorem refill_get (h : Heap) (b : Nat) (z : ZStream) (l : UncLoop) (r : BRef) :
    Space.get (refilledHeap h b z l) r = Space.get h r := by
  cases r <;> rfl

theorem refill_ro (h : Heap) (b : Nat) (z : ZStream) (l : UncLoop) (r : BRef) :
    Space.ro (refilledHeap h b z l) r = Space.ro h r := by
  cases r <;> rfl

theorem bytes_prefix (h : Heap) (p : BPtr) (n k : Nat) (xs : List UInt8)
    (readable : Bytes h p n xs) (bound : k ≤ n) : ∃ ys, Bytes h p k ys := by
  rcases readable with ⟨null, empty, _⟩ | ⟨r, off, a, ptr, get, room, _⟩
  · have zero : k = 0 := by omega
    exact ⟨[], Or.inl ⟨null, zero, rfl⟩⟩
  · exact ⟨(a.toList.drop off).take k, Or.inr ⟨r, off, a, ptr, get, by omega, rfl⟩⟩

theorem writable_prefix (h : Heap) (p : BPtr) (n k : Nat)
    (writable : Writable h p n) (bound : k ≤ n) : Writable h p k := by
  rcases writable with ⟨null, empty⟩ | ⟨r, off, a, ptr, get, ro, room⟩
  · exact Or.inl ⟨null, by omega⟩
  · exact Or.inr ⟨r, off, a, ptr, get, ro, by omega⟩

theorem refill_owned (h : Heap) (b : Nat) (z : ZStream) (l : UncLoop)
    (hz : h.streams b = some z) (x : Nat) :
    StreamOwned (refilledHeap h b z l) (.tab b) x ↔ StreamOwned h (.tab b) x := by
  simp [StreamOwned, ZStreamRef.get, refilledHeap, refilledStream, hz]

theorem callerRange_refill (h : Heap) (b : Nat) (z : ZStream) (l : UncLoop)
    (hz : h.streams b = some z) (p : BPtr) (n k : Nat) (write : Bool)
    (range : CallerRange h (.tab b) p n write) (bound : k ≤ n) :
    CallerRange (refilledHeap h b z l) (.tab b) p k write := by
  rcases range with null | ⟨⟨xs, readable⟩, writable, unowned⟩
  · exact Or.inl null
  · obtain ⟨ys, initial⟩ := bytes_prefix h p n k xs readable bound
    refine Or.inr ⟨⟨ys, ?_⟩, ?_, ?_⟩
    · simpa only [Bytes, refill_get] using initial
    · intro yes
      have short := writable_prefix h p n k (writable yes) bound
      simpa only [Writable, refill_get, refill_ro] using short
    · intro x root owned
      exact unowned x root ((refill_owned h b z l hz x).mp owned)

theorem separate_prefix (p q : BPtr) (n m k j : Nat)
    (separate : Separate p n q m) (hk : k ≤ n) (hj : j ≤ m) :
    Separate p k q j := by
  rcases separate with empty | empty | disjoint
  · exact Or.inl (by omega)
  · exact Or.inr (Or.inl (by omega))
  · apply Or.inr ∘ Or.inr
    cases p with
    | null => trivial
    | ref r off =>
      cases q with
      | null => trivial
      | ref r' off' =>
        rcases disjoint with distinct | before | after
        · exact Or.inl distinct
        · exact Or.inr (Or.inl (by omega))
        · exact Or.inr (Or.inr (by omega))

/-- The outer remainder ranges justify the exact UInt32 views passed to inflate,
including refilling from zero availability. Caller ownership and disjointness are
preserved on the actual refilled heap. -/
theorem refilled_stream_buffers (h : Heap) (b : Nat) (z : ZStream) (l : UncLoop)
    (hz : h.streams b = some z)
    (input : CallerRange h (.tab b) z.next_in (l.len.toNat + z.avail_in.toNat) false)
    (output : CallerRange h (.tab b) z.next_out (l.left.toNat + z.avail_out.toNat) true)
    (separate : Separate z.next_in (l.len.toNat + z.avail_in.toNat)
      z.next_out (l.left.toNat + z.avail_out.toNat)) :
    StreamBuffers (refilledHeap h b z l) (.tab b) := by
  have hi := refill_input_count z l
  have ho := refill_output_count z l
  have ki : (refilledStream z l).avail_in.toNat ≤ l.len.toNat + z.avail_in.toNat := by omega
  have ko : (refilledStream z l).avail_out.toNat ≤ l.left.toNat + z.avail_out.toNat := by omega
  refine ⟨refilledStream z l, by simp [refilledHeap, ZStreamRef.get], ?_, ?_, ?_⟩
  · simpa only [refilledStream] using callerRange_refill h b z l hz z.next_in
      (l.len.toNat + z.avail_in.toNat) (refilledStream z l).avail_in.toNat false input ki
  · simpa only [refilledStream] using callerRange_refill h b z l hz z.next_out
      (l.left.toNat + z.avail_out.toNat) (refilledStream z l).avail_out.toNat true output ko
  · exact separate_prefix z.next_in z.next_out _ _ _ _ separate ki ko

/-- The exact wrapper iteration is safe, accounts for all consumption/output,
retains its representation and allocation ledger, and strictly decreases its
remaining-byte budget on Z_OK. Its caller premises are the complete remaining
ranges, which are then restricted to the actual refill sizes. -/
theorem loop_iteration_from_ranges (h : Heap) (b zs : Nat) (z : ZStream) (l : UncLoop)
    (s : InflateState)
    (invariant : Zlib.Inflate.Proofs.DefaultStateJ h (.tab b) zs z s)
    (allocator : Zlib.Inflate.Spec.DefAlloc z)
    (input : CallerRange h (.tab b) z.next_in (l.len.toNat + z.avail_in.toNat) false)
    (output : CallerRange h (.tab b) z.next_out (l.left.toNat + z.avail_out.toNat) true)
    (separate : Separate z.next_in (l.len.toNat + z.avail_in.toNat)
      z.next_out (l.left.toNat + z.avail_out.toNat)) :
    ∃ rc after stream state used output,
      C.run (loopBody (some (.tab b)) l) h =
        .ok ({ refilledLocals z l with err := rc }, after) ∧
      Zlib.Inflate.Proofs.DefaultStateJ after (.tab b) zs stream state ∧
      Zlib.Inflate.Spec.DefAlloc stream ∧
      ZlibF.Spec.Public.StreamAccounting (refilledStream z l) stream used output.length ∧
      ZlibF.Spec.Public.Bytes after z.next_out output.length output ∧
      Zlib.Inflate.Proofs.PublicInflateCode rc ∧
      ZlibF.Spec.Public.BufferFrame (refilledHeap h b z l) after
        (fun x => ZlibF.Spec.Public.StreamRoot (.tab b) x ∨
          ZlibF.Spec.Public.InflateOwned zs s x) [⟨z.next_out, output.length⟩] ∧
      ZlibF.Spec.Public.LiveChange (refilledHeap h b z l) after
        (fun x => ZlibF.Spec.Public.InflateOwned zs state x ∧
          ¬ (refilledHeap h b z l).live x) (fun _ => False) ∧
      ((refilledLocals z l).len.toNat + stream.avail_in.toNat +
        (refilledLocals z l).left.toNat + stream.avail_out.toNat + used + output.length =
        l.len.toNat + z.avail_in.toNat + l.left.toNat + z.avail_out.toNat) ∧
      (rc = Z_OK →
        (refilledLocals z l).len.toNat + stream.avail_in.toNat +
          (refilledLocals z l).left.toNat + stream.avail_out.toNat <
          l.len.toNat + z.avail_in.toNat + l.left.toNat + z.avail_out.toNat) := by
  exact loop_iteration_memory h b zs z l s invariant allocator
    (refilled_stream_buffers h b z l invariant.good.live.hz input output separate)

#print axioms refilled_stream_buffers
#print axioms loop_iteration_from_ranges

end Zlib.Uncompr.Proof.Buffers
