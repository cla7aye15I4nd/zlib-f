import ZlibF.Proof.«deflate.c.quiet-phi»
import ZlibF.Proof.«deflate.c.universal-call-assemble»

/-!
# deflate.c: `DeflateQuiet`

`gz_comp`'s loop `do { deflate(strm, flush) } while (have)` with no input ends when its buffer has
at least 8 bytes. `call_quiet` is the per-call fact on the deflate invariant: a call from at least 8
bytes of room that fills the output lowers the potential `phiD` lexicographically (`LexLt`), and a
call that ends with room leaves `QuietD`. `deflate_quiet_holds` is `DeflateQuiet` (the statement of
the gz skeleton, written out here) from `call_quiet`, `quiet_silent` and `stateOf_rebuffer`.
-/

namespace Zlib.Deflate.Universal.Quiet
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Deflate.Engine.Proofs Zlib.Deflate.Universal.Call
set_option autoImplicit false

/-- **One `deflate` call with no input** on the invariant: from at least 8 bytes of room, a call that
fills the output lowers the potential; a call that ends with room leaves the state quiet. -/
theorem call_quiet {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState} {flush : Int32}
    (inv : DInv h r ds z d) (header : HeaderInv d) (facts : CallFacts d) (buffers : StreamBuffers h r)
    (active : ActiveHeader h r) (out : z.next_out ≠ .null) (lower : 0 ≤ flush.toInt) (upper : flush.toInt ≤ 4)
    (empty : z.avail_in = 0) :
    ∃ rc after z' d', C.run (deflate (some r) flush) h = .ok (rc, after) ∧ DInv after r ds z' d' ∧
      (8 ≤ z.avail_out.toNat → z'.avail_out = 0 → LexLt d' d) ∧
      (z.avail_out ≠ 0 → z'.avail_out ≠ 0 → QuietD flush d') := by
  sorry

/-- A public `deflate` call that returned is the run of the translated `deflate`. -/
theorem run_of_execute {h after : Heap} {r : ZStreamRef} {flush value : Int32}
    (exec : Call.execute (.deflate (some r) flush) default h = .ok ((value, default), after)) :
    C.run (deflate (some r) flush) h = .ok (value, after) := by
  change heapCall (deflate (some r) flush) default h = _ at exec
  change deflate (some r) flush h = _
  cases e : deflate (some r) flush h with
  | error f => simp [heapCall, e] at exec
  | ok p =>
    obtain ⟨v, a⟩ := p
    simp [heapCall, e] at exec
    obtain ⟨⟨rfl, -⟩, rfl⟩ := exec
    rfl

/-- **`DeflateQuiet`** (the statement of the gz skeleton, `gz.skeleton-write.lean`). -/
theorem deflate_quiet_holds :
    ∃ (Φ : Int32 → Heap → ZStreamRef → Nat) (Quiet : Int32 → Heap → ZStreamRef → Prop),
    (∀ (flush : Int32) (h : Heap) (r : ZStreamRef) (z : ZStream) (value : Int32) (after : Heap) (z' : ZStream),
      0 ≤ flush.toInt → flush.toInt ≤ 4 →
      StreamReachable .deflate h r → StreamBuffers h r → ActiveHeader h r →
      r.get h = some z → z.next_out ≠ .null → z.avail_in = 0 → 8 ≤ z.avail_out.toNat →
      Call.execute (.deflate (some r) flush) default h = .ok ((value, default), after) → r.get after = some z' →
      z'.avail_out = 0 → Φ flush after r < Φ flush h r) ∧
    (∀ (flush : Int32) (h : Heap) (r : ZStreamRef) (z : ZStream) (value : Int32) (after : Heap) (z' : ZStream),
      0 ≤ flush.toInt → flush.toInt ≤ 4 →
      StreamReachable .deflate h r → StreamBuffers h r → ActiveHeader h r →
      r.get h = some z → z.next_out ≠ .null → z.avail_in = 0 → z.avail_out ≠ 0 →
      Call.execute (.deflate (some r) flush) default h = .ok ((value, default), after) → r.get after = some z' →
      z'.avail_out ≠ 0 → Quiet flush after r) ∧
    (∀ (flush : Int32) (h : Heap) (r : ZStreamRef) (z : ZStream) (value : Int32) (after : Heap) (z' : ZStream),
      Quiet flush h r → 0 ≤ flush.toInt → flush.toInt ≤ 4 →
      StreamReachable .deflate h r → StreamBuffers h r → ActiveHeader h r →
      r.get h = some z → z.next_out ≠ .null → z.avail_in = 0 →
      Call.execute (.deflate (some r) flush) default h = .ok ((value, default), after) → r.get after = some z' →
      z'.avail_out = z.avail_out) ∧
    (∀ (flush : Int32) (h after : Heap) (r : ZStreamRef) (z z' : ZStream), StreamReachable .deflate h r →
      Rebuffer h after r → r.get h = some z →
      r.get after = some z' → z'.next_in = z.next_in → z'.avail_in = z.avail_in →
      Φ flush after r = Φ flush h r ∧ (Quiet flush h r → Quiet flush after r)) := by
  refine ⟨Phi, QuietS, ?_, ?_, ?_, ?_⟩
  · intro flush h r z value after z' lower upper reach buffers active get out empty room exec get' full
    obtain ⟨ds, z0, d, inv, header, facts⟩ := reachable_inv_of (Call.sequence_facts_of tinyOverlay) reach
    have same : z0 = z := Option.some.inj (inv.good.live.hz.symm.trans get)
    subst same
    obtain ⟨rc, a, z1, d1, run, inv1, fill, _⟩ :=
      call_quiet inv header facts buffers active out lower upper empty
    have e := (run_of_execute exec).symm.trans run
    simp only [Except.ok.injEq, Prod.mk.injEq] at e
    obtain ⟨-, rfl⟩ := e
    have z1e : z1 = z' := Option.some.inj (inv1.good.live.hz.symm.trans get')
    subst z1e
    rw [Phi_eq flush inv1, Phi_eq flush inv]
    exact phiD_lt (fill room full)
  · intro flush h r z value after z' lower upper reach buffers active get out empty room exec get' left
    obtain ⟨ds, z0, d, inv, header, facts⟩ := reachable_inv_of (Call.sequence_facts_of tinyOverlay) reach
    have same : z0 = z := Option.some.inj (inv.good.live.hz.symm.trans get)
    subst same
    obtain ⟨rc, a, z1, d1, run, inv1, _, quiet⟩ :=
      call_quiet inv header facts buffers active out lower upper empty
    have e := (run_of_execute exec).symm.trans run
    simp only [Except.ok.injEq, Prod.mk.injEq] at e
    obtain ⟨-, rfl⟩ := e
    have z1e : z1 = z' := Option.some.inj (inv1.good.live.hz.symm.trans get')
    subst z1e
    exact ⟨d1, stateOf_eq inv1, quiet room left⟩
  · intro flush h r z value after z' q lower upper reach buffers active get _ empty exec get'
    obtain ⟨ds, z0, d, inv, _, facts⟩ := reachable_inv_of (Call.sequence_facts_of tinyOverlay) reach
    have same : z0 = z := Option.some.inj (inv.good.live.hz.symm.trans get)
    subst same
    obtain ⟨d', st, qd⟩ := q
    have de : d' = d := Option.some.inj (st.symm.trans (stateOf_eq inv))
    subst de
    obtain ⟨rc, a, z1, run, get1, eq⟩ := quiet_silent inv facts buffers qd lower upper empty
    have e := (run_of_execute exec).symm.trans run
    simp only [Except.ok.injEq, Prod.mk.injEq] at e
    obtain ⟨-, rfl⟩ := e
    have z1e : z1 = z' := Option.some.inj (get1.symm.trans get')
    subst z1e
    exact eq
  · intro flush h after r z z' reach edit _ _ _ _
    have st := stateOf_rebuffer reach edit
    refine ⟨by unfold Phi; rw [st], fun ⟨d, s, q⟩ => ⟨d, st.trans s, q⟩⟩

end Zlib.Deflate.Universal.Quiet
