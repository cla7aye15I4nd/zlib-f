import ZlibF.Proof.«deflate.c.quiet-in-call»
import ZlibF.Proof.«deflate.c.quiet-call»

/-!
# deflate.c: `DeflateQuietIn`

The potential: with no gzip header record (`gzhead = NULL`, as gz never sets one) the mixed-radix
`phiN = ((phase·8 + rank)·2^18 + work)·2^18 + pending`; with a record `phiG`, which adds the header
position `2^64 − 1 − gzindex` below the rank. The work term is below `2^18` and `pending` at most
`2^17` (`work_lt_of_inv`, `pending_le_of_inv`), so every component fits its radix, `phiN < 2^41`, and
a decrease `DecIn` (lexicographic in phase, rank and header position, then the work term plus four per
input byte, then `pending`) lowers `Φ + 2^30·avail_in`: a byte of input consumed may raise the work
term by four, which is `2^20 < 2^30` in `Φ`. `Quiet` is `QuietS`.

`deflate_quiet_in_of` is `DeflateQuietIn` (batch C's statement, written out here) from `call_in`,
`deflate_call_full` (the call keeps `gzhead`), `quiet_silent` and `stateOf_rebuffer`, under the open
fact `StoredStop` of `deflate_stored` with input.
-/

namespace Zlib.Deflate.Universal.Quiet
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Deflate.Engine.Proofs Zlib.Deflate.Universal.Call
set_option autoImplicit false

/-- The potential of a state with a gzip header record. -/
def phiG (d : DeflateState) : Nat :=
  (((phase d * 8 + rank d) * 2 ^ 64 + gzrem d) * 2 ^ 18 + work d) * 2 ^ 18 + d.pending.toNat

/-- The potential of a state with no gzip header record. -/
def phiN (d : DeflateState) : Nat :=
  ((phase d * 8 + rank d) * 2 ^ 18 + work d) * 2 ^ 18 + d.pending.toNat

def psi (d : DeflateState) : Nat := if d.gzhead = none then phiN d else phiG d

/-- `Φ` of `DeflateQuietIn`. -/
def PhiIn (_flush : Int32) (h : Heap) (r : ZStreamRef) : Nat :=
  match stateOf h r with
  | some d => psi d
  | none => 0

theorem PhiIn_eq {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState} (flush : Int32)
    (inv : DInv h r ds z d) : PhiIn flush h r = psi d := by
  unfold PhiIn; rw [stateOf_eq inv]

/-- **A `DecIn` decrease lowers `Φ + 2^30·avail_in`.** -/
theorem dec_psi {d d' : DeflateState} {a a' : Nat} (dec : DecIn d a d' a') (gh : d'.gzhead = d.gzhead)
    (w : work d < 2 ^ 18) (w' : work d' < 2 ^ 18) (p : d.pending.toNat < 2 ^ 18) (p' : d'.pending.toNat < 2 ^ 18) :
    psi d' + 2 ^ 30 * a' < psi d + 2 ^ 30 * a := by
  have r1 := rank_le d; have r2 := rank_le d'; have g1 := gzrem_lt d; have g2 := gzrem_lt d'
  have ph1 := phase_le d; have ph2 := phase_le d'
  unfold psi; rw [gh]
  obtain ⟨ale, top | ⟨pe, re, ge, wle, eq⟩⟩ := dec
  · split
    · rename_i hn
      unfold phiN
      rcases top with t | ⟨_, rl⟩ | ⟨_, _, ne, _⟩
      · omega
      · omega
      · exact absurd hn ne
    · unfold phiG
      rcases top with t | ⟨_, rl⟩ | ⟨_, _, _, gl⟩
      · omega
      · omega
      · omega
  · by_cases ea : a' = a
    · rcases eq ea with wl | ⟨we, pl⟩
      · split
        · unfold phiN; omega
        · unfold phiG; omega
      · split
        · unfold phiN; omega
        · unfold phiG; omega
    · split
      · unfold phiN; omega
      · unfold phiG; omega

/-- The bound (B): with no gzip header record, `Φ < 2^41`. -/
theorem psi_lt {d : DeflateState} (none : d.gzhead = none) (w : work d < 2 ^ 18) (p : d.pending.toNat < 2 ^ 18) :
    psi d < 2 ^ 41 := by
  have r1 := rank_le d; have ph1 := phase_le d
  unfold psi; rw [if_pos none]; unfold phiN; omega

/-- A call on the invariant, its `CallIn`, and the record kept. -/
theorem call_in_gz {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState} {flush : Int32}
    (inv : DInv h r ds z d) (header : HeaderInv d) (facts : CallFacts d) (buffers : StreamBuffers h r)
    (active : ActiveHeader h r) (out : z.next_out ≠ .null) (lower : 0 ≤ flush.toInt) (upper : flush.toInt ≤ 4)
    (sstop : StoredStop) :
    ∃ rc after z' d', C.run (deflate (some r) flush) h = .ok (rc, after) ∧ DInv after r ds z' d' ∧
      d'.gzhead = d.gzhead ∧
      (8 ≤ z.avail_out.toNat → z'.avail_out = 0 → DecIn d z.avail_in.toNat d' z'.avail_in.toNat) ∧
      (z'.avail_out ≠ 0 → (z.avail_in = 0 ∨ (d.status ≠ FINISH_STATE ∧ rc ≠ Z_STREAM_ERROR)) →
        z'.avail_in = 0 ∧ QuietD flush d') ∧
      (d.status = FINISH_STATE → z.avail_in ≠ 0 → z'.avail_out ≠ 0 → rc ≠ Z_STREAM_ERROR →
        z'.avail_in = z.avail_in ∧ d'.status = FINISH_STATE ∧ d'.pending = 0) := by
  obtain ⟨rc, a, z1, d1, run, inv1, cA, cQ, cF⟩ :=
    call_in inv (tinyOverlay.at _) header facts buffers active out lower upper sstop
  obtain ⟨rc2, a2, z2, d2, _, _, run2, inv2, _, _, _, _, _, gz2, _⟩ :=
    deflate_call_full inv (tinyOverlay.at _) header facts buffers active flush
  have e := Except.ok.inj (run2.symm.trans run)
  obtain ⟨_, rfl⟩ := Prod.mk.inj e
  obtain ⟨_, _, rfl⟩ := inv1.unique inv2.good
  exact ⟨rc, a2, z1, d2, run, inv1, gz2, cA, cQ, cF⟩

/-- **`DeflateQuietIn`** (batch C's statement, `gzwrite.c.comp`), under the open fact `StoredStop`. -/
theorem deflate_quiet_in_of (sstop : StoredStop) :
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
      Φ flush after r = Φ flush h r ∧ (Quiet flush h r → Quiet flush after r)) ∧
    -- (B)
    (∀ (flush : Int32) (h : Heap) (r : ZStreamRef) (z : ZStream) (k : Nat) (d : DeflateState),
      0 ≤ flush.toInt → flush.toInt ≤ 4 → StreamReachable .deflate h r → r.get h = some z →
      z.state = some (.deflate k) → h.dstates k = some d → d.gzhead = none → Φ flush h r < 2 ^ 62) ∧
    -- (1')
    (∀ (flush : Int32) (h : Heap) (r : ZStreamRef) (z : ZStream) (value : Int32) (after : Heap) (z' : ZStream),
      0 ≤ flush.toInt → flush.toInt ≤ 4 →
      StreamReachable .deflate h r → StreamBuffers h r → ActiveHeader h r →
      r.get h = some z → z.next_out ≠ .null → z.avail_in ≠ 0 → 8 ≤ z.avail_out.toNat →
      Call.execute (.deflate (some r) flush) default h = .ok ((value, default), after) → r.get after = some z' →
      z'.avail_out = 0 → Φ flush after r + 2 ^ 30 * z'.avail_in.toNat < Φ flush h r + 2 ^ 30 * z.avail_in.toNat) ∧
    -- (2')
    (∀ (flush : Int32) (h : Heap) (r : ZStreamRef) (z : ZStream) (k : Nat) (d : DeflateState) (value : Int32)
      (after : Heap) (z' : ZStream),
      0 ≤ flush.toInt → flush.toInt ≤ 4 →
      StreamReachable .deflate h r → StreamBuffers h r → ActiveHeader h r →
      r.get h = some z → z.state = some (.deflate k) → h.dstates k = some d → d.status ≠ FINISH_STATE →
      z.next_out ≠ .null → z.avail_in ≠ 0 → z.avail_out ≠ 0 →
      Call.execute (.deflate (some r) flush) default h = .ok ((value, default), after) → value ≠ Z_STREAM_ERROR →
      r.get after = some z' → z'.avail_out ≠ 0 → z'.avail_in = 0 ∧ Quiet flush after r) ∧
    -- (2f)
    (∀ (flush : Int32) (h : Heap) (r : ZStreamRef) (z : ZStream) (k : Nat) (d : DeflateState) (value : Int32)
      (after : Heap) (z' : ZStream),
      0 ≤ flush.toInt → flush.toInt ≤ 4 →
      StreamReachable .deflate h r → StreamBuffers h r → ActiveHeader h r →
      r.get h = some z → z.state = some (.deflate k) → h.dstates k = some d → d.status = FINISH_STATE →
      z.next_out ≠ .null → z.avail_in ≠ 0 → z.avail_out ≠ 0 →
      Call.execute (.deflate (some r) flush) default h = .ok ((value, default), after) → value ≠ Z_STREAM_ERROR →
      r.get after = some z' → z'.avail_out ≠ 0 →
      z'.avail_in = z.avail_in ∧ ∃ d', after.dstates k = some d' ∧ d'.status = FINISH_STATE ∧ d'.pending = 0) := by
  refine ⟨PhiIn, QuietS, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro flush h r z value after z' lower upper reach buffers active get out empty room exec get' full
    obtain ⟨ds, z0, d, inv, header, facts⟩ := reachable_inv_of (Call.sequence_facts_of tinyOverlay) reach
    have same : z0 = z := Option.some.inj (inv.good.live.hz.symm.trans get)
    subst same
    obtain ⟨rc, a, z1, d1, run, inv1, gz, cA, _, _⟩ :=
      call_in_gz inv header facts buffers active out lower upper sstop
    have e := (run_of_execute exec).symm.trans run
    simp only [Except.ok.injEq, Prod.mk.injEq] at e
    obtain ⟨-, rfl⟩ := e
    have z1e : z1 = z' := Option.some.inj (inv1.good.live.hz.symm.trans get')
    subst z1e
    rw [PhiIn_eq flush inv1, PhiIn_eq flush inv]
    have dec := dec_psi (cA room full) gz (work_lt_of_inv inv) (work_lt_of_inv inv1)
      (by have := pending_le_of_inv inv; omega) (by have := pending_le_of_inv inv1; omega)
    rw [empty] at dec
    simp at dec
    omega
  · intro flush h r z value after z' lower upper reach buffers active get out empty room exec get' left
    obtain ⟨ds, z0, d, inv, header, facts⟩ := reachable_inv_of (Call.sequence_facts_of tinyOverlay) reach
    have same : z0 = z := Option.some.inj (inv.good.live.hz.symm.trans get)
    subst same
    obtain ⟨rc, a, z1, d1, run, inv1, _, _, cQ, _⟩ :=
      call_in_gz inv header facts buffers active out lower upper sstop
    have e := (run_of_execute exec).symm.trans run
    simp only [Except.ok.injEq, Prod.mk.injEq] at e
    obtain ⟨-, rfl⟩ := e
    have z1e : z1 = z' := Option.some.inj (inv1.good.live.hz.symm.trans get')
    subst z1e
    exact ⟨d1, stateOf_eq inv1, (cQ left (Or.inl empty)).2⟩
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
    refine ⟨by unfold PhiIn; rw [st], fun ⟨d, s, q⟩ => ⟨d, st.trans s, q⟩⟩
  · intro flush h r z k d _ _ reach get hk hd none
    obtain ⟨ds, z0, dI, inv, _, _⟩ := reachable_inv_of (Call.sequence_facts_of tinyOverlay) reach
    have same : z0 = z := Option.some.inj (inv.good.live.hz.symm.trans get)
    subst same
    have kd : k = ds := by
      have := hk.symm.trans inv.good.live.zst
      simpa only [Option.some.injEq, StateRef.deflate.injEq] using this
    subst kd
    have de : d = dI := Option.some.inj (hd.symm.trans inv.good.live.hs)
    subst de
    rw [PhiIn_eq flush inv]
    have := psi_lt none (work_lt_of_inv inv) (by have := pending_le_of_inv inv; omega)
    omega
  · intro flush h r z value after z' lower upper reach buffers active get out _ room exec get' full
    obtain ⟨ds, z0, d, inv, header, facts⟩ := reachable_inv_of (Call.sequence_facts_of tinyOverlay) reach
    have same : z0 = z := Option.some.inj (inv.good.live.hz.symm.trans get)
    subst same
    obtain ⟨rc, a, z1, d1, run, inv1, gz, cA, _, _⟩ :=
      call_in_gz inv header facts buffers active out lower upper sstop
    have e := (run_of_execute exec).symm.trans run
    simp only [Except.ok.injEq, Prod.mk.injEq] at e
    obtain ⟨-, rfl⟩ := e
    have z1e : z1 = z' := Option.some.inj (inv1.good.live.hz.symm.trans get')
    subst z1e
    rw [PhiIn_eq flush inv1, PhiIn_eq flush inv]
    exact dec_psi (cA room full) gz (work_lt_of_inv inv) (work_lt_of_inv inv1)
      (by have := pending_le_of_inv inv; omega) (by have := pending_le_of_inv inv1; omega)
  · intro flush h r z k d value after z' lower upper reach buffers active get hk hd nf out _ _ exec nerr get' left
    obtain ⟨ds, z0, dI, inv, header, facts⟩ := reachable_inv_of (Call.sequence_facts_of tinyOverlay) reach
    have same : z0 = z := Option.some.inj (inv.good.live.hz.symm.trans get)
    subst same
    have kd : k = ds := by
      have := hk.symm.trans inv.good.live.zst
      simpa only [Option.some.injEq, StateRef.deflate.injEq] using this
    subst kd
    have de : d = dI := Option.some.inj (hd.symm.trans inv.good.live.hs)
    subst de
    obtain ⟨rc, a, z1, d1, run, inv1, _, _, cQ, _⟩ :=
      call_in_gz inv header facts buffers active out lower upper sstop
    have e := (run_of_execute exec).symm.trans run
    simp only [Except.ok.injEq, Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    have z1e : z1 = z' := Option.some.inj (inv1.good.live.hz.symm.trans get')
    subst z1e
    obtain ⟨i0, q⟩ := cQ left (Or.inr ⟨nf, nerr⟩)
    exact ⟨i0, d1, stateOf_eq inv1, q⟩
  · intro flush h r z k d value after z' lower upper reach buffers active get hk hd fin out inp _ exec nerr get' left
    obtain ⟨ds, z0, dI, inv, header, facts⟩ := reachable_inv_of (Call.sequence_facts_of tinyOverlay) reach
    have same : z0 = z := Option.some.inj (inv.good.live.hz.symm.trans get)
    subst same
    have kd : k = ds := by
      have := hk.symm.trans inv.good.live.zst
      simpa only [Option.some.injEq, StateRef.deflate.injEq] using this
    subst kd
    have de : d = dI := Option.some.inj (hd.symm.trans inv.good.live.hs)
    subst de
    obtain ⟨rc, a, z1, d1, run, inv1, _, _, _, cF⟩ :=
      call_in_gz inv header facts buffers active out lower upper sstop
    have e := (run_of_execute exec).symm.trans run
    simp only [Except.ok.injEq, Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    have z1e : z1 = z' := Option.some.inj (inv1.good.live.hz.symm.trans get')
    subst z1e
    obtain ⟨i0, st, p0⟩ := cF fin inp left nerr
    exact ⟨i0, d1, inv1.good.live.hs, st, p0⟩

end Zlib.Deflate.Universal.Quiet

#print axioms Zlib.Deflate.Universal.Quiet.deflate_quiet_in_of
