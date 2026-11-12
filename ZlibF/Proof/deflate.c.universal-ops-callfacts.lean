import ZlibF.Proof.«deflate.c.universal-ops-header»

/-!
# deflate.c: the between-calls facts `CallFacts` after one stream operation

`CallFacts d` (`deflate.c.universal-invariant`: P1, P1b, P4 and `finishLook`) holds beside `DInv`
and `HeaderInv` in every reachable state. This module shows it after each operation of
`StreamOperation .deflate`, case by case, as `operation_header_of` does for `HeaderInv`.
`deflateReset` leaves a fresh state; `deflatePrime`, `deflateTune` and `deflateSetHeader` change no
field the facts read; the queries keep the state. The operations whose lemma is not yet a theorem
are hypotheses of `operation_callfacts_of`: `deflate` (`deflate_call`), `deflateParams` and
`deflateSetDictionary`.
-/

namespace Zlib.Deflate.Universal
open C ZlibF.Spec Zlib.Deflate Zlib.Deflate.Spec ZlibF.Spec.Public Zlib.Deflate.Proofs.GeneralInit
open Zlib.Deflate.Proofs Zlib.Deflate.Proofs.DefaultInit
open Zlib.Deflate.Engine.Proofs
open Zlib.Trees.Proofs.Out (setB)
set_option autoImplicit false

/-- A call that leaves the heap unchanged keeps the between-calls facts. -/
theorem callfacts_unchanged {h : Heap} {r : ZStreamRef} {ds ds' : Nat} {z z' : ZStream} {d d' : DeflateState}
    (inv : DInv h r ds z d) (calls : CallFacts d) (invAfter : DInv h r ds' z' d') : CallFacts d' := by
  obtain ⟨-, -, e⟩ := inv.unique invAfter.good
  rw [e]
  exact calls

/-- The state `deflateReset` leaves is fresh: no lookahead, no symbol, no lazy state, the block at
`strstart = 0`, and a header status. -/
theorem reset_state_callfacts (ds : Nat) (d : DeflateState) (a1 a2 a3 : Array CtData) :
    CallFacts (lmD (rkPost ds (rkMid d) a1 a2 a3)) := by
  refine ⟨fun _ => ?_, fun _ => ?_, fun _ => ?_, fun _ => ?_, fun _ => ?_⟩
  · simp [lmD, rkPost, rkPost3, rkMid, Zlib.Trees.Proofs.Out.ibRec, Zlib.Trees.Proofs.Out.trInitRec, MIN_MATCH_u]
  · simp [lmD]
  · simp [lmD, rkPost, rkPost3, rkMid, Zlib.Trees.Proofs.Out.ibRec, Zlib.Trees.Proofs.Out.trInitRec]
  · simp [lmD]
  · simp [lmD, rkPost, rkPost3, rkMid, Zlib.Trees.Proofs.Out.ibRec, Zlib.Trees.Proofs.Out.trInitRec]

/-- **`deflateReset`** leaves the between-calls facts, whatever the state before. -/
theorem reset_callfacts {h after : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d d' : DeflateState}
    {rc : Int32} (good : DGood h r ds z d)
    (run : C.run (deflateReset (some r)) h = .ok (rc, after)) (state : after.dstates ds = some d') :
    CallFacts d' := by
  obtain ⟨c1, c2, c3, h1, e1, rfl, -, -, -, good1, -⟩ := deflateResetKeep_safe good
  obtain ⟨q, qa, h2, e2, -, -, he, -, -⟩ := lm_init_safe good1
  have run' : C.run (deflateReset (some r)) h = .ok (Z_OK, h2) := by
    have hz1 := good1.live
    unfold deflateReset
    rw [C.run] at e1 ⊢
    simp only [bind_app, e1, beq_self_eq_true, ↓reduceIte, zrd_eq, hz1.hz, hz1.zst, castD, pure_app]
    rw [C.run] at e2
    rw [e2]
  have same := run.symm.trans run'
  simp only [Except.ok.injEq, Prod.mk.injEq] at same
  obtain ⟨-, rfl⟩ := same
  rw [he, setD_dstates_same] at state
  cases state
  exact reset_state_callfacts ds d c1 c2 c3

/-- `deflateTune` writes only the tuning fields. -/
theorem tune_callfacts {h after : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d d' : DeflateState}
    {g m n c rc : Int32} (good : DGood h r ds z d) (calls : CallFacts d)
    (run : C.run (deflateTune (some r) g m n c) h = .ok (rc, after)) (state : after.dstates ds = some d') :
    CallFacts d' := by
  obtain ⟨_, run', rfl, _, _⟩ := deflateTune_safe good g m n c
  have same := run.symm.trans run'
  simp only [Except.ok.injEq, Prod.mk.injEq] at same
  obtain ⟨-, rfl⟩ := same
  rw [setD_dstates_same] at state
  cases state
  exact calls.tune g m n c

/-- `deflateSetHeader` writes only the header pointer (or nothing). -/
theorem setHeader_callfacts {h after : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d d' : DeflateState}
    {head : GzHeaderPtr} {rc : Int32} (good : DGood h r ds z d) (calls : CallFacts d)
    (run : C.run (deflateSetHeader (some r) head) h = .ok (rc, after)) (state : after.dstates ds = some d') :
    CallFacts d' := by
  by_cases wrap : d.wrap = 2
  · obtain ⟨_, run', rfl, _, _⟩ := deflateSetHeader_safe good wrap head (gzOk_any h head)
    have same := run.symm.trans run'
    simp only [Except.ok.injEq, Prod.mk.injEq] at same
    obtain ⟨-, rfl⟩ := same
    rw [setD_dstates_same] at state
    cases state
    exact calls.setHeader head
  · have run' := deflateSetHeader_run_other good.live wrap head
    rw [C.run] at run
    have same := run.symm.trans run'
    simp only [Except.ok.injEq, Prod.mk.injEq] at same
    obtain ⟨-, rfl⟩ := same
    rw [good.live.hs] at state
    cases state
    exact calls

/-- **`deflatePrime`** writes only `pending_buf` and the pending and bit fields of the state. -/
theorem prime_callfacts {h after : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d d' : DeflateState}
    {bits value rc : Int32} (inv : DInv h r ds z d) (calls : CallFacts d)
    (notFinished : d.status ≠ FINISH_STATE)
    (run : C.run (deflatePrime (some r) bits value) h = .ok (rc, after)) (state : after.dstates ds = some d') :
    CallFacts d' := by
  have good := inv.good
  have hL := good.live
  by_cases range : bits.toInt < 0 ∨ 16 < bits.toInt
  · have same := run.symm.trans (deflatePrime_invalid_count hL bits value range)
    simp only [Except.ok.injEq, Prod.mk.injEq] at same
    obtain ⟨-, rfl⟩ := same
    rw [hL.hs] at state
    cases state
    exact calls
  have b0 : 0 ≤ bits.toInt := by omega
  have b16 : bits.toInt ≤ 16 := by omega
  obtain ⟨d0, b, buf, trees⟩ := good.trees
  have e0 : d0 = d := Option.some.inj (trees.base.dstate.symm.trans hL.hs)
  rw [e0] at trees
  obtain ⟨w, p, q, b', blocks⟩ := good.inv.blocks
  have bb : b = b' := by
    have := blocks.pbuf; rw [trees.base.pbuf] at this; cases this; rfl
  subst bb
  obtain ⟨off, pout, offFit⟩ := blocks.pout
  have v0 : 0 ≤ d.bi_valid.toInt := good.inv.bits.1
  have v7 : d.bi_valid.toInt ≤ 7 := inv.shape.biValid
  have notRange : (bits < 0 || bits > 16) = false := by
    have l1 : ¬ bits < 0 := fun lt => by have := Int32.lt_iff_toInt_lt.mp lt; simp at this; omega
    have l2 : ¬ bits > 16 := fun lt => by have := Int32.lt_iff_toInt_lt.mp lt; simp at this; omega
    simp [l1, l2]
  have move : ∃ a, deflatePrime (some r) bits value h =
      primeTail (some (.tab ds)) bits value (setD (setB h b a) ds { d with pending_out := d.pending_buf }) ∧
      a.size = buf.size := by
    by_cases mv : d.pending_out = d.pending_buf
    · refine ⟨buf, ?_, rfl⟩
      have same : ({ d with pending_out := d.pending_buf } : DeflateState) = d := by
        cases d; simp only at mv; subst mv; rfl
      rw [same, self_heap trees.base.bytes hL.hs, prime_split]
      simp [stateCheck_live hL, zrd_eq, hL.hz, hL.zst, castD, ldD_eq, hL.hs, notRange, mv]
    · obtain ⟨st, a, loop, size⟩ := move_loop trees.base.bytes trees.base.rw d.pending (off := off)
        (by have := trees.base.psize; omega)
      have loop' : cwhile moveCond moveBody (d.pending, d.pending_buf, d.pending_out) h = .ok (st, setB h b a) := by
        rw [trees.base.pbuf, pout]; exact loop
      refine ⟨a, ?_, size⟩
      rw [prime_split]
      simp [stateCheck_live hL, zrd_eq, hL.hz, hL.zst, castD, ldD_eq, hL.hs, notRange, mv, loop', wrD_eq]
  obtain ⟨a, runMove, sizeA⟩ := move
  obtain ⟨_, trees1⟩ := move_good good trees sizeA
  obtain ⟨rc', bf, e, runTail, -, -, ⟨p2, w2, v2, u2, rfl⟩, -⟩ :=
    prime_tail bits value trees1 b0 b16 v0 v7
  rw [C.run, runMove, runTail] at run
  simp only [Except.ok.injEq, Prod.mk.injEq] at run
  obtain ⟨-, rfl⟩ := run
  rw [setD_dstates_same] at state
  cases state
  exact ⟨calls.fresh, calls.freshStart, calls.finishSym, calls.finishLook,
    fun st => absurd st notFinished⟩

/-- **`operation_callfacts` from the open lemmas.** Hypotheses (not yet theorems): `deflateCalls`
(`deflate_call`, inflate batch 2), `paramsCalls` and `setDictionaryCalls` (inflate batch 1). -/
theorem operation_callfacts_of
    (deflateCalls : ∀ {h after : Heap} {r : ZStreamRef} {ds ds' : Nat} {z z' : ZStream}
      {d d' : DeflateState} {flush rc : Int32}, DInv h r ds z d → HeaderInv d → CallFacts d →
      StreamBuffers h r → ActiveHeader h r → C.run (Zlib.Deflate.deflate (some r) flush) h = .ok (rc, after) →
      DInv after r ds' z' d' → CallFacts d')
    (paramsCalls : ∀ {h after : Heap} {r : ZStreamRef} {ds ds' : Nat} {z z' : ZStream}
      {d d' : DeflateState} {level strategy rc : Int32}, DInv h r ds z d → HeaderInv d → CallFacts d →
      StreamBuffers h r → ActiveHeader h r →
      C.run (Zlib.Deflate.deflateParams (some r) level strategy) h = .ok (rc, after) →
      DInv after r ds' z' d' → CallFacts d')
    (setDictionaryCalls : ∀ {h after : Heap} {r : ZStreamRef} {ds ds' : Nat} {z z' : ZStream}
      {d d' : DeflateState} {dictionary : BPtr} {dictLength : UInt32} {rc : Int32}, DInv h r ds z d →
      HeaderInv d → CallFacts d → CallerRange h r dictionary dictLength.toNat false →
      C.run (Zlib.Deflate.deflateSetDictionary (some r) dictionary dictLength) h = .ok (rc, after) →
      DInv after r ds' z' d' → CallFacts d')
    {h after : Heap} {r : ZStreamRef} {ds ds' : Nat} {z z' : ZStream}
    {d d' : DeflateState} {call : Call} {value : call.Result}
    (inv : DInv h r ds z d) (header : HeaderInv d) (calls : CallFacts d)
    (operation : StreamOperation .deflate r call)
    (args : StreamArguments h r call) (run : call.execute default h = .ok ((value, default), after))
    (invAfter : DInv after r ds' z' d') : CallFacts d' := by
  have good := inv.good
  have hL := good.live
  cases call
  all_goals first
    | (exfalso; simp [StreamOperation] at operation; done)
    | skip
  case deflate p flush =>
    simp [StreamOperation] at operation
    subst operation
    obtain ⟨buffers, act⟩ := args
    exact deflateCalls inv header calls buffers act (heapCall_ok run) invAfter
  case deflateReset p =>
    simp [StreamOperation] at operation
    subst operation
    have r' := heapCall_ok run
    obtain ⟨a1, a2, a3, q, qa, h', run', -, -, -, -, -, he, -, -⟩ := deflateReset_safe good
    have same := r'.symm.trans run'
    cases same
    have getA : r.get after = some (rkZ z d) := by
      rw [he]; simp [ZStreamRef.get_put_same hL.hz]
    exact reset_callfacts good r' (state_after getA (by simpa [rkZ] using hL.zst) invAfter)
  case deflateParams p level strategy =>
    simp [StreamOperation] at operation
    subst operation
    obtain ⟨buffers, act⟩ := args
    exact paramsCalls inv header calls buffers act (heapCall_ok run) invAfter
  case deflatePrime p bits value' =>
    simp [StreamOperation] at operation
    subst operation
    have r' := heapCall_ok run
    have same := prime_stream inv r'
    have notFinished : d.status ≠ FINISH_STATE := by
      obtain ⟨z1, i, s, get, zst, hs, stat⟩ := args
      have zz : z1 = z := Option.some.inj (get.symm.trans hL.hz)
      subst zz
      rw [hL.zst] at zst
      cases zst
      rw [hL.hs] at hs
      cases hs
      rcases stat with e | e <;> rw [e] <;> decide
    exact prime_callfacts inv calls notFinished r' (state_after (same.trans hL.hz) hL.zst invAfter)
  case deflateGetDictionary p dictionary hasDictLength =>
    simp [StreamOperation] at operation
    subst operation
    have plain := plain_dictionary_of_args args
    obtain ⟨z1, i, s, get, zst, hs, range, -⟩ := args
    have zz : z1 = z := Option.some.inj (get.symm.trans hL.hz)
    subst zz
    rw [hL.zst] at zst
    cases zst
    have ss : s = d := Option.some.inj (hs.symm.trans hL.hs)
    subst ss
    have hfill := inv.shape.room
    have hwsz : s.w_size.toNat ≤ 32768 := by
      have := good.inv.wsize
      have : 2 ^ s.w_bits.toNat ≤ 2 ^ 15 := Nat.pow_le_pow_right (by omega) good.inv.wbits_hi
      omega
    have hlen := dictLen_toNat good.inv.wsz hwsz hfill
    have notOwnedBlk : ∀ x off, dictionary = .ref (.blk x) off → ¬ StreamOwned h r x := by
      intro x off eq owned
      rcases range with null | ⟨_, _, notOwned⟩
      · rw [eq] at null; cases null
      · exact notOwned x (by rw [eq]; rfl) owned
    have hdict : dictionary ≠ .null → dictLen s ≠ 0 →
        DictDest h s (s.strstart.toNat + s.lookahead.toNat - (dictLen s).toNat) (dictLen s).toNat dictionary := by
      intro nn _
      rcases range with null | ⟨⟨xs, bytes⟩, writable, _⟩
      · exact absurd null nn
      rcases bytes with ⟨null, _, _⟩ | ⟨q', j, a, eq, get, fit, _⟩
      · exact absurd null nn
      obtain ⟨x, rfl⟩ := plain q' j eq
      rcases writable rfl with ⟨null, _⟩ | ⟨q2, i2, a2, eq2, get2, ro2, _⟩
      · exact absurd null nn
      rw [eq] at eq2
      cases eq2
      refine ⟨x, j, a, eq, get, ro2, by omega, fun w' ew => Or.inl ?_⟩
      rintro rfl
      exact notOwnedBlk x j eq ((inv.owned x).2 (Or.inr (Or.inl ew)))
    obtain ⟨h', run', -, -, dst, str, gzs, -⟩ :=
      deflateGetDictionary_safe good hfill dictionary hasDictLength hdict
    have same := (heapCall_ok run).symm.trans run'
    cases same
    have getA : r.get after = some z1 := by
      rw [← hL.hz]; cases r <;> simp [ZStreamRef.get, str, gzs]
    have state := state_after getA hL.zst invAfter
    rw [dst, hL.hs] at state
    cases state
    exact calls
  case deflateSetDictionary p dictionary dictLength =>
    simp [StreamOperation] at operation
    subst operation
    exact setDictionaryCalls inv header calls args (heapCall_ok run) invAfter
  case deflateSetHeader p head =>
    simp [StreamOperation] at operation
    subst operation
    obtain ⟨-, z1, i, s, get, zst, hs, -⟩ := args
    have zz : z1 = z := Option.some.inj (get.symm.trans hL.hz)
    subst zz
    rw [hL.zst] at zst
    cases zst
    have ss : s = d := Option.some.inj (hs.symm.trans hL.hs)
    subst ss
    have r' := heapCall_ok run
    have getA : r.get after = some z1 := by
      by_cases wrap : s.wrap = 2
      · obtain ⟨h', run', rfl, -, -⟩ := deflateSetHeader_safe good wrap head (gzOk_any h head)
        have same := r'.symm.trans run'
        cases same
        simpa using hL.hz
      · have same := r'.symm.trans (deflateSetHeader_run_other hL wrap head)
        cases same
        exact hL.hz
    exact setHeader_callfacts good calls r' (state_after getA hL.zst invAfter)
  case deflateTune p g m n c =>
    simp [StreamOperation] at operation
    subst operation
    have r' := heapCall_ok run
    obtain ⟨h', run', rfl, -, -⟩ := deflateTune_safe good g m n c
    have same := r'.symm.trans run'
    cases same
    exact tune_callfacts good calls r' (state_after (by simpa using hL.hz) hL.zst invAfter)
  case deflatePending p hasPending hasBits =>
    simp [StreamOperation] at operation
    subst operation
    have same := (heapCall_ok run).symm.trans (deflatePending_run hL hasPending hasBits)
    cases same
    exact callfacts_unchanged inv calls invAfter
  case deflateUsed p hasBits =>
    simp [StreamOperation] at operation
    subst operation
    have same := (heapCall_ok run).symm.trans (deflateUsed_run hL hasBits)
    cases same
    exact callfacts_unchanged inv calls invAfter
  case deflateBound p n =>
    simp [StreamOperation] at operation
    subst operation
    obtain ⟨-, live⟩ := args
    obtain ⟨wl, -, run'⟩ := deflateBound_safe good (hdrStrOk_of_live inv live) n
    have same := (heapCall_ok run).symm.trans run'
    cases same
    exact callfacts_unchanged inv calls invAfter
  case deflateBound_z p n =>
    simp [StreamOperation] at operation
    subst operation
    obtain ⟨-, live⟩ := args
    obtain ⟨wl, -, run'⟩ := deflateBound_z_safe good (hdrStrOk_of_live inv live) n
    have same := (heapCall_ok run).symm.trans run'
    cases same
    exact callfacts_unchanged inv calls invAfter

end Zlib.Deflate.Universal
