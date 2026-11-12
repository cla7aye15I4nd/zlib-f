import ZlibF.Proof.«deflate.c.universal-ops-header»
import ZlibF.Proof.«deflate.c.universal-ops-params»

/-!
# deflate.c: the header facts after `deflateSetDictionary` and `deflateParams`

Batch C (`operation_header`). `HeaderInv` after the cases of `deflateSetDictionary` and
`deflateParams` whose `DInv` step is proved (batch B, `deflate.c.universal-ops-dictionary`,
`-params`): the refusals, the dictionary when no level-0 slide is pending, and the parameter
change with the same strategy and compression function. Each lemma has the form of a hypothesis
of `operation_header_of`, with the case's extra premise.
-/

namespace Zlib.Deflate.Universal
open C ZlibF.Spec ZlibF.Spec.Public Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Engine.Proofs
open Zlib.Deflate.Proofs
set_option autoImplicit false

/-- Two successful runs of one program from one heap end in the same heap. -/
theorem same_after {α : Type} {p : M α} {h after after' : Heap} {v v' : α}
    (run : p h = .ok (v, after)) (run' : p h = .ok (v', after')) : after = after' := by
  have e := run.symm.trans run'
  simp only [Except.ok.injEq, Prod.mk.injEq] at e
  exact e.2

/-- **`deflateSetDictionary` keeps the header facts** when no slide of a level-0 stream is pending
(`matches = 0`, every stream at a nonzero level), including its refusals. -/
theorem setDictionary_header_unslid {h after : Heap} {r : ZStreamRef} {ds ds' : Nat} {z z' : ZStream}
    {d d' : DeflateState} {dictionary : BPtr} {dictLength : UInt32} {rc : Int32}
    (inv : DInv h r ds z d) (header : HeaderInv d) (args : CallerRange h r dictionary dictLength.toNat false)
    (zeroM : d.«matches» = 0)
    (run : C.run (Zlib.Deflate.deflateSetDictionary (some r) dictionary dictLength) h = .ok (rc, after))
    (invAfter : DInv after r ds' z' d') : HeaderInv d' := by
  have good := inv.good
  have check := stateCheck_live good.live
  rw [C.run] at run
  by_cases null : dictionary = .null
  · have run' : deflateSetDictionary (some r) dictionary dictLength h = .ok (Z_STREAM_ERROR, h) := by
      rw [setdict_checks]
      simp [bind_app, check, null]
      try rfl
    have e := same_after run run'
    subst e
    exact header_unchanged inv header invAfter
  have nullB : (dictionary == .null) = false := by simpa using null
  have stateRun : zrd (some r) (·.state) h = .ok (z.state, h) := by rw [zrd_eq, good.live.hz]
  have ldRun : ldDeflateState (some (.tab ds)) h = .ok (d, h) := ldDeflateState_tab good.live.hs
  by_cases refuse : (d.wrap == 2 || (d.wrap == 1 && d.status != INIT_STATE) || d.lookahead != 0 ||
      (d.wrap == 0 && d.strstart.toUInt64.toInt64 != d.block_start)) = true
  · have run' : deflateSetDictionary (some r) dictionary dictLength h = .ok (Z_STREAM_ERROR, h) := by
      rw [setdict_checks]
      simp only [bind_app, check, nullB, bne_self_eq_false, Bool.false_or, Bool.false_eq_true, ite_false, stateRun,
        good.live.zst, castD, ldRun, refuse, ite_true]
      rfl
    have e := same_after run run'
    subst e
    exact header_unchanged inv header invAfter
  · have la0 : d.lookahead = 0 := by
      by_cases e : d.lookahead = 0
      · exact e
      · exfalso; apply refuse; simp [e]
    obtain ⟨after2, zF, dF, bodyRun, invF, _, _, _, _, _, headerF, _⟩ :=
      setdict_body inv dictionary dictLength args null zeroM la0
    have run' : deflateSetDictionary (some r) dictionary dictLength h = .ok (Z_OK, after2) := by
      rw [setdict_checks]
      simp only [Bool.not_eq_true] at refuse
      simp only [bind_app, check, nullB, bne_self_eq_false, Bool.false_or, Bool.false_eq_true, ite_false, stateRun,
        good.live.zst, castD, ldRun, refuse]
      exact bodyRun
    have e := same_after run run'
    subst e
    obtain ⟨-, -, same⟩ := invF.unique invAfter.good
    subst same
    exact headerF header

set_option maxHeartbeats 2000000 in
/-- **`deflateParams` refusing** a level or strategy out of range keeps the header facts. -/
theorem params_header_refuse {h after : Heap} {r : ZStreamRef} {ds ds' : Nat} {z z' : ZStream}
    {d d' : DeflateState} {level strategy rc : Int32}
    (inv : DInv h r ds z d) (header : HeaderInv d)
    (refuse : (decide ((if level == Z_DEFAULT_COMPRESSION then 6 else level) < 0) ||
      decide ((if level == Z_DEFAULT_COMPRESSION then 6 else level) > 9) ||
      decide (strategy < 0) || decide (strategy > Z_FIXED)) = true)
    (run : C.run (Zlib.Deflate.deflateParams (some r) level strategy) h = .ok (rc, after))
    (invAfter : DInv after r ds' z' d') : HeaderInv d' := by
  have good := inv.good
  have check := stateCheck_live good.live
  have stateRun : zrd (some r) (·.state) h = .ok (z.state, h) := by rw [zrd_eq, good.live.hz]
  have run' : deflateParams (some r) level strategy h = .ok (Z_STREAM_ERROR, h) := by
    rw [params_source]
    simp only [bind_app, check, bne_self_eq_false, Bool.false_eq_true, ite_false, stateRun, good.live.zst, castD,
      refuse, ite_true, pure_app]
  rw [C.run] at run
  have e := same_after run run'
  subst e
  exact header_unchanged inv header invAfter

set_option maxHeartbeats 4000000 in
/-- **`deflateParams` with the same strategy and the same compression function** keeps the header
facts: at most the level, its tuning and the strategy change. -/
theorem params_header_same {h after : Heap} {r : ZStreamRef} {ds ds' : Nat} {z z' : ZStream}
    {d d' : DeflateState} {level strategy rc : Int32}
    (inv : DInv h r ds z d) (header : HeaderInv d)
    (lo : 0 ≤ (if level == Z_DEFAULT_COMPRESSION then 6 else level).toInt)
    (hi : (if level == Z_DEFAULT_COMPRESSION then 6 else level).toInt ≤ 9)
    (slo : 0 ≤ strategy.toInt) (shi : strategy.toInt ≤ 4)
    (sameStrategy : strategy = d.strategy)
    (sameFunc : (configuration_table[d.level.toInt.toNat]!).func =
      (configuration_table[(if level == Z_DEFAULT_COMPRESSION then 6 else level).toInt.toNat]!).func)
    (run : C.run (Zlib.Deflate.deflateParams (some r) level strategy) h = .ok (rc, after))
    (invAfter : DInv after r ds' z' d') : HeaderInv d' := by
  have good := inv.good
  have check := stateCheck_live good.live
  obtain ⟨lv, lvDef⟩ : ∃ x, x = if level == Z_DEFAULT_COMPRESSION then 6 else level := ⟨_, rfl⟩
  rw [← lvDef] at lo hi sameFunc
  have stateRun : zrd (some r) (·.state) h = .ok (z.state, h) := by rw [zrd_eq, good.live.hz]
  have ldRun : ldDeflateState (some (.tab ds)) h = .ok (d, h) := ldDeflateState_tab good.live.hs
  have rangeB : (decide (lv < 0) || decide (lv > 9) || decide (strategy < 0) || decide (strategy > Z_FIXED)) = false := by
    simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, Int32.lt_iff_toInt_lt, GT.gt]
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · change ¬ lv.toInt < 0; omega
    · change ¬ (9 : Int) < lv.toInt; omega
    · change ¬ strategy.toInt < 0; omega
    · change ¬ (4 : Int) < strategy.toInt; omega
  have cfgD := config_at_run h good.inv.level_lo good.inv.level_hi
  have cfgL := config_at_run h lo hi
  have stratB : (strategy != d.strategy) = false := by simp [sameStrategy]
  have funcB : ((configuration_table[d.level.toInt.toNat]!).func != (configuration_table[lv.toInt.toNat]!).func) = false := by
    rw [sameFunc]; exact bne_self_eq_false _
  have toTail : ∀ out, paramsTail (some (.tab ds)) lv strategy h = out →
      deflateParams (some r) level strategy h = out := by
    intro out tail
    rw [params_source, ← lvDef]
    simp only [bind_app, check, bne_self_eq_false, Bool.false_eq_true, ite_false, stateRun, good.live.zst, castD,
      rangeB, ldRun, cfgD, stratB, cfgL, funcB, pure_app, Bool.false_and, tail]
  rw [C.run] at run
  -- the state after the call is at the same block
  have atState : ∀ e : DeflateState, after = setD h ds e → after.dstates ds = some d' := by
    intro e eq
    have getA : r.get after = some z := by rw [eq]; simpa using good.live.hz
    exact state_after getA good.live.zst invAfter
  by_cases sameLevel : d.level = lv
  · have levelB : (d.level != lv) = false := by simp [sameLevel]
    have stateEq : ({ d with strategy := strategy } : DeflateState) = d := by rw [sameStrategy]
    have tailRun : paramsTail (some (.tab ds)) lv strategy h = .ok (Z_OK, h) := by
      unfold paramsTail
      simp only [bind_app, ldRun, levelB, Bool.false_eq_true, ite_false, wrD_eq, good.live.hs, stateEq,
        setD_self good.live.hs]
      rfl
    have e := same_after run (toTail _ tailRun)
    subst e
    exact header_unchanged inv header invAfter
  · have levelB : (d.level != lv) = true := by simpa using sameLevel
    have cls := func_class (a := d.level.toInt.toNat) (b := lv.toInt.toNat)
      (by have := good.inv.level_lo; have := good.inv.level_hi; omega) (by omega) sameFunc
    have dNonzero : d.level ≠ 0 := by
      intro zero
      apply sameLevel
      rw [zero]
      have : lv.toInt.toNat = 0 := cls.1.mp (by rw [zero]; rfl)
      apply Int32.toInt_inj.mp
      change (0 : Int) = lv.toInt
      omega
    have zeroB : (d.level == 0 && d.«matches» != 0) = false := by simp [dNonzero]
    let c := configuration_table[lv.toInt.toNat]!
    let d2 := paramsState d lv strategy c
    have tailRun : paramsTail (some (.tab ds)) lv strategy h = .ok (Z_OK, setD h ds d2) := by
      unfold paramsTail
      simp only [bind_app, ldRun, levelB, ite_true, zeroB, Bool.false_eq_true, ite_false, cfgL, wrD_eq,
        good.live.hs, setD_dstates_same, setD_setD]
      rfl
    have e := same_after run (toTail _ tailRun)
    subst e
    have st := atState d2 rfl
    rw [setD_dstates_same] at st
    have e2 := Option.some.inj st
    subst e2
    exact header.keep rfl rfl rfl

end Zlib.Deflate.Universal
