import ZlibF.Proof.«deflate.c.universal-ops-params-general»
import ZlibF.Proof.«deflate.c.universal-call-assemble»
import ZlibF.Proof.«deflate.c.engine.overlay-header-ref»
import ZlibF.Proof.«deflate.c.borrow-stable»

/-!
# deflate.c: the accounting of `deflateParams`

`params_full`: one `deflateParams` call on a stream of the deflate invariant returns, keeps the invariant with the
same state block, moves the input and output pointers by what it consumed and produced (`StreamAccounting`), writes
only the stream's blocks and the output it produced, keeps the live blocks, the owned blocks and the gzip header
record. The gz write side (`gzsetparams`) needs these facts to keep its invariant across the call.

The proof follows `step_params` branch by branch: a refusal and a call with the same strategy and compression
function change no stream field; with no `deflate` call yet (`last_flush = -2`) the tail changes no stream field;
otherwise `deflate(Z_BLOCK)` (`deflate_call_full`) gives the accounting, and the tail after it changes no stream
field.
-/

namespace Zlib.Deflate.Universal
open C ZlibF.Spec ZlibF.Spec.Public Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Engine.Proofs
open Zlib.Deflate.Proofs
set_option autoImplicit false

/-- What a returning `deflateParams` call does to the stream `r`. -/
def ParamsFull (h : Heap) (r : ZStreamRef) (ds : Nat) (z : ZStream) (d : DeflateState) (level strategy : Int32) :
    Prop :=
  ∃ rc after z' d' used k, C.run (deflateParams (some r) level strategy) h = .ok (rc, after) ∧
    DInv after r ds z' d' ∧ StreamAccounting z z' used k ∧
    BufferFrame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) [⟨z.next_out, k⟩] ∧
    (∀ b, after.live b ↔ h.live b) ∧ (∀ b, DeflateOwned ds d b ↔ DeflateOwned ds d' b) ∧ d'.gzhead = d.gzhead

theorem accounting_refl (z : ZStream) : StreamAccounting z z 0 0 := by
  refine ⟨Nat.zero_le _, Nat.zero_le _, rfl, rfl, ?_, ?_, rfl, rfl, rfl, rfl, rfl⟩ <;>
  · cases z.next_in <;> cases z.next_out <;> rfl

/-- A run that keeps the stream record and every byte view. -/
theorem full_same {h after : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d d' : DeflateState}
    {level strategy rc : Int32} (run : C.run (deflateParams (some r) level strategy) h = .ok (rc, after))
    (inv' : DInv after r ds z d') (frame : Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b))
    (views : ∀ ref : BRef, (Space.get after ref : Option (Array UInt8)) = Space.get h ref)
    (live : ∀ b, after.live b ↔ h.live b) (owned : ∀ b, DeflateOwned ds d b ↔ DeflateOwned ds d' b)
    (gz : d'.gzhead = d.gzhead) : ParamsFull h r ds z d level strategy :=
  ⟨rc, after, z, d', 0, 0, run, inv', accounting_refl z,
    buffer_frame_same_views frame (fun _ _ ref _ _ => views ref), live, owned, gz⟩

set_option maxHeartbeats 4000000 in
/-- `params_same_run` with the owned blocks of the final state. -/
theorem params_same_run' {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (good : DGood h r ds z d) (level strategy : Int32)
    (rangeB : (decide ((if level == Z_DEFAULT_COMPRESSION then 6 else level) < 0) ||
      decide ((if level == Z_DEFAULT_COMPRESSION then 6 else level) > 9) ||
      decide (strategy < 0) || decide (strategy > Z_FIXED)) = false)
    (lo : 0 ≤ (if level == Z_DEFAULT_COMPRESSION then 6 else level).toInt)
    (hi : (if level == Z_DEFAULT_COMPRESSION then 6 else level).toInt ≤ 9)
    (sameStrategy : strategy = d.strategy)
    (sameFunc : (configuration_table[d.level.toInt.toNat]!).func =
      (configuration_table[(if level == Z_DEFAULT_COMPRESSION then 6 else level).toInt.toNat]!).func) :
    ∃ dK, deflateParams (some r) level strategy h = .ok (Z_OK, setD h ds dK) ∧
      dK.gzhead = d.gzhead ∧ (∀ b, DeflateOwned ds d b ↔ DeflateOwned ds dK b) ∧ dK.depth = d.depth := by
  have check := stateCheck_live good.live
  have stateRun : zrd (some r) (·.state) h = .ok (z.state, h) := by rw [zrd_eq, good.live.hz]
  have ldRun : ldDeflateState (some (.tab ds)) h = .ok (d, h) := ldDeflateState_tab good.live.hs
  have cfgD := config_at_run h good.inv.level_lo good.inv.level_hi
  have cfgL := config_at_run h lo hi
  have stratB : (strategy != d.strategy) = false := by simp [sameStrategy]
  have funcB : ((configuration_table[d.level.toInt.toNat]!).func !=
      (configuration_table[(if level == Z_DEFAULT_COMPRESSION then 6 else level).toInt.toNat]!).func) = false := by
    rw [sameFunc]; exact bne_self_eq_false _
  have toTail : deflateParams (some r) level strategy h =
      paramsTail (some (.tab ds)) (if level == Z_DEFAULT_COMPRESSION then 6 else level) strategy h := by
    rw [params_source]
    simp only [bind_app, check, bne_self_eq_false, Bool.false_eq_true, ite_false, stateRun, good.live.zst, castD,
      rangeB, ldRun, cfgD, stratB, cfgL, funcB, pure_app, Bool.false_and]
  rw [toTail]
  have dlo := good.inv.level_lo
  have dhi := good.inv.level_hi
  have cls := func_class (a := d.level.toInt.toNat)
    (b := (if level == Z_DEFAULT_COMPRESSION then 6 else level).toInt.toNat) (by omega) (by omega) sameFunc
  by_cases sameLevel : d.level = (if level == Z_DEFAULT_COMPRESSION then 6 else level)
  · have levelB : (d.level != (if level == Z_DEFAULT_COMPRESSION then 6 else level)) = false := by simp [sameLevel]
    refine ⟨{ d with strategy }, ?_, rfl, fun _ => Iff.rfl, rfl⟩
    unfold paramsTail
    simp only [bind_app, ldRun, levelB, Bool.false_eq_true, ite_false, wrD_eq, good.live.hs]
    all_goals (try rfl)
  · have levelB : (d.level != (if level == Z_DEFAULT_COMPRESSION then 6 else level)) = true := by simpa using sameLevel
    have dNonzero : d.level ≠ 0 := by
      intro zero
      apply sameLevel
      rw [zero]
      have : (if level == Z_DEFAULT_COMPRESSION then 6 else level).toInt.toNat = 0 := cls.1.mp (by rw [zero]; rfl)
      apply Int32.toInt_inj.mp
      change (0 : Int) = _
      omega
    have zeroB : (d.level == 0 && d.«matches» != 0) = false := by simp [dNonzero]
    refine ⟨paramsState d (if level == Z_DEFAULT_COMPRESSION then 6 else level) strategy
      configuration_table[(if level == Z_DEFAULT_COMPRESSION then 6 else level).toInt.toNat]!, ?_, rfl,
      fun _ => Iff.rfl, rfl⟩
    unfold paramsTail
    simp only [bind_app, ldRun, levelB, ite_true, zeroB, Bool.false_eq_true, ite_false, cfgL, wrD_eq,
      good.live.hs, setD_dstates_same, setD_setD]
    all_goals (try rfl)

theorem get_setD_stream (h : Heap) (r : ZStreamRef) (ds : Nat) (d : DeflateState) : r.get (setD h ds d) = r.get h := by
  cases r <;> rfl

/-- A `DInv` of a run's heap is about the stream record and state block of a known run. -/
theorem dinv_ident {h : Heap} {r : ZStreamRef} {ds ds' : Nat} {z z' : ZStream} {d' dK : DeflateState}
    (hz : r.get h = some z) (hzst : z.state = some (.deflate ds)) (hk : h.dstates ds = some dK)
    (inv : DInv h r ds' z' d') : DInv h r ds z dK := by
  have e1 : z' = z := Option.some.inj (inv.good.live.hz.symm.trans hz)
  subst e1
  have e2 : ds' = ds := by
    have := inv.good.live.zst
    rw [hzst] at this
    cases this
    rfl
  subst e2
  have e3 : d' = dK := Option.some.inj (inv.good.live.hs.symm.trans hk)
  subst e3
  exact inv

set_option maxHeartbeats 8000000 in
/-- **`deflateParams`, with its accounting.** -/
theorem params_full {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv h r ds z d) (headerInv : HeaderInv d) (calls : CallFacts d) (buffers : StreamBuffers h r)
    (header : ActiveHeader h r) (level strategy : Int32) : ParamsFull h r ds z d level strategy := by
  have good := inv.good
  have check := stateCheck_live good.live
  have stateRun : zrd (some r) (·.state) h = .ok (z.state, h) := by rw [zrd_eq, good.live.hz]
  by_cases refuse : (decide ((if level == Z_DEFAULT_COMPRESSION then 6 else level) < 0) ||
      decide ((if level == Z_DEFAULT_COMPRESSION then 6 else level) > 9) ||
      decide (strategy < 0) || decide (strategy > Z_FIXED)) = true
  · have run : C.run (deflateParams (some r) level strategy) h = .ok (Z_STREAM_ERROR, h) := by
      rw [C.run, params_source]
      simp only [bind_app, check, bne_self_eq_false, Bool.false_eq_true, ite_false, stateRun, good.live.zst, castD,
        refuse, ite_true, pure_app]
    exact full_same run inv ⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _,
      fun _ _ _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
      (fun _ => rfl) (fun _ => Iff.rfl) (fun _ => Iff.rfl) rfl
  have rangeB : (decide ((if level == Z_DEFAULT_COMPRESSION then 6 else level) < 0) ||
      decide ((if level == Z_DEFAULT_COMPRESSION then 6 else level) > 9) ||
      decide (strategy < 0) || decide (strategy > Z_FIXED)) = false := by simpa using refuse
  have ranges : 0 ≤ (if level == Z_DEFAULT_COMPRESSION then 6 else level).toInt ∧
      (if level == Z_DEFAULT_COMPRESSION then 6 else level).toInt ≤ 9 ∧ 0 ≤ strategy.toInt ∧ strategy.toInt ≤ 4 := by
    have r2 := rangeB
    simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, Int32.lt_iff_toInt_lt, GT.gt] at r2
    obtain ⟨⟨⟨a, b⟩, c⟩, e⟩ := r2
    have z0 : (0 : Int32).toInt = 0 := rfl
    have n9 : (9 : Int32).toInt = 9 := rfl
    have f4 : Z_FIXED.toInt = 4 := rfl
    omega
  obtain ⟨lo, hi, slo, shi⟩ := ranges
  by_cases same : strategy = d.strategy ∧ (configuration_table[d.level.toInt.toNat]!).func =
      (configuration_table[(if level == Z_DEFAULT_COMPRESSION then 6 else level).toInt.toNat]!).func
  · obtain ⟨dK, runK, gzK, ownK, depthK⟩ := params_same_run' good level strategy rangeB lo hi same.1 same.2
    obtain ⟨value, after, runS, ⟨ds', z', d', invS⟩, bfS, lcS⟩ :=
      step_params_same inv level strategy lo hi slo shi same.1 same.2
    change heapCall (deflateParams (some r) level strategy) default h = _ at runS
    rw [heapCall_run runK] at runS
    have eA : setD h ds dK = after := (Prod.mk.inj (Except.ok.inj runS)).2
    subst eA
    have invK : DInv (setD h ds dK) r ds z dK :=
      dinv_ident (by rw [get_setD_stream]; exact good.live.hz) good.live.zst (setD_dstates_same h ds dK) invS
    have shapeK := shape_setD good.live.hs dK
    exact full_same runK invK (owned_frame_setD h r ds d dK) (views_setD good.live.hs depthK
      rfl rfl rfl rfl) (fun b => shapeK.live b) ownK gzK
  have differs : strategy ≠ d.strategy ∨ (configuration_table[d.level.toInt.toNat]!).func ≠
      (configuration_table[(if level == Z_DEFAULT_COMPRESSION then 6 else level).toInt.toNat]!).func := by
    by_cases s : strategy = d.strategy
    · exact Or.inr (fun f => same ⟨s, f⟩)
    · exact Or.inl s
  have source := params_differs good level strategy rangeB lo hi differs
  by_cases reset : d.last_flush = -2
  · have resetB : (d.last_flush != -2) = false := by simp [reset]
    obtain ⟨after, dF, tailRun, invF, shapeF, frameF, -, -, -, viewsF, ownedF, -, -, gzF, -⟩ :=
      params_tail inv (Flushed.of_reset calls reset) _ strategy lo hi slo shi
    have run : C.run (deflateParams (some r) level strategy) h = .ok (Z_OK, after) := by
      rw [C.run, source, resetB]
      exact tailRun
    exact full_same run invF frameF viewsF (fun b => shapeF.live b) (fun b => (ownedF b).symm) gzF
  · have resetB : (d.last_flush != -2) = true := by simpa using reset
    obtain ⟨rc, after1, z1, d1, used, out, run1, inv1, -, -, clauses1, owned1, -, gz1, -⟩ :=
      Call.deflate_call_full inv (tinyOverlay.at _) headerInv calls buffers header Z_BLOCK
    obtain ⟨account, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, frame1, live1, -⟩ := clauses1
    have liveOne : ∀ b, after1.live b ↔ h.live b := fun b => by simpa [LiveChange] using live1 b
    have run1' : deflate (some r) Z_BLOCK h = .ok (rc, after1) := run1
    have flushRun : ∀ v after, paramsAfter (some r) (some (.tab ds)) (if level == Z_DEFAULT_COMPRESSION then 6 else level) strategy rc after1 = .ok (v, after) →
        C.run (deflateParams (some r) level strategy) h = .ok (v, after) := by
      intro v after e
      rw [C.run, source, if_pos resetB, params_flush_split]
      simp only [bind_app, run1']
      exact e
    rcases params_after_outcome inv1 rc _ strategy lo hi slo shi with
      ⟨v, stop⟩ | ⟨after, dF, tailRun, invF, shapeF, frameF, -, -, -, viewsF, ownedF, -, -, gzF, -⟩
    · exact ⟨v, after1, z1, d1, used, out.length, flushRun v after1 stop, inv1, account, frame1, liveOne,
        owned1, gz1⟩
    · have run : C.run (deflateParams (some r) level strategy) h = .ok (Z_OK, after) := flushRun _ _ tailRun
      refine ⟨Z_OK, after, z1, dF, used, out.length, run, invF, account, ?_,
        fun b => (shapeF.live b).trans (liveOne b), fun b => (owned1 b).trans (ownedF b).symm, gzF.trans gz1⟩
      have sameO : (fun b => StreamRoot r b ∨ DeflateOwned ds d1 b) = (fun b => StreamRoot r b ∨ DeflateOwned ds d b) := by
        funext b; rw [owned1 b]
      rw [sameO] at frameF
      refine buffer_frame_then_frame frame1 frameF (fun ref _ _ => viewsF ref) ?_
      intro ref off ptr i root
      rcases output_target good buffers with null | ⟨ob, oo, arr, eo, get, outside⟩ | ⟨owner, oo, foreign, eo, get, outside⟩
      · rw [null] at ptr; cases ptr
      · rw [eo] at ptr
        injection ptr with ptr1 _
        subst ptr1
        have ei : ob = i := by rcases root with e | e <;> cases e; rfl
        subst ei
        refine ⟨outside, ?_⟩
        obtain ⟨a', get', -, -⟩ := frame1.2 _ (List.mem_singleton.mpr rfl) (.blk ob) oo arr eo get
        refine Or.inl ?_
        rw [show after1.bytes ob = some a' from get']
        exact Option.some_ne_none _
      · rw [eo] at ptr
        injection ptr with ptr1 _
        subst ptr1
        have ei : owner = i := by rcases root with e | e <;> cases e; rfl
        subst ei
        refine ⟨outside, ?_⟩
        obtain ⟨a', get', -, -⟩ := frame1.2 _ (List.mem_singleton.mpr rfl) (.dstate_depth owner) oo foreign.depth
          eo (show (h.dstates owner).map (·.depth) = some foreign.depth by rw [get]; rfl)
        refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
        intro none
        change (after1.dstates owner).map (·.depth) = some a' at get'
        rw [none] at get'
        cases get'

end Zlib.Deflate.Universal

namespace Zlib.Deflate.BorrowProofs
open C C.LibcBorrow Zlib.Deflate
set_option autoImplicit false

/-- `deflateParams` keeps the `strerror` borrow. -/
theorem stable_deflateParams (p : ZStreamPtr) (level strategy : Int32) : StableM (deflateParams p level strategy) := by
  unfold deflateParams
  repeat' first
    | with_reducible exact stable_deflate _ _
    | with_reducible exact stable_deflateStateCheck _
    | with_reducible exact stable_config_at _
    | with_reducible exact stable_slide_hash _
    | with_reducible exact stable_CLEAR_HASH _
    | with_reducible exact stable_ladd _ _
    | deflate_borrow_step

end Zlib.Deflate.BorrowProofs
