import ZlibF.Proof.«deflate.c.universal-ops-dictionary»

/-!
# deflate.c: `deflateParams` keeps the invariant (batch B, part of `operation_step`)

`deflateParams` normalizes and checks the level and the strategy. If the strategy or the
compression function changes after the first `deflate` call, it first runs `deflate(Z_BLOCK)`
and refuses with `Z_BUF_ERROR` unless all input is consumed and the block is empty. A level
change then repairs the hash table of a level-0 stream (`slide_hash` for one pending slide,
`CLEAR_HASH` for more) and loads the tuning of the new level; the strategy is stored last.

This file proves the refusals and the change without a flush and without a repair.
-/

namespace Zlib.Deflate.Universal
open C ZlibF.Spec ZlibF.Spec.Public Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Engine.Proofs
open Zlib.Deflate.Proofs
set_option autoImplicit false

/-- `deflateParams` after the flush: the level change and the strategy. -/
def paramsTail (s : DeflateStatePtr) (level strategy : Int32) : M Int32 := do
  let d ← ldDeflateState s
  if d.level != level then
    if d.level == 0 && d.«matches» != 0 then
      if d.«matches» == 1 then slide_hash s else CLEAR_HASH s
      wr s (fun d => { d with «matches» := 0 })
    let c ← config_at level
    wr s (fun d => { d with level := level, max_lazy_match := c.max_lazy.toUInt32, good_match := c.good_length.toUInt32,
                            nice_match := c.nice_length.toUInt32.toInt32, max_chain_length := c.max_chain.toUInt32 })
  wr s (fun d => { d with strategy })
  return Z_OK

/-- The source of `deflateParams` with the tail named. -/
theorem params_source (strm : ZStreamPtr) (level strategy : Int32) :
    deflateParams strm level strategy = (do
      if (← deflateStateCheck strm) != 0 then return Z_STREAM_ERROR
      let s ← castDeflateState (← zrd strm (·.state))
      let level := if level == Z_DEFAULT_COMPRESSION then 6 else level
      if level < 0 || level > 9 || strategy < 0 || strategy > Z_FIXED then return Z_STREAM_ERROR
      let d ← ldDeflateState s
      let func := (← config_at d.level).func
      let differs ← if strategy != d.strategy then pure true else do
        pure (func != (← config_at level).func)
      if differs && d.last_flush != -2 then
        let err ← deflate strm Z_BLOCK
        if err == Z_STREAM_ERROR then return err
        let d ← ldDeflateState s
        let diff ← lsub d.strstart.toUInt64.toInt64 d.block_start
        let tot ← ladd diff d.lookahead.toUInt64.toInt64
        if (← zrd strm (·.avail_in)) != 0 || tot != 0 then return Z_BUF_ERROR
        paramsTail s level strategy
      else
        paramsTail s level strategy) := by
  unfold deflateParams paramsTail
  by_cases c : (level == Z_DEFAULT_COMPRESSION) = true
  · simp only [c, ite_true]
  · simp only [c, Bool.false_eq_true, ite_false]

/-- Putting back the array a view already holds changes nothing. -/
theorem put_same_view {g : Heap} {ref : BRef} {a : Array UInt8} (get : Space.get g ref = some a) :
    Space.put g ref a = g := by
  cases ref with
  | blk b =>
    change { g with bytes := upd g.bytes b (some a) } = g
    rw [upd_self g.bytes b a get]
  | str i => rfl
  | dstate_depth i =>
    change (match g.dstates i with | some s => { g with dstates := upd g.dstates i (some { s with depth := a }) } | none => g) = g
    change (g.dstates i).map (·.depth) = some a at get
    cases e : g.dstates i with
    | none => rfl
    | some s =>
      rw [e] at get
      simp only [Option.map_some, Option.some.injEq] at get
      subst get
      simp only []
      rw [upd_self g.dstates i s e]
  | st_dist_code => rfl
  | st_length_code => rfl

/-- A run that leaves every view of the write regions as it was has the frame of its storage. -/
theorem buffer_frame_same_views {h after : Heap} {changed : Nat → Prop} {regions : List Region}
    (frame : Frame h after changed)
    (same : ∀ region, region ∈ regions → ∀ r off, region.pointer = .ref r off →
      (Space.get after r : Option (Array UInt8)) = Space.get h r) :
    BufferFrame h after changed regions := by
  let f : Heap → Region → Heap := fun current region => match region.pointer with
    | .null => current
    | .ref r _ => match (Space.get h r : Option (Array UInt8)) with
      | none => current
      | some a => Space.put current r a
  have fx : ∀ x, x ∈ regions → f after x = after := by
    intro x m
    show (match x.pointer with
      | .null => after
      | .ref r _ => match (Space.get h r : Option (Array UInt8)) with
        | none => after
        | some a => Space.put after r a) = after
    rcases e : x.pointer with _ | ⟨r, off⟩
    · rfl
    · have hx := same x m r off e
      simp only []
      cases g : (Space.get h r : Option (Array UInt8)) with
      | none => rfl
      | some a => exact put_same_view (by rw [hx, g])
  have gen : ∀ rs : List Region, (∀ x, x ∈ rs → f after x = after) → rs.foldl f after = after := by
    intro rs
    induction rs with
    | nil => intro _; rfl
    | cons x rs ih =>
      intro hs
      rw [List.foldl_cons, hs x List.mem_cons_self]
      exact ih (fun y m => hs y (List.mem_cons_of_mem _ m))
  have restored : restoreRegions h after regions = after := gen regions fx
  refine ⟨by rw [restored]; exact frame, ?_⟩
  intro region m r off a pointer get
  refine ⟨a, by rw [same region m r off pointer]; exact get, rfl, fun _ _ _ => rfl⟩

/-- `step_setD` for a call with write regions the run does not touch. -/
theorem step_setD_regions {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d d' : DeflateState}
    {call : Call} (inv : DInv h r ds z d) (value : call.Result)
    (run : call.execute default h = .ok ((value, default), setD h ds d'))
    (depth : d'.depth = d.depth) (inv' : DInv (setD h ds d') r ds z d')
    (sameOwned : ∀ b, DeflateOwned ds d b ↔ DeflateOwned ds d' b) :
    StepOk h r call := by
  refine ⟨value, setD h ds d', run, ⟨ds, z, d', inv'⟩, ?_, ?_⟩
  · refine buffer_frame_same_views ?_ ?_
    · refine ⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _, fun b _ unchanged => ?_⟩
      have ne : b ≠ ds := by
        rintro rfl
        exact unchanged (Or.inr (Or.inl ((inv.owned b).2 (Or.inl rfl))))
      exact ⟨rfl, rfl, rfl, rfl, setD_dstates_ne h ds b d' ne, rfl, rfl, rfl⟩
    · intro region _ ref off _
      cases ref with
      | dstate_depth i =>
        change ((setD h ds d').dstates i).map (·.depth) = (h.dstates i).map (·.depth)
        by_cases e : i = ds
        · subst e; rw [setD_dstates_same, inv.good.live.hs]; simp [depth]
        · rw [setD_dstates_ne _ _ _ _ e]
      | _ => rfl
  · have shape := shape_setD inv.good.live.hs d'
    intro b
    rw [shape.live b]
    constructor
    · intro live
      refine Or.inl ⟨live, fun ⟨owned, not⟩ => not ?_⟩
      exact (inv'.owned b).2 ((sameOwned b).1 ((inv.owned b).1 owned))
    · rintro (⟨live, _⟩ | ⟨owned, _⟩)
      · exact live
      · exact owned_live inv.good ((sameOwned b).2 ((inv'.owned b).1 owned))

/-- The compression function of each level. -/
theorem table_func (n : Nat) (hn : n < 10) : (configuration_table[n]!).func =
    if n = 0 then .stored else if n ≤ 3 then .fast else .slow := by
  match n, hn with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rfl
  | 7, _ => rfl
  | 8, _ => rfl
  | 9, _ => rfl

/-- Levels with the same compression function: both 0, both in 1..3, or both in 4..9. -/
theorem func_class {a b : Nat} (ha : a < 10) (hb : b < 10)
    (e : (configuration_table[a]!).func = (configuration_table[b]!).func) :
    (a = 0 ↔ b = 0) ∧ (a ≤ 3 ↔ b ≤ 3) := by
  rw [table_func a ha, table_func b hb] at e
  by_cases a0 : a = 0 <;> by_cases b0 : b = 0 <;> by_cases a3 : a ≤ 3 <;> by_cases b3 : b ≤ 3 <;>
    simp only [a0, b0, a3, b3, if_true, if_false, reduceCtorEq] at e <;> omega

/-- The state after a level change that needs no table repair. -/
def paramsState (d : DeflateState) (level strategy : Int32) (c : Config) : DeflateState :=
  { d with level := level, max_lazy_match := c.max_lazy.toUInt32, good_match := c.good_length.toUInt32, nice_match := c.nice_length.toUInt32.toInt32, max_chain_length := c.max_chain.toUInt32, strategy := strategy }

set_option maxHeartbeats 4000000 in
/-- **`deflateParams` with the same strategy and the same compression function**: no flush and no
table repair; at most the level and its tuning change. -/
theorem step_params_same {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv h r ds z d) (level strategy : Int32)
    (lo : 0 ≤ (if level == Z_DEFAULT_COMPRESSION then 6 else level).toInt)
    (hi : (if level == Z_DEFAULT_COMPRESSION then 6 else level).toInt ≤ 9)
    (slo : 0 ≤ strategy.toInt) (shi : strategy.toInt ≤ 4)
    (sameStrategy : strategy = d.strategy)
    (sameFunc : (configuration_table[d.level.toInt.toNat]!).func =
      (configuration_table[(if level == Z_DEFAULT_COMPRESSION then 6 else level).toInt.toNat]!).func) :
    StepOk h r (.deflateParams (some r) level strategy) := by
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
      Call.execute (.deflateParams (some r) level strategy) default h =
        (out.map fun p => ((p.1, default), p.2)) := by
    intro out tail
    simp only [Call.execute, heapCall]
    rw [params_source, ← lvDef]
    simp only [bind_app, check, bne_self_eq_false, Bool.false_eq_true, ite_false, stateRun, good.live.zst, castD,
      rangeB, ldRun, cfgD, stratB, cfgL, funcB, pure_app, Bool.false_and, tail]
    rcases out with e | ⟨v, after⟩ <;> rfl
  have shape := inv.shape
  have dlo := good.inv.level_lo
  have dhi := good.inv.level_hi
  have cls := func_class (a := d.level.toInt.toNat) (b := lv.toInt.toNat) (by omega) (by omega) sameFunc
  by_cases sameLevel : d.level = lv
  · -- only the strategy is stored, and it is the old one
    have levelB : (d.level != lv) = false := by simp [sameLevel]
    have stateEq : ({ d with strategy := strategy } : DeflateState) = d := by rw [sameStrategy]
    have tailRun : paramsTail (some (.tab ds)) lv strategy h = .ok (Z_OK, h) := by
      unfold paramsTail
      simp only [bind_app, ldRun, levelB, Bool.false_eq_true, ite_false, wrD_eq, good.live.hs, stateEq,
        setD_self good.live.hs]
      rfl
    have run : Call.execute (.deflateParams (some r) level strategy) default h = .ok ((Z_OK, default), setD h ds d) := by
      rw [toTail _ tailRun, setD_self good.live.hs]; rfl
    exact step_setD_regions inv Z_OK run rfl (by rw [setD_self good.live.hs]; exact inv) (fun _ => Iff.rfl)
  · have levelB : (d.level != lv) = true := by simpa using sameLevel
    have dNonzero : d.level ≠ 0 := by
      intro zero
      apply sameLevel
      rw [zero]
      have : lv.toInt.toNat = 0 := cls.1.mp (by rw [zero]; rfl)
      apply Int32.toInt_inj.mp
      change (0 : Int) = lv.toInt
      omega
    have lvNonzero : lv ≠ 0 := by
      intro zero
      apply dNonzero
      have : d.level.toInt.toNat = 0 := cls.1.mpr (by rw [zero]; rfl)
      apply Int32.toInt_inj.mp
      change d.level.toInt = 0
      omega
    have zeroB : (d.level == 0 && d.«matches» != 0) = false := by simp [dNonzero]
    let c := configuration_table[lv.toInt.toNat]!
    let d2 := paramsState d lv strategy c
    have tailRun : paramsTail (some (.tab ds)) lv strategy h = .ok (Z_OK, setD h ds d2) := by
      unfold paramsTail
      simp only [bind_app, ldRun, levelB, ite_true, zeroB, Bool.false_eq_true, ite_false, cfgL, wrD_eq,
        good.live.hs, setD_dstates_same, setD_setD]
      rfl
    have inv2 : DStInv h ds d2 := { good.inv with blocks := good.inv.blocks_keys rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl, level_lo := lo, level_hi := hi, strat_lo := slo, strat_hi := shi }
    have good2 : DGood (setD h ds d2) r ds z d2 := good.setD' rfl good.live.status inv2 (by trkeep)
    refine step_setD_regions (d' := d2) inv Z_OK (by rw [toTail _ tailRun]; rfl) rfl (inv.of_fields good2 ?_ ?_ ?_)
      (fun b => by simp [DeflateOwned, d2, paramsState])
    · intro sh
      refine ⟨sh.room, sh.insert, sh.insertDone, sh.prevLength, sh.matchLength, sh.matchAvailable, sh.blockStart,
        fun _ => sh.blockSpan dNonzero, fun z0 => absurd z0 lvNonzero, sh.available, sh.pendingMatch, ?_,
        sh.highWater, sh.windowInit, sh.lastFlush, sh.headerFlush, sh.trailer, sh.biValid, sh.cursor, sh.symRoom,
        ⟨sh.slides.1, fun _ => sh.slides.2 dNonzero⟩, ?_, sh.symBlock, ?_, sh.lazyStart⟩
      · intro l1 l3 s2 s3
        change 1 ≤ lv.toInt at l1
        change lv.toInt ≤ 3 at l3
        have : d.level.toInt.toNat ≤ 3 := cls.2.mpr (by omega)
        have dl1 : 1 ≤ d.level.toInt := by
          have : d.level.toInt ≠ 0 := fun e => dNonzero (Int32.toInt_inj.mp (by rw [e]; rfl))
          omega
        exact sh.fastLazy dl1 (by omega) (by rw [← sameStrategy]; exact s2) (by rw [← sameStrategy]; exact s3)
      · intro large
        obtain ⟨p1, p2, p3, p4⟩ := sh.lazyPrev large
        refine ⟨?_, by show strategy.toInt ≠ 2; rw [sameStrategy]; exact p2,
          by show strategy.toInt ≠ 3; rw [sameStrategy]; exact p3, p4⟩
        change 4 ≤ lv.toInt
        by_cases c : lv.toInt.toNat ≤ 3
        · have := cls.2.mpr c; omega
        · omega
      · intro nz
        obtain ⟨p1, p2, p3⟩ := sh.lazyAvail nz
        refine ⟨?_, by show strategy.toInt ≠ 2; rw [sameStrategy]; exact p2,
          by show strategy.toInt ≠ 3; rw [sameStrategy]; exact p3⟩
        change 4 ≤ lv.toInt
        by_cases c : lv.toInt.toNat ≤ 3
        · have := cls.2.mpr c; omega
        · omega
    · intro hashing
      obtain ⟨ch, sl, ro⟩ := hashing
      refine ⟨fun m => ch m, fun m => sl m, fun s2 s3 large => ro (by rw [← sameStrategy]; exact s2)
        (by rw [← sameStrategy]; exact s3) large⟩
    · rintro ⟨⟨xs, ⟨b, a, pbuf, bytes, ledger⟩, near⟩, clear, below⟩
      exact ⟨⟨xs, ⟨b, a, pbuf, bytes, ledger.keep rfl rfl rfl rfl⟩, near⟩,
        ⟨clear.bl, clear.opt, clear.fixed⟩, below⟩

set_option maxHeartbeats 2000000 in
/-- **`deflateParams` refuses** a level outside `-1..9` or a strategy outside `0..4` and leaves
the heap as it is. -/
theorem step_params_refuse {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv h r ds z d) (level strategy : Int32)
    (refuse : (decide ((if level == Z_DEFAULT_COMPRESSION then 6 else level) < 0) ||
      decide ((if level == Z_DEFAULT_COMPRESSION then 6 else level) > 9) ||
      decide (strategy < 0) || decide (strategy > Z_FIXED)) = true) :
    StepOk h r (.deflateParams (some r) level strategy) := by
  have good := inv.good
  have check := stateCheck_live good.live
  have stateRun : zrd (some r) (·.state) h = .ok (z.state, h) := by rw [zrd_eq, good.live.hz]
  have run : Call.execute (.deflateParams (some r) level strategy) default h =
      .ok ((Z_STREAM_ERROR, default), setD h ds d) := by
    rw [setD_self good.live.hs]
    simp only [Call.execute, heapCall]
    rw [params_source]
    simp only [bind_app, check, bne_self_eq_false, Bool.false_eq_true, ite_false, stateRun, good.live.zst, castD,
      refuse, ite_true, pure_app]
  exact step_setD_regions inv Z_STREAM_ERROR run rfl (by rw [setD_self good.live.hs]; exact inv) (fun _ => Iff.rfl)

end Zlib.Deflate.Universal
