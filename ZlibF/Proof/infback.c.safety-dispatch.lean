import ZlibF.Proof.«infback.c.safety-len»

/-!
# infback.c: one round of the dispatch loop on the invariant

`dispatch_p` is one round of `for (;;) switch (state->mode)`: `TYPE`, `STORED`, `TABLE` (with its
fall-through into `LEN`), `LEN`, and the two exits `DONE` and `BAD`. The default case is
unreachable: `ModeOk` names the six modes. The fast path of `case LEN` is the premise `LenFast`
until its own lemma is checked; every other case is proved here.
-/

namespace Zlib.Infback.Safety
open C ZlibF.Spec ZlibF.Spec.Public Zlib.Inflate Zlib.Inflate.Proofs Zlib.Infback Zlib.Infback.Proofs
open Zlib.Inflate.Spec (setI)
set_option autoImplicit false

/-- `Round` is `TRound` at the measure of the round's start. -/
theorem Round.of_le {c : BCtx} {r : ZStreamRef} {i : Nat} {window : BPtr} {n : Nat}
    {pr : Proto c r i window n} {h0 h : Heap} {l : IL} {log : BackLog} {B : Nat}
    {res : Except Ex Unit} {l' : IL} {h' : Heap}
    (T : TRound c pr h0 B res l' h') (le : B ≤ backMeasure pr h l log) : Round c pr h0 h l log res l' h' := by
  obtain ⟨log', I', alt, sh⟩ := T
  refine ⟨log', I', ?_, sh⟩
  rcases alt with ⟨e, lt⟩ | x
  · exact Or.inl ⟨e, Nat.lt_of_lt_of_le lt le⟩
  · exact Or.inr x

/-- The fast path of `case LEN` (`RESTORE`, `inflate_fast`, `LOAD`) on the invariant. -/
def LenFast (c : BCtx) {r : ZStreamRef} {i : Nat} {window : BPtr} {n : Nat}
    (pr : Proto c r i window n) (h0 : Heap) : Prop :=
  ∀ (h : Heap) (l : IL) (log : BackLog) (s : InflateState), PInv c pr h0 h l log → h.istates i = some s →
    s.mode = LEN → l.bits.toNat < 8 → (l.have_ >= 6 && l.left >= 258) = true →
    ∃ res l' h', runX (back_LEN c) l h = .ok ((res, l'), h') ∧ Round c pr h0 h l log res l' h'

/-- **`case LEN` on the invariant**, with the fast path from `LenFast`. -/
theorem LEN_p (c : BCtx) {r : ZStreamRef} {i : Nat} {window : BPtr} {n : Nat}
    (pr : Proto c r i window n) {h0 h : Heap} {l : IL} {log : BackLog} (I : PInv c pr h0 h l log)
    {w woff : Nat} (hw : window = .ref (.blk w) woff) (fast : LenFast c pr h0) {s : InflateState}
    (hs : h.istates i = some s) (mode : s.mode = LEN) (short : l.bits.toNat < 8) :
    ∃ res l' h', runX (back_LEN c) l h = .ok ((res, l'), h') ∧ Round c pr h0 h l log res l' h' := by
  cases f : (l.have_ >= 6 && l.left >= 258)
  · exact LEN_slow_p c pr I hw hs mode short f
  · exact fast h l log s I hs mode short f

/-- **`case TABLE` on the invariant**, through its fall-through into `LEN`. -/
theorem TABLE_p (c : BCtx) {r : ZStreamRef} {i : Nat} {window : BPtr} {n : Nat}
    (pr : Proto c r i window n) {h0 h : Heap} {l : IL} {log : BackLog} (I : PInv c pr h0 h l log)
    {w woff : Nat} (hw : window = .ref (.blk w) woff) (fast : LenFast c pr h0) {s : InflateState}
    (hs : h.istates i = some s) (mode : s.mode = TABLE) (short : l.bits.toNat < 8) :
    ∃ res l' h', runX (back_TABLE c) l h = .ok ((res, l'), h') ∧ Round c pr h0 h l log res l' h' := by
  have m0 : backMeasure pr h l log = baseM pr l log + 2 := by
    rw [backMeasure_of pr hs, mode]; rfl
  rcases TABLE_pre_p c pr I hs mode short with
    ⟨res, l', h', run', T⟩ | ⟨l1, h1, log1, s1, run1, I1, hs1, mode1, -, le1, short1⟩
  · exact ⟨res, l', h', run', Round.of_le T (by rw [m0]; exact Nat.le_refl _)⟩
  · obtain ⟨res, l', h', run', R⟩ := LEN_p c pr I1 hw fast hs1 mode1 short1
    refine ⟨res, l', h', by rw [run1]; exact run', Round.of_le (B := backMeasure pr h1 l1 log1) R ?_⟩
    rw [backMeasure_of pr hs1, mode1, m0]
    exact le1

/-- **The exits `DONE` and `BAD`**: `ret` is set and the loop is left. -/
theorem exit_p (c : BCtx) {r : ZStreamRef} {i : Nat} {window : BPtr} {n : Nat}
    (pr : Proto c r i window n) {h0 h : Heap} {l : IL} {log : BackLog} (I : PInv c pr h0 h l log)
    (v : Int32) (hv : v = Z_STREAM_END ∨ v = Z_DATA_ERROR) :
    Round c pr h0 h l log (.error Ex.leave) { l with ret := v } h :=
  ⟨log, { I with put := I.put, chunk := I.chunk, bits := I.bits }, Or.inr ⟨rfl, by rcases hv with e | e <;> simp [e]⟩,
    fun x => (nomatch x)⟩

set_option maxRecDepth 100000 in
/-- **One round of the dispatch loop on the invariant.** At the start of the round fewer than
8 bits are held when the mode is `TYPE`, `TABLE` or `LEN` (`Short`). -/
theorem dispatch_p (c : BCtx) {r : ZStreamRef} {i : Nat} {window : BPtr} {n : Nat}
    (pr : Proto c r i window n) {h0 h : Heap} {l : IL} {log : BackLog} (I : PInv c pr h0 h l log)
    {w woff : Nat} (hw : window = .ref (.blk w) woff) (fast : LenFast c pr h0) (short : Short i l h) :
    ∃ res l' h', runX (back_dispatch c) l h = .ok ((res, l'), h') ∧ Round c pr h0 h l log res l' h' := by
  obtain ⟨z, s, valid, -, -⟩ := I.valid
  have hs := valid.2.1
  have rd : runX (monadLift (rdS c.st (·.mode)) : X UInt32) l h = .ok ((.ok s.mode, l), h) :=
    runX_lift_ok (rdS_ok I.cst hs _) l
  rcases (I.mode s hs).1 with m | m | m | m | m | m
  · obtain ⟨res, l', h', run', R⟩ := TYPE_p c pr I hs m (short s hs (Or.inl m))
    refine ⟨res, l', h', ?_, R⟩
    unfold back_dispatch
    simp only [runX_bind, rd, m, beq_self_eq_true, ↓reduceIte]
    exact run'
  · obtain ⟨res, l', h', run', R⟩ := STORED_p c pr I hw hs m
    refine ⟨res, l', h', ?_, R⟩
    unfold back_dispatch
    simp only [runX_bind, rd, m, beq_self_eq_true, ↓reduceIte,
      show (STORED == TYPE) = false from by decide, Bool.false_eq_true]
    exact run'
  · obtain ⟨res, l', h', run', R⟩ := TABLE_p c pr I hw fast hs m (short s hs (Or.inr (Or.inl m)))
    refine ⟨res, l', h', ?_, R⟩
    unfold back_dispatch
    simp only [runX_bind, rd, m, beq_self_eq_true, ↓reduceIte, Bool.false_eq_true,
      show (TABLE == TYPE) = false from by decide, show (TABLE == STORED) = false from by decide]
    exact run'
  · obtain ⟨res, l', h', run', R⟩ := LEN_p c pr I hw fast hs m (short s hs (Or.inr (Or.inr m)))
    refine ⟨res, l', h', ?_, R⟩
    unfold back_dispatch
    simp only [runX_bind, rd, m, beq_self_eq_true, ↓reduceIte, Bool.false_eq_true,
      show (LEN == TYPE) = false from by decide, show (LEN == STORED) = false from by decide,
      show (LEN == TABLE) = false from by decide]
    exact run'
  · refine ⟨.error Ex.leave, { l with ret := Z_STREAM_END }, h, ?_, exit_p c pr I _ (Or.inl rfl)⟩
    unfold back_dispatch
    simp only [runX_bind, rd, m, beq_self_eq_true, ↓reduceIte, Bool.false_eq_true,
      show (DONE == TYPE) = false from by decide, show (DONE == STORED) = false from by decide,
      show (DONE == TABLE) = false from by decide, show (DONE == LEN) = false from by decide,
      runX_modify, runX_throw]
  · refine ⟨.error Ex.leave, { l with ret := Z_DATA_ERROR }, h, ?_, exit_p c pr I _ (Or.inr rfl)⟩
    unfold back_dispatch
    simp only [runX_bind, rd, m, beq_self_eq_true, ↓reduceIte, Bool.false_eq_true,
      show (BAD == TYPE) = false from by decide, show (BAD == STORED) = false from by decide,
      show (BAD == TABLE) = false from by decide, show (BAD == LEN) = false from by decide,
      show (BAD == DONE) = false from by decide, runX_modify, runX_throw]

/-- A predicate on `Nat` that holds somewhere has a least witness. -/
theorem exists_least (P : Nat → Prop) (m : Nat) (hm : P m) : ∃ k, P k ∧ ∀ j, P j → k ≤ j := by
  induction m using Nat.strongRecOn with
  | ind m ih =>
    classical
    by_cases ex : ∃ j, j < m ∧ P j
    · obtain ⟨j, lt, pj⟩ := ex
      exact ih j lt pj
    · exact ⟨m, hm, fun j pj => Nat.le_of_not_lt (fun lt => ex ⟨j, lt, pj⟩)⟩

/-- The measures of a round start over the logs that carry the invariant. -/
def LoopAt (c : BCtx) {r : ZStreamRef} {i : Nat} {window : BPtr} {n : Nat}
    (pr : Proto c r i window n) (h0 : Heap) (l : IL) (h : Heap) (m : Nat) : Prop :=
  ∃ log, PInv c pr h0 h l log ∧ Short i l h ∧ backMeasure pr h l log = m

/-- The least of them (0 when there is none). -/
noncomputable def loopM (c : BCtx) {r : ZStreamRef} {i : Nat} {window : BPtr} {n : Nat}
    (pr : Proto c r i window n) (h0 : Heap) (l : IL) (h : Heap) : Nat := by
  classical
  exact if hI : ∃ m, LoopAt c pr h0 l h m then
    Classical.choose (exists_least _ (Classical.choose hI) (Classical.choose_spec hI)) else 0

theorem loopM_spec {c : BCtx} {r : ZStreamRef} {i : Nat} {window : BPtr} {n : Nat}
    {pr : Proto c r i window n} {h0 : Heap} {l : IL} {h : Heap} {m : Nat} (hm : LoopAt c pr h0 l h m) :
    LoopAt c pr h0 l h (loopM c pr h0 l h) ∧ ∀ j, LoopAt c pr h0 l h j → loopM c pr h0 l h ≤ j := by
  classical
  have hI : ∃ m, LoopAt c pr h0 l h m := ⟨m, hm⟩
  have e : loopM c pr h0 l h =
      Classical.choose (exists_least _ (Classical.choose hI) (Classical.choose_spec hI)) := by
    unfold loopM; rw [dif_pos hI]
  rw [e]
  exact Classical.choose_spec (exists_least _ (Classical.choose hI) (Classical.choose_spec hI))

theorem backMeasure_lt {c : BCtx} {r : ZStreamRef} {i : Nat} {window : BPtr} {n : Nat}
    {pr : Proto c r i window n} {h0 h : Heap} {l : IL} {log : BackLog} (I : PInv c pr h0 h l log)
    (bound : pr.inputBound < 2 ^ 48) : backMeasure pr h l log + 1 < fuel := by
  have b := I.bits.1
  have hv := l.have_.toNat_lt
  have rk : ((h.istates i).map (fun s => modeRank s.mode)).getD 0 ≤ 2 := by
    cases h.istates i with
    | none => simp
    | some s => simpa using modeRank_le s.mode
  unfold backMeasure fuel
  omega

/-- **The dispatch loop on the invariant**: `for (;;) switch (state->mode)` leaves by
`goto inf_leave` with one of the three results, the invariant kept. The input bound below
`2^48` keeps the measure below the runtime's `2^64` rounds. -/
theorem loop_p (c : BCtx) {r : ZStreamRef} {i : Nat} {window : BPtr} {n : Nat}
    (pr : Proto c r i window n) {h0 h : Heap} {l : IL} {log : BackLog} (I : PInv c pr h0 h l log)
    {w woff : Nat} (hw : window = .ref (.blk w) woff) (fast : LenFast c pr h0) (short : Short i l h)
    (bound : pr.inputBound < 2 ^ 48) :
    ∃ l' h' log', runX (xwhile (pure true) (back_dispatch c)) l h = .ok ((.error Ex.leave, l'), h') ∧
      PInv c pr h0 h' l' log' ∧ (l'.ret = Z_STREAM_END ∨ l'.ret = Z_DATA_ERROR ∨ l'.ret = Z_BUF_ERROR) := by
  classical
  let Inv : IL → Heap → Prop := fun l1 h1 => ∃ log1, PInv c pr h0 h1 l1 log1 ∧ Short i l1 h1
  let Q : Except Ex Unit → IL → Heap → Prop := fun res l1 h1 => res = .error Ex.leave ∧
    ∃ log1, PInv c pr h0 h1 l1 log1 ∧ (l1.ret = Z_STREAM_END ∨ l1.ret = Z_DATA_ERROR ∨ l1.ret = Z_BUF_ERROR)
  have mem : ∀ l1 h1, Inv l1 h1 →
      ∃ log1, PInv c pr h0 h1 l1 log1 ∧ Short i l1 h1 ∧ backMeasure pr h1 l1 log1 = loopM c pr h0 l1 h1 := by
    intro l1 h1 ⟨log1, I1, s1⟩
    exact (loopM_spec (m := backMeasure pr h1 l1 log1) ⟨log1, I1, s1, rfl⟩).1
  have low : ∀ l1 h1 log1, PInv c pr h0 h1 l1 log1 → Short i l1 h1 →
      loopM c pr h0 l1 h1 ≤ backMeasure pr h1 l1 log1 := fun l1 h1 log1 I1 s1 =>
    (loopM_spec (m := backMeasure pr h1 l1 log1) ⟨log1, I1, s1, rfl⟩).2 _ ⟨log1, I1, s1, rfl⟩
  have loop := xwhileBrk_wf (cond := pure true) (body := (do back_dispatch c; pure false : X Bool)) Inv Q
    (loopM c pr h0)
    (by
      intro l1 h1 hI
      obtain ⟨log1, I1, s1, e1⟩ := mem l1 h1 hI
      refine ⟨l1, h1, true, rfl, fun _ => ?_, fun x => (nomatch x)⟩
      obtain ⟨res, l2, h2, run2, log2, I2, alt, sh2⟩ := dispatch_p c pr I1 hw fast s1
      rcases alt with ⟨rfl, lt⟩ | ⟨rfl, ret⟩
      · refine ⟨.ok false, l2, h2, by rw [runX_bind, run2]; rfl, ⟨log2, I2, sh2 rfl⟩, ?_⟩
        have := low l2 h2 log2 I2 (sh2 rfl)
        omega
      · exact ⟨.error Ex.leave, l2, h2, by rw [runX_bind, run2], rfl, log2, I2, ret⟩)
    (l := l) (h := h) ⟨log, I, short⟩
    (Nat.lt_of_le_of_lt (Nat.add_le_add_right (low l h log I short) 1) (backMeasure_lt I bound))
  obtain ⟨res, l', h', run, rfl, log', I', ret⟩ := loop
  exact ⟨l', h', log', run, I', ret⟩

end Zlib.Infback.Safety
