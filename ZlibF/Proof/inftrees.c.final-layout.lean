import ZlibF.Proof.«inftrees.c.step»

/-! Retain the actual last iteration's layout fields. The ordinary loop
postcondition intentionally keeps only the facts needed for safety; these
partial-correctness lemmas preserve the additional fields on that same run. -/

namespace Zlib.Inftrees.Proofs
open C Zlib.Inftrees
set_option autoImplicit false

private theorem bind_return {α β : Type} {m : M α} {f : α → M β}
    {h after : Heap} {value : β} (run : (m >>= f) h = .ok (value, after)) :
    ∃ a middle, m h = .ok (a, middle) ∧ f a middle = .ok (value, after) := by
  cases first : m h with
  | error fault => simp only [bind_app, first] at run; contradiction
  | ok pair => exact ⟨pair.1, pair.2, rfl, by simpa only [bind_app, first] using run⟩

private theorem while_projection {σ α : Type} (project : σ → α) (test : σ → Bool)
    (body : σ → M σ)
    (preserves : ∀ s h result after, body s h = .ok (result, after) → project result = project s)
    {s result : σ} {h after : Heap}
    (run : cwhile (fun s => pure (test s, s)) body s h = .ok (result, after)) :
    project result = project s := by
  have go : ∀ n s h, cwhile.go (fun s => pure (test s, s)) body n s h =
      .ok (result, after) → project result = project s := by
    intro n
    induction n with
    | zero => intro s h run; cases run
    | succ n ih =>
      intro s h run
      simp only [cwhile.go, bind_app, pure_app] at run
      split at run
      · obtain ⟨next, middle, first, rest⟩ := bind_return run
        exact (ih next middle rest).trans (preserves s h next middle first)
      · cases run; rfl
  exact go fuel s h run

private theorem doWhile_projection {σ α : Type} (project : σ → α) (test : σ → Bool)
    (body : σ → M σ)
    (preserves : ∀ s h result after, body s h = .ok (result, after) → project result = project s)
    {s result : σ} {h after : Heap}
    (run : cdoWhile body (fun s => pure (test s, s)) s h = .ok (result, after)) :
    project result = project s := by
  have go : ∀ n s h, cdoWhile.go body (fun s => pure (test s, s)) n s h =
      .ok (result, after) → project result = project s := by
    intro n
    induction n with
    | zero => intro s h run; cases run
    | succ n ih =>
      intro s h run
      change (body s >>= fun next => do
        let (again, next) ← (pure (test next, next) : M (Bool × σ))
        if again then cdoWhile.go body (fun s => pure (test s, s)) n next else pure next) h = _ at run
      obtain ⟨next, middle, first, rest⟩ := bind_return run
      simp only [bind_app, pure_app] at rest
      split at rest
      · exact (ih next middle rest).trans (preserves s h next middle first)
      · cases rest
        exact preserves s h result after first
  exact go fuel s h run

private def retained (s : TS) : TS :=
  { s with low := 0, min := 0, fill := 0, incr := 0, here := default, left := 0 }

private def layout (s : TS) : UInt32 × UInt32 × UInt32 × UInt32 × CodePtr :=
  (s.len, s.curr, s.drop, s.used, s.next)

private theorem jp1_last_layout {c : Ctx} {s result : TS} {h after : Heap}
    (max : s.len = c.max) (inside : s.len.toNat < s.count.size)
    (last : s.count[s.len.toNat] = 1)
    (run : jp1 c s h = .ok (result, after)) : layout result = layout s := by
  unfold jp1 at run
  simp only [geta_eq inside, bind_app, pure_app, last] at run
  try dsimp only at run
  rw [seta_eq inside] at run
  simp only [bind_app, pure_app, UInt16.sub_self, beq_self_eq_true, ite_true] at run
  simp only [max, beq_self_eq_true, ite_true, pure_app] at run
  cases run
  simp only [layout, max]

private theorem jp1_last_huff {c : Ctx} {s result : TS} {h after : Heap}
    (max : s.len = c.max) (inside : s.len.toNat < s.count.size)
    (last : s.count[s.len.toNat] = 1)
    (run : jp1 c s h = .ok (result, after)) : result.huff = s.huff := by
  unfold jp1 at run
  simp only [geta_eq inside, bind_app, pure_app, last] at run
  rw [seta_eq inside] at run
  simp only [bind_app, pure_app, UInt16.sub_self, beq_self_eq_true, ite_true] at run
  simp only [max, beq_self_eq_true, ite_true, pure_app] at run
  cases run
  rfl

private theorem hereTop_jp0_cut {c : Ctx} {s result : TS} {h after : Heap}
    (run : hereTop c s h = .ok (result, after)) :
    ∃ here middle, jp0 c { s with here := here } middle = .ok (result, after) := by
  unfold hereTop at run
  obtain ⟨w, h1, _, run⟩ := bind_return run
  split at run
  · obtain ⟨w2, h2, _, run⟩ := bind_return run
    exact ⟨_, h2, run⟩
  · obtain ⟨w2, h2, _, run⟩ := bind_return run
    split at run
    · obtain ⟨w3, h3, _, run⟩ := bind_return run
      obtain ⟨extra, h4, _, run⟩ := bind_return run
      obtain ⟨w4, h5, _, run⟩ := bind_return run
      obtain ⟨base, h6, _, run⟩ := bind_return run
      exact ⟨_, h6, run⟩
    · exact ⟨_, h2, run⟩

private theorem jp0_single_huff {c : Ctx} {s result : TS} {h after : Heap}
    (len : s.len = 1) (max : s.len = c.max) (huff : s.huff = 0)
    (inside : s.len.toNat < s.count.size) (last : s.count[s.len.toNat] = 1)
    (run : jp0 c s h = .ok (result, after)) : result.huff = 1 := by
  unfold jp0 at run
  obtain ⟨incr, h1, _, run⟩ := bind_return run
  obtain ⟨fill, h2, _, run⟩ := bind_return run
  obtain ⟨filled, h3, fillRun, run⟩ := bind_return run
  have frame := doWhile_projection retained (fun s : TS => s.fill != 0) _
    (by
      intro before h value after run
      obtain ⟨hd, middle, _, run⟩ := bind_return run
      obtain ⟨ignored, middle', _, run⟩ := bind_return run
      cases run
      rfl) fillRun
  have lenFill : filled.len = s.len := by simpa only [retained] using congrArg TS.len frame
  have countFill : filled.count = s.count := by simpa only [retained] using congrArg TS.count frame
  have huffFill : filled.huff = 0 := by
    have equality : filled.huff = s.huff := by simpa only [retained] using congrArg TS.huff frame
    exact equality.trans huff
  obtain ⟨incr2, h4, incrRun, run⟩ := bind_return run
  rw [lenFill, len] at incrRun
  change Except.ok ((1 : UInt32), h3) = Except.ok (incr2, h4) at incrRun
  cases incrRun
  obtain ⟨incremented, h5, incrementRun, run⟩ := bind_return run
  have stopped : cwhile (fun s : TS => pure (s.huff &&& s.incr != 0, s))
      (fun s => pure { s with incr := s.incr >>> 1 }) { filled with incr := 1 } h3 =
      .ok ({ filled with incr := 1 }, h3) := by
    unfold cwhile
    change cwhile.go _ _ (18446744073709551615 + 1) _ _ = _
    rw [cwhile.go]
    simp [huffFill]
  rw [stopped] at incrementRun
  cases incrementRun
  dsimp only at run
  have branch : ((1 : UInt32) != 0) = true := rfl
  rw [if_pos branch] at run
  have value : (filled.huff &&& ((1 : UInt32) - 1)) + 1 = 1 := by rw [huffFill]; rfl
  rw [value] at run
  exact jp1_last_huff (s := { filled with incr := 1, huff := 1 })
    (by exact lenFill.trans max) (by simpa only [lenFill, countFill] using inside)
    (by simpa only [lenFill, countFill] using last) run

/-- The accepted incomplete singleton leaves huff at one, so the final
invalid entry is actually written rather than merely allowed by the post. -/
theorem hereTop_single_huff {c : Ctx} {s result : TS} {h after : Heap}
    (len : s.len = 1) (max : s.len = c.max) (huff : s.huff = 0)
    (inside : s.len.toNat < s.count.size) (last : s.count[s.len.toNat] = 1)
    (run : hereTop c s h = .ok (result, after)) : result.huff = 1 := by
  obtain ⟨here, middle, cut⟩ := hereTop_jp0_cut run
  exact jp0_single_huff (s := { s with here := here }) len max huff inside last cut

/-- A final symbol's fill and bit-increment loops preserve its allocation
layout. The final count decrement stops before any new subtable is opened. -/
private theorem jp0_last_layout {c : Ctx} {s result : TS} {h after : Heap}
    (max : s.len = c.max) (inside : s.len.toNat < s.count.size)
    (last : s.count[s.len.toNat] = 1)
    (run : jp0 c s h = .ok (result, after)) : layout result = layout s := by
  unfold jp0 at run
  obtain ⟨incr, h1, _, run⟩ := bind_return run
  obtain ⟨fill, h2, _, run⟩ := bind_return run
  obtain ⟨filled, h3, fillRun, run⟩ := bind_return run
  have fillFrame := doWhile_projection retained (fun s : TS => s.fill != 0) _
    (by
      intro before h value after run
      obtain ⟨hd, middle, _, run⟩ := bind_return run
      obtain ⟨unit, middle', _, run⟩ := bind_return run
      cases run
      rfl) fillRun
  have len : filled.len = s.len := by simpa only [retained] using congrArg TS.len fillFrame
  have count : filled.count = s.count := by simpa only [retained] using congrArg TS.count fillFrame
  have fields : layout filled = layout s := by simpa only [retained, layout] using congrArg layout fillFrame
  obtain ⟨incr2, h4, _, run⟩ := bind_return run
  obtain ⟨incremented, h5, incrementRun, run⟩ := bind_return run
  have incrementFrame := while_projection retained (fun s : TS => s.huff &&& s.incr != 0) _
    (by intro before h value after run; cases run; rfl) incrementRun
  have len' : incremented.len = filled.len := by
    simpa only [retained] using congrArg TS.len incrementFrame
  have count' : incremented.count = filled.count := by
    simpa only [retained] using congrArg TS.count incrementFrame
  have fields' : layout incremented = layout filled := by
    simpa only [retained, layout] using congrArg layout incrementFrame
  have len2 := len'.trans len
  have count2 := count'.trans count
  have fields2 := fields'.trans fields
  have final : ∀ huff, jp1 c { incremented with huff := huff } h5 = .ok (result, after) →
      layout result = layout s := by
    intro huff run
    exact (jp1_last_layout (s := { incremented with huff := huff }) (by exact len2.trans max)
      (by simpa only [len2, count2] using inside)
      (by simpa only [len2, count2] using last) run).trans fields2
  dsimp only at run
  split at run
  all_goals exact final _ run

/-- The actual last iteration retains len, curr, drop, used and next.
This complements, rather than assumes or changes, hereTop_wp. -/
theorem hereTop_last_layout {c : Ctx} {s result : TS} {h after : Heap}
    (max : s.len = c.max) (inside : s.len.toNat < s.count.size)
    (last : s.count[s.len.toNat] = 1)
    (run : hereTop c s h = .ok (result, after)) :
    result.len = s.len ∧ result.curr = s.curr ∧ result.drop = s.drop ∧
      result.used = s.used ∧ result.next = s.next := by
  have fields : layout result = layout s := by
    have final : ∀ here middle, jp0 c { s with here := here } middle = .ok (result, after) →
        layout result = layout s := by
      intro here middle run
      exact jp0_last_layout (s := { s with here := here }) max inside last run
    unfold hereTop at run
    obtain ⟨w, h1, _, run⟩ := bind_return run
    split at run
    · obtain ⟨w2, h2, _, run⟩ := bind_return run
      exact final _ _ run
    · obtain ⟨w2, h2, _, run⟩ := bind_return run
      split at run
      · obtain ⟨w3, h3, _, run⟩ := bind_return run
        obtain ⟨extra, h4, _, run⟩ := bind_return run
        obtain ⟨w4, h5, _, run⟩ := bind_return run
        obtain ⟨base, h6, _, run⟩ := bind_return run
        exact final _ _ run
      · exact final _ _ run
  exact ⟨congrArg Prod.fst fields, congrArg (fun p => p.2.1) fields,
    congrArg (fun p => p.2.2.1) fields, congrArg (fun p => p.2.2.2.1) fields,
    congrArg (fun p => p.2.2.2.2) fields⟩

/-- The final iteration has exactly one remaining code of its length. -/
theorem MI_final_entry {e : Env} {i : Nat} {s : TS} {ca : Array Code}
    (inv : MI e i s ca) (final : i + 1 = e.m) :
    s.len = e.c.max ∧ ∃ inside : s.len.toNat < s.count.size,
      s.count[s.len.toNat]'inside = 1 := by
  have hi : i < Tc e.f e.n 15 := inv.1
  have len : s.len.toNat = lenAt e.f e.n i := inv.2.2.2.1
  have count := inv.2.2.2.2.2.2.1
  have interval := lenAt_bounds (f := e.f) (n := e.n) hi
  have maxLen : e.l i = e.mx := by
    change lenAt e.f e.n i = lenAt e.f e.n (Tc e.f e.n 15 - 1)
    congr 1
    change i + 1 = Tc e.f e.n 15 at final
    omega
  have max : s.len = e.c.max := by
    apply UInt32.toNat_inj.mp
    rw [e.h_max]
    exact len.trans maxLen
  have inside : s.len.toNat < s.count.size := by rw [count.1, len]; omega
  have counted := count.2 (lenAt e.f e.n i) interval.1 interval.2
  have block := (lenAt_eq_iff (f := e.f) (n := e.n) interval.1 interval.2 hi).mp rfl
  have top := Tc_mono (f := e.f) (n := e.n) interval.2
  have last : s.count[s.len.toNat] = 1 := by
    apply UInt16.toNat_inj.mp
    rw [← len] at counted
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem inside,
      Option.getD_some] at counted
    change i + 1 = Tc e.f e.n 15 at final
    unfold rem at counted
    conv at counted => rhs; rw [len]
    change (s.count[s.len.toNat]).toNat = 1
    omega
  exact ⟨max, inside, last⟩

/-- Retain the final descriptor from the actual final iteration. The last
symbol and count hypotheses are derived from MI, not supplied by a caller. -/
theorem hereTop_final_descriptor {e : Env} {i : Nat} {s result : TS} {ca : Array Code}
    {after : Heap} (inv : MI e i s ca) (cells : Ex e i s ca)
    (final : i + 1 = e.m) (run : hereTop e.c s (e.hc ca) = .ok (result, after)) :
    DescB e i result ∧ result.drop.toNat = (e.D i).drop ∧ result.len.toNat = e.l i := by
  have len : s.len.toNat = lenAt e.f e.n i := inv.2.2.2.1
  obtain ⟨max, inside, last⟩ := MI_final_entry inv final
  obtain ⟨len', curr, drop, used, next⟩ := hereTop_last_layout max inside last run
  refine ⟨?_, ?_, by rw [len']; exact len⟩
  · obtain ⟨⟨k, pointer, base⟩, width, extent⟩ := cells.1.1
    exact ⟨⟨k, by rw [next]; exact pointer, base⟩,
      by rw [curr]; exact width, by rw [used]; exact extent⟩
  · rw [drop]
    exact cells.1.2.1

/-- The final singleton iteration's nonzero huff fact comes from its actual
bit-increment execution. -/
theorem hereTop_final_single_huff {e : Env} {i : Nat} {s result : TS} {ca : Array Code}
    {after : Heap} (inv : MI e i s ca) (final : i + 1 = e.m)
    (single : e.m = 1) (one : e.mx = 1)
    (run : hereTop e.c s (e.hc ca) = .ok (result, after)) : result.huff = 1 := by
  have zero : i = 0 := by omega
  obtain ⟨max, inside, last⟩ := MI_final_entry inv final
  have maxOne : e.c.max = 1 := by
    apply UInt32.toNat_inj.mp
    rw [e.h_max]
    exact one
  have len : s.len = 1 := max.trans maxOne
  have huff : s.huff = 0 := by
    apply UInt32.toNat_inj.mp
    have value := inv.2.2.2.2.1
    rw [zero, show e.v 0 = 0 from val_zero e.h_pos, rev_zero] at value
    exact value
  exact hereTop_single_huff len max huff inside last run

end Zlib.Inftrees.Proofs
