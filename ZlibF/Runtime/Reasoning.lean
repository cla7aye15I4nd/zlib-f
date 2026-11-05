import ZlibF.Runtime.Core

/-!
# Reasoning rules for the C runtime

`OkOn h m x`: running `m` on heap `h` returns `x` and leaves the heap
unchanged. This covers read-only code such as checksums. Loop rules take an
invariant indexed by the exact number of remaining iterations, so the same
argument proves termination within `fuel` and the loop result.
-/

namespace C

def OkOn {α} (h : Heap) (m : CM α) (x : α) : Prop := m.run h = .ok (x, h)

@[simp] theorem except_ok_bind {ε α β} (x : α) (f : α → Except ε β) :
    (Except.ok x >>= f) = f x := rfl

theorem OkOn.pure {α} (h : Heap) (x : α) : OkOn h (Pure.pure x : CM α) x := rfl

theorem OkOn.bind {α β} {h : Heap} {m : CM α} {f : α → CM β} {x : α} {y : β}
    (hm : OkOn h m x) (hf : OkOn h (f x) y) : OkOn h (m >>= f) y := by
  unfold OkOn at *
  simp only [StateT.run_bind, hm]
  exact hf

theorem OkOn.bind_ex {α β} {h : Heap} {m : CM α} {f : α → CM β} {R : α → Prop} {T : β → Prop}
    (hm : ∃ x, OkOn h m x ∧ R x) (hf : ∀ x, R x → ∃ y, OkOn h (f x) y ∧ T y) :
    ∃ y, OkOn h (m >>= f) y ∧ T y := by
  obtain ⟨x, hx, hR⟩ := hm
  obtain ⟨y, hy, hT⟩ := hf x hR
  exact ⟨y, OkOn.bind hx hy, hT⟩

theorem OkOn.bind_ex_pure {α} {h : Heap} {m : CM α} {x : α} (hm : OkOn h m x) :
    ∃ y, OkOn h m y ∧ y = x := ⟨x, hm, rfl⟩

/-- `while` rule. `P k s`: exactly `k` more iterations remain from state `s`. -/
theorem cwhile_go_ok {σ} {h : Heap} {cond : σ → CM (Bool × σ)} {body : σ → CM σ}
    (P : Nat → σ → Prop) (Q : σ → Prop)
    (hstep : ∀ k s, P (k + 1) s → ∃ s1 s2, OkOn h (cond s) (true, s1) ∧ OkOn h (body s1) s2 ∧ P k s2)
    (hstop : ∀ s, P 0 s → ∃ s1, OkOn h (cond s) (false, s1) ∧ Q s1) :
    ∀ k n s, P k s → k < n → ∃ s', OkOn h (cwhile.go cond body n s) s' ∧ Q s' := by
  intro k
  induction k with
  | zero =>
    intro n s hP hn
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    obtain ⟨s1, hc, hQ⟩ := hstop s hP
    refine ⟨s1, ?_, hQ⟩
    unfold OkOn at *
    simp [cwhile.go, StateT.run_bind, hc]
    rfl
  | succ k ih =>
    intro n s hP hn
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    obtain ⟨s1, s2, hc, hb, hP2⟩ := hstep k s hP
    obtain ⟨s', hgo, hQ⟩ := ih n s2 hP2 (by omega)
    refine ⟨s', ?_, hQ⟩
    unfold OkOn at *
    simp [cwhile.go, StateT.run_bind, hc, hb, hgo]

theorem cwhile_ok {σ} {h : Heap} {cond : σ → CM (Bool × σ)} {body : σ → CM σ}
    (P : Nat → σ → Prop) (Q : σ → Prop)
    (hstep : ∀ k s, P (k + 1) s → ∃ s1 s2, OkOn h (cond s) (true, s1) ∧ OkOn h (body s1) s2 ∧ P k s2)
    (hstop : ∀ s, P 0 s → ∃ s1, OkOn h (cond s) (false, s1) ∧ Q s1)
    {k : Nat} {s : σ} (hP : P k s) (hk : k < fuel) :
    ∃ s', OkOn h (cwhile cond body s) s' ∧ Q s' :=
  cwhile_go_ok P Q hstep hstop k fuel s hP hk

/-- `do ... while` rule. `P k s`: the body runs exactly `k + 1` more times. -/
theorem cdoWhile_go_ok {σ} {h : Heap} {body : σ → CM σ} {cond : σ → CM (Bool × σ)}
    (P : Nat → σ → Prop) (Q : σ → Prop)
    (hstep : ∀ k s, P (k + 1) s → ∃ s1 s2, OkOn h (body s) s1 ∧ OkOn h (cond s1) (true, s2) ∧ P k s2)
    (hlast : ∀ s, P 0 s → ∃ s1 s2, OkOn h (body s) s1 ∧ OkOn h (cond s1) (false, s2) ∧ Q s2) :
    ∀ k n s, P k s → k < n → ∃ s', OkOn h (cdoWhile.go body cond n s) s' ∧ Q s' := by
  intro k
  induction k with
  | zero =>
    intro n s hP hn
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    obtain ⟨s1, s2, hb, hc, hQ⟩ := hlast s hP
    refine ⟨s2, ?_, hQ⟩
    unfold OkOn at *
    simp [cdoWhile.go, StateT.run_bind, hb, hc]
    rfl
  | succ k ih =>
    intro n s hP hn
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    obtain ⟨s1, s2, hb, hc, hP2⟩ := hstep k s hP
    obtain ⟨s', hgo, hQ⟩ := ih n s2 hP2 (by omega)
    refine ⟨s', ?_, hQ⟩
    unfold OkOn at *
    simp [cdoWhile.go, StateT.run_bind, hb, hc, hgo]

theorem cdoWhile_ok {σ} {h : Heap} {body : σ → CM σ} {cond : σ → CM (Bool × σ)}
    (P : Nat → σ → Prop) (Q : σ → Prop)
    (hstep : ∀ k s, P (k + 1) s → ∃ s1 s2, OkOn h (body s) s1 ∧ OkOn h (cond s1) (true, s2) ∧ P k s2)
    (hlast : ∀ s, P 0 s → ∃ s1 s2, OkOn h (body s) s1 ∧ OkOn h (cond s1) (false, s2) ∧ Q s2)
    {k : Nat} {s : σ} (hP : P k s) (hk : k < fuel) :
    ∃ s', OkOn h (cdoWhile body cond s) s' ∧ Q s' :=
  cdoWhile_go_ok P Q hstep hstop k fuel s hP hk
where hstop := hlast

/-! Memory access rules. -/

theorem Ptr.add_ok {h : Heap} {blk : Nat} {bytes : ByteArray} {off k : Int}
    (hb : h.blocks[blk]? = some (some bytes)) (h0 : 0 ≤ off + k) (h1 : off + k ≤ bytes.size) :
    OkOn h ((Ptr.ref blk off).add k) (.ref blk (off + k)) := by
  unfold OkOn
  simp [Ptr.add, blockSize, StateT.run_bind, hb, h0, h1]
  rfl

theorem load8_ok {h : Heap} {blk : Nat} {bytes : ByteArray} {off : Nat}
    (hb : h.blocks[blk]? = some (some bytes)) (hlt : off < bytes.size) :
    OkOn h (load8 (.ref blk off)) bytes[off] := by
  unfold OkOn
  simp [load8, StateT.run_bind, hb, hlt]
  rfl

theorem index8_ok {h : Heap} {blk : Nat} {bytes : ByteArray} {off i : Nat}
    (hb : h.blocks[blk]? = some (some bytes)) (hlt : off + i < bytes.size) :
    OkOn h (index8 (.ref blk off) i) bytes[off + i] := by
  unfold index8
  refine OkOn.bind (Ptr.add_ok hb (by omega) (by omega)) ?_
  have : ((off : Int) + (i : Int)) = ((off + i : Nat) : Int) := by omega
  rw [this]
  exact load8_ok hb hlt

end C
