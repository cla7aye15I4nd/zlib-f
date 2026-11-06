import ZlibF.Proof.«inffast.c.step1»

namespace Zlib.Inffast.Proofs
open C Zlib.Inffast Zlib.Inffast.Spec

/-! ### Copying bytes: the pure array functions -/

/-- `k` bytes copied from the fixed array `S` (offset `fo`) into `A` (offset `oo`), one at a time. -/
def blitN (S : Array UInt8) : Nat → Nat → Nat → Array UInt8 → Array UInt8
  | 0, _, _, A => A
  | k + 1, fo, oo, A => blitN S k (fo + 1) (oo + 1) (A.set! oo (S.getD fo 0))

/-- `k` bytes copied inside `A` from offset `fo` to offset `oo`, one at a time (the source may be written meanwhile). -/
def cpyN : Nat → Nat → Nat → Array UInt8 → Array UInt8
  | 0, _, _, A => A
  | k + 1, fo, oo, A => cpyN k (fo + 1) (oo + 1) (A.set! oo (A.getD fo 0))

theorem blitN_size (S : Array UInt8) : ∀ k fo oo A, (blitN S k fo oo A).size = A.size
  | 0, _, _, _ => rfl
  | k + 1, fo, oo, A => by simp [blitN, blitN_size S k]

theorem cpyN_size : ∀ k fo oo (A : Array UInt8), (cpyN k fo oo A).size = A.size
  | 0, _, _, _ => rfl
  | k + 1, fo, oo, A => by simp [cpyN, cpyN_size k]

theorem blitN_add (S : Array UInt8) : ∀ k1 k2 fo oo A,
    blitN S (k1 + k2) fo oo A = blitN S k2 (fo + k1) (oo + k1) (blitN S k1 fo oo A)
  | 0, k2, fo, oo, A => by simp [blitN]
  | k1 + 1, k2, fo, oo, A => by
    have := blitN_add S k1 k2 (fo + 1) (oo + 1) (A.set! oo (S.getD fo 0))
    rw [show k1 + 1 + k2 = (k1 + k2) + 1 by omega]
    simp only [blitN]
    rw [this]
    simp [Nat.add_assoc, Nat.add_comm 1 k1]

theorem cpyN_add : ∀ k1 k2 fo oo (A : Array UInt8),
    cpyN (k1 + k2) fo oo A = cpyN k2 (fo + k1) (oo + k1) (cpyN k1 fo oo A)
  | 0, k2, fo, oo, A => by simp [cpyN]
  | k1 + 1, k2, fo, oo, A => by
    have := cpyN_add k1 k2 (fo + 1) (oo + 1) (A.set! oo (A.getD fo 0))
    rw [show k1 + 1 + k2 = (k1 + k2) + 1 by omega]
    simp only [cpyN]
    rw [this]
    simp [Nat.add_assoc, Nat.add_comm 1 k1]

variable (e : Env)

/-- Writing the output block of `e.heap A` gives `e.heap A'`. -/
theorem Env.heap_put (A A' : Array UInt8) (msg m) :
    Space.put (e.heap A msg m) (BRef.blk e.ob) A' = e.heap A' msg m := by
  rw [BRef.put_blk]
  unfold Env.heap
  rw [put_bytes_comm]
  simp only [put_bytes, upd_upd]

/-- `*out++ = *from++;` on the heap `e.heap A msg m`, the source block `fb` holding `S`. -/
theorem copy1_run (A S : Array UInt8) (msg : BPtr) (m : UInt32) (l : L) (fb fo oo : Nat)
    (hf : l.from_ = .ref (BRef.blk fb) fo) (ho : l.out = .ref (BRef.blk e.ob) oo)
    (hSg : (e.heap A msg m).bytes fb = some S) (hfo : fo < S.size) (hoo : oo < A.size) :
    copy1 l (e.heap A msg m) = .ok ({ l with from_ := .ref (BRef.blk fb) (fo + 1), out := .ref (BRef.blk e.ob) (oo + 1) },
      e.heap (A.set! oo (S.getD fo 0)) msg m) := by
  have hAg : Space.get (e.heap A msg m) (BRef.blk e.ob) = some A := e.heap_bytes_ob A msg m
  have hSg' : Space.get (e.heap A msg m) (BRef.blk fb) = some S := hSg
  have hSd : S.getD fo 0 = S[fo] := by simp [Array.getD_eq_getD_getElem?, hfo]
  have hst : store8 (Ptr.ref (BRef.blk e.ob) oo) S[fo] (e.heap A msg m) =
      .ok ((), e.heap (A.set! oo S[fo]) msg m) := by
    rw [← e.heap_put A (A.set! oo S[fo]) msg m]
    exact Ptr.store_ok hAg (e.heap_ro_ob A msg m) hoo
  have hsz : (A.set! oo S[fo]).size = A.size := by simp
  have hAg2 : Space.get (e.heap (A.set! oo S[fo]) msg m) (BRef.blk e.ob) = some (A.set! oo S[fo]) :=
    e.heap_bytes_ob _ msg m
  have hadd := Ptr.add_nat_ok (h := e.heap A msg m) (r := BRef.blk fb) (a := S) (off := fo) (n := 1) hSg' (by omega)
  have hadd2 := Ptr.add_nat_ok (h := e.heap (A.set! oo S[fo]) msg m) (r := BRef.blk e.ob) (a := A.set! oo S[fo])
    (off := oo) (n := 1) hAg2 (by omega)
  unfold copy1
  rw [hf, ho, bind_ok (Ptr.load_ok hSg' hfo), bind_ok (by exact hadd), bind_ok hst,
    bind_ok (by exact hadd2), hSd]
  rfl


theorem u32_sub_one_toNat {x : UInt32} (h : 1 ≤ x.toNat) : (x - 1).toNat = x.toNat - 1 :=
  u32_toNat_sub (by simpa using h)

theorem u32_sub_one_ne {x : UInt32} (h : 2 ≤ x.toNat) : ((x - 1) != 0) = true := by
  have := u32_sub_one_toNat (x := x) (by omega)
  simp only [bne_iff_ne, ne_eq]
  intro h0
  rw [h0] at this
  simp at this
  omega

theorem u32_sub_one_eq {x : UInt32} (h : x.toNat = 1) : ((x - 1) != 0) = false := by
  have := u32_sub_one_toNat (x := x) (by omega)
  have h0 : x - 1 = 0 := by
    apply UInt32.toNat_inj.mp
    simp [this, h]
  simp [h0]

/-- `do { *out++ = *from++; } while (--op);` copying from a block `fb` other than the output block. -/
theorem copyOp_win_go (A S : Array UInt8) (msg : BPtr) (m : UInt32) (fb : Nat) (hfb : fb ≠ e.ob)
    (hSg : e.h0.bytes fb = some S) :
    ∀ n (l : L) (fo oo : Nat) (A : Array UInt8) (fu : Nat), l.op.toNat = n + 1 → n ≤ fu →
      l.from_ = .ref (BRef.blk fb) fo → l.out = .ref (BRef.blk e.ob) oo → fo + n + 1 ≤ S.size → oo + n + 1 ≤ A.size →
      cdoWhile.go copy1 (fun l => let op := l.op - 1; pure (op != 0, { l with op })) (fu + 1) l (e.heap A msg m) =
        .ok ({ l with from_ := .ref (BRef.blk fb) (fo + n + 1), out := .ref (BRef.blk e.ob) (oo + n + 1), op := 0 },
          e.heap (blitN S (n + 1) fo oo A) msg m) := by
  intro n
  induction n with
  | zero =>
    intro l fo oo A fu hop _ hf ho hfo hoo
    have hS : (e.heap A msg m).bytes fb = some S := by rw [e.heap_bytes_ne A msg m hfb]; exact hSg
    simp only [cdoWhile.go, bind_app]
    rw [copy1_run e A S msg m l fb fo oo hf ho hS (by omega) (by omega)]
    simp only [pure_app]
    have h1 : (l.op - 1 != 0) = false := u32_sub_one_eq (by omega)
    have h0 : l.op - 1 = 0 := by
      apply UInt32.toNat_inj.mp
      simp [u32_sub_one_toNat (x := l.op) (by omega), hop]
    simp [h1, h0, blitN]
  | succ n ih =>
    intro l fo oo A fu hop hfu hf ho hfo hoo
    obtain ⟨fu, rfl⟩ : ∃ fu', fu = fu' + 1 := ⟨fu - 1, by omega⟩
    have hS : (e.heap A msg m).bytes fb = some S := by rw [e.heap_bytes_ne A msg m hfb]; exact hSg
    rw [cdoWhile.go]
    simp only [bind_app]
    rw [copy1_run e A S msg m l fb fo oo hf ho hS (by omega) (by omega)]
    simp only [pure_app]
    have h1 : (l.op - 1 != 0) = true := u32_sub_one_ne (by omega)
    simp only [h1, ite_true]
    have hop1 : (l.op - 1).toNat = n + 1 := by rw [u32_sub_one_toNat (by omega)]; omega
    rw [ih { l with from_ := Ptr.ref (BRef.blk fb) (fo + 1), out := Ptr.ref (BRef.blk e.ob) (oo + 1), op := l.op - 1 }
      (fo + 1) (oo + 1) (A.set! oo (S.getD fo 0)) fu hop1 (by omega) rfl rfl (by omega) (by simp; omega)]
    have h0 : (0 : Nat) = 0 := rfl
    simp [blitN, Nat.add_assoc, Nat.add_comm 1 n]

theorem fuel_pred : fuel - 1 + 1 = fuel := by unfold fuel; omega

/-- `do { *out++ = *from++; } while (--op);` with `op = n ≥ 1`, from a block other than the output block. -/
theorem copyOp_win (S : Array UInt8) (msg : BPtr) (m : UInt32) (fb : Nat) (hfb : fb ≠ e.ob)
    (hSg : e.h0.bytes fb = some S) (A : Array UInt8) (l : L) (n fo oo : Nat) (hop : l.op.toNat = n) (hn : 1 ≤ n)
    (hf : l.from_ = .ref (BRef.blk fb) fo) (ho : l.out = .ref (BRef.blk e.ob) oo)
    (hfo : fo + n ≤ S.size) (hoo : oo + n ≤ A.size) :
    copyOp l (e.heap A msg m) = .ok ({ l with from_ := .ref (BRef.blk fb) (fo + n), out := .ref (BRef.blk e.ob) (oo + n), op := 0 },
      e.heap (blitN S n fo oo A) msg m) := by
  obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hlt := UInt32.toNat_lt l.op
  have key := copyOp_win_go e A S msg m fb hfb hSg n l fo oo A (fuel - 1) (by omega) (by unfold fuel; omega) hf ho
    (by omega) (by omega)
  rw [fuel_pred] at key
  unfold copyOp cdoWhile
  rw [key]
  simp [Nat.add_assoc]

/-- The same, copying inside the output block. -/
theorem copyOp_out_go : ∀ n (l : L) (fo oo : Nat) (A : Array UInt8) (msg : BPtr) (m : UInt32) (fu : Nat),
    l.op.toNat = n + 1 → n ≤ fu →
    l.from_ = .ref (BRef.blk e.ob) fo → l.out = .ref (BRef.blk e.ob) oo → fo + n + 1 ≤ A.size → oo + n + 1 ≤ A.size →
    cdoWhile.go copy1 (fun l => let op := l.op - 1; pure (op != 0, { l with op })) (fu + 1) l (e.heap A msg m) =
      .ok ({ l with from_ := .ref (BRef.blk e.ob) (fo + n + 1), out := .ref (BRef.blk e.ob) (oo + n + 1), op := 0 },
        e.heap (cpyN (n + 1) fo oo A) msg m) := by
  intro n
  induction n with
  | zero =>
    intro l fo oo A msg m fu hop _ hf ho hfo hoo
    have hS : (e.heap A msg m).bytes e.ob = some A := e.heap_bytes_ob A msg m
    simp only [cdoWhile.go, bind_app]
    rw [copy1_run e A A msg m l e.ob fo oo hf ho hS (by omega) (by omega)]
    simp only [pure_app]
    have h1 : (l.op - 1 != 0) = false := u32_sub_one_eq (by omega)
    have h0 : l.op - 1 = 0 := by
      apply UInt32.toNat_inj.mp
      simp [u32_sub_one_toNat (x := l.op) (by omega), hop]
    simp [h0, cpyN]
  | succ n ih =>
    intro l fo oo A msg m fu hop hfu hf ho hfo hoo
    obtain ⟨fu, rfl⟩ : ∃ fu', fu = fu' + 1 := ⟨fu - 1, by omega⟩
    have hS : (e.heap A msg m).bytes e.ob = some A := e.heap_bytes_ob A msg m
    rw [cdoWhile.go]
    simp only [bind_app]
    rw [copy1_run e A A msg m l e.ob fo oo hf ho hS (by omega) (by omega)]
    simp only [pure_app]
    have h1 : (l.op - 1 != 0) = true := u32_sub_one_ne (by omega)
    simp only [h1, ite_true]
    have hop1 : (l.op - 1).toNat = n + 1 := by rw [u32_sub_one_toNat (by omega)]; omega
    rw [ih { l with from_ := Ptr.ref (BRef.blk e.ob) (fo + 1), out := Ptr.ref (BRef.blk e.ob) (oo + 1), op := l.op - 1 }
      (fo + 1) (oo + 1) (A.set! oo (A.getD fo 0)) msg m fu hop1 (by omega) rfl rfl (by simp; omega) (by simp; omega)]
    simp [cpyN, Nat.add_assoc, Nat.add_comm 1 n]

theorem copyOp_out (A : Array UInt8) (msg : BPtr) (m : UInt32) (l : L) (n fo oo : Nat) (hop : l.op.toNat = n)
    (hn : 1 ≤ n) (hf : l.from_ = .ref (BRef.blk e.ob) fo) (ho : l.out = .ref (BRef.blk e.ob) oo)
    (hfo : fo + n ≤ A.size) (hoo : oo + n ≤ A.size) :
    copyOp l (e.heap A msg m) = .ok ({ l with from_ := .ref (BRef.blk e.ob) (fo + n), out := .ref (BRef.blk e.ob) (oo + n), op := 0 },
      e.heap (cpyN n fo oo A) msg m) := by
  obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hlt := UInt32.toNat_lt l.op
  have key := copyOp_out_go e n l fo oo A msg m (fuel - 1) (by omega) (by unfold fuel; omega) hf ho (by omega) (by omega)
  rw [fuel_pred] at key
  unfold copyOp cdoWhile
  rw [key]
  simp [Nat.add_assoc]


/-! ### The tail of a match copy, for either source -/

/-- `k` bytes copied from `sel A` (offset `fo`) into `A` (offset `oo`), one at a time; `sel` is the identity when the
source is the output block (it changes as the copy goes) and a constant when it is the window. -/
def cpyG (sel : Array UInt8 → Array UInt8) : Nat → Nat → Nat → Array UInt8 → Array UInt8
  | 0, _, _, A => A
  | k + 1, fo, oo, A => cpyG sel k (fo + 1) (oo + 1) (A.set! oo ((sel A).getD fo 0))

theorem cpyG_size (sel : Array UInt8 → Array UInt8) : ∀ k fo oo (A : Array UInt8), (cpyG sel k fo oo A).size = A.size
  | 0, _, _, _ => rfl
  | k + 1, fo, oo, A => by simp [cpyG, cpyG_size sel k]

theorem cpyG_add (sel : Array UInt8 → Array UInt8) : ∀ k1 k2 fo oo (A : Array UInt8),
    cpyG sel (k1 + k2) fo oo A = cpyG sel k2 (fo + k1) (oo + k1) (cpyG sel k1 fo oo A)
  | 0, k2, fo, oo, A => by simp [cpyG]
  | k1 + 1, k2, fo, oo, A => by
    have := cpyG_add sel k1 k2 (fo + 1) (oo + 1) (A.set! oo ((sel A).getD fo 0))
    rw [show k1 + 1 + k2 = (k1 + k2) + 1 by omega]
    simp only [cpyG]
    rw [this]
    simp [Nat.add_assoc, Nat.add_comm 1 k1]

theorem cpyG_id : ∀ k fo oo (A : Array UInt8), cpyG id k fo oo A = cpyN k fo oo A
  | 0, _, _, _ => rfl
  | k + 1, fo, oo, A => by simp [cpyG, cpyN, cpyG_id k]

theorem cpyG_const (S : Array UInt8) : ∀ k fo oo (A : Array UInt8), cpyG (fun _ => S) k fo oo A = blitN S k fo oo A
  | 0, _, _, _ => rfl
  | k + 1, fo, oo, A => by simp [cpyG, blitN, cpyG_const S k]

/-- The source block `fb` holds `sel A` while the output block holds `A`. -/
structure Src (fb : Nat) (sel : Array UInt8 → Array UInt8) : Prop where
  get : ∀ A msg m, (e.heap A msg m).bytes fb = some (sel A)
  size : ∀ (A : Array UInt8) i x, (sel (A.set! i x)).size = (sel A).size

theorem Src.out : Src e e.ob id :=
  ⟨fun A msg m => e.heap_bytes_ob A msg m, fun A i x => by simp⟩

theorem Src.win (fb : Nat) (S : Array UInt8) (hfb : fb ≠ e.ob) (hS : e.h0.bytes fb = some S) :
    Src e fb (fun _ => S) :=
  ⟨fun A msg m => by rw [e.heap_bytes_ne A msg m hfb]; exact hS, fun _ _ _ => rfl⟩

variable {e}

theorem copy1_src {fb : Nat} {sel : Array UInt8 → Array UInt8} (hs : Src e fb sel) (A : Array UInt8) (msg : BPtr)
    (m : UInt32) (l : L) (fo oo : Nat) (hf : l.from_ = .ref (BRef.blk fb) fo) (ho : l.out = .ref (BRef.blk e.ob) oo)
    (hfo : fo < (sel A).size) (hoo : oo < A.size) :
    copy1 l (e.heap A msg m) = .ok ({ l with from_ := .ref (BRef.blk fb) (fo + 1), out := .ref (BRef.blk e.ob) (oo + 1) },
      e.heap (A.set! oo ((sel A).getD fo 0)) msg m) :=
  copy1_run e A (sel A) msg m l fb fo oo hf ho (hs.get A msg m) hfo hoo

/-- `if (len) { *out++ = *from++; if (len > 1) *out++ = *from++; }` -/
def tailIf (l : L) : M L := do
  let mut l := l
  if l.len != 0 then
    l ← copy1 l
    if l.len > 1 then l ← copy1 l
  pure l

/-- The condition `len > 2`. -/
def cond3 (l : L) : M (Bool × L) := pure (l.len > 2, l)

/-- The body `*out++ = *from++;` three times and `len -= 3;`. -/
def body3 (l : L) : M L := do
  let l ← copy1 l
  let l ← copy1 l
  let l ← copy1 l
  pure { l with len := l.len - 3 }

/-- Three copies in a row (the body of the unrolled loop, without `len -= 3`). -/
theorem copy3_src {fb : Nat} {sel : Array UInt8 → Array UInt8} (hs : Src e fb sel) (A : Array UInt8) (msg : BPtr)
    (m : UInt32) (l : L) (fo oo : Nat) (hf : l.from_ = .ref (BRef.blk fb) fo) (ho : l.out = .ref (BRef.blk e.ob) oo)
    (hfo : fo + 3 ≤ (sel A).size) (hoo : oo + 3 ≤ A.size) :
    body3 l (e.heap A msg m) =
      .ok ({ l with from_ := .ref (BRef.blk fb) (fo + 3), out := .ref (BRef.blk e.ob) (oo + 3), len := l.len - 3 },
        e.heap (cpyG sel 3 fo oo A) msg m) := by
  have hsz : ∀ (B : Array UInt8) i x, (sel (B.set! i x)).size = (sel B).size := hs.size
  unfold body3
  rw [bind_ok (copy1_src hs A msg m l fo oo hf ho (by omega) (by omega))]
  rw [bind_ok (copy1_src hs (A.set! oo ((sel A).getD fo 0)) msg m _ (fo + 1) (oo + 1) rfl rfl
    (by rw [hsz]; omega) (by simp; omega))]
  rw [bind_ok (copy1_src hs (A.set! oo ((sel A).getD fo 0) |>.set! (oo + 1) ((sel (A.set! oo ((sel A).getD fo 0))).getD (fo + 1) 0))
    msg m _ (fo + 2) (oo + 2) rfl rfl (by rw [hsz, hsz]; omega) (by simp; omega))]
  simp only [pure_app, cpyG]


/-- `while (len > 2) { three copies; len -= 3; }` followed by `tailIf`. -/
def tailW (l : L) : M L := do
  let l ← cwhile cond3 body3 l
  tailIf l

/-- `do { three copies; len -= 3; } while (len > 2);` followed by `tailIf`. -/
def tailD (l : L) : M L := do
  let l ← cdoWhile body3 cond3 l
  tailIf l

theorem tailIf_run {fb : Nat} {sel : Array UInt8 → Array UInt8} (hs : Src e fb sel) (A : Array UInt8) (msg : BPtr)
    (m : UInt32) (l : L) (r fo oo : Nat) (hr : l.len.toNat = r) (hr2 : r < 3)
    (hf : l.from_ = .ref (BRef.blk fb) fo) (ho : l.out = .ref (BRef.blk e.ob) oo)
    (hfo : fo + r ≤ (sel A).size) (hoo : oo + r ≤ A.size) :
    tailIf l (e.heap A msg m) = .ok ({ l with from_ := .ref (BRef.blk fb) (fo + r), out := .ref (BRef.blk e.ob) (oo + r) },
      e.heap (cpyG sel r fo oo A) msg m) := by
  have hsz : ∀ (B : Array UInt8) i x, (sel (B.set! i x)).size = (sel B).size := hs.size
  unfold tailIf
  by_cases h0 : r = 0
  · subst h0
    have hl : l.len = 0 := by apply UInt32.toNat_inj.mp; simpa using hr
    simp only [hl, bne_self_eq_false, Bool.false_eq_true, ite_false, pure_app, cpyG, Nat.add_zero]
    rcases l with ⟨i1, o1, h1, b1, he1, op1, ln1, d1, f1, br1, al1, ad1⟩
    simp only at hf ho hl ⊢
    subst hf ho hl
    rfl
  · have hne : (l.len != 0) = true := by
      simp only [bne_iff_ne, ne_eq]
      intro h; rw [h] at hr; simp at hr; omega
    simp only [hne, ite_true]
    rw [bind_ok (copy1_src hs A msg m l fo oo hf ho (by omega) (by omega))]
    dsimp only
    by_cases h1 : r = 1
    · subst h1
      have hgt : ¬ (l.len > 1) := by
        intro h; have := (UInt32.lt_iff_toNat_lt.mp h); simp at this; omega
      simp only [hgt, ite_false, pure_app, cpyG]
    · have h2 : r = 2 := by omega
      subst h2
      have hgt : (l.len > 1) := by
        apply UInt32.lt_iff_toNat_lt.mpr; simp; omega
      simp only [hgt, ite_true]
      rw [bind_ok (copy1_src hs (A.set! oo ((sel A).getD fo 0)) msg m _ (fo + 1) (oo + 1) rfl rfl
        (by rw [hsz]; omega) (by simp; omega))]
      simp only [pure_app, cpyG]


theorem len_gt2_iff (x : UInt32) : decide (x > 2) = decide (2 < x.toNat) := by
  by_cases h : x > 2
  · have := UInt32.lt_iff_toNat_lt.mp h; simp at this; simp [h]; omega
  · have : ¬ (2 < x.toNat) := fun h2 => h (UInt32.lt_iff_toNat_lt.mpr (by simpa using h2))
    simp [h, this]

theorem len_sub3 {x : UInt32} (h : 3 ≤ x.toNat) : (x - 3).toNat = x.toNat - 3 :=
  u32_toNat_sub (by simpa using h)

theorem Src.sel_cpyG {fb : Nat} {sel : Array UInt8 → Array UInt8} (hs : Src e fb sel) :
    ∀ k fo oo (A : Array UInt8), (sel (cpyG sel k fo oo A)).size = (sel A).size
  | 0, _, _, _ => rfl
  | k + 1, fo, oo, A => by
    simp only [cpyG]
    rw [Src.sel_cpyG hs k, hs.size]

theorem cond3_true {l : L} (h : 3 ≤ l.len.toNat) (hp : Heap) : cond3 l hp = .ok ((true, l), hp) := by
  have hd : decide (l.len > 2) = true := by rw [len_gt2_iff]; simp; omega
  simp [cond3, hd]

theorem cond3_false {l : L} (h : l.len.toNat ≤ 2) (hp : Heap) : cond3 l hp = .ok ((false, l), hp) := by
  have hd : decide (l.len > 2) = false := by rw [len_gt2_iff]; simp; omega
  simp [cond3, hd]

theorem whileTail_go {fb : Nat} {sel : Array UInt8 → Array UInt8} (hs : Src e fb sel) (msg : BPtr) (m : UInt32) :
    ∀ q (l : L) fo oo (A : Array UInt8) fu r, r < 3 → l.len.toNat = 3 * q + r → q ≤ fu →
      l.from_ = .ref (BRef.blk fb) fo → l.out = .ref (BRef.blk e.ob) oo →
      fo + 3 * q ≤ (sel A).size → oo + 3 * q ≤ A.size →
      cwhile.go cond3 body3 (fu + 1) l (e.heap A msg m) =
        .ok ({ l with from_ := .ref (BRef.blk fb) (fo + 3 * q), out := .ref (BRef.blk e.ob) (oo + 3 * q),
                      len := UInt32.ofNat r }, e.heap (cpyG sel (3 * q) fo oo A) msg m) := by
  intro q
  induction q with
  | zero =>
    intro l fo oo A fu r hr hl _ hf ho _ _
    rw [cwhile.go, bind_ok (cond3_false (by omega) _)]
    simp only [Bool.false_eq_true, ite_false, pure_app, cpyG, Nat.mul_zero, Nat.add_zero]
    have hlen : l.len = UInt32.ofNat r := by
      apply UInt32.toNat_inj.mp; simp [UInt32.toNat_ofNat, Nat.mod_eq_of_lt (show r < 2 ^ 32 by omega)]; omega
    rcases l with ⟨i1, o1, h1, b1, he1, op1, ln1, d1, f1, br1, al1, ad1⟩
    simp only at hf ho hlen ⊢
    subst hf ho hlen
    rfl
  | succ q ih =>
    intro l fo oo A fu r hr hl hfu hf ho hfo hoo
    obtain ⟨fu, rfl⟩ : ∃ fu', fu = fu' + 1 := ⟨fu - 1, by omega⟩
    rw [cwhile.go, bind_ok (cond3_true (by omega) _)]
    simp only [ite_true]
    rw [bind_ok (copy3_src hs A msg m l fo oo hf ho (by omega) (by omega))]
    have hl3 : (l.len - 3).toNat = 3 * q + r := by rw [len_sub3 (by omega)]; omega
    rw [ih { l with from_ := Ptr.ref (BRef.blk fb) (fo + 3), out := Ptr.ref (BRef.blk e.ob) (oo + 3), len := l.len - 3 }
      (fo + 3) (oo + 3) (cpyG sel 3 fo oo A) fu r hr hl3 (by omega) rfl rfl
      (by rw [hs.sel_cpyG]; omega) (by rw [cpyG_size]; omega)]
    have e1 : fo + 3 + 3 * q = fo + 3 * (q + 1) := by omega
    have e2 : oo + 3 + 3 * q = oo + 3 * (q + 1) := by omega
    have e3 : cpyG sel (3 * q) (fo + 3) (oo + 3) (cpyG sel 3 fo oo A) = cpyG sel (3 * (q + 1)) fo oo A := by
      rw [show 3 * (q + 1) = 3 + 3 * q by omega, cpyG_add]
    rw [e1, e2, e3]


theorem tailW_run {fb : Nat} {sel : Array UInt8 → Array UInt8} (hs : Src e fb sel) (A : Array UInt8) (msg : BPtr)
    (m : UInt32) (l : L) (n fo oo : Nat) (hn : l.len.toNat = n) (hf : l.from_ = .ref (BRef.blk fb) fo)
    (ho : l.out = .ref (BRef.blk e.ob) oo) (hfo : fo + n ≤ (sel A).size) (hoo : oo + n ≤ A.size) :
    tailW l (e.heap A msg m) = .ok ({ l with from_ := .ref (BRef.blk fb) (fo + n), out := .ref (BRef.blk e.ob) (oo + n), len := UInt32.ofNat (n % 3) }, e.heap (cpyG sel n fo oo A) msg m) := by
  have hlt := UInt32.toNat_lt l.len
  have key := whileTail_go hs msg m (n / 3) l fo oo A (fuel - 1) (n % 3) (by omega) (by omega) (by unfold fuel; omega)
    hf ho (by omega) (by omega)
  rw [fuel_pred] at key
  unfold tailW cwhile
  rw [bind_ok key]
  have hr : (UInt32.ofNat (n % 3)).toNat = n % 3 := by simp [UInt32.toNat_ofNat]; omega
  have hn3 : n = 3 * (n / 3) + n % 3 := by omega
  rw [tailIf_run hs (cpyG sel (3 * (n / 3)) fo oo A) msg m _ (n % 3) (fo + 3 * (n / 3)) (oo + 3 * (n / 3)) hr
    (by omega) rfl rfl (by rw [hs.sel_cpyG]; omega) (by rw [cpyG_size]; omega)]
  have e1 : fo + 3 * (n / 3) + n % 3 = fo + n := by omega
  have e2 : oo + 3 * (n / 3) + n % 3 = oo + n := by omega
  have e3 : cpyG sel (n % 3) (fo + 3 * (n / 3)) (oo + 3 * (n / 3)) (cpyG sel (3 * (n / 3)) fo oo A) = cpyG sel n fo oo A := by
    conv => rhs; rw [hn3, cpyG_add]
  rw [e1, e2, e3]

theorem doTail_go {fb : Nat} {sel : Array UInt8 → Array UInt8} (hs : Src e fb sel) (msg : BPtr) (m : UInt32) :
    ∀ q (l : L) fo oo (A : Array UInt8) fu r, r < 3 → l.len.toNat = 3 * (q + 1) + r → q ≤ fu →
      l.from_ = .ref (BRef.blk fb) fo → l.out = .ref (BRef.blk e.ob) oo →
      fo + 3 * (q + 1) ≤ (sel A).size → oo + 3 * (q + 1) ≤ A.size →
      cdoWhile.go body3 cond3 (fu + 1) l (e.heap A msg m) =
        .ok ({ l with from_ := .ref (BRef.blk fb) (fo + 3 * (q + 1)), out := .ref (BRef.blk e.ob) (oo + 3 * (q + 1)), len := UInt32.ofNat r }, e.heap (cpyG sel (3 * (q + 1)) fo oo A) msg m) := by
  intro q
  induction q with
  | zero =>
    intro l fo oo A fu r hr hl _ hf ho hfo hoo
    rw [cdoWhile.go, bind_ok (copy3_src hs A msg m l fo oo hf ho (by omega) (by omega))]
    have hl3 : (l.len - 3).toNat = r := by rw [len_sub3 (by omega)]; omega
    rw [bind_ok (cond3_false (l := { l with from_ := Ptr.ref (BRef.blk fb) (fo + 3), out := Ptr.ref (BRef.blk e.ob) (oo + 3), len := l.len - 3 }) (by simp; omega) _)]
    simp only [Bool.false_eq_true, ite_false, pure_app, cpyG]
    have hlen : l.len - 3 = UInt32.ofNat r := by
      apply UInt32.toNat_inj.mp; simp [UInt32.toNat_ofNat, Nat.mod_eq_of_lt (show r < 2 ^ 32 by omega)]; omega
    simp [hlen]
  | succ q ih =>
    intro l fo oo A fu r hr hl hfu hf ho hfo hoo
    obtain ⟨fu, rfl⟩ : ∃ fu', fu = fu' + 1 := ⟨fu - 1, by omega⟩
    rw [cdoWhile.go, bind_ok (copy3_src hs A msg m l fo oo hf ho (by omega) (by omega))]
    have hl3 : (l.len - 3).toNat = 3 * (q + 1) + r := by rw [len_sub3 (by omega)]; omega
    rw [bind_ok (cond3_true (l := { l with from_ := Ptr.ref (BRef.blk fb) (fo + 3), out := Ptr.ref (BRef.blk e.ob) (oo + 3), len := l.len - 3 }) (by simp; omega) _)]
    simp only [ite_true]
    rw [ih { l with from_ := Ptr.ref (BRef.blk fb) (fo + 3), out := Ptr.ref (BRef.blk e.ob) (oo + 3), len := l.len - 3 }
      (fo + 3) (oo + 3) (cpyG sel 3 fo oo A) fu r hr hl3 (by omega) rfl rfl
      (by rw [hs.sel_cpyG]; omega) (by rw [cpyG_size]; omega)]
    have e1 : fo + 3 + 3 * (q + 1) = fo + 3 * (q + 1 + 1) := by omega
    have e2 : oo + 3 + 3 * (q + 1) = oo + 3 * (q + 1 + 1) := by omega
    have e3 : cpyG sel (3 * (q + 1)) (fo + 3) (oo + 3) (cpyG sel 3 fo oo A) = cpyG sel (3 * (q + 1 + 1)) fo oo A := by
      rw [show 3 * (q + 1 + 1) = 3 + 3 * (q + 1) by omega, cpyG_add]
    rw [e1, e2, e3]

theorem tailD_run {fb : Nat} {sel : Array UInt8 → Array UInt8} (hs : Src e fb sel) (A : Array UInt8) (msg : BPtr)
    (m : UInt32) (l : L) (n fo oo : Nat) (hn : l.len.toNat = n) (h3 : 3 ≤ n) (hf : l.from_ = .ref (BRef.blk fb) fo)
    (ho : l.out = .ref (BRef.blk e.ob) oo) (hfo : fo + n ≤ (sel A).size) (hoo : oo + n ≤ A.size) :
    tailD l (e.heap A msg m) = .ok ({ l with from_ := .ref (BRef.blk fb) (fo + n), out := .ref (BRef.blk e.ob) (oo + n), len := UInt32.ofNat (n % 3) }, e.heap (cpyG sel n fo oo A) msg m) := by
  have hlt := UInt32.toNat_lt l.len
  obtain ⟨q, hq⟩ : ∃ q, n / 3 = q + 1 := ⟨n / 3 - 1, by omega⟩
  have key := doTail_go hs msg m q l fo oo A (fuel - 1) (n % 3) (by omega) (by omega) (by unfold fuel; omega)
    hf ho (by omega) (by omega)
  rw [fuel_pred] at key
  unfold tailD cdoWhile
  rw [bind_ok key]
  have hr : (UInt32.ofNat (n % 3)).toNat = n % 3 := by simp [UInt32.toNat_ofNat]; omega
  have hn3 : n = 3 * (q + 1) + n % 3 := by omega
  rw [tailIf_run hs (cpyG sel (3 * (q + 1)) fo oo A) msg m _ (n % 3) (fo + 3 * (q + 1)) (oo + 3 * (q + 1)) hr
    (by omega) rfl rfl (by rw [hs.sel_cpyG]; omega) (by rw [cpyG_size]; omega)]
  have e1 : fo + 3 * (q + 1) + n % 3 = fo + n := by omega
  have e2 : oo + 3 * (q + 1) + n % 3 = oo + n := by omega
  have e3 : cpyG sel (n % 3) (fo + 3 * (q + 1)) (oo + 3 * (q + 1)) (cpyG sel (3 * (q + 1)) fo oo A) = cpyG sel n fo oo A := by
    conv => rhs; rw [hn3, cpyG_add]
  rw [e1, e2, e3]

end Zlib.Inffast.Proofs
