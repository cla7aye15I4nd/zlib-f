import ZlibF.Proof.«trees.c.heap.pq»
import ZlibF.Proof.«trees.c.heap.gbtree»

/-!
# trees.c: `gen_bitlen` cut into its loops

`gbTop` is `gen_bitlen` with each loop body named, so that every loop has a statement of its own
(`gen_bitlen_eq : gen_bitlen = gbTop` by `rfl`: the text is the same).
-/

namespace Zlib.Trees.Proofs
open C Zlib.Trees

/-- `for (bits = 0; bits <= MAX_BITS; bits++) s->bl_count[bits] = 0;` -/
def gbZero (s : DeflateStatePtr) : M Int32 :=
  cfor (σ := Int32) (fun b => pure (decide (b.toInt ≤ MAX_BITS.toInt))) (fun b => iadd b 1)
    (fun b => do setAt (← pBlCount s) b.toInt 0; pure b) 0

/-- The cost added for a leaf `n` whose `Len` is `bits` and whose extra bits are `xbits`. -/
def gbTail2 (s : DeflateStatePtr) (tree stree : CtDataPtr) (h n bits ov xbits : Int32) : M (Int32 × Int32) := do
  let f ← getFc tree n.toInt
  let t ← iadd bits xbits
  md s fun d => { d with opt_len := d.opt_len + f.toUInt64 * (i2u t).toUInt64 }
  if stree != .null then
    let t2 ← iadd (u16i (← getDl stree n.toInt)) xbits
    md s fun d => { d with static_len := d.static_len + f.toUInt64 * (i2u t2).toUInt64 }
  return (h, ov)

/-- The part of the first-pass body after `Len` is stored: count the leaf and add its cost. -/
def gbTail1 (s : DeflateStatePtr) (tree stree : CtDataPtr) (extra : IPtr) (max_code base : Int32)
    (h n bits ov : Int32) : M (Int32 × Int32) := do
  if n.toInt > max_code.toInt then return (h, ov)
  let bc ← pBlCount s
  setAt bc bits.toInt ((← Ptr.index bc bits.toInt) + 1)
  if n.toInt ≥ base.toInt then
    let x ← Ptr.index extra (← isub n base).toInt
    gbTail2 s tree stree h n bits ov x
  else gbTail2 s tree stree h n bits ov 0

/-- The body of the first pass, `h` and `overflow` carried. -/
def gbBody1 (s : DeflateStatePtr) (tree stree : CtDataPtr) (extra : IPtr) (max_code base max_length : Int32) :
    Int32 × Int32 → M (Int32 × Int32) :=
  fun (h, overflow) => do
    let n ← heapAt s h
    let bits ← iadd (u16i (← getDl tree (u16i (← getDl tree n.toInt)).toInt)) 1
    if bits.toInt > max_length.toInt then
      let ov ← iadd overflow 1
      setDl tree n.toInt (i2us max_length)
      gbTail1 s tree stree extra max_code base h n max_length ov
    else
      setDl tree n.toInt (i2us bits)
      gbTail1 s tree stree extra max_code base h n bits overflow

def gbCond1 : Int32 × Int32 → M Bool := fun (h, _) => pure (decide (h.toInt < HEAP_SIZE.toInt))

/-- The first pass. -/
def gbPass1 (s : DeflateStatePtr) (tree stree : CtDataPtr) (extra : IPtr) (max_code base max_length : Int32)
    (h0 : Int32) : M (Int32 × Int32) :=
  cfor (σ := Int32 × Int32) gbCond1 (fun (h, o) => do pure (← iadd h 1, o))
    (gbBody1 s tree stree extra max_code base max_length) (h0, 0)

/-- One round of the repair: `do { ... } while (overflow > 0)` body. -/
def gbFix (s : DeflateStatePtr) (max_length : Int32) : Int32 → M Int32 :=
  fun overflow => do
    let bits ← isub max_length 1
    let bc ← pBlCount s
    let bits ← cwhile (σ := Int32)
      (fun b => do pure (decide ((← Ptr.index bc b.toInt) == 0), b))
      (fun b => isub b 1) bits
    setAt bc bits.toInt ((← Ptr.index bc bits.toInt) - 1)
    let b1 ← iadd bits 1
    setAt bc b1.toInt ((← Ptr.index bc b1.toInt) + 2)
    setAt bc max_length.toInt ((← Ptr.index bc max_length.toInt) - 1)
    isub overflow 2

/-- The inner loop of the reassignment: `n` leaves of length `bits` are taken from the heap, going down. -/
def gbInner (s : DeflateStatePtr) (tree : CtDataPtr) (max_code bits : Int32) : Int32 × Int32 → M (Int32 × Int32) :=
  fun (n, h) => do
    let h ← isub h 1
    let m ← heapAt s h
    if m.toInt > max_code.toInt then return (n, h)
    let lm ← getDl tree m.toInt
    if lm.toUInt32 != i2u bits then
      let fm ← getFc tree m.toInt
      md s fun d => { d with opt_len := d.opt_len + (i2ul bits - lm.toUInt64) * fm.toUInt64 }
      setDl tree m.toInt (i2us bits)
    pure (← isub n 1, h)

/-- The outer loop body of the reassignment. -/
def gbOuter (s : DeflateStatePtr) (tree : CtDataPtr) (max_code : Int32) : Int32 × Int32 → M (Int32 × Int32) :=
  fun (bits, h) => do
    let n0 := u16i (← Ptr.index (← pBlCount s) bits.toInt)
    let (_, h) ← cwhile (σ := Int32 × Int32)
      (fun (n, h) => pure (n != 0, (n, h)))
      (gbInner s tree max_code bits) (n0, h)
    pure (bits, h)

def gbTop (s : DeflateStatePtr) (desc : TreeDescPtr) : M Unit := do
  let dd ← ldTreeDesc desc
  let tree := dd.dyn_tree
  let max_code := dd.max_code
  let sd ← ldStaticTreeDesc dd.stat_desc
  let stree := sd.static_tree
  let extra := sd.extra_bits
  let base := sd.extra_base
  let max_length := sd.max_length
  let _ ← gbZero s
  setDl tree (← heapAt s (← rd s).heap_max).toInt 0
  let h0 ← iadd (← rd s).heap_max 1
  let (h, overflow) ← gbPass1 s tree stree extra max_code base max_length h0
  if overflow == 0 then return
  let _ ← cdoWhile (σ := Int32) (gbFix s max_length)
    (fun overflow => pure (decide (overflow.toInt > 0), overflow)) overflow
  let _ ← cfor (σ := Int32 × Int32)
    (fun (bits, _) => pure (bits != 0))
    (fun (bits, h) => do pure (← isub bits 1, h))
    (gbOuter s tree max_code)
    (max_length, h)

theorem gen_bitlen_eq (s : DeflateStatePtr) (desc : TreeDescPtr) : gen_bitlen s desc = gbTop s desc := rfl


/-! ### The loop `cfor` as a `cwhile` rule -/

theorem WS.cfor2 {h0 : Heap} {id : Nat} {σ : Type} {cond : σ → M Bool} {step : σ → M σ} {body : σ → M σ}
    (Inv : σ → DeflateState → Prop) (μ : σ → DeflateState → Nat) (Q : σ → DeflateState → Prop)
    (hstep : ∀ s d, Inv s d → WS h0 id (cond s) d (fun c d1 =>
      (c = false ∧ Q s d1) ∨
      (c = true ∧ WS h0 id (do step (← body s)) d1 (fun s2 d2 => Inv s2 d2 ∧ μ s2 d2 < μ s d))))
    {s : σ} {d : DeflateState} (hI : Inv s d) (hfuel : μ s d < fuel) :
    WS h0 id (cfor cond step body s) d (fun s' d' => Q s' d') := by
  unfold cfor
  refine WS.cwhile2 Inv μ Q ?_ hI hfuel
  intro s d hI
  have := hstep s d hI
  refine WS.bind' this fun c d1 hq => ?_
  rcases hq with ⟨hc, hq⟩ | ⟨hc, hq⟩
  · subst hc; exact WS.pure' (Or.inl ⟨rfl, hq⟩)
  · subst hc; exact WS.pure' (Or.inr ⟨rfl, hq⟩)

theorem ws_gbZero {h0 : Heap} {id : Nat} (d : DeflateState) (hsz : d.bl_count.size = 16) :
    WS h0 id (gbZero (Sp id)) d (fun _ d' => ∃ B : Array UInt16, d' = { d with bl_count := B } ∧ B.size = 16 ∧
      ∀ i, i < 16 → B[i]! = 0) := by
  unfold gbZero
  let Inv : Int32 → DeflateState → Prop := fun b e => ∃ (k : Nat) (B : Array UInt16), b.toInt = k ∧ k ≤ 16 ∧
    e = { d with bl_count := B } ∧ B.size = 16 ∧ ∀ i, i < 16 → B[i]! = if i < k then 0 else d.bl_count[i]!
  refine WS.cfor2 (id := id) Inv (fun b _ => 16 - b.toInt.toNat) (fun b e => ∃ B : Array UInt16, e = { d with bl_count := B } ∧
    B.size = 16 ∧ ∀ i, i < 16 → B[i]! = 0) ?_ ⟨0, d.bl_count, rfl, by omega, rfl, hsz, by intro i hi; simp⟩
    (by simp only [fuel]; omega)
  rintro b e ⟨k, B, hb, hk, rfl, hB, hv⟩
  refine WS.pure' ?_
  by_cases hlt : k ≤ 15
  · refine Or.inr ⟨?_, ?_⟩
    · have : MAX_BITS.toInt = 15 := rfl
      simp only [decide_eq_true_eq]; omega
    · have h1i : (1 : Int32).toInt = 1 := rfl
      have hb0 : 0 ≤ b.toInt := by omega
      have inner : WS h0 id (do setAt (← pBlCount (Sp id)) b.toInt 0; pure b) { d with bl_count := B }
          (fun b' e => b' = b ∧ e = { d with bl_count := B.set! k 0 }) := by
        refine WS.bind' ws_pBlCount fun p e1 ⟨hp, he1⟩ => ?_
        subst e1; subst hp
        refine WS.bind' (ws_setAt_blc b.toInt 0 hb0 (by show b.toInt < (B.size : Int); omega)) fun _ e3 he3 => ?_
        subst he3
        refine WS.pure' ⟨rfl, ?_⟩
        have : b.toInt.toNat = k := by omega
        simp only [this]
      show WS h0 id (do let b' ← (do setAt (← pBlCount (Sp id)) b.toInt 0; pure b); iadd b' 1) _ _
      refine WS.bind' inner fun b' e1 ⟨hb', he1⟩ => ?_
      subst b'; subst he1
      refine WS.mono (ws_iadd b (1 : Int32) (by have : (1 : Int32).toInt = 1 := rfl; omega)
        (by have : (1 : Int32).toInt = 1 := rfl; omega)) ?_
      intro b2 e2 ⟨hb2, he2⟩
      subst he2
      have h1i : (1 : Int32).toInt = 1 := rfl
      refine ⟨⟨k + 1, B.set! k 0, by omega, by omega, rfl, by rw [size_set!]; exact hB, ?_⟩, ?_⟩
      · intro i hi
        rw [getD_set B k i 0 (by omega), hv i hi]
        by_cases e : i = k
        · subst e; simp
        · simp only [e, ite_false]; by_cases e2 : i < k <;> simp [e2] <;> omega
      · show 16 - b2.toInt.toNat < 16 - b.toInt.toNat
        omega
  · refine Or.inl ⟨?_, ?_⟩
    · have : MAX_BITS.toInt = 15 := rfl
      simp only [decide_eq_false_iff_not]; omega
    · refine ⟨B, rfl, hB, fun i hi => ?_⟩
      rw [hv i hi]; simp; omega
end Zlib.Trees.Proofs
