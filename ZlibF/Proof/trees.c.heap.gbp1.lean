import ZlibF.Proof.«trees.c.heap.gbdef»
import ZlibF.Proof.«trees.c.heap.gbclk»

/-!
# trees.c: `gen_bitlen`, the first pass

The loop `for (h = heap_max + 1; h < HEAP_SIZE; h++)` stores in `tree[n].Len` the depth of each node clamped to
`max_length`, counts the leaves into `bl_count`, counts the clamped nodes in `overflow`, and adds each leaf's
cost to `opt_len` and `static_len`. The invariant and the clamped depths `clK` are those of the earlier attempt
(`GenBitlenPass1.lean`, `GenBitlenBase.lean`).
-/

namespace Zlib.Trees.Proofs
open C Zlib.Trees

theorem i2u_u64 (t : Int32) (h : 0 ≤ t.toInt) : (i2u t).toUInt64 = UInt64.ofNat t.toInt.toNat := by
  have h2 : t.toInt < 2147483648 := by
    have := t.toInt_le
    have e : Int32.maxValue.toInt = 2147483647 := by decide
    omega
  apply UInt64.toNat_inj.mp
  unfold i2u
  rw [UInt32.toNat_toUInt64, UInt32.toNat_ofNat', UInt64.toNat_ofNat']
  omega

theorem u16_u64 (f : UInt16) : f.toUInt64 = UInt64.ofNat f.toNat := by
  apply UInt64.toNat_inj.mp
  rw [UInt16.toNat_toUInt64, UInt64.toNat_ofNat']
  have := f.toNat_lt
  omega

theorem u16i_toInt (x : UInt16) : (u16i x).toInt = x.toNat := by
  unfold u16i
  have := x.toNat_lt
  rw [Int32.toInt_ofInt]
  have : Int32.size = 4294967296 := rfl
  rw [this, Int.bmod_eq_of_le] <;> omega

/-- `s0` with `c` added, when there is a static tree. -/
def addOpt (s0 : UInt64) : Option Nat → UInt64
  | none => s0
  | some c => s0 + UInt64.ofNat c

/-- The record after the cost of a leaf with `fv` occurrences is added. -/
def costAdd (e : DeflateState) (fv bits xbv : Nat) (slv : Option Nat) : DeflateState :=
  { e with opt_len := e.opt_len + UInt64.ofNat (fv * (bits + xbv)),
           static_len := addOpt e.static_len (slv.map fun l => fv * (l + xbv)) }


theorem opt_add (o : UInt64) (f : UInt16) (t : Int32) (ht : 0 ≤ t.toInt) (b x : Nat) (hb : t.toInt.toNat = b + x) :
    o + f.toUInt64 * (i2u t).toUInt64 = o + UInt64.ofNat (f.toNat * (b + x)) := by
  rw [u16_u64, i2u_u64 t ht, hb, UInt64.ofNat_mul]

theorem ws_gbTail2_null {h0 : Heap} {id : Nat} (tk : TK) (e : DeflateState) (h n bits ov xbits : Int32)
    (hn : 0 ≤ n.toInt ∧ n.toInt < (tk.arr e).size) (hb : 0 ≤ bits.toInt ∧ bits.toInt ≤ 15)
    (hx : 0 ≤ xbits.toInt ∧ xbits.toInt ≤ 1000) :
    WS h0 id (gbTail2 (Sp id) (Ptr.ref (tk.ref id) 0) Ptr.null h n bits ov xbits) e (fun r e' =>
      r = (h, ov) ∧ e' = costAdd e ((tk.arr e)[n.toInt.toNat]!).fc.toNat bits.toInt.toNat xbits.toInt.toNat none) := by
  unfold gbTail2
  refine WS.bind' (ws_getFc tk n.toInt hn.1 hn.2) fun f e1 ⟨hf, he1⟩ => ?_
  subst e1; subst hf
  refine WS.bind' (ws_iadd bits xbits (by omega) (by omega)) fun t e1 ⟨ht, he1⟩ => ?_
  subst e1
  refine WS.bind' (ws_md _) fun _ e1 he1 => ?_
  subst he1
  simp only [bne_self_eq_false, Bool.false_eq_true, ite_false]
  refine WS.pure' ⟨rfl, ?_⟩
  unfold costAdd
  rw [opt_add _ _ t (by omega) bits.toInt.toNat xbits.toInt.toNat (by omega)]
  rfl

theorem ws_gbTail2_ref {h0 : Heap} {id : Nat} (tk : TK) (e : DeflateState) (r : CtDataRef) (st : Array CtData)
    (h n bits ov xbits : Int32)
    (hn : 0 ≤ n.toInt ∧ n.toInt < (tk.arr e).size) (hb : 0 ≤ bits.toInt ∧ bits.toInt ≤ 15)
    (hx : 0 ≤ xbits.toInt ∧ xbits.toInt ≤ 1000) (hr : ∀ e', Space.get (setD h0 id e') r = some st)
    (hs : n.toInt < st.size) (hl : (st[n.toInt.toNat]!).dl.toNat ≤ 15) :
    WS h0 id (gbTail2 (Sp id) (Ptr.ref (tk.ref id) 0) (Ptr.ref r 0) h n bits ov xbits) e (fun res e' =>
      res = (h, ov) ∧ e' = costAdd e ((tk.arr e)[n.toInt.toNat]!).fc.toNat bits.toInt.toNat xbits.toInt.toNat
        (some ((st[n.toInt.toNat]!).dl.toNat))) := by
  unfold gbTail2
  refine WS.bind' (ws_getFc tk n.toInt hn.1 hn.2) fun f e1 ⟨hf, he1⟩ => ?_
  subst e1; subst hf
  refine WS.bind' (ws_iadd bits xbits (by omega) (by omega)) fun t e1 ⟨ht, he1⟩ => ?_
  subst e1
  refine WS.bind' (ws_md _) fun _ e1 he1 => ?_
  subst he1
  have hne : (Ptr.ref r 0 != (Ptr.null : CtDataPtr)) = true := by simp
  simp only [hne, ite_true]
  have hdl : WS h0 id (getDl (Ptr.ref r 0) n.toInt) { e with opt_len := e.opt_len + ((tk.arr e)[n.toInt.toNat]!).fc.toUInt64 * (i2u t).toUInt64 }
      (fun v e' => v = (st[n.toInt.toNat]!).dl ∧ e' = { e with opt_len := e.opt_len + ((tk.arr e)[n.toInt.toNat]!).fc.toUInt64 * (i2u t).toUInt64 }) := by
    unfold getDl
    have := index0_ok (h := setD h0 id { e with opt_len := e.opt_len + ((tk.arr e)[n.toInt.toNat]!).fc.toUInt64 * (i2u t).toUInt64 })
      (hr _) (i := n.toInt) hn.1 hs
    exact WS.of_eq (by simp only [bind_app, this]; rfl) ⟨rfl, rfl⟩
  refine WS.bind' hdl fun dl e1 ⟨hdl1, he1⟩ => ?_
  subst e1; subst hdl1
  refine WS.bind' (ws_iadd (u16i _) xbits (by rw [u16i_toInt]; omega) (by rw [u16i_toInt]; omega)) fun t2 e1 ⟨ht2, he1⟩ => ?_
  subst e1
  refine WS.bind' (ws_md _) fun _ e1 he1 => ?_
  subst he1
  refine WS.pure' ⟨rfl, ?_⟩
  unfold costAdd
  rw [u16i_toInt] at ht2
  simp only [addOpt, Option.map, opt_add _ _ t (by omega) bits.toInt.toNat xbits.toInt.toNat (by omega),
    opt_add _ _ t2 (by omega) (st[n.toInt.toNat]!).dl.toNat xbits.toInt.toNat (by omega)]

/-- `Ptr.index` through a static array (found by `setD h0 id e` for every `e`). -/
theorem ws_index_static {R T : Type} [Space Heap R T] [Inhabited T] {h0 : Heap} {id : Nat} (e : DeflateState)
    (r : R) (a : Array T) (hr : ∀ e', Space.get (setD h0 id e') r = some a) (i : Int) (h1 : 0 ≤ i)
    (h2 : i < a.size) :
    WS h0 id (Ptr.index (Ptr.ref r 0) i) e (fun v e' => v = a[i.toNat]! ∧ e' = e) :=
  WS.of_eq (index0_ok (hr e) h1 h2) ⟨rfl, rfl⟩

@[simp] theorem tk_arr_bl_count (tk : TK) (d : DeflateState) (a : Array UInt16) :
    tk.arr { d with bl_count := a } = tk.arr d := by cases tk <;> rfl

/-- The result of the tail of the first-pass body for a leaf. -/
def leafEff (tk : TK) (e : DeflateState) (n bits : Nat) (xbv : Nat) (slv : Option Nat) : DeflateState :=
  costAdd { e with bl_count := e.bl_count.set! bits (e.bl_count[bits]! + 1) } ((tk.arr e)[n]!).fc.toNat bits xbv slv

theorem ws_gbTail1 {h0 : Heap} {id : Nat} (tk : TK) (e : DeflateState) (stree : CtDataPtr) (extra : IPtr)
    (mc base h n bits ov : Int32) (xbv : Nat) (slv : Option Nat) (hbase : 0 ≤ base.toInt)
    (hn : 0 ≤ n.toInt ∧ n.toInt < (tk.arr e).size) (hb : 0 ≤ bits.toInt ∧ bits.toInt ≤ 15)
    (hbc : e.bl_count.size = 16)
    (hxb : (base.toInt ≤ n.toInt → n.toInt ≤ mc.toInt → ∃ (r : IRef) (ex : Array Int32), extra = Ptr.ref r 0 ∧
        (∀ e', Space.get (setD h0 id e') r = some ex) ∧ 0 ≤ n.toInt - base.toInt ∧ n.toInt - base.toInt < ex.size ∧
        0 ≤ (ex[(n.toInt - base.toInt).toNat]!).toInt ∧ (ex[(n.toInt - base.toInt).toNat]!).toInt ≤ 1000 ∧
        xbv = (ex[(n.toInt - base.toInt).toNat]!).toInt.toNat) ∧
      (n.toInt < base.toInt → xbv = 0))
    (hst : n.toInt ≤ mc.toInt → (stree = Ptr.null ∧ slv = none) ∨ (∃ (r : CtDataRef) (st : Array CtData),
      stree = Ptr.ref r 0 ∧
      (∀ e', Space.get (setD h0 id e') r = some st) ∧ n.toInt < st.size ∧ (st[n.toInt.toNat]!).dl.toNat ≤ 15 ∧
      slv = some ((st[n.toInt.toNat]!).dl.toNat)))
    (hxsz : xbv ≤ 1000) :
    WS h0 id (gbTail1 (Sp id) (Ptr.ref (tk.ref id) 0) stree extra mc base h n bits ov) e (fun r e' =>
      r = (h, ov) ∧ (n.toInt ≤ mc.toInt → e' = leafEff tk e n.toInt.toNat bits.toInt.toNat xbv slv) ∧
        (¬ n.toInt ≤ mc.toInt → e' = e)) := by
  unfold gbTail1
  have hnb : n.toInt ≤ 2147483647 := by
    have := n.toInt_le
    have e : Int32.maxValue.toInt = 2147483647 := by decide
    omega
  by_cases hmc : n.toInt > mc.toInt
  · refine WS.ite' (fun _ => ?_) (fun hh => absurd hmc hh)
    exact WS.pure' ⟨rfl, fun h' => by omega, fun _ => rfl⟩
  · refine WS.ite' (fun hh => absurd hh hmc) (fun _ => ?_)
    refine WS.bind' ws_pBlCount fun bc e1 ⟨hbc1, he1⟩ => ?_
    subst e1; subst hbc1
    refine WS.bind' (ws_index_blc bits.toInt hb.1 (by omega)) fun v e1 ⟨hv, he1⟩ => ?_
    subst e1; subst hv
    refine WS.bind' (ws_setAt_blc bits.toInt _ hb.1 (by omega)) fun _ e1 he1 => ?_
    subst he1
    have hmc' : n.toInt ≤ mc.toInt := by omega
    have hn' : 0 ≤ n.toInt ∧ n.toInt < (tk.arr { e with bl_count := e.bl_count.set! bits.toInt.toNat (e.bl_count[bits.toInt.toNat]! + 1) }).size := by
      rw [tk_arr_bl_count]; exact hn
    -- the tail2 call, for a given extra-bits value
    have fin : ∀ (x : Int32), 0 ≤ x.toInt → x.toInt ≤ 1000 → x.toInt.toNat = xbv →
        WS h0 id (gbTail2 (Sp id) (Ptr.ref (tk.ref id) 0) stree h n bits ov x)
          { e with bl_count := e.bl_count.set! bits.toInt.toNat (e.bl_count[bits.toInt.toNat]! + 1) }
          (fun r e' => r = (h, ov) ∧ (n.toInt ≤ mc.toInt → e' = leafEff tk e n.toInt.toNat bits.toInt.toNat xbv slv) ∧
            (¬ n.toInt ≤ mc.toInt → e' = e)) := by
      intro x hx1 hx2 hx3
      rcases hst hmc' with ⟨hs, hsl⟩ | ⟨r, st, hs, hrr, hs1, hs2, hsl⟩
      · subst hs; subst hsl
        refine WS.mono (ws_gbTail2_null (h0 := h0) (id := id) tk _ h n bits ov x hn' hb ⟨hx1, hx2⟩) ?_
        intro res e' ⟨h1, h2⟩
        refine ⟨h1, fun _ => ?_, fun hh => absurd hmc' hh⟩
        rw [h2, tk_arr_bl_count, hx3]; rfl
      · subst hs; subst hsl
        refine WS.mono (ws_gbTail2_ref (h0 := h0) (id := id) tk _ r st h n bits ov x hn' hb ⟨hx1, hx2⟩ hrr hs1 hs2) ?_
        intro res e' ⟨h1, h2⟩
        refine ⟨h1, fun _ => ?_, fun hh => absurd hmc' hh⟩
        rw [h2, tk_arr_bl_count, hx3]; rfl
    by_cases hge : n.toInt ≥ base.toInt
    · refine WS.ite' (fun _ => ?_) (fun hh => absurd hge hh)
      obtain ⟨r, ex, hex, hrr, h0', h1', h2', h3', hxv⟩ := hxb.1 hge hmc'
      refine WS.bind' (ws_isub n base (by omega) (by omega)) fun d' e1 ⟨hd', he1⟩ => ?_
      subst e1
      have hidx : d'.toInt = n.toInt - base.toInt := hd'
      rw [hex]
      refine WS.bind' (ws_index_static _ r ex hrr d'.toInt (by omega) (by omega)) fun x e1 ⟨hx, he1⟩ => ?_
      subst e1; subst hx
      refine fin _ (by rw [hidx]; exact h2') (by rw [hidx]; exact h3') (by rw [hidx]; exact hxv.symm)
    · refine WS.ite' (fun hh => absurd hh hge) (fun _ => ?_)
      have := hxb.2 (by omega)
      exact fin 0 (by decide) (by decide) (by rw [this]; rfl)
/-! ### The state of the first pass -/

open Zlib.Trees.Proofs.GB

/-- The record `d` with the tree array replaced and `bl_count`, `opt_len`, `static_len` set. -/
def mkP1 (tk : TK) (d : DeflateState) (Tk : Array CtData) (Bk : Array UInt16) (O S : UInt64) : DeflateState :=
  { tk.setArr d Tk with bl_count := Bk, opt_len := O, static_len := S }

@[simp] theorem tk_arr_mkP1 (tk : TK) (d Tk Bk O S) : tk.arr (mkP1 tk d Tk Bk O S) = Tk := by
  cases tk <;> rfl
theorem setArr_mkP1 (tk : TK) (d Tk Bk O S A) : tk.setArr (mkP1 tk d Tk Bk O S) A = mkP1 tk d A Bk O S := by
  cases tk <;> rfl
theorem costAdd_mkP1 (tk : TK) (d Tk Bk O S fv bits xbv slv) :
    costAdd (mkP1 tk d Tk Bk O S) fv bits xbv slv = mkP1 tk d Tk Bk (O + UInt64.ofNat (fv * (bits + xbv)))
      (addOpt S (slv.map fun l => fv * (l + xbv))) := by
  cases slv <;> rfl
theorem bl_mkP1 (tk : TK) (d Tk Bk O S B) : ({ mkP1 tk d Tk Bk O S with bl_count := B } : DeflateState) =
    mkP1 tk d Tk B O S := by
  cases tk <;> rfl

/-- `Tk` with the `Len` of node `v` set to `c`. -/
def setLen (Tk : Array CtData) (v c : Nat) : Array CtData := Tk.set! v { Tk[v]! with dl := UInt16.ofNat c }

/-- The nodes of the heap array, as numbers. -/
def Hn (d : DeflateState) (q : Nat) : Nat := (d.heap[q]!).toInt.toNat
/-- The frequency of a symbol. -/
def frn (T : Array CtData) (v : Nat) : Nat := (T[v]!).fc.toNat

/-- The state after `k` non-root positions of the first pass. -/
def P1State (tk : TK) (d : DeflateState) (hm J elems maxc L : Nat) (xb : Nat → Nat) (slOpt : Option (Nat → Nat))
    (k : Nat) (e : DeflateState) : Prop :=
  ∃ (Tk : Array CtData) (Bk : Array UInt16) (O S : UInt64), e = mkP1 tk d Tk Bk O S ∧
    O = d.opt_len + UInt64.ofNat (costP (Hn d) hm maxc (frn (tk.arr d)) (clK (Hn d) hm elems L (2 * J)) xb k) ∧
    S = addOpt d.static_len (slOpt.map fun sl => costP (Hn d) hm maxc (frn (tk.arr d)) sl xb k) ∧
    Tk.size = (tk.arr d).size ∧ Bk.size = 16 ∧
    (∀ q, hm ≤ q → q ≤ hm + k → (Tk[Hn d q]!).dl = UInt16.ofNat (clK (Hn d) hm elems L (2 * J) (Hn d q))) ∧
    (∀ i, k ≤ i → i < 2 * J → (Tk[Hn d (hm + 1 + i)]!).dl = UInt16.ofNat (dadP elems (hm + 1 + i))) ∧
    (∀ v : Nat, (Tk[v]!).fc = ((tk.arr d)[v]!).fc) ∧
    (∀ v : Nat, (∀ q, hm ≤ q → q < 573 → Hn d q ≠ v) → (Tk[v]!).dl = ((tk.arr d)[v]!).dl) ∧
    (∀ b, b < 16 → Bk[b]! = UInt16.ofNat (blP (Hn d) hm maxc (clK (Hn d) hm elems L (2 * J)) k b))

@[simp] theorem mkP1_bl_count (tk : TK) (d Tk Bk O S) : (mkP1 tk d Tk Bk O S).bl_count = Bk := by cases tk <;> rfl

theorem mkP1_heap (tk : TK) (d Tk Bk O S) : (mkP1 tk d Tk Bk O S).heap = d.heap := by cases tk <;> rfl

/-- All the preconditions of the first pass. -/
structure P1Ctx (h0 : Heap) (id : Nat) (tk : TK) (d : DeflateState) (stree : CtDataPtr) (extra : IPtr)
    (mc base ml : Int32) (hm J elems maxc L baseN : Nat) (xb : Nat → Nat) (slOpt : Option (Nat → Nat)) : Prop where
  hsz : d.heap.size = 573
  bsz : d.bl_count.size = 16
  hnn : ∀ q, hm ≤ q → q < 573 → 0 ≤ (d.heap[q]!).toInt
  shape : PShape (Hn d) hm J elems maxc
  nc : elems + J ≤ (tk.arr d).size
  tsz : (tk.arr d).size ≤ 600
  mcv : mc.toInt = maxc
  basev : base.toInt = baseN
  mlv : ml.toInt = L
  L1 : 1 ≤ L
  L15 : L ≤ 15
  dad : ∀ i, i < 2 * J → ((tk.arr d)[Hn d (hm + 1 + i)]!).dl = UInt16.ofNat (dadP elems (hm + 1 + i))
  xbOK : ∀ n, n ≤ maxc → (baseN ≤ n → ∃ (r : IRef) (ex : Array Int32), extra = Ptr.ref r 0 ∧
      (∀ e, Space.get (setD h0 id e) r = some ex) ∧ n - baseN < ex.size ∧ 0 ≤ (ex[n - baseN]!).toInt ∧
      (ex[n - baseN]!).toInt ≤ 1000 ∧ xb n = (ex[n - baseN]!).toInt.toNat) ∧ (n < baseN → xb n = 0)
  stOK : (stree = Ptr.null ∧ slOpt = none) ∨ ∃ (r : CtDataRef) (st : Array CtData) (sl : Nat → Nat),
    stree = Ptr.ref r 0 ∧ slOpt = some sl ∧ (∀ e, Space.get (setD h0 id e) r = some st) ∧
    ∀ n, n ≤ maxc → n < st.size ∧ (st[n]!).dl.toNat ≤ 15 ∧ sl n = (st[n]!).dl.toNat

theorem ws_gbBody1 {h0 : Heap} {id : Nat} {tk : TK} {d : DeflateState} {stree : CtDataPtr} {extra : IPtr}
    {mc base ml : Int32} {hm J elems maxc L baseN : Nat} {xb : Nat → Nat} {slOpt : Option (Nat → Nat)}
    (ctx : P1Ctx h0 id tk d stree extra mc base ml hm J elems maxc L baseN xb slOpt) (k : Nat) (hk : k < 2 * J)
    (h o : Int32) (hh : h.toInt = (hm + 1 + k : Nat)) (ho : o.toInt = ovP (Hn d) hm elems L (clK (Hn d) hm elems L (2 * J)) k)
    (e : DeflateState) (hst : P1State tk d hm J elems maxc L xb slOpt k e) :
    WS h0 id (gbBody1 (Sp id) (Ptr.ref (tk.ref id) 0) stree extra mc base ml (h, o)) e (fun r e' =>
      r.1.toInt = (hm + 1 + k : Nat) ∧ r.2.toInt = ovP (Hn d) hm elems L (clK (Hn d) hm elems L (2 * J)) (k + 1) ∧
      P1State tk d hm J elems maxc L xb slOpt (k + 1) e') := by
  have PS := ctx.shape
  have hm_eq := PS.hm_eq
  have hC : Clamped (Hn d) hm J elems L (clK (Hn d) hm elems L (2 * J)) := clK_clamped PS
  obtain ⟨Tk, Bk, O, S, rfl, hO, hS, hTs, hBs, hcl, hdad, hfc, hout, hbl⟩ := hst
  have hq1 : hm + 1 + k < 573 := by omega
  have hnn := ctx.hnn (hm + 1 + k) (by omega) hq1
  have hnode : Hn d (hm + 1 + k) < elems + J := by
    rcases PS.kind (hm + 1 + k) (by omega) hq1 with h1 | h1
    · have := PS.maxc_lt; omega
    · omega
  have hdv : dadP elems (hm + 1 + k) < elems + J := by unfold dadP; omega
  obtain ⟨q', hq'1, hq'2, hq'e⟩ := dad_pos PS k hk
  have hCd := hC.dad_le PS k hk
  have hsz573 := ctx.hsz
  have hTn := ctx.nc
  have htsz := ctx.tsz
  have hL1 := ctx.L1
  have hL15 := ctx.L15
  have hmlv := ctx.mlv
  have hbasev := ctx.basev
  have hmcv := ctx.mcv
  have hTk : (tk.arr (mkP1 tk d Tk Bk O S)).size = (tk.arr d).size := by rw [tk_arr_mkP1]; exact hTs
  unfold gbBody1
  refine WS.bind' (ws_heapAt h (by omega) (by rw [mkP1_heap]; omega)) fun n e1 ⟨hn, he1⟩ => ?_
  subst e1
  have hnv : n.toInt = (Hn d (hm + 1 + k) : Int) := by
    rw [mkP1_heap] at hn
    have : h.toInt.toNat = hm + 1 + k := by omega
    rw [this] at hn
    rw [hn]; unfold Hn; omega
  have hdn := hdad k (Nat.le_refl _) hk
  refine WS.bind' (ws_getDl tk n.toInt (by omega) (by rw [hTk]; omega)) fun a1 e1 ⟨ha1, he1⟩ => ?_
  subst e1
  have ha1' : a1 = UInt16.ofNat (dadP elems (hm + 1 + k)) := by
    rw [ha1, tk_arr_mkP1]
    have : n.toInt.toNat = Hn d (hm + 1 + k) := by omega
    rw [this]; exact hdn
  have hdvlt : dadP elems (hm + 1 + k) < 65536 := by omega
  have hu1 : (u16i a1).toInt = (dadP elems (hm + 1 + k) : Int) := by
    rw [u16i_toInt, ha1', UInt16.toNat_ofNat']; omega
  refine WS.bind' (ws_getDl tk (u16i a1).toInt (by omega) (by rw [hTk]; omega)) fun a2 e1 ⟨ha2, he1⟩ => ?_
  subst e1
  have ha2' : a2 = UInt16.ofNat (clK (Hn d) hm elems L (2 * J) (dadP elems (hm + 1 + k))) := by
    rw [ha2, tk_arr_mkP1]
    have : (u16i a1).toInt.toNat = Hn d q' := by omega
    rw [this]
    have := hcl q' hq'1 (by omega)
    rw [this, hq'e]
  have hCdv : (u16i a2).toInt = (clK (Hn d) hm elems L (2 * J) (dadP elems (hm + 1 + k)) : Int) := by
    rw [u16i_toInt, ha2', UInt16.toNat_ofNat']; omega
  refine WS.bind' (ws_iadd (u16i a2) 1 (by have : (1 : Int32).toInt = 1 := rfl; omega)
    (by have : (1 : Int32).toInt = 1 := rfl; omega)) fun bits e1 ⟨hbits, he1⟩ => ?_
  subst e1
  have h1i : (1 : Int32).toInt = 1 := rfl
  have hCn : clK (Hn d) hm elems L (2 * J) (Hn d (hm + 1 + k)) =
      min (clK (Hn d) hm elems L (2 * J) (dadP elems (hm + 1 + k)) + 1) L := hC.step k hk
  have hCnL : 1 ≤ clK (Hn d) hm elems L (2 * J) (Hn d (hm + 1 + k)) ∧
      clK (Hn d) hm elems L (2 * J) (Hn d (hm + 1 + k)) ≤ L := by omega
  have hnT : Hn d (hm + 1 + k) < (tk.arr d).size := by omega
  have hnvn : n.toInt.toNat = Hn d (hm + 1 + k) := by omega
  have hleaf : n.toInt ≤ mc.toInt ↔ Hn d (hm + 1 + k) ≤ maxc := by rw [hnv, ctx.mcv]; omega
  -- everything after `Len` is stored
  have fin : ∀ (bitsv ov' : Int32), bitsv.toInt = (clK (Hn d) hm elems L (2 * J) (Hn d (hm + 1 + k)) : Int) →
      ov'.toInt = (ovP (Hn d) hm elems L (clK (Hn d) hm elems L (2 * J)) (k + 1) : Int) →
      WS h0 id (do setDl (Ptr.ref (tk.ref id) 0) n.toInt (i2us bitsv)
                   gbTail1 (Sp id) (Ptr.ref (tk.ref id) 0) stree extra mc base h n bitsv ov')
        (mkP1 tk d Tk Bk O S) (fun r e' => r.1.toInt = (hm + 1 + k : Nat) ∧
          r.2.toInt = (ovP (Hn d) hm elems L (clK (Hn d) hm elems L (2 * J)) (k + 1) : Int) ∧
          P1State tk d hm J elems maxc L xb slOpt (k + 1) e') := by
    intro bitsv ov' hbv hov
    have hbvn : 0 ≤ bitsv.toInt ∧ bitsv.toInt ≤ 15 := by omega
    have hi2us : i2us bitsv = UInt16.ofNat (clK (Hn d) hm elems L (2 * J) (Hn d (hm + 1 + k))) := by
      unfold i2us; rw [hbv]; congr 1; omega
    refine WS.bind' (ws_setDl tk n.toInt (i2us bitsv) (by omega) (by rw [hTk]; omega)) fun _ e2 he2 => ?_
    rw [setArr_mkP1, tk_arr_mkP1, hnvn, hi2us] at he2
    change e2 = mkP1 tk d (setLen Tk (Hn d (hm + 1 + k)) (clK (Hn d) hm elems L (2 * J) (Hn d (hm + 1 + k)))) Bk O S at he2
    subst he2
    have hTk's : (setLen Tk (Hn d (hm + 1 + k)) (clK (Hn d) hm elems L (2 * J) (Hn d (hm + 1 + k)))).size = Tk.size :=
      size_set! _ _ _
    have hnTk : Hn d (hm + 1 + k) < Tk.size := by omega
    obtain ⟨xbv, hxbv⟩ : ∃ x : Nat, x = (if Hn d (hm + 1 + k) ≤ maxc then xb (Hn d (hm + 1 + k)) else 0) := ⟨_, rfl⟩
    obtain ⟨slv, hslv⟩ : ∃ x : Option Nat, x = slOpt.map (fun sl => if Hn d (hm + 1 + k) ≤ maxc then sl (Hn d (hm + 1 + k)) else 0) := ⟨_, rfl⟩
    obtain ⟨Tn, hTn'⟩ : ∃ T2, T2 = setLen Tk (Hn d (hm + 1 + k)) (clK (Hn d) hm elems L (2 * J) (Hn d (hm + 1 + k))) := ⟨_, rfl⟩
    rw [← hTn'] at hTk's ⊢
    have hTns : Tn.size = (tk.arr d).size := by rw [hTk's]; exact hTs
    -- facts about the new tree array
    have getTn : ∀ v, Tn[v]! = if v = Hn d (hm + 1 + k) then
        { Tk[Hn d (hm + 1 + k)]! with dl := UInt16.ofNat (clK (Hn d) hm elems L (2 * J) (Hn d (hm + 1 + k))) } else Tk[v]! := by
      intro v; rw [hTn']; exact getD_set Tk _ v _ hnTk
    have hinj : ∀ q2, hm ≤ q2 → q2 < 573 → Hn d q2 = Hn d (hm + 1 + k) → q2 = hm + 1 + k :=
      fun q2 h1 h2 h3 => PS.inj q2 (hm + 1 + k) h1 h2 (by omega) hq1 h3
    have Tn_cl : ∀ q2, hm ≤ q2 → q2 ≤ hm + (k + 1) → (Tn[Hn d q2]!).dl =
        UInt16.ofNat (clK (Hn d) hm elems L (2 * J) (Hn d q2)) := by
      intro q2 h1 h2
      rw [getTn]
      by_cases e : Hn d q2 = Hn d (hm + 1 + k)
      · rw [if_pos e, e]
      · rw [if_neg e]
        have hne : q2 ≠ hm + 1 + k := fun h' => e (by rw [h'])
        exact hcl q2 h1 (by omega)
    have Tn_dad : ∀ i, k + 1 ≤ i → i < 2 * J → (Tn[Hn d (hm + 1 + i)]!).dl = UInt16.ofNat (dadP elems (hm + 1 + i)) := by
      intro i h1 h2
      rw [getTn, if_neg]
      · exact hdad i (by omega) h2
      · intro e; have := hinj (hm + 1 + i) (by omega) (by omega) e; omega
    have Tn_fc : ∀ v : Nat, (Tn[v]!).fc = ((tk.arr d)[v]!).fc := by
      intro v; rw [getTn]; split
      · rename_i e; subst e; exact hfc _
      · exact hfc v
    have Tn_out : ∀ v : Nat, (∀ q, hm ≤ q → q < 573 → Hn d q ≠ v) → (Tn[v]!).dl = ((tk.arr d)[v]!).dl := by
      intro v hv; rw [getTn, if_neg]
      · exact hout v hv
      · intro e; exact hv (hm + 1 + k) (by omega) hq1 e.symm
    have hCn' : clK (Hn d) hm elems L (2 * J) (Hn d (hm + 1 + k)) ≤ 15 := by omega
    have hnTn : 0 ≤ n.toInt ∧ n.toInt < (tk.arr (mkP1 tk d Tn Bk O S)).size := by
      rw [tk_arr_mkP1, hTns]; omega
    have hxb1000 : xbv ≤ 1000 := by
      rw [hxbv]; split
      · rename_i hl
        by_cases hb : baseN ≤ Hn d (hm + 1 + k)
        · obtain ⟨r, ex, -, -, -, -, h1, h2⟩ := (ctx.xbOK _ hl).1 hb
          omega
        · rw [(ctx.xbOK _ hl).2 (by omega)]; omega
      · omega
    have hbase0 : 0 ≤ base.toInt := by have := ctx.basev; omega
    have tail := ws_gbTail1 (h0 := h0) (id := id) tk (mkP1 tk d Tn Bk O S) stree extra mc base h n bitsv ov' xbv slv
      hbase0 hnTn hbvn (by rw [mkP1_bl_count]; exact hBs)
      (by
        constructor
        · intro hb hl
          have hl' : Hn d (hm + 1 + k) ≤ maxc := hleaf.mp hl
          obtain ⟨r, ex, h1, h2, h3, h4, h5, h7⟩ := (ctx.xbOK _ hl').1 (by omega)
          refine ⟨r, ex, h1, h2, by omega, ?_, ?_, ?_, ?_⟩
          · have : n.toInt - base.toInt = ((Hn d (hm + 1 + k) - baseN : Nat) : Int) := by omega
            rw [this]; omega
          · have : (n.toInt - base.toInt).toNat = Hn d (hm + 1 + k) - baseN := by omega
            rw [this]; exact h4
          · have : (n.toInt - base.toInt).toNat = Hn d (hm + 1 + k) - baseN := by omega
            rw [this]; exact h5
          · have : (n.toInt - base.toInt).toNat = Hn d (hm + 1 + k) - baseN := by omega
            rw [this, hxbv, if_pos hl']; exact h7
        · intro hb
          rw [hxbv]; split
          · rename_i hl'; exact (ctx.xbOK _ hl').2 (by omega)
          · rfl)
      (by
        intro hl
        have hl' : Hn d (hm + 1 + k) ≤ maxc := hleaf.mp hl
        rcases ctx.stOK with ⟨h1, h2⟩ | ⟨r, st, sl, h1, h2, h3, h4⟩
        · left; refine ⟨h1, ?_⟩; rw [hslv, h2]; rfl
        · right
          obtain ⟨g1, g2, g3⟩ := h4 _ hl'
          refine ⟨r, st, h1, h3, by omega, by rw [hnvn]; exact g2, ?_⟩
          rw [hslv, h2, hnvn]; simp [hl', g3])
      hxb1000
    refine WS.mono tail ?_
    rintro r e' ⟨hr, hl1, hl2⟩
    subst hr
    refine ⟨by omega, hov, ?_⟩
    have hbn : bitsv.toInt.toNat = clK (Hn d) hm elems L (2 * J) (Hn d (hm + 1 + k)) := by omega
    have hcs := costP_succ (Hn d) hm maxc (frn (tk.arr d)) (clK (Hn d) hm elems L (2 * J)) xb k
    have hcs2 : ∀ sl, costP (Hn d) hm maxc (frn (tk.arr d)) sl xb (k + 1) = costP (Hn d) hm maxc (frn (tk.arr d)) sl xb k +
        (if Hn d (hm + 1 + k) ≤ maxc then frn (tk.arr d) (Hn d (hm + 1 + k)) * (sl (Hn d (hm + 1 + k)) + xb (Hn d (hm + 1 + k))) else 0) :=
      fun sl => costP_succ (Hn d) hm maxc (frn (tk.arr d)) sl xb k
    have hfv : ((tk.arr (mkP1 tk d Tn Bk O S))[n.toInt.toNat]!).fc.toNat = frn (tk.arr d) (Hn d (hm + 1 + k)) := by
      rw [tk_arr_mkP1, hnvn]; unfold frn; rw [Tn_fc]
    by_cases hl : Hn d (hm + 1 + k) ≤ maxc
    · have he' := hl1 (hleaf.mpr hl)
      unfold leafEff at he'
      rw [bl_mkP1, costAdd_mkP1, hfv, hbn] at he'
      simp only [mkP1_bl_count] at he'
      refine ⟨Tn, Bk.set! (clK (Hn d) hm elems L (2 * J) (Hn d (hm + 1 + k))) (Bk[clK (Hn d) hm elems L (2 * J) (Hn d (hm + 1 + k))]! + 1),
        O + UInt64.ofNat (frn (tk.arr d) (Hn d (hm + 1 + k)) * (clK (Hn d) hm elems L (2 * J) (Hn d (hm + 1 + k)) + xbv)),
        (addOpt S (slv.map fun l => frn (tk.arr d) (Hn d (hm + 1 + k)) * (l + xbv))),
        he', ?_, ?_, hTns, ?_, Tn_cl, Tn_dad, Tn_fc, Tn_out, ?_⟩
      · rw [hO, hcs, if_pos hl, hxbv, if_pos hl, UInt64.ofNat_add]; ac_rfl
      · rw [hS, hslv]
        cases slOpt with
        | none => rfl
        | some sl =>
          simp only [Option.map, addOpt, hcs2, if_pos hl, hxbv, UInt64.ofNat_add, UInt64.add_assoc]
      · rw [size_set!]; exact hBs
      · intro b hb
        rw [getD_set Bk _ b _ (by omega), blP_succ]
        by_cases e : b = clK (Hn d) hm elems L (2 * J) (Hn d (hm + 1 + k))
        · subst e; rw [if_pos rfl, hbl _ hb, if_pos ⟨hl, rfl⟩, UInt16.ofNat_add]; rfl
        · rw [if_neg e, hbl b hb, if_neg (fun hh => e hh.2.symm)]; simp
    · have he' := hl2 (fun hh => hl (hleaf.mp hh))
      refine ⟨Tn, Bk, O, S, he', ?_, ?_, hTns, hBs, Tn_cl, Tn_dad, Tn_fc, Tn_out, ?_⟩
      · rw [hO, hcs, if_neg hl]; simp
      · rw [hS]; cases slOpt with
        | none => rfl
        | some sl => simp only [Option.map, addOpt, hcs2, if_neg hl, Nat.add_zero]
      · intro b hb
        rw [hbl b hb, blP_succ, if_neg (fun hh => hl hh.1)]; simp
  have hovs : ovP (Hn d) hm elems L (clK (Hn d) hm elems L (2 * J)) (k + 1) =
      ovP (Hn d) hm elems L (clK (Hn d) hm elems L (2 * J)) k +
        (if clK (Hn d) hm elems L (2 * J) (dadP elems (hm + 1 + k)) = L then 1 else 0) := rfl
  have hovle := ovP_le (Hn d) hm elems L (clK (Hn d) hm elems L (2 * J)) k
  refine WS.ite' (fun hgt => ?_) (fun hle => ?_)
  · refine WS.bind' (ws_iadd o 1 (by omega) (by omega)) fun ov e1 ⟨hov, he1⟩ => ?_
    subst e1
    have hcd : clK (Hn d) hm elems L (2 * J) (dadP elems (hm + 1 + k)) = L := by omega
    refine fin ml ov (by omega) (by rw [hovs, if_pos hcd]; omega)
  · have hcd : ¬ clK (Hn d) hm elems L (2 * J) (dadP elems (hm + 1 + k)) = L := by omega
    refine fin bits o (by omega) (by rw [hovs, if_neg hcd]; omega)

/-- **The first pass.** From the state after `Len` of the root is zero, the pass ends with `h = HEAP_SIZE`, `overflow` the
number of clamped nodes, and the state of `k = 2J` positions processed. -/
theorem ws_gbPass1 {h0 : Heap} {id : Nat} {tk : TK} {d : DeflateState} {stree : CtDataPtr} {extra : IPtr}
    {mc base ml : Int32} {hm J elems maxc L baseN : Nat} {xb : Nat → Nat} {slOpt : Option (Nat → Nat)}
    (ctx : P1Ctx h0 id tk d stree extra mc base ml hm J elems maxc L baseN xb slOpt)
    (h0v : Int32) (hh0 : h0v.toInt = (hm + 1 : Nat)) (e : DeflateState)
    (hst : P1State tk d hm J elems maxc L xb slOpt 0 e) :
    WS h0 id (gbPass1 (Sp id) (Ptr.ref (tk.ref id) 0) stree extra mc base ml h0v) e (fun r e' =>
      r.1.toInt = 573 ∧ r.2.toInt = (ovP (Hn d) hm elems L (clK (Hn d) hm elems L (2 * J)) (2 * J) : Int) ∧
      P1State tk d hm J elems maxc L xb slOpt (2 * J) e') := by
  have PS := ctx.shape
  have hm_eq := PS.hm_eq
  unfold gbPass1
  refine WS.cfor2 (id := id)
    (fun (st : Int32 × Int32) e => ∃ k, k ≤ 2 * J ∧ st.1.toInt = (hm + 1 + k : Nat) ∧
      st.2.toInt = (ovP (Hn d) hm elems L (clK (Hn d) hm elems L (2 * J)) k : Int) ∧
      P1State tk d hm J elems maxc L xb slOpt k e)
    (fun (st : Int32 × Int32) _ => (573 : Nat) - st.1.toInt.toNat)
    (fun (r : Int32 × Int32) e' => r.1.toInt = 573 ∧ r.2.toInt = (ovP (Hn d) hm elems L (clK (Hn d) hm elems L (2 * J)) (2 * J) : Int) ∧
      P1State tk d hm J elems maxc L xb slOpt (2 * J) e') ?_
    ⟨0, by omega, by show h0v.toInt = _; omega, ?_, hst⟩ (by simp only [fuel]; omega)
  · rintro ⟨h, o⟩ e ⟨k, hk, hh, ho, hs⟩
    simp only at hh ho
    refine WS.pure' ?_
    have hH : HEAP_SIZE.toInt = 573 := rfl
    by_cases hlt : k < 2 * J
    · refine Or.inr ⟨?_, ?_⟩
      · simp only [gbCond1, decide_eq_true_eq]; omega
      · refine WS.bind' (ws_gbBody1 ctx k hlt h o hh ho e hs) fun r e1 ⟨h1, h2, h3⟩ => ?_
        have h1i : (1 : Int32).toInt = 1 := rfl
        refine WS.bind' (ws_iadd r.1 1 (by omega) (by omega)) fun h' e2 ⟨hh', he2⟩ => ?_
        subst e2
        refine WS.pure' ⟨⟨k + 1, by omega, ?_, ?_, h3⟩, ?_⟩
        · show h'.toInt = _; omega
        · exact h2
        · show 573 - h'.toInt.toNat < 573 - h.toInt.toNat; omega
    · refine Or.inl ⟨?_, ?_⟩
      · simp only [gbCond1, decide_eq_false_iff_not]; show ¬ h.toInt < 573; omega
      · have hk2 : k = 2 * J := by omega
        subst hk2
        exact ⟨by show h.toInt = 573; omega, ho, hs⟩
  · show (0 : Int32).toInt = _
    simp [ovP]

end Zlib.Trees.Proofs
