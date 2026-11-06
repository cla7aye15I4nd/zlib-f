import ZlibF.Math.DeflateCodes
import ZlibF.Proof.«trees.c.monad»
import ZlibF.Proof.«trees.c.heap.gbp1»
import ZlibF.Proof.«trees.c.reverse»

/-!
# trees.c: canonical code assignment

The two loop invariants follow the reference `zlib-formal` `GenCodes` proof.
The executions below use this repository's actual accessors and checked
arithmetic. No tree-construction contract is assumed.
-/

namespace Zlib.Trees.Proofs
open C Zlib.Trees

/-- The first loop of `gen_codes`, verbatim. -/
def gcStart (bl_count : WPtr) : M (Int32 × UInt32 × Array UInt16) :=
  cfor (σ := Int32 × UInt32 × Array UInt16)
    (fun (bits, _, _) => pure (decide (bits.toInt ≤ MAX_BITS.toInt)))
    (fun (bits, code, nc) => do pure (← iadd bits 1, code, nc))
    (fun (bits, code, nc) => do
      let b ← Ptr.index bl_count (← isub bits 1).toInt
      let code := (code + b.toUInt32) <<< 1
      if bits.toInt < 0 ∨ nc.size ≤ bits.toInt.toNat then ub "next_code index outside its array"
      pure (bits, code, nc.set! bits.toInt.toNat code.toUInt16))
    (1, 0, Array.replicate 16 0)

/-- The symbol loop of `gen_codes`, verbatim. -/
def gcAssign (tree : CtDataPtr) (max_code : Int32) (next_code : Array UInt16) :
    M (Int32 × Array UInt16) :=
  cfor (σ := Int32 × Array UInt16)
    (fun (n, _) => pure (decide (n.toInt ≤ max_code.toInt)))
    (fun (n, nc) => do pure (← iadd n 1, nc))
    (fun (n, nc) => do
      let len := u16i (← getDl tree n.toInt)
      if len == 0 then return (n, nc)
      let li := len.toInt.toNat
      if nc.size ≤ li then ub "next_code index outside its array"
      let old := nc[li]!
      let nc := nc.set! li (old + 1)
      let r ← bi_reverse old.toUInt32 len
      setFc tree n.toInt r.toUInt16
      pure (n, nc))
    (0, next_code)

theorem gen_codes_eq (tree : CtDataPtr) (max_code : Int32) (bl_count : WPtr) :
    gen_codes tree max_code bl_count = (do
      let (_, _, nc) ← gcStart bl_count
      let _ ← gcAssign tree max_code nc
      pure ()) := rfl

/-- All fifteen canonical starting codes are computed without changing the
heap. Counts are arbitrary unsigned 16-bit values; wrapping is accounted for. -/
theorem gcStart_run {h0 : Heap} {id : Nat} (d : DeflateState)
    (hsz : 15 ≤ d.bl_count.size) :
    WS h0 id (gcStart (.ref (.dstate_bl_count id) 0)) d (fun r e =>
      e = d ∧ r.2.2.size = 16 ∧ ∀ b, 1 ≤ b → b < 16 →
        r.2.2[b]! = UInt16.ofNat (Math.nextCode (fun i => d.bl_count[i]!.toNat) b)) := by
  let bl : Nat → Nat := fun i => d.bl_count[i]!.toNat
  let Inv : Int32 × UInt32 × Array UInt16 → DeflateState → Prop := fun r e =>
    ∃ k : Nat, k ≤ 15 ∧ e = d ∧ r.1.toInt = k + 1 ∧
      r.2.1.toNat = Math.nextCode bl k % 4294967296 ∧ r.2.2.size = 16 ∧
      ∀ b, 1 ≤ b → b ≤ k → r.2.2[b]! = UInt16.ofNat (Math.nextCode bl b)
  unfold gcStart
  refine WS.cfor2 Inv (fun r _ => 15 - (r.1.toInt - 1).toNat) _ ?_
    ⟨0, by omega, rfl, rfl, rfl, by simp, fun b h1 h2 => by omega⟩ (by simp [fuel])
  rintro ⟨bits, code, nc⟩ e ⟨k, hk, rfl, hb, hc, hs, hv⟩
  change bits.toInt = (k : Int) + 1 at hb
  change code.toNat = Math.nextCode bl k % 4294967296 at hc
  change nc.size = 16 at hs
  change ∀ b, 1 ≤ b → b ≤ k → nc[b]! = UInt16.ofNat (Math.nextCode bl b) at hv
  refine WS.pure' ?_
  by_cases hlt : k < 15
  · refine Or.inr ⟨by simp only [decide_eq_true_eq]; change bits.toInt ≤ 15; omega, ?_⟩
    have h1 : (1 : Int32).toInt = 1 := rfl
    dsimp only
    simp only [M_bind_assoc]
    refine WS.bind' (ws_isub bits 1 (by omega) (by omega)) fun ix e1 ⟨hi, he1⟩ => ?_
    subst e1
    have hik : ix.toInt = k := by omega
    refine WS.bind' (ws_index_blc ix.toInt (by omega) (by omega)) fun v e1 ⟨hv0, he1⟩ => ?_
    subst e1; subst v
    have hiN : ix.toInt.toNat = k := by omega
    have hbN : bits.toInt.toNat = k + 1 := by omega
    have hbad : ¬ (bits.toInt < 0 ∨ nc.size ≤ bits.toInt.toNat) := by omega
    simp only [hbad, ite_false, M_pure_bind]
    refine WS.bind' (ws_iadd bits 1 (by omega) (by omega)) fun bits' e1 ⟨hb', he1⟩ => ?_
    subst e1
    refine WS.pure' ⟨⟨k + 1, by omega, rfl, by dsimp; omega, ?_, ?_, ?_⟩, ?_⟩
    · dsimp only
      rw [UInt32.toNat_shiftLeft, UInt32.toNat_add, hc, hiN]
      simp only [UInt16.toNat_toUInt32, Math.nextCode]
      rw [show (1 : UInt32).toNat % 32 = 1 from rfl, Nat.shiftLeft_eq]
      dsimp only [bl]
      omega
    · simpa only [size_set!] using hs
    · intro b h1 h2
      dsimp only
      rw [getD_set nc bits.toInt.toNat b _ (by omega), hbN]
      by_cases heq : b = k + 1
      · rw [if_pos heq]
        subst b
        apply UInt16.toNat_inj.mp
        simp only [UInt32.toNat_toUInt16, UInt16.toNat_ofNat', UInt32.toNat_shiftLeft,
          UInt32.toNat_add, hc, UInt16.toNat_toUInt32, hiN, Math.nextCode]
        rw [show (1 : UInt32).toNat % 32 = 1 from rfl, Nat.shiftLeft_eq]
        dsimp only [bl]
        omega
      · rw [if_neg heq]; exact hv b h1 (by omega)
    · dsimp only; omega
  · refine Or.inl ⟨by simp only [decide_eq_false_iff_not]; change ¬ bits.toInt ≤ 15; omega,
      rfl, hs, fun b h1 h2 => hv b h1 (by omega)⟩

private theorem gc_reverse_eq (c k : Nat) : Out.revBits c k = Math.reverseLowBits c k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [Out.revBits, Math.reverseLowBits, ih]

private theorem gc_setArr_twice (tk : TK) (d : DeflateState) (a b : Array CtData) :
    tk.setArr (tk.setArr d a) b = tk.setArr d b := by cases tk <;> rfl

/-- The actual symbol loop writes each positive-length symbol's canonical,
bit-reversed code. Zero-length symbols and every other field are preserved.
The internal domain includes empty ranges and arbitrary length/count arrays;
only the array bounds and the fifteen-bit length limit are required. -/
theorem gcAssign_run {h0 : Heap} {id : Nat} (d : DeflateState) (tk : TK)
    (max_code : Int32) (nc : Array UInt16)
    (hm0 : -1 ≤ max_code.toInt) (hm1 : max_code.toInt < 573)
    (hfit : (max_code.toInt + 1).toNat ≤ (tk.arr d).size)
    (hlen : ∀ j < (max_code.toInt + 1).toNat, ((tk.arr d)[j]!).dl.toNat ≤ 15)
    (hnc : nc.size = 16)
    (hstart : ∀ b, 1 ≤ b → b < 16 →
      nc[b]! = UInt16.ofNat (Math.nextCode (fun i => d.bl_count[i]!.toNat) b)) :
    WS h0 id (gcAssign (.ref (tk.ref id) 0) max_code nc) d (fun _ e =>
      ∃ a : Array CtData, e = tk.setArr d a ∧ a.size = (tk.arr d).size ∧
        ∀ j < a.size, a[j]! =
          if j < (max_code.toInt + 1).toNat ∧ ((tk.arr d)[j]!).dl ≠ 0 then
            { (tk.arr d)[j]! with fc := UInt16.ofNat (Math.storedCode
              (fun i => d.bl_count[i]!.toNat) (fun i => ((tk.arr d)[i]!).dl.toNat) j) }
          else (tk.arr d)[j]!) := by
  let M := (max_code.toInt + 1).toNat
  let orig := tk.arr d
  let len : Nat → Nat := fun j => orig[j]!.dl.toNat
  let bl : Nat → Nat := fun j => d.bl_count[j]!.toNat
  let entry : Nat → Nat → CtData := fun m j =>
    if j < m ∧ orig[j]!.dl ≠ 0 then
      { orig[j]! with fc := UInt16.ofNat (Math.storedCode bl len j) }
    else orig[j]!
  let Inv : Int32 × Array UInt16 → DeflateState → Prop := fun r e =>
    ∃ (m : Nat) (a : Array CtData), m ≤ M ∧ r.1.toInt = m ∧
      e = tk.setArr d a ∧ a.size = orig.size ∧ r.2.size = 16 ∧
      (∀ b, 1 ≤ b → b < 16 →
        r.2[b]! = UInt16.ofNat (Math.nextCode bl b + Math.countBefore len b m)) ∧
      ∀ j < a.size, a[j]! = entry m j
  have hi1 : (1 : Int32).toInt = 1 := rfl
  have hMv : max_code.toInt + 1 = M := by dsimp [M]; omega
  have hself : tk.setArr d orig = d := by cases tk <;> rfl
  unfold gcAssign
  refine WS.cfor2 Inv (fun r _ => M - r.1.toInt.toNat) _ ?_
    ⟨0, orig, by omega, rfl, hself.symm, rfl, hnc, ?_, ?_⟩ (by simp only [fuel]; omega)
  · rintro ⟨n, nc⟩ e ⟨m, a, hm, hn, he, hsz, hnc, hv, ha⟩
    subst e
    change n.toInt = (m : Int) at hn
    change nc.size = 16 at hnc
    change ∀ b, 1 ≤ b → b < 16 →
      nc[b]! = UInt16.ofNat (Math.nextCode bl b + Math.countBefore len b m) at hv
    refine WS.pure' ?_
    by_cases hlt : m < M
    · refine Or.inr ⟨by simp only [decide_eq_true_eq]; omega, ?_⟩
      have hnN : n.toInt.toNat = m := by omega
      have hmA : m < a.size := by dsimp [orig] at hsz; dsimp [M] at hlt; omega
      have hmOrig : m < orig.size := by omega
      have hdl : a[m]!.dl = orig[m]!.dl := by
        rw [ha m hmA]; dsimp only [entry]; split <;> rfl
      have hlen15 : len m ≤ 15 := hlen m hlt
      dsimp only
      simp only [M_bind_assoc]
      refine WS.bind' (ws_getDl tk n.toInt (by omega) (by simp only [tk_arr_setArr]; omega))
        fun v e1 ⟨hv0, he1⟩ => ?_
      subst e1
      have hv' : v = orig[m]!.dl := by simpa only [tk_arr_setArr, hnN, hdl] using hv0
      subst v
      simp only [tk_arr_setArr, hnN, hdl]
      have hlenInt : (u16i orig[m]!.dl).toInt = len m := u16i_toInt _
      by_cases hz : orig[m]!.dl = 0
      · have hzero : (u16i orig[m]!.dl == 0) = true := by simp [hz, u16i]
        simp only [hzero, Bool.true_eq, ite_true, M_pure_bind]
        refine WS.bind' (ws_iadd n 1 (by have : (1 : Int32).toInt = 1 := rfl; omega)
          (by have : (1 : Int32).toInt = 1 := rfl; omega)) fun n' e1 ⟨hn', he1⟩ => ?_
        subst e1
        refine WS.pure' ⟨⟨m + 1, a, by omega, by dsimp; have : (1 : Int32).toInt = 1 := rfl; omega,
          rfl, hsz, hnc, ?_, ?_⟩, by dsimp; have : (1 : Int32).toInt = 1 := rfl; omega⟩
        · intro b hb1 hb2
          have hlzero : len m = 0 := by dsimp [len]; rw [hz]; rfl
          rw [Math.countBefore_succ, if_neg (by omega), Nat.add_zero]
          exact hv b hb1 hb2
        · intro j hj
          rw [ha j hj]
          dsimp only [entry]
          by_cases heq : j = m
          · subst j; simp [hz]
          · have hcut : (j < m) ↔ (j < m + 1) := by omega
            simp only [hcut]
      · have hlenPos : 1 ≤ len m := by
          have h0 : orig[m]!.dl.toNat ≠ 0 := fun h => hz (UInt16.toNat_inj.mp h)
          dsimp only [len]; omega
        have hnonzero : (u16i orig[m]!.dl == 0) = false := by
          simp only [beq_eq_false_iff_ne]
          intro h; have hh := congrArg Int32.toInt h
          rw [hlenInt] at hh; have : (0 : Int32).toInt = 0 := rfl; omega
        have hbad : ¬ nc.size ≤ (u16i orig[m]!.dl).toInt.toNat := by omega
        simp only [hnonzero, Bool.false_eq_true, ite_false, hbad]
        have hli : (u16i orig[m]!.dl).toInt.toNat = len m := by omega
        rw [hli]
        let X := Math.nextCode bl (len m) + Math.countBefore len (len m) m
        have hncval : nc[len m]! = UInt16.ofNat X := hv (len m) hlenPos (by omega)
        obtain ⟨r, hr, hrv⟩ := Out.bi_reverse_correct (setD h0 id (tk.setArr d a))
          nc[len m]!.toUInt32 (u16i orig[m]!.dl) (by omega) (by omega)
        have hcode : r.toNat = Math.storedCode bl len m := by
          rw [hrv, hli, hncval, UInt16.toNat_toUInt32, UInt16.toNat_ofNat', gc_reverse_eq]
          change Math.reverseLowBits (X % 2 ^ 16) (len m) = Math.reverseLowBits X (len m)
          exact Math.reverseLowBits_mod_of_le X (len m) 16 (by omega)
        simp only [M_bind_assoc, M_pure_bind]
        have hrev : WS h0 id (bi_reverse nc[len m]!.toUInt32 (u16i orig[m]!.dl))
            (tk.setArr d a) (fun v e => v = r ∧ e = tk.setArr d a) := WS.of_eq hr ⟨rfl, rfl⟩
        refine WS.bind' hrev
          fun r' e1 ⟨hr', he1⟩ => ?_
        subst e1; subst r'
        refine WS.bind' (ws_setFc tk n.toInt r.toUInt16 (by omega)
          (by simp only [tk_arr_setArr]; omega)) fun _ e1 he1 => ?_
        subst e1
        simp only [tk_arr_setArr, hnN, gc_setArr_twice]
        refine WS.bind' (ws_iadd n 1 (by have : (1 : Int32).toInt = 1 := rfl; omega)
          (by have : (1 : Int32).toInt = 1 := rfl; omega)) fun n' e1 ⟨hn', he1⟩ => ?_
        subst e1
        refine WS.pure' ⟨⟨m + 1, a.set! m { a[m]! with fc := r.toUInt16 }, by omega,
          by dsimp; have : (1 : Int32).toInt = 1 := rfl; omega,
          rfl, by simpa only [size_set!] using hsz,
          by simpa only [size_set!] using hnc, ?_, ?_⟩,
          by dsimp; have : (1 : Int32).toInt = 1 := rfl; omega⟩
        · intro b hb1 hb2
          dsimp only
          rw [getD_set nc (len m) b _ (by omega), Math.countBefore_succ]
          by_cases heq : len m = b
          · rw [if_pos heq, if_pos heq.symm]
            subst b
            rw [hncval]
            apply UInt16.toNat_inj.mp
            simp only [UInt16.toNat_add, UInt16.toNat_ofNat']
            change (X % 65536 + 1) % 65536 = (X + 1) % 65536
            omega
          · rw [if_neg heq, if_neg (Ne.symm heq), Nat.add_zero]
            exact hv b hb1 hb2
        · intro j hj
          have hjA : j < a.size := by simpa only [size_set!] using hj
          rw [getD_set a m j _ hmA]
          by_cases heq : j = m
          · rw [if_pos heq]
            subst j
            have hsame : a[m]! = orig[m]! := by
              rw [ha m hmA]; dsimp only [entry]; simp
            have hcv : r.toUInt16 = UInt16.ofNat (Math.storedCode bl len m) := by
              apply UInt16.toNat_inj.mp
              simp only [UInt32.toNat_toUInt16, UInt16.toNat_ofNat', hcode]
            dsimp only [entry]
            simp only [Nat.lt_succ_self, hz, ne_eq, not_false_eq_true, and_self, ite_true]
            rw [hsame, hcv]
          · rw [if_neg heq, ha j hjA]
            dsimp only [entry]
            have hcut : (j < m) ↔ (j < m + 1) := by omega
            simp only [hcut]
    · refine Or.inl ⟨by simp only [decide_eq_false_iff_not]; omega,
        a, rfl, hsz, ?_⟩
      intro j hj
      have hmM : m = M := by omega
      simpa only [hmM] using ha j hj
  · intro b h1 h2
    simpa only [Math.countBefore_zero, Nat.add_zero] using hstart b h1 h2
  · intro j hj
    dsimp only [entry]
    simp

/-- `gen_codes` composes its two actual loops on one state. All lengths and
all fields outside the selected tree's code cells are preserved. -/
theorem ws_gen_codes {h0 : Heap} {id : Nat} (d : DeflateState) (tk : TK)
    (max_code : Int32) (hbc : 15 ≤ d.bl_count.size)
    (hm0 : -1 ≤ max_code.toInt) (hm1 : max_code.toInt < 573)
    (hfit : (max_code.toInt + 1).toNat ≤ (tk.arr d).size)
    (hlen : ∀ j < (max_code.toInt + 1).toNat, ((tk.arr d)[j]!).dl.toNat ≤ 15) :
    WS h0 id (gen_codes (.ref (tk.ref id) 0) max_code (.ref (.dstate_bl_count id) 0)) d
      (fun _ e => ∃ a : Array CtData, e = tk.setArr d a ∧ a.size = (tk.arr d).size ∧
        ∀ j < a.size, a[j]! =
          if j < (max_code.toInt + 1).toNat ∧ ((tk.arr d)[j]!).dl ≠ 0 then
            { (tk.arr d)[j]! with fc := UInt16.ofNat (Math.storedCode
              (fun i => d.bl_count[i]!.toNat) (fun i => ((tk.arr d)[i]!).dl.toNat) j) }
          else (tk.arr d)[j]!) := by
  rw [gen_codes_eq]
  refine WS.bind' (gcStart_run d hbc) fun r e ⟨he, hsz, hv⟩ => ?_
  subst e
  rcases r with ⟨bits, code, nc⟩
  dsimp only at hsz hv ⊢
  refine WS.bind' (gcAssign_run d tk max_code nc hm0 hm1 hfit hlen hsz hv) fun _ e he => ?_
  exact WS.pure' he

/-- `local void gen_codes(ct_data *tree, int max_code, ushf *bl_count)`.
For any of the three live dynamic tree arrays, an internal symbol range
`-1 ≤ max_code < 573` fitting that array, at least fifteen readable counts,
and code lengths at most fifteen, the actual translated function terminates
without a fault. Every positive-length symbol receives its canonical code
in reversed bit order. Only those code cells change. No consistency or Kraft
condition on the counts and lengths is assumed. This is an internal callee
result; its preconditions still have to be established by `build_tree`. -/
theorem gen_codes_correct {h : Heap} {id : Nat} {d : DeflateState}
    (hd : h.dstates id = some d) (tk : TK) (max_code : Int32)
    (hbc : 15 ≤ d.bl_count.size) (hm0 : -1 ≤ max_code.toInt) (hm1 : max_code.toInt < 573)
    (hfit : (max_code.toInt + 1).toNat ≤ (tk.arr d).size)
    (hlen : ∀ j < (max_code.toInt + 1).toNat, ((tk.arr d)[j]!).dl.toNat ≤ 15) :
    ∃ a : Array CtData,
      gen_codes (.ref (tk.ref id) 0) max_code (.ref (.dstate_bl_count id) 0) h =
        .ok ((), setD h id (tk.setArr d a)) ∧
      a.size = (tk.arr d).size ∧ ∀ j < a.size, a[j]! =
        if j < (max_code.toInt + 1).toNat ∧ ((tk.arr d)[j]!).dl ≠ 0 then
          { (tk.arr d)[j]! with fc := UInt16.ofNat (Math.storedCode
            (fun i => d.bl_count[i]!.toNat) (fun i => ((tk.arr d)[i]!).dl.toNat) j) }
        else (tk.arr d)[j]! := by
  obtain ⟨u, e, hr, a, rfl, hsz, hv⟩ := ws_gen_codes (h0 := h) (id := id) d tk max_code hbc hm0 hm1 hfit hlen
  cases u
  rw [setD_self hd] at hr
  exact ⟨a, hr, hsz, hv⟩

end Zlib.Trees.Proofs
