import ZlibF.Zlib.«inftrees.c.proofs.base»

namespace Zlib.Inftrees.Proofs
open C Zlib.Inftrees

/-- Everything the main loop of `inflate_table` reads and never changes. `hb` is the heap before the loop (after the
sort); inside the loop the heap is `hb` with the table array replaced. -/
structure Env where
  c : Ctx
  f : Nat → Nat
  n : Nat
  R : Nat
  cap : Nat
  rc : CodeRef
  oc : Nat
  rw : WRef
  ow : Nat
  rl : WRef
  ol : Nat
  hb : Heap
  la : Array UInt16
  wa : Array UInt16
  h_table : c.table = .ref rc oc
  h_lens : c.lens = .ref rl ol
  h_work : c.work = .ref rw ow
  h_ro : Space.ro hb rc = false
  h_live : ∃ ca0, Space.get hb rc = some ca0
  h_get_la : Space.get hb rl = some la
  h_get_wa : Space.get hb rw = some wa
  h_f : ∀ k, f k = (la.getD (ol + k) 0).toNat
  h_la : ol + n ≤ la.size
  h_f15 : ∀ k, k < n → f k ≤ 15
  h_wa : ow + n ≤ wa.size
  h_wcont : ∀ i, i < Tc f n 15 → wa[ow + i]? = some (UInt16.ofNat ((wsAux f n 15).getD i 0))
  h_n : n ≤ 288
  h_root : c.root.toNat = R
  h_max : c.max.toNat = mxl f n
  h_R1 : 1 ≤ R
  h_Rmx : R ≤ mxl f n
  h_R0 : lenAt f n 0 ≤ R
  h_pos : 0 < Tc f n 15
  h_fits : Fits f n
  h_end : Kc f n 15 = 2 ^ 15 ∨ (mxl f n = 1 ∧ Tc f n 15 = 1 ∧ c.type ≠ CODES)
  h_type : c.type = CODES ∨ c.type = LENS ∨ c.type = DISTS
  h_cap : cap = (if c.type = CODES then 128 else if c.type = LENS then 852 else 592)
  h_codes : c.type = CODES → mxl f n ≤ 7 ∧ R = mxl f n ∧ n ≤ 19 ∧ c.match_ = 20
  h_lens' : c.type = LENS → n ≤ 288 ∧ c.base = lbase ∧ c.extra = lext ∧ c.match_ = 257
  h_dists : c.type = DISTS → n ≤ 32 ∧ c.base = dbase ∧ c.extra = dext ∧ c.match_ = 0

namespace Env
def m (e : Env) : Nat := Tc e.f e.n 15
def l (e : Env) (i : Nat) : Nat := lenAt e.f e.n i
def v (e : Env) (i : Nat) : Nat := val e.f e.n i
def p (e : Env) (i : Nat) : Nat := pre e.f e.n e.R i
def mx (e : Env) : Nat := mxl e.f e.n
/-- The heap inside the loop: the table array is `ca`. -/
def hc (e : Env) (ca : Array Code) : Heap := Space.put e.hb e.rc ca
end Env

/-- `count[l]` is the number of symbols of length `l` that are still to be coded. -/
def CountOK (e : Env) (count : Array UInt16) (i : Nat) : Prop :=
  count.size = 16 ∧ ∀ l, 1 ≤ l → l ≤ 15 → (count.getD l 0).toNat = rem e.f e.n i l

/-- The state of the table that the main loop keeps while it handles the `i`-th code. -/
def TabSt (e : Env) (i : Nat) (s : TS) : Prop :=
  (∃ k, s.next = .ref e.rc (e.oc + k) ∧ k + 2 ^ s.curr.toNat = s.used.toNat) ∧
  s.used.toNat ≤ e.cap ∧ 2 ^ e.R ≤ s.used.toNat ∧ 1 ≤ s.curr.toNat ∧ s.curr.toNat ≤ 15 ∧
  (e.l i ≤ e.R → s.drop = 0 ∧ s.low = 0xffffffff ∧ s.curr.toNat = e.R ∧ s.used.toNat = 2 ^ e.R) ∧
  (e.R < e.l i → s.drop.toNat = e.R ∧ s.low.toNat = rev e.R (e.p i) ∧ e.l i ≤ e.R + s.curr.toNat ∧
    e.R + s.curr.toNat ≤ e.mx ∧
    ∀ j, j < e.m → e.R < e.l j → e.p j = e.p i → e.l j ≤ e.R + s.curr.toNat)

/-- The invariant of the main loop at the top of the iteration for the `i`-th code. -/
def MI (e : Env) (i : Nat) (s : TS) (ca : Array Code) : Prop :=
  i < e.m ∧ s.exit = 0 ∧ s.sym.toNat = i ∧ s.len.toNat = e.l i ∧ s.huff.toNat = rev (e.l i) (e.v i) ∧
  s.mask.toNat = 2 ^ e.R - 1 ∧ CountOK e s.count i ∧ e.oc + e.cap ≤ ca.size ∧ TabSt e i s

/-- After the new `huff` is computed and before `sym++`. -/
def MI1 (e : Env) (i : Nat) (s : TS) (ca : Array Code) : Prop :=
  i < e.m ∧ s.exit = 0 ∧ s.sym.toNat = i ∧ s.len.toNat = e.l i ∧
  (i + 1 < e.m → s.huff.toNat = rev (e.l (i + 1)) (e.v (i + 1))) ∧
  (i + 1 = e.m → s.huff.toNat = 0 ∨ s.huff.toNat < 2 ^ s.curr.toNat) ∧
  s.mask.toNat = 2 ^ e.R - 1 ∧ CountOK e s.count i ∧ e.oc + e.cap ≤ ca.size ∧ TabSt e i s ∧
  s.min.toNat = 2 ^ s.curr.toNat

/-- After `sym++`, the count and the new length, before the test for a new sub-table. -/
def MI2 (e : Env) (i : Nat) (s : TS) (ca : Array Code) : Prop :=
  i + 1 < e.m ∧ s.exit = 0 ∧ s.sym.toNat = i + 1 ∧ s.len.toNat = e.l (i + 1) ∧
  s.huff.toNat = rev (e.l (i + 1)) (e.v (i + 1)) ∧
  s.mask.toNat = 2 ^ e.R - 1 ∧ CountOK e s.count (i + 1) ∧ e.oc + e.cap ≤ ca.size ∧ TabSt e i s ∧
  s.min.toNat = 2 ^ s.curr.toNat

/-- The state after the last code: what the final store and the pointer advance need. -/
def Final (e : Env) (s : TS) : Prop :=
  (∃ k, s.next = .ref e.rc (e.oc + k) ∧ k + 2 ^ s.curr.toNat = s.used.toNat) ∧
  s.used.toNat ≤ e.cap ∧ (s.huff.toNat = 0 ∨ s.huff.toNat < 2 ^ s.curr.toNat)

/-- The table array changes only inside the space the caller gave. -/
def FrameCA (e : Env) (ca ca' : Array Code) : Prop :=
  ca'.size = ca.size ∧ ∀ x, (x < e.oc ∨ e.oc + e.cap ≤ x) → ca'[x]? = ca[x]?

def StepPost (e : Env) (i : Nat) (s' : TS) (ca' : Array Code) : Prop :=
  (i + 1 < e.m ∧ MI e (i + 1) s' ca') ∨ (i + 1 = e.m ∧ s'.exit = 1 ∧ Final e s' ∧ e.oc + e.cap ≤ ca'.size) ∨
  (s'.exit = 2 ∧ e.c.type ≠ CODES ∧ e.oc + e.cap ≤ ca'.size)

theorem Env.get_hc (e : Env) (ca : Array Code) : Space.get (e.hc ca) e.rc = some ca := by
  obtain ⟨ca0, h0⟩ := e.h_live
  exact cget_put_self h0 e.h_ro ca

theorem Env.get_wa (e : Env) (ca : Array Code) : Space.get (e.hc ca) e.rw = some e.wa := by
  unfold Env.hc; rw [wget_put_code]; exact e.h_get_wa

theorem Env.get_la (e : Env) (ca : Array Code) : Space.get (e.hc ca) e.rl = some e.la := by
  unfold Env.hc; rw [wget_put_code]; exact e.h_get_la

theorem Env.hc_hc (e : Env) (ca ca' : Array Code) : Space.put (e.hc ca) e.rc ca' = e.hc ca' := by
  unfold Env.hc; rw [cput_put]

theorem i32_ofInt_toInt {v : Int} (h1 : -2147483648 ≤ v) (h2 : v ≤ 2147483647) : (Int32.ofInt v).toInt = v := by
  rw [Int32.toInt_ofInt]
  simp only [Int32.size, Int.bmod]
  omega

theorem i32_le_zero {x : Int32} : x ≤ 0 ↔ x.toInt ≤ 0 := by
  rw [Int32.le_iff_toInt_le, Int32.toInt_zero]

theorem u32_succ {x : UInt32} (h : x.toNat < 1000000) : (x + 1).toNat = x.toNat + 1 := by
  rw [u32_add (by simp [UInt32.toNat_one]; omega)]; simp [UInt32.toNat_one]

def sizeCond (drop mx : UInt32) : UInt32 × Int32 × Bool → M (Bool × (UInt32 × Int32 × Bool)) :=
  fun x => match x with | (curr, left, brk) => pure (!brk && decide (curr + drop < mx), (curr, left, brk))

def sizeBody (count : Array UInt16) (drop : UInt32) : UInt32 × Int32 × Bool → M (UInt32 × Int32 × Bool) :=
  fun x => match x with
    | (curr, left, brk) => do
      let cc ← geta count (curr + drop).toNat
      let left ← chk32 (left.toInt - cc.toNat)
      if left ≤ 0 then pure (curr, left, true)
      else
        let curr := curr + 1
        let left ← chk32 (left.toInt * 2)
        pure (curr, left, brk)

theorem sizeBody_eq (count : Array UInt16) (drop curr : UInt32) (left : Int32) (brk : Bool)
    (hi : (curr + drop).toNat < count.size)
    (hv1 : -2147483648 ≤ left.toInt - (count[(curr + drop).toNat]).toNat)
    (hv2 : left.toInt - (count[(curr + drop).toNat]).toNat ≤ 2147483647)
    (hv3 : left.toInt - (count[(curr + drop).toNat]).toNat ≤ 0 ∨
      (-2147483648 ≤ (left.toInt - (count[(curr + drop).toNat]).toNat) * 2 ∧
        (left.toInt - (count[(curr + drop).toNat]).toNat) * 2 ≤ 2147483647)) :
    sizeBody count drop (curr, left, brk) =
      pure (if left.toInt - (count[(curr + drop).toNat]).toNat ≤ 0 then
              (curr, Int32.ofInt (left.toInt - (count[(curr + drop).toNat]).toNat), true)
            else (curr + 1, Int32.ofInt ((left.toInt - (count[(curr + drop).toNat]).toNat) * 2), brk)) := by
  simp only [sizeBody]
  rw [geta_eq hi, M_pure_bind, chk32_eq hv1 hv2, M_pure_bind]
  generalize hv : left.toInt - (count[(curr + drop).toNat]).toNat = v at *
  have hle : (Int32.ofInt v ≤ 0) ↔ v ≤ 0 := by rw [i32_le_zero, i32_ofInt_toInt hv1 hv2]
  by_cases h0 : v ≤ 0
  · rw [if_pos (hle.mpr h0), if_pos h0]
  · rw [if_neg (fun hh => h0 (hle.mp hh)), if_neg h0]
    have : -2147483648 ≤ v * 2 ∧ v * 2 ≤ 2147483647 := by
      rcases hv3 with h | h
      · exact absurd h h0
      · exact h
    rw [i32_ofInt_toInt hv1 hv2, chk32_eq this.1 this.2, M_pure_bind]

/-- The sub-table sizing loop of `inflate_table`, run on the count array of the symbols that are still to be coded. -/
theorem size_loop (e : Env) (i0 : Nat) (count : Array UInt16) (drop mx curr0 : UInt32) (left0 : Int32) (h : Heap)
    (hcnt : CountOK e count i0) (hdrop : drop.toNat = e.R) (hmx : mx.toNat = e.mx) (hR : e.R < e.l i0)
    (hc0 : curr0.toNat = e.l i0 - e.R) (hl0 : left0.toInt = 2 ^ curr0.toNat) (hi0 : i0 < e.m) :
    Wp (cwhile (sizeCond drop mx) (sizeBody count drop) (curr0, left0, false)) h
      (fun r h' => h' = h ∧ r.1.toNat = currOf e.f e.n e.R i0) := by
  have hmxle : e.mx ≤ 15 := by
    have := lenAt_bounds (f := e.f) (n := e.n) (show e.m - 1 < Tc e.f e.n 15 by have := e.h_pos; unfold Env.m; omega)
    exact this.2
  have hlmx : e.l i0 ≤ e.mx := lenAt_mono (f := e.f) (n := e.n) (show i0 ≤ Tc e.f e.n 15 - 1 by
    have : i0 < e.m := hi0
    unfold Env.m at this; omega) (by have := e.h_pos; omega)
  have hR1 := e.h_R1
  let T0 := SL (rem e.f e.n i0) e.R e.mx curr0.toNat left0.toInt
  have hT0 : currOf e.f e.n e.R i0 = T0.1 := by
    show (SL (rem e.f e.n i0) e.R e.mx (e.l i0 - e.R) ((2 ^ (e.l i0 - e.R) : Nat) : Int)).1 = T0.1
    have : (curr0.toNat) = e.l i0 - e.R := hc0
    simp only [T0, hl0, this]
    push_cast; rfl
  have hge1 : 1 ≤ e.l i0 - e.R := by omega
  refine Wp.cwhile
    (fun (x : UInt32 × Int32 × Bool) h' => h' = h ∧ x.1.toNat + e.R ≤ e.mx ∧
      (x.2.2 = false → 0 < x.2.1.toInt ∧ x.2.1.toInt ≤ 2 ^ x.1.toNat ∧
          SL (rem e.f e.n i0) e.R e.mx x.1.toNat x.2.1.toInt = T0) ∧
      (x.2.2 = true → (x.1.toNat, x.2.1.toInt) = T0))
    (fun (x : UInt32 × Int32 × Bool) => if x.2.2 then 0 else e.mx - e.R - x.1.toNat + 1)
    (fun (x : UInt32 × Int32 × Bool) h' => h' = h ∧ x.1.toNat = currOf e.f e.n e.R i0) ?_ ?_ ?_
  · rintro ⟨curr, left, brk⟩ h' ⟨hh, hb, hnb, hbk⟩
    simp only at hb hnb hbk
    by_cases hc : (!brk && decide (curr + drop < mx)) = true
    · right
      simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hc
      obtain ⟨hbrk, hlt0⟩ := hc
      have hlt : curr.toNat + e.R < e.mx := by
        simp only [UInt32.lt_iff_toNat_lt] at hlt0
        rw [u32_add (by have := UInt32.toNat_lt curr; omega)] at hlt0
        omega
      obtain ⟨hp, hle, hsl⟩ := hnb hbrk
      have hidx : (curr + drop).toNat = curr.toNat + e.R := by
        rw [u32_add (by have := UInt32.toNat_lt curr; have := UInt32.toNat_lt drop; omega), hdrop]
      have hlt16 : (curr + drop).toNat < count.size := by rw [hcnt.1, hidx]; omega
      have hcc : (count[(curr + drop).toNat]).toNat = rem e.f e.n i0 (curr.toNat + e.R) := by
        have key := hcnt.2 (curr + drop).toNat (by omega) (by omega)
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hlt16] at key
        rw [← hidx]
        simpa using key
      have hccle : (count[(curr + drop).toNat]).toNat < 65536 := UInt16.toNat_lt _
      have hpow : ((2:Int) ^ curr.toNat) ≤ 16384 := by
        have h14 : 2 ^ curr.toNat ≤ 2 ^ 14 := Nat.pow_le_pow_right (by omega) (by omega)
        have : ((2 ^ curr.toNat : Nat) : Int) ≤ ((2 ^ 14 : Nat) : Int) := Int.ofNat_le.mpr h14
        simpa [Int.natCast_pow] using this
      have e1 := sizeBody_eq count drop curr left brk hlt16 (by omega) (by omega) (by omega)
      have hsl' := hsl
      rw [SL_lt (show e.R + curr.toNat < e.mx by omega), show e.R + curr.toNat = curr.toNat + e.R by omega, ← hcc] at hsl'
      have hrun : sizeBody count drop (curr, left, brk) h' = .ok
          ((if left.toInt - (count[(curr + drop).toNat]).toNat ≤ 0 then
              (curr, Int32.ofInt (left.toInt - (count[(curr + drop).toNat]).toNat), true)
            else (curr + 1, Int32.ofInt ((left.toInt - (count[(curr + drop).toNat]).toNat) * 2), brk)), h') := by
        rw [e1]; rfl
      have hcond : sizeCond drop mx (curr, left, brk) h' = .ok ((true, (curr, left, brk)), h') := by
        simp only [sizeCond]
        show (pure ((!brk && decide (curr + drop < mx)), (curr, left, brk)) : M _) h' = _
        rw [show ((!brk && decide (curr + drop < mx))) = true from by
          simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq]; exact ⟨hbrk, hlt0⟩]
        rfl
      generalize hvd : left.toInt - (count[(curr + drop).toNat]).toNat = v at *
      have hr1 : -2147483648 ≤ v := by omega
      have hr2 : v ≤ 2147483647 := by omega
      have hp2 : (2:Int) ^ (curr.toNat + 1) = 2 ^ curr.toNat * 2 := Int.pow_succ _ _
      refine ⟨(curr, left, brk), h', _, h', hcond, hrun, ?_, ?_⟩
      · by_cases hv : v ≤ 0
        · rw [if_pos hv]
          refine ⟨hh, by omega, fun hx => by simp at hx, fun _ => ?_⟩
          rw [if_pos hv] at hsl'
          simp only []
          rw [i32_ofInt_toInt hr1 hr2]
          exact hsl'
        · rw [if_neg hv]
          have hcu : (curr + 1).toNat = curr.toNat + 1 := u32_succ (by omega)
          have hr3 : -2147483648 ≤ v * 2 := by omega
          have hr4 : v * 2 ≤ 2147483647 := by omega
          refine ⟨hh, by rw [hcu]; omega, fun _ => ?_, fun hx => by simp [hbrk] at hx⟩
          simp only []
          rw [hcu, i32_ofInt_toInt hr3 hr4]
          refine ⟨by omega, by omega, ?_⟩
          rw [if_neg hv] at hsl'
          exact hsl'
      · by_cases hv : v ≤ 0
        · rw [if_pos hv]; simp [hbrk] <;> omega
        · rw [if_neg hv]
          have hcu : (curr + 1).toNat = curr.toNat + 1 := u32_succ (by omega)
          simp [hbrk, hcu] <;> omega
    · left
      have hcond : sizeCond drop mx (curr, left, brk) h' = .ok ((false, (curr, left, brk)), h') := by
        simp only [sizeCond]
        show (pure ((!brk && decide (curr + drop < mx)), (curr, left, brk)) : M _) h' = _
        have : ((!brk && decide (curr + drop < mx))) = false := by
          cases hb2 : ((!brk && decide (curr + drop < mx)))
          · rfl
          · exact absurd hb2 hc
        rw [this]; rfl
      refine ⟨(curr, left, brk), h', hcond, hh, ?_⟩
      rw [hT0]
      cases hbrk : brk
      · have hn : ¬ (curr + drop < mx) := by
          intro hlt0
          apply hc
          simp [hbrk, hlt0]
        simp only [UInt32.lt_iff_toNat_lt] at hn
        rw [u32_add (by have := UInt32.toNat_lt curr; omega)] at hn
        obtain ⟨hp, hle, hsl⟩ := hnb hbrk
        rw [SL_ge (by omega)] at hsl
        rw [← hsl]
      · have := hbk hbrk
        rw [← this]
  · dsimp only
    refine ⟨rfl, by omega, fun _ => ⟨?_, ?_, rfl⟩, fun hx => by simp at hx⟩
    · rw [hl0]; exact_mod_cast (Nat.pow_pos (by omega : 0 < 2) : 0 < 2 ^ curr0.toNat)
    · rw [hl0]; exact Int.le_refl _
  · show (if false = true then 0 else e.mx - e.R - curr0.toNat + 1) < fuel
    simp only [Bool.false_eq_true, ite_false]
    exact lt_fuel (by omega)

theorem Wp.pure_eq {α : Type} {m : M α} {a : α} {h : Heap} {Q : α → Heap → Prop} (e : m = pure a) (hq : Q a h) :
    Wp m h Q := ⟨a, h, by rw [e]; rfl, hq⟩

theorem wp_add (e : Env) (ca : Array Code) (off n : Nat) (hn : off + n ≤ ca.size) :
    Wp (Ptr.add (Ptr.ref e.rc off) (n : Int)) (e.hc ca) (fun q h' => q = Ptr.ref e.rc (off + n) ∧ h' = e.hc ca) :=
  Wp.of_eq (Ptr.add_nat_ok (e.get_hc ca) hn) ⟨rfl, rfl⟩

/-- `q = table + low; e = *q; *q = F e; K` -/
theorem wp_update {β : Type} (e : Env) (ca : Array Code) (low : Nat) (F : Code → Code) (hlow : e.oc + low < ca.size)
    (K : M β) (Q : β → Heap → Prop)
    (hK : ∀ ca1, ca1 = ca.set! (e.oc + low) (F ca[e.oc + low]) → Wp K (e.hc ca1) Q) :
    Wp (do
        let q ← Ptr.add (Ptr.ref e.rc e.oc) (low : Int)
        let x ← Ptr.load q
        Ptr.store q (F x)
        K) (e.hc ca) Q := by
  apply Wp.bind' (wp_add e ca e.oc low (by omega))
  rintro q h' ⟨rfl, rfl⟩
  apply Wp.bind' (Q := fun x h' => x = ca[e.oc + low] ∧ h' = e.hc ca)
  · exact Wp.of_eq (Ptr.load_ok (e.get_hc ca) hlow) ⟨rfl, rfl⟩
  · rintro x h' ⟨rfl, rfl⟩
    apply Wp.bind' (Q := fun _ h' => h' = e.hc (ca.set! (e.oc + low) (F ca[e.oc + low])))
    · refine ⟨(), _, Ptr.store_ok (e.get_hc ca) e.h_ro (by omega), ?_⟩
      rw [Env.hc_hc]
    · rintro _ h' rfl
      exact hK _ rfl

theorem getElem?_set!_ne {α : Type} {a : Array α} {i j : Nat} {v : α} (h : i ≠ j) : (a.set! i v)[j]? = a[j]? := by
  rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]; simp [h]

theorem getElem?_set!_self {α : Type} {a : Array α} {i : Nat} {v : α} (h : i < a.size) : (a.set! i v)[i]? = some v := by
  rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]; simp [h]

theorem tooBig_ne {t u : UInt32} (h : tooBig t u = true) : t ≠ CODES := by
  intro ht
  subst ht
  simp [tooBig, CODES, LENS, DISTS] at h

theorem tooBig_le (e : Env) {u : UInt32} (h : tooBig e.c.type u = false) (hne : e.c.type ≠ CODES) :
    u.toNat ≤ e.cap := by
  have hcap := e.h_cap
  rcases e.h_type with ht | ht | ht
  · exact absurd ht hne
  · rw [ht] at h hcap
    simp only [tooBig, LENS, DISTS, CODES] at h hcap
    have h2 : ¬ (u > ENOUGH_LENS.toUInt32) := by simpa using h
    rw [UInt32.not_lt, UInt32.le_iff_toNat_le] at h2
    have : (ENOUGH_LENS.toUInt32).toNat = 852 := rfl
    simp at hcap
    omega
  · rw [ht] at h hcap
    simp only [tooBig, LENS, DISTS, CODES] at h hcap
    have h2 : ¬ (u > ENOUGH_DISTS.toUInt32) := by simpa using h
    rw [UInt32.not_lt, UInt32.le_iff_toNat_le] at h2
    have : (ENOUGH_DISTS.toUInt32).toNat = 592 := rfl
    simp at hcap
    omega

def fillBody : TS → M TS := fun s => do
  let fill := s.fill - s.incr
  let hd ← shr32 s.huff s.drop
  storeCode s.next (hd + fill).toNat s.here
  pure { s with fill }

def fillCond : TS → M (Bool × TS) := fun s => pure (s.fill != 0, s)

theorem Nat_mul_pred (S q : Nat) (hq : 1 ≤ q) : S * (q - 1) + S = S * q := by
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
  simp [Nat.mul_succ]

theorem fillBody_wp (e : Env) (s : TS) (ca1 : Array Code) (k : Nat) (hnext : s.next = .ref e.rc (e.oc + k))
    (hdrop : s.drop.toNat < 32)
    (hidx : e.oc + k + ((s.huff >>> s.drop) + (s.fill - s.incr)).toNat < ca1.size) :
    Wp (fillBody s) (e.hc ca1) (fun s1 h1 => s1 = { s with fill := s.fill - s.incr } ∧
      h1 = e.hc (ca1.set! (e.oc + k + ((s.huff >>> s.drop) + (s.fill - s.incr)).toNat) s.here)) := by
  unfold fillBody
  rw [shr32_eq hdrop]
  apply Wp.bind' (Q := fun r h' => r = s.huff >>> s.drop ∧ h' = e.hc ca1) (Wp.pure' ⟨rfl, rfl⟩)
  rintro hd h' ⟨rfl, rfl⟩
  unfold storeCode
  rw [hnext]
  apply Wp.bind' (Q := fun _ h' => h' = e.hc (ca1.set! (e.oc + k + ((s.huff >>> s.drop) + (s.fill - s.incr)).toNat) s.here))
  · apply Wp.bind' (wp_add e ca1 (e.oc + k) ((s.huff >>> s.drop) + (s.fill - s.incr)).toNat (by omega))
    rintro q h' ⟨rfl, rfl⟩
    refine ⟨(), _, Ptr.store_ok (e.get_hc ca1) e.h_ro (by omega), ?_⟩
    rw [Env.hc_hc]
  · rintro _ h' rfl
    exact Wp.pure' ⟨rfl, rfl⟩

/-- The `do ... while (fill != 0)` loop that writes a code into the table: `S = 2^b` is the stride, `N` the number
of copies, `fill` starts at `S * N`. -/
theorem fill_loop (e : Env) (s0 : TS) (ca : Array Code) (S N k hd : Nat)
    (hnext : s0.next = .ref e.rc (e.oc + k)) (hS : s0.incr.toNat = S) (hF : s0.fill.toNat = S * N)
    (hN : 1 ≤ N) (hSpos : 1 ≤ S) (hhd : (s0.huff >>> s0.drop).toNat = hd) (hhdS : hd < S)
    (hdrop : s0.drop.toNat < 32) (hk : k + S * N ≤ e.cap) (hsz : e.oc + e.cap ≤ ca.size) :
    Wp (cdoWhile fillBody fillCond s0) (e.hc ca) (fun s' h' => ∃ ca', h' = e.hc ca' ∧
      s' = { s0 with fill := 0 } ∧ ca'.size = ca.size ∧
      (∀ x, (∃ q', q' < N ∧ x = e.oc + k + hd + S * q') → ca'[x]? = some s0.here) ∧
      (∀ x, ¬ (∃ q', q' < N ∧ x = e.oc + k + hd + S * q') → ca'[x]? = ca[x]?)) := by
  refine Wp.cdoWhile
    (fun (s : TS) h' => ∃ q ca1, 1 ≤ q ∧ q ≤ N ∧ s = { s0 with fill := UInt32.ofNat (S * q) } ∧ h' = e.hc ca1 ∧
      ca1.size = ca.size ∧
      (∀ x, (∃ q', q ≤ q' ∧ q' < N ∧ x = e.oc + k + hd + S * q') → ca1[x]? = some s0.here) ∧
      (∀ x, ¬ (∃ q', q ≤ q' ∧ q' < N ∧ x = e.oc + k + hd + S * q') → ca1[x]? = ca[x]?))
    (fun (s : TS) => s.fill.toNat) _ ?_ ?_ ?_
  · rintro s h' ⟨q, ca1, hq1, hqN, rfl, rfl, hp0, hp1, hp2⟩
    dsimp only
    have hSq : S * q ≤ S * N := Nat.mul_le_mul_left S hqN
    have hSq' := Nat_mul_pred S q hq1
    have hlt32 : S * q < 2 ^ 32 := by
      have : s0.fill.toNat < 2 ^ 32 := UInt32.toNat_lt _
      omega
    have hfill : (UInt32.ofNat (S * q)).toNat = S * q := by
      rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt hlt32]
    have hsub : (UInt32.ofNat (S * q) - s0.incr).toNat = S * (q - 1) := by
      rw [u32_sub (by rw [hfill, hS]; omega), hfill, hS]; omega
    have hidx : e.oc + k + hd + S * (q - 1) < e.oc + k + S * N := by omega
    have hidx2 : e.oc + k + hd + S * (q - 1) < ca1.size := by omega
    obtain ⟨s1, h1, hrun, hs1, hh1⟩ := fillBody_wp e { s0 with fill := UInt32.ofNat (S * q) } ca1 k hnext hdrop
      (by
        show e.oc + k + ((s0.huff >>> s0.drop) + (UInt32.ofNat (S * q) - s0.incr)).toNat < ca1.size
        have : (s0.huff >>> s0.drop + (UInt32.ofNat (S * q) - s0.incr)).toNat = hd + S * (q - 1) := by
          rw [u32_add (by rw [hsub, hhd]; omega), hsub, hhd]
        omega)
    have hidxv : ((s0.huff >>> s0.drop) + (UInt32.ofNat (S * q) - s0.incr)).toNat = hd + S * (q - 1) := by
      rw [u32_add (by rw [hsub, hhd]; omega), hsub, hhd]
    simp only [] at hs1 hh1
    rw [hidxv] at hh1
    refine ⟨s1, h1, hrun, ?_⟩
    have hPlt : e.oc + k + (hd + S * (q - 1)) < ca1.size := by omega
    have hnew : ∀ ca2 : Array Code, ca2 = ca1.set! (e.oc + k + (hd + S * (q - 1))) s0.here →
        ca2.size = ca.size ∧
        (∀ x, (∃ q', q - 1 ≤ q' ∧ q' < N ∧ x = e.oc + k + hd + S * q') → ca2[x]? = some s0.here) ∧
        (∀ x, ¬ (∃ q', q - 1 ≤ q' ∧ q' < N ∧ x = e.oc + k + hd + S * q') → ca2[x]? = ca[x]?) := by
      intro ca2 h2
      refine ⟨by rw [h2, Array.size_set!]; exact hp0, ?_, ?_⟩
      · rintro x ⟨q', hq1', hq2', hx⟩
        by_cases hxP : x = e.oc + k + (hd + S * (q - 1))
        · rw [h2, hxP]; exact getElem?_set!_self hPlt
        · have hq'q : q ≤ q' := by
            apply Classical.byContradiction; intro hcon
            apply hxP
            have : q' = q - 1 := by omega
            rw [hx, this]; omega
          rw [h2, getElem?_set!_ne (Ne.symm hxP)]
          exact hp1 x ⟨q', hq'q, hq2', hx⟩
      · intro x hx
        have hxP : x ≠ e.oc + k + (hd + S * (q - 1)) := by
          intro hxx; apply hx; exact ⟨q - 1, Nat.le_refl _, by omega, by omega⟩
        rw [h2, getElem?_set!_ne (Ne.symm hxP)]
        apply hp2
        rintro ⟨q', hq1', hq2', hx'⟩
        exact hx ⟨q', by omega, hq2', hx'⟩
    by_cases hq : q = 1
    · subst hq
      left
      have hfz : (UInt32.ofNat (S * 1) - s0.incr) = 0 := by
        apply UInt32.toNat_inj.mp
        rw [hsub]; simp
      refine ⟨s1, h1, ?_, _, hh1, ?_, (hnew _ rfl).1, ?_, ?_⟩
      · rw [hs1]; simp only [fillCond, hfz]; rfl
      · rw [hs1, hfz]
      · exact fun x ⟨q', h2, h3⟩ => (hnew _ rfl).2.1 x ⟨q', by omega, h2, h3⟩
      · exact fun x hx => (hnew _ rfl).2.2 x (fun ⟨q', h2, h3, h4⟩ => hx ⟨q', h3, h4⟩)
    · right
      have hfnz : (UInt32.ofNat (S * q) - s0.incr) ≠ 0 := by
        intro h0
        have := congrArg UInt32.toNat h0
        rw [hsub] at this
        simp at this
        have hpos : 0 < S * (q - 1) := Nat.mul_pos (by omega) (by omega)
        omega
      refine ⟨s1, h1, ?_, ?_, ?_⟩
      · rw [hs1]; simp only [fillCond]
        have : ((UInt32.ofNat (S * q) - s0.incr) != 0) = true := by simpa using hfnz
        rw [this]; rfl
      · refine ⟨q - 1, _, by omega, by omega, ?_, hh1, (hnew _ rfl).1, (hnew _ rfl).2.1, (hnew _ rfl).2.2⟩
        rw [hs1]
        have : UInt32.ofNat (S * (q - 1)) = UInt32.ofNat (S * q) - s0.incr := by
          apply UInt32.toNat_inj.mp
          rw [hsub, UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
        rw [this]
      · rw [hs1]
        simp only []
        rw [hsub, hfill]
        have : 0 < S := hSpos
        have : S * (q - 1) + S = S * q := hSq'
        omega
  · refine ⟨N, ca, hN, Nat.le_refl _, ?_, rfl, rfl, ?_, ?_⟩
    · have : s0.fill = UInt32.ofNat (S * N) := by
        apply UInt32.toNat_inj.mp
        rw [hF, UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by have := UInt32.toNat_lt s0.fill; omega)]
      rw [← this]
    · rintro x ⟨q', h1, h2, _⟩; omega
    · intro x _; rfl
  · exact lt_fuel (UInt32.toNat_lt s0.fill)

theorem and_pow_zero_iff (x e : Nat) : x &&& 2 ^ e = 0 ↔ x.testBit e = false := by
  constructor
  · intro h
    have := congrArg (fun y => y.testBit e) h
    simpa [Nat.testBit_and, Nat.testBit_two_pow] using this
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_and, Nat.testBit_two_pow, Nat.zero_testBit]
    by_cases hie : e = i
    · subst hie; simp [h]
    · simp [hie]

def incrCond : TS → M (Bool × TS) := fun s => pure (s.huff &&& s.incr != 0, s)
def incrBody : TS → M TS := fun s => pure { s with incr := s.incr >>> 1 }

/-- `while (huff & incr) incr >>= 1;` started at `incr = 2^e`. -/
theorem incr_loop (s3 : TS) (e : Nat) (he : e < 32) (hi : s3.incr.toNat = 2 ^ e) (h : Heap) :
    Wp (cwhile incrCond incrBody s3) h (fun s' h' => h' = h ∧
      ∃ X : UInt32, s' = { s3 with incr := X } ∧ X.toNat = incrLoop s3.huff.toNat e) := by
  refine Wp.cwhile
    (fun (s : TS) h' => h' = h ∧ (∃ X : UInt32, s = { s3 with incr := X }) ∧
      ((∃ e', e' ≤ e ∧ s.incr.toNat = 2 ^ e' ∧ incrLoop s3.huff.toNat e' = incrLoop s3.huff.toNat e) ∨
       (s.incr = 0 ∧ incrLoop s3.huff.toNat e = 0)))
    (fun (s : TS) => s.incr.toNat) _ ?_ ?_ ?_
  · rintro s h' ⟨rfl, ⟨X, rfl⟩, hinv⟩
    dsimp only at hinv ⊢
    rcases hinv with ⟨e', he', hX, hT⟩ | ⟨hX, hT⟩
    · have hand : (s3.huff &&& X).toNat = s3.huff.toNat &&& 2 ^ e' := by rw [UInt32.toNat_and, hX]
      by_cases hb : s3.huff.toNat.testBit e' = true
      · right
        have hne : (s3.huff &&& X != 0) = true := by
          simp only [bne_iff_ne, ne_eq, ← UInt32.toNat_inj, hand]
          intro hz
          have := (and_pow_zero_iff _ _).mp hz
          rw [hb] at this; exact absurd this (by simp)
        refine ⟨{ s3 with incr := X }, h', { s3 with incr := X >>> 1 }, h', ?_, ?_, ?_, ?_⟩
        · simp only [incrCond]; rw [hne]; rfl
        · simp only [incrBody]; rfl
        · refine ⟨rfl, ⟨X >>> 1, rfl⟩, ?_⟩
          rcases Nat.eq_zero_or_pos e' with h0 | hpos
          · right
            subst h0
            refine ⟨?_, ?_⟩
            · apply UInt32.toNat_inj.mp
              rw [u32_shr (by decide), hX]; simp
            · rw [← hT]; simp [incrLoop, hb]
          · left
            refine ⟨e' - 1, by omega, ?_, ?_⟩
            · rw [u32_shr (by decide), hX]
              obtain ⟨r, rfl⟩ : ∃ r, e' = r + 1 := ⟨e' - 1, by omega⟩
              simp [Nat.pow_succ, Nat.mul_div_cancel]
            · rw [← hT]
              obtain ⟨r, rfl⟩ : ∃ r, e' = r + 1 := ⟨e' - 1, by omega⟩
              simp [incrLoop, hb]
        · dsimp only
          rw [u32_shr (by decide), hX]
          simp only [UInt32.toNat_one, Nat.pow_one]
          have : 0 < 2 ^ e' := Nat.pow_pos (by omega)
          omega
      · left
        have hb' : s3.huff.toNat.testBit e' = false := by simpa using hb
        have hz : (s3.huff &&& X != 0) = false := by
          have : (s3.huff &&& X).toNat = 0 := by rw [hand]; exact (and_pow_zero_iff _ _).mpr hb'
          have h2 : s3.huff &&& X = 0 := UInt32.toNat_inj.mp (by rw [this]; rfl)
          simp [h2]
        refine ⟨{ s3 with incr := X }, h', ?_, rfl, X, rfl, ?_⟩
        · simp only [incrCond]; rw [hz]; rfl
        · rw [← hT, hX]
          obtain ⟨r, hr⟩ : ∃ r, e' = r := ⟨e', rfl⟩
          cases e' with
          | zero => simp [incrLoop, hb']
          | succ r => simp [incrLoop, hb']
    · left
      have hz : (s3.huff &&& X != 0) = false := by simp [hX]
      refine ⟨{ s3 with incr := X }, h', ?_, rfl, X, rfl, ?_⟩
      · simp only [incrCond]; rw [hz]; rfl
      · rw [hX, hT]; rfl
  · refine ⟨rfl, ⟨s3.incr, rfl⟩, Or.inl ⟨e, Nat.le_refl _, hi, rfl⟩⟩
  · exact lt_fuel (UInt32.toNat_lt _)

theorem FrameCA.trans {e : Env} {a b c : Array Code} (h1 : FrameCA e a b) (h2 : FrameCA e b c) : FrameCA e a c :=
  ⟨h2.1.trans h1.1, fun x hx => (h2.2 x hx).trans (h1.2 x hx)⟩

/-- Premise of `openBody`: the state when a new sub-table is opened for the code `i + 1`. -/
def OB (e : Env) (i : Nat) (s : TS) (ca : Array Code) : Prop :=
  i + 1 < e.m ∧ s.exit = 0 ∧ s.sym.toNat = i + 1 ∧ s.len.toNat = e.l (i + 1) ∧
  s.huff.toNat = rev (e.l (i + 1)) (e.v (i + 1)) ∧ s.mask.toNat = 2 ^ e.R - 1 ∧
  CountOK e s.count (i + 1) ∧ e.oc + e.cap ≤ ca.size ∧
  (∃ k, s.next = .ref e.rc (e.oc + k) ∧ k + 2 ^ s.curr.toNat = s.used.toNat) ∧
  s.used.toNat ≤ e.cap ∧ 2 ^ e.R ≤ s.used.toNat ∧ 1 ≤ s.curr.toNat ∧ s.curr.toNat ≤ 15 ∧
  s.min.toNat = 2 ^ s.curr.toNat ∧ e.R < e.l (i + 1) ∧ s.drop.toNat = e.R ∧
  e.v (i + 1) % 2 ^ (e.l (i + 1) - e.R) = 0

theorem openBody_wp (e : Env) (i : Nat) (s : TS) (ca : Array Code) (h : OB e i s ca) :
    Wp (openBody e.c s) (e.hc ca) (fun s' h' => ∃ ca', h' = e.hc ca' ∧ FrameCA e ca ca' ∧
      ((s'.exit = 0 ∧ MI e (i + 1) s' ca') ∨ (s'.exit = 2 ∧ e.c.type ≠ CODES ∧ e.oc + e.cap ≤ ca'.size))) := by
  obtain ⟨hi, hex, hsym, hlen, hhuff, hmask, hcnt, hsz, ⟨k, hnext, hku⟩, hucap, hu2R, hc1, hc15, hmin, hRl, hdrop, halign⟩ := h
  have hmxle : e.mx ≤ 15 := by
    have := lenAt_bounds (f := e.f) (n := e.n) (show e.m - 1 < Tc e.f e.n 15 by have := e.h_pos; unfold Env.m; omega)
    exact this.2
  have hlmx : e.l (i + 1) ≤ e.mx := lenAt_mono (f := e.f) (n := e.n) (show i + 1 ≤ Tc e.f e.n 15 - 1 by
    have : i + 1 < e.m := hi
    unfold Env.m at this; omega) (by have := e.h_pos; omega)
  have hR1 := e.h_R1
  rcases s with ⟨huff, sym, len, curr, drop, low, used, min, fill, incr, mask, left, next, here, count, exit⟩
  dsimp only at *
  subst hnext
  unfold openBody
  apply Wp.bind' (wp_add e ca (e.oc + k) min.toNat (by rw [hmin]; omega))
  rintro nxt h' ⟨rfl, rfl⟩
  dsimp only
  rw [e.h_table]
  have hR15 : e.R + 1 ≤ e.l (i + 1) := hRl
  have hsubl : (len - drop).toNat = e.l (i + 1) - e.R := by
    rw [u32_sub (by omega), hlen, hdrop]
  have hcl31 : (len - drop).toNat < 31 := by omega
  apply Wp.bind' (Q := fun r h' => r = 1 <<< (len - drop).toInt32 ∧ h' = e.hc ca)
    (Wp.pure_eq (shl1i32_eq hcl31) ⟨rfl, rfl⟩)
  rintro l0 h' ⟨rfl, rfl⟩
  have hl0 : (1 <<< (len - drop).toInt32 : Int32).toInt = 2 ^ (len - drop).toNat := shl1i32_toInt hcl31
  apply Wp.bind' (size_loop e (i + 1) count drop e.c.max (len - drop) _ (e.hc ca) hcnt hdrop e.h_max hRl hsubl hl0 hi)
  rintro ⟨cs, ls, bs⟩ h' ⟨rfl, hcs⟩
  dsimp only at hcs ⊢
  obtain ⟨bb1, bb2, bb3⟩ := block_bound (f := e.f) (n := e.n) (R := e.R) (i0 := i + 1) hi hRl halign
  have hcs' : cs.toNat = currOf e.f e.n e.R (i + 1) := hcs
  have hbb1 : e.l (i + 1) ≤ e.R + cs.toNat := by rw [hcs']; exact bb1
  have hbb2 : e.R + cs.toNat ≤ e.mx := by rw [hcs']; exact bb2
  have hne : e.c.type ≠ CODES := by
    intro ht
    have := (e.h_codes ht).2.1
    have h3 : e.mx = mxl e.f e.n := rfl
    omega
  have hcs32 : cs.toNat < 32 := by omega
  apply Wp.bind' (Q := fun r h' => r = 1 <<< cs ∧ h' = e.hc ca) (Wp.pure_eq (shl32_eq hcs32) ⟨rfl, rfl⟩)
  rintro u h' ⟨rfl, rfl⟩
  have hu : ((1 : UInt32) <<< cs).toNat = 2 ^ cs.toNat := u32_shl1 hcs32
  have hpow14 : 2 ^ cs.toNat ≤ 2 ^ 14 := Nat.pow_le_pow_right (by omega) (by omega)
  have hcap_le : e.cap ≤ 852 := by
    have := e.h_cap
    rcases e.h_type with ht | ht | ht <;> simp [ht, CODES, LENS, DISTS] at this <;> omega
  have hused' : (used + (1 <<< cs)).toNat = used.toNat + 2 ^ cs.toNat := by
    rw [u32_add (a := used) (b := 1 <<< cs) (by omega), hu]
  by_cases hb : tooBig e.c.type (used + (1 <<< cs)) = true
  · rw [if_pos hb]
    exact Wp.pure' ⟨ca, rfl, ⟨rfl, fun _ _ => rfl⟩, Or.inr ⟨rfl, tooBig_ne hb, hsz⟩⟩
  · rw [if_neg hb]
    have hb' : tooBig e.c.type (used + (1 <<< cs)) = false := by simpa using hb
    have hucap' := tooBig_le e hb' hne
    rw [hused'] at hucap'
    have hmask' : (huff &&& mask).toNat = rev e.R (e.p (i + 1)) := by
      rw [u32_and_mod (k := e.R) (by rw [hmask]), hhuff]
      exact huff_low (f := e.f) (n := e.n) (R := e.R) (j := i + 1) (show e.R ≤ e.l (i + 1) by omega)
    have hlowlt : (huff &&& mask).toNat < 2 ^ e.R := by rw [hmask']; exact rev_lt _ _
    have hidx : e.oc + (huff &&& mask).toNat < ca.size := by omega
    refine wp_update e ca (huff &&& mask).toNat (fun x => ⟨cs.toUInt8, x.bits, x.val⟩) hidx _ _ (fun ca1 h1 => ?_)
    have hs1 : ca1.size = ca.size := by rw [h1, Array.size_set!]
    refine wp_update e ca1 (huff &&& mask).toNat (fun x => ⟨x.op, e.c.root.toUInt8, x.val⟩) (by omega) _ _
      (fun ca2 h2 => ?_)
    have hs2 : ca2.size = ca.size := by rw [h2, Array.size_set!, hs1]
    apply Wp.bind' (Q := fun d h' => d = Int64.ofInt ((↑(e.oc + k + min.toNat) : Int) - ↑e.oc) ∧ h' = e.hc ca2)
      (Wp.of_eq (Ptr.diff_ok (o1 := e.oc + k + min.toNat) (o2 := e.oc) (e.get_hc ca2) (by omega) (by omega)
        (by constructor <;> omega)) ⟨rfl, rfl⟩)
    rintro d h' ⟨hd, rfl⟩
    refine wp_update e ca2 (huff &&& mask).toNat
      (fun x => ⟨x.op, x.bits, d.toUInt64.toUInt16⟩)
      (by omega) _ _ (fun ca3 h3 => ?_)
    have hs3 : ca3.size = ca.size := by rw [h3, Array.size_set!, hs2]
    have hfr : ∀ x, (x < e.oc ∨ e.oc + e.cap ≤ x) → ca3[x]? = ca[x]? := by
      intro x hx
      have hne1 : e.oc + (huff &&& mask).toNat ≠ x := by omega
      rw [h3, getElem?_set!_ne hne1, h2, getElem?_set!_ne hne1, h1, getElem?_set!_ne hne1]
    refine Wp.pure' ⟨ca3, rfl, ⟨hs3, hfr⟩, Or.inl ⟨hex, hi, hex, hsym, hlen, hhuff, hmask, hcnt, by omega, ?_⟩⟩
    unfold TabSt
    dsimp only
    rw [hused']
    refine ⟨⟨k + min.toNat, by rw [Nat.add_assoc], by omega⟩, by omega, by omega, by omega, by omega,
      fun h => by omega, fun _ => ⟨hdrop, hmask', hbb1, hbb2, ?_⟩⟩
    intro j hj hRj hpj
    rw [← hcs'] at bb3
    exact bb3 j hj hRj hpj

theorem cond_iff (len root huff mask low : UInt32) :
    (decide (len > root) && huff &&& mask != low) = true ↔
      (root.toNat < len.toNat ∧ (huff &&& mask).toNat ≠ low.toNat) := by
  simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, UInt32.lt_iff_toNat_lt, gt_iff_lt]
  rw [← UInt32.toNat_inj]

theorem jp2_wp (e : Env) (i : Nat) (s : TS) (ca : Array Code) (h : MI2 e i s ca) :
    Wp (jp2 e.c s) (e.hc ca) (fun s' h' => ∃ ca', h' = e.hc ca' ∧ FrameCA e ca ca' ∧
      ((s'.exit = 0 ∧ MI e (i + 1) s' ca') ∨ (s'.exit = 2 ∧ e.c.type ≠ CODES ∧ e.oc + e.cap ≤ ca'.size))) := by
  obtain ⟨hi, hex, hsym, hlen, hhuff, hmask, hcnt, hsz, hTab, hmin⟩ := h
  have hTab' := hTab
  obtain ⟨⟨k, hnext, hku⟩, hucap, hu2R, hc1, hc15, hphA, hphB⟩ := hTab'
  have hmono : e.l i ≤ e.l (i + 1) := lenAt_mono (f := e.f) (n := e.n) (Nat.le_succ i) hi
  have hroot := e.h_root
  have hR1 := e.h_R1
  have hmxle : e.mx ≤ 15 := by
    have := lenAt_bounds (f := e.f) (n := e.n) (show e.m - 1 < Tc e.f e.n 15 by have := e.h_pos; unfold Env.m; omega)
    exact this.2
  have hlmx : e.l (i + 1) ≤ e.mx := lenAt_mono (f := e.f) (n := e.n) (show i + 1 ≤ Tc e.f e.n 15 - 1 by
    have : i + 1 < e.m := hi
    unfold Env.m at this; omega) (by have := e.h_pos; omega)
  have hmask' : (s.huff &&& s.mask).toNat = rev e.R (e.p (i + 1)) ∨ ¬ (e.R ≤ e.l (i + 1)) := by
    by_cases hle : e.R ≤ e.l (i + 1)
    · left
      rw [u32_and_mod (k := e.R) (by rw [hmask]), hhuff]
      exact huff_low (f := e.f) (n := e.n) (R := e.R) (j := i + 1) hle
    · right; exact hle
  unfold jp2
  by_cases hRl : e.R < e.l (i + 1)
  · have hmk : (s.huff &&& s.mask).toNat = rev e.R (e.p (i + 1)) := by
      rcases hmask' with h | h
      · exact h
      · omega
    have hpl : e.p (i + 1) < 2 ^ e.R := pre_lt e.h_fits hi (show e.R ≤ e.l (i + 1) by omega)
    have hne : e.c.type ≠ CODES := by
      intro ht
      have := (e.h_codes ht).2.1
      have h3 : e.mx = mxl e.f e.n := rfl
      omega
    by_cases hAi : e.l i ≤ e.R
    · -- no table so far: open one
      obtain ⟨hd0, hlow, hcR, huR⟩ := hphA hAi
      have hc : (decide (s.len > e.c.root) && s.huff &&& s.mask != s.low) = true := by
        rw [cond_iff]
        refine ⟨by omega, ?_⟩
        rw [hlow, hmk]
        have := rev_lt e.R (e.p (i + 1))
        have h15 : 2 ^ e.R ≤ 2 ^ 15 := Nat.pow_le_pow_right (by omega) (by omega)
        have : (0xffffffff : UInt32).toNat = 4294967295 := rfl
        omega
      rw [if_pos hc, if_pos (by simp [hd0])]
      apply openBody_wp
      refine ⟨hi, hex, hsym, hlen, hhuff, hmask, hcnt, hsz, ⟨k, hnext, hku⟩, hucap, hu2R, hc1, hc15, hmin, hRl, ?_, ?_⟩
      · exact hroot
      · exact align_succ e.h_fits hi hRl (Or.inl hAi)
    · have hBi : e.R < e.l i := by omega
      obtain ⟨hd, hlow, hbb1, hbb2, hblk⟩ := hphB hBi
      by_cases hpe : e.p (i + 1) = e.p i
      · -- same prefix: the table stays
        have hc : ¬ ((decide (s.len > e.c.root) && s.huff &&& s.mask != s.low) = true) := by
          rw [cond_iff]
          rintro ⟨_, hh⟩
          apply hh
          rw [hlow, hmk, hpe]
        rw [if_neg hc]
        refine Wp.pure' ⟨ca, rfl, ⟨rfl, fun _ _ => rfl⟩, Or.inl ⟨hex, hi, hex, hsym, hlen, hhuff, hmask, hcnt, hsz, ?_⟩⟩
        refine ⟨⟨k, hnext, hku⟩, hucap, hu2R, hc1, hc15, fun h => by omega, fun _ => ⟨hd, ?_, ?_, hbb2, ?_⟩⟩
        · rw [hlow, hpe]
        · exact hblk (i + 1) hi hRl hpe
        · intro j hj hRj hpj
          exact hblk j hj hRj (hpj.trans hpe)
      · -- new prefix
        have hc : (decide (s.len > e.c.root) && s.huff &&& s.mask != s.low) = true := by
          rw [cond_iff]
          refine ⟨by omega, ?_⟩
          rw [hlow, hmk]
          intro heq
          apply hpe
          have := rev_inj e.R _ _ heq
          have hpi : e.p i < 2 ^ e.R := pre_lt e.h_fits (show i < Tc e.f e.n 15 by have : i + 1 < e.m := hi; unfold Env.m at this; omega) (show e.R ≤ e.l i by omega)
          rw [Nat.mod_eq_of_lt hpl, Nat.mod_eq_of_lt hpi] at this
          exact this
        have hdne : ¬ ((s.drop == 0) = true) := by
          simp only [beq_iff_eq]; intro h0; rw [h0] at hd; simp at hd; omega
        rw [if_pos hc, if_neg hdne]
        apply openBody_wp
        refine ⟨hi, hex, hsym, hlen, hhuff, hmask, hcnt, hsz, ⟨k, hnext, hku⟩, hucap, hu2R, hc1, hc15, hmin, hRl, hd, ?_⟩
        exact align_succ e.h_fits hi hRl (Or.inr ⟨hBi, hpe⟩)
  · -- the code is not longer than the root: no table
    have hc : ¬ ((decide (s.len > e.c.root) && s.huff &&& s.mask != s.low) = true) := by
      rw [cond_iff]; rintro ⟨h1, _⟩; omega
    rw [if_neg hc]
    have hAi : e.l i ≤ e.R := by omega
    obtain ⟨hd0, hlow, hcR, huR⟩ := hphA hAi
    refine Wp.pure' ⟨ca, rfl, ⟨rfl, fun _ _ => rfl⟩, Or.inl ⟨hex, hi, hex, hsym, hlen, hhuff, hmask, hcnt, hsz, ?_⟩⟩
    refine ⟨⟨k, hnext, hku⟩, hucap, hu2R, hc1, hc15, fun _ => ⟨hd0, hlow, hcR, huR⟩, fun h => by omega⟩

theorem ws_getD_lt {f : Nat → Nat} {n i : Nat} (hi : i < Tc f n 15) : (wsAux f n 15).getD i 0 < n := by
  have hlen' : (wsAux f n 15).length = Tc f n 15 := wsAux_length 15
  have hlt' : i < (wsAux f n 15).length := by omega
  have hm := List.getElem_mem hlt'
  have := (mem_wsAux.mp hm).1
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt', Option.getD_some]
  exact this

theorem jp1_wp (e : Env) (i : Nat) (s : TS) (ca : Array Code) (h : MI1 e i s ca) :
    Wp (jp1 e.c s) (e.hc ca) (fun s' h' => ∃ ca', h' = e.hc ca' ∧ FrameCA e ca ca' ∧ StepPost e i s' ca') := by
  obtain ⟨hi, hex, hsym, hlen, hhuff, hhfin, hmask, hcnt, hsz, hTab, hmin⟩ := h
  have hmono := fun (hi1 : i + 1 < e.m) => lenAt_mono (f := e.f) (n := e.n) (Nat.le_succ i) hi1
  have hi0 : i < Tc e.f e.n 15 := hi
  obtain ⟨hb1, hb2⟩ := lenAt_bounds (f := e.f) (n := e.n) hi0
  have hblk := (lenAt_eq_iff (f := e.f) (n := e.n) (l := lenAt e.f e.n i) hb1 hb2 hi0).mp rfl
  have hm15 : e.m = Tc e.f e.n 15 := rfl
  have hmxle : e.mx ≤ 15 := by
    have := lenAt_bounds (f := e.f) (n := e.n) (show e.m - 1 < Tc e.f e.n 15 by have := e.h_pos; unfold Env.m; omega)
    exact this.2
  have hTs := Tc_succ' (f := e.f) (n := e.n) hb1
  simp only [Env.l] at hlen hblk hTs
  have hlen16 : s.len.toNat < 16 := by rw [hlen]; exact Nat.lt_succ_of_le hb2
  have hsz16 : s.len.toNat < s.count.size := by rw [hcnt.1]; exact hlen16
  have hcl : (s.count[s.len.toNat]).toNat = Tc e.f e.n (lenAt e.f e.n i) - i := by
    have key := hcnt.2 (lenAt e.f e.n i) hb1 hb2
    rw [Array.getD_eq_getD_getElem?, show lenAt e.f e.n i = s.len.toNat from hlen.symm, Array.getElem?_eq_getElem hsz16] at key
    simp only [Option.getD_some] at key
    rw [key, hlen]; unfold rem; omega
  have hcl_pos : 1 ≤ (s.count[s.len.toNat]).toNat := by rw [hcl]; omega
  have hcl1 : ((s.count[s.len.toNat]) - 1).toNat = (s.count[s.len.toNat]).toNat - 1 := by
    rw [UInt16.toNat_sub_of_le _ _ (by simp [UInt16.le_iff_toNat_le]; omega)]; rfl
  have hcnt' : ∀ cnt' : Array UInt16, cnt' = s.count.set! s.len.toNat ((s.count[s.len.toNat]) - 1) →
      CountOK e cnt' (i + 1) := by
    intro cnt' hc'
    refine ⟨by rw [hc', Array.size_set!]; exact hcnt.1, fun l hl1 hl2 => ?_⟩
    rw [hc', getD_set!, rem_succ hl1 hl2 hi0]
    by_cases hl : s.len.toNat = l
    · have hli : lenAt e.f e.n i = l := by rw [← hl]; exact hlen.symm
      rw [if_pos ⟨hl, hsz16⟩, if_pos hli, hcl1, hcl]
      subst hli
      unfold rem; omega
    · have hli : ¬ (lenAt e.f e.n i = l) := by intro h2; apply hl; rw [hlen]; exact h2
      rw [if_neg (fun h2 => hl h2.1), if_neg hli, Nat.sub_zero]
      exact hcnt.2 l hl1 hl2
  unfold jp1
  rcases s with ⟨huff, sym, len, curr, drop, low, used, min, fill, incr, mask, left, next, here, count, exit⟩
  dsimp only at *
  have hsym' : (sym + 1).toNat = i + 1 := by
    have := e.h_n; have : e.m ≤ e.n := Tc_le 15 e.n
    rw [u32_succ (by omega), hsym]
  apply Wp.bind' (Q := fun r h' => r = count[len.toNat] ∧ h' = e.hc ca) (Wp.pure_eq (geta_eq hsz16) ⟨rfl, rfl⟩)
  rintro cl h' ⟨rfl, rfl⟩
  try dsimp only
  apply Wp.bind' (Q := fun r h' => r = count.set! len.toNat (count[len.toNat] - 1) ∧ h' = e.hc ca)
    (Wp.pure_eq (seta_eq hsz16) ⟨rfl, rfl⟩)
  rintro cnt' h' ⟨hc', rfl⟩
  try dsimp only
  have hCO := hcnt' cnt' hc'
  have tail : ∀ (s2 : TS), s2.exit = 0 → s2.sym.toNat = i + 1 → s2.len.toNat = e.l (i + 1) → i + 1 < e.m →
      s2.huff = huff → s2.mask = mask → s2.count = cnt' → s2.curr = curr → s2.drop = drop → s2.low = low →
      s2.used = used → s2.min = min → s2.next = next →
      Wp (jp2 e.c s2) (e.hc ca) (fun s' h' => ∃ ca', h' = e.hc ca' ∧ FrameCA e ca ca' ∧ StepPost e i s' ca') := by
    intro s2 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
    refine Wp.mono (jp2_wp e i s2 ca ?_) ?_
    · refine ⟨h4, h1, h2, h3, ?_, by rw [h6]; exact hmask, by rw [h7]; exact hCO, hsz, ?_, by rw [h12, h8]; exact hmin⟩
      · rw [h5]; exact hhuff h4
      · obtain ⟨⟨k, hn, hk⟩, r⟩ := hTab
        unfold TabSt
        rw [h13, h8, h11, h9, h10]
        exact ⟨⟨k, hn, hk⟩, r⟩
    · rintro s' h' ⟨ca', hh, hf, hr⟩
      refine ⟨ca', hh, hf, ?_⟩
      rcases hr with ⟨hx, hm⟩ | ⟨hx, hy, hz⟩
      · exact Or.inl ⟨h4, hm⟩
      · exact Or.inr (Or.inr ⟨hx, hy, hz⟩)
  have hmxeq : (len == e.c.max) = true ↔ lenAt e.f e.n i = e.mx := by
    rw [beq_iff_eq, ← UInt32.toNat_inj, e.h_max, hlen]; rfl
  have hTle : e.m ≤ e.n := Tc_le 15 e.n
  by_cases hz : ((count[len.toNat] - 1 == 0) = true)
  · rw [if_pos hz]
    have hcl0 : (count[len.toNat] - 1).toNat = 0 := by
      have := beq_iff_eq.mp hz
      rw [this]; rfl
    have hTl : i + 1 = Tc e.f e.n (lenAt e.f e.n i) := by omega
    by_cases hmx : (len == e.c.max) = true
    · rw [if_pos hmx]
      have hlm := hmxeq.mp hmx
      have him : i + 1 = e.m := by
        have h1 : Tc e.f e.n e.mx = Tc e.f e.n 15 := by
          have := Tc_mono (f := e.f) (n := e.n) (show e.mx ≤ 15 from hmxle)
          have hh := (lenAt_le_iff (f := e.f) (n := e.n) (l := e.mx) hmxle (show e.m - 1 < Tc e.f e.n 15 by have := e.h_pos; unfold Env.m; omega)).mp (Nat.le_refl _)
          omega
        rw [hTl, hlm]; exact h1
      refine Wp.pure' ⟨ca, rfl, ⟨rfl, fun _ _ => rfl⟩, Or.inr (Or.inl ⟨him, rfl, ?_, hsz⟩)⟩
      obtain ⟨⟨k, hn, hk⟩, hu, _⟩ := hTab
      exact ⟨⟨k, hn, hk⟩, hu, hhfin him⟩
    · rw [if_neg hmx]
      have hi1 : i + 1 < e.m := by
        apply Classical.byContradiction
        intro hcon
        apply hmx
        rw [hmxeq]
        have him : i + 1 = e.m := by omega
        have : i = Tc e.f e.n 15 - 1 := by have : e.m = Tc e.f e.n 15 := rfl; omega
        rw [this]; rfl
      have hwlt : e.ow + (i + 1) < e.wa.size := by have := e.h_wa; omega
      have hw := e.h_wcont (i + 1) hi1
      rw [Array.getElem?_eq_getElem hwlt] at hw
      have hw' : e.wa[e.ow + (i + 1)]'hwlt = UInt16.ofNat ((wsAux e.f e.n 15).getD (i + 1) 0) := Option.some.inj hw
      have hwsm : (wsAux e.f e.n 15).getD (i + 1) 0 < e.n := ws_getD_lt (by omega)
      have hlenx : e.l (i + 1) = e.f ((wsAux e.f e.n 15).getD (i + 1) 0) := rfl
      generalize (wsAux e.f e.n 15).getD (i + 1) 0 = x at hw' hwsm hlenx
      have hn288 := e.h_n
      have hx16 : x < 2 ^ 16 := by omega
      have hwn : (UInt16.ofNat x).toNat = x := by
        rw [UInt16.toNat_ofNat', Nat.mod_eq_of_lt hx16]
      rw [e.h_work, e.h_lens]
      apply Wp.bind' (Q := fun r h' => r = e.wa[e.ow + (i + 1)]'hwlt ∧ h' = e.hc ca)
      · rw [hsym']; exact Wp.of_eq (Ptr.index_ok (e.get_wa ca) hwlt) ⟨rfl, rfl⟩
      · rintro w h' ⟨rfl, rfl⟩
        rw [hw']
        have hlr : e.ol + (UInt16.ofNat x).toNat < e.la.size := by
          rw [hwn]; have := e.h_la; omega
        apply Wp.bind' (Q := fun r h' => r = e.la[e.ol + (UInt16.ofNat x).toNat]'hlr ∧ h' = e.hc ca)
        · exact Wp.of_eq (Ptr.index_ok (e.get_la ca) hlr) ⟨rfl, rfl⟩
        · rintro l h' ⟨rfl, rfl⟩
          have hlv : (e.la[e.ol + (UInt16.ofNat x).toNat]'hlr).toNat = e.l (i + 1) := by
            have hf := e.h_f x
            rw [hlenx, hf, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (show e.ol + x < e.la.size by rw [hwn] at hlr; exact hlr),
              Option.getD_some]
            simp only [hwn]
          have hl32 : (e.la[e.ol + (UInt16.ofNat x).toNat]'hlr).toUInt32.toNat = e.l (i + 1) := by
            rw [UInt16.toNat_toUInt32]; exact hlv
          exact tail { huff := huff, sym := sym + 1, len := (e.la[e.ol + (UInt16.ofNat x).toNat]'hlr).toUInt32, curr := curr, drop := drop, low := low, used := used, min := min, fill := fill, incr := incr, mask := mask, left := left, next := next, here := here, count := cnt', exit := exit } hex hsym' hl32 hi1 rfl rfl rfl rfl rfl rfl rfl rfl rfl
  · rw [if_neg hz]
    have hcl2 : 2 ≤ (count[len.toNat]).toNat := by
      apply Classical.byContradiction
      intro hcon
      apply hz
      have : (count[len.toNat]).toNat = 1 := by omega
      have h1 : count[len.toNat] = 1 := by
        apply UInt16.toNat_inj.mp; rw [this]; rfl
      rw [h1]; rfl
    have hi1 : i + 1 < Tc e.f e.n (lenAt e.f e.n i) := by omega
    have hmi1 : i + 1 < e.m := by
      have := Tc_mono (f := e.f) (n := e.n) hb2
      have : e.m = Tc e.f e.n 15 := rfl
      omega
    have hl' : e.l (i + 1) = lenAt e.f e.n i := by
      have := (lenAt_eq_iff (f := e.f) (n := e.n) (l := lenAt e.f e.n i) hb1 hb2 hmi1).mpr ⟨by omega, hi1⟩
      exact this
    exact tail { huff := huff, sym := sym + 1, len := len, curr := curr, drop := drop, low := low, used := used, min := min, fill := fill, incr := incr, mask := mask, left := left, next := next, here := here, count := cnt', exit := exit } hex hsym' (by rw [hl']; exact hlen) hmi1 rfl rfl rfl rfl rfl rfl rfl rfl rfl

theorem incrLoop_pow (h : Nat) : ∀ e, incrLoop h e = 0 ∨ ∃ e' ≤ e, incrLoop h e = 2 ^ e'
  | 0 => by
    by_cases hb : h.testBit 0
    · left; simp [incrLoop, hb]
    · right; exact ⟨0, Nat.le_refl _, by simp [incrLoop, hb]⟩
  | e + 1 => by
    by_cases hb : h.testBit (e + 1)
    · rcases incrLoop_pow h e with h0 | ⟨e', he', h1⟩
      · left; simp [incrLoop, hb, h0]
      · right; exact ⟨e', by omega, by simp [incrLoop, hb, h1]⟩
    · right; exact ⟨e + 1, Nat.le_refl _, by simp [incrLoop, hb]⟩

theorem jp0_wp (e : Env) (i : Nat) (s : TS) (ca : Array Code) (h : MI e i s ca) :
    Wp (jp0 e.c s) (e.hc ca) (fun s' h' => ∃ ca', h' = e.hc ca' ∧ FrameCA e ca ca' ∧ StepPost e i s' ca') := by
  obtain ⟨hi, hex, hsym, hlen, hhuff, hmask, hcnt, hsz, hTab⟩ := h
  have hTab' := hTab
  obtain ⟨⟨k, hnext, hku⟩, hucap, hu2R, hc1, hc15, hphA, hphB⟩ := hTab'
  have hi0 : i < Tc e.f e.n 15 := hi
  have hbd : 1 ≤ e.l i ∧ e.l i ≤ 15 := lenAt_bounds (f := e.f) (n := e.n) hi0
  have hR1 := e.h_R1
  have hdb : s.drop.toNat ≤ s.len.toNat ∧ s.len.toNat - s.drop.toNat ≤ s.curr.toNat ∧
      1 ≤ s.len.toNat - s.drop.toNat ∧ s.drop.toNat ≤ 15 := by
    by_cases hA : e.l i ≤ e.R
    · obtain ⟨hd0, _, hcR, _⟩ := hphA hA
      rw [hd0]
      simp only [UInt32.toNat_zero]
      omega
    · obtain ⟨hd, _, hbb1, hbb2, _⟩ := hphB (by omega)
      omega
  obtain ⟨hdn, hbc1, hbc2, hbc3⟩ := hdb
  have hb32 : (s.len - s.drop).toNat < 32 := by rw [u32_sub hdn]; omega
  have hcurr32 : s.curr.toNat < 32 := by omega
  have hmxle : e.mx ≤ 15 := by
    have := lenAt_bounds (f := e.f) (n := e.n) (show e.m - 1 < Tc e.f e.n 15 by have := e.h_pos; unfold Env.m; omega)
    exact this.2
  have hm15 : e.m = Tc e.f e.n 15 := rfl
  rcases s with ⟨huff, sym, len, curr, drop, low, used, min, fill, incr, mask, left, next, here, count, exit⟩
  dsimp only at *
  unfold jp0
  apply Wp.bind' (Q := fun r h' => r = 1 <<< (len - drop) ∧ h' = e.hc ca) (Wp.pure_eq (shl32_eq hb32) ⟨rfl, rfl⟩)
  rintro incr0 h' ⟨rfl, rfl⟩
  apply Wp.bind' (Q := fun r h' => r = 1 <<< curr ∧ h' = e.hc ca) (Wp.pure_eq (shl32_eq hcurr32) ⟨rfl, rfl⟩)
  rintro fill0 h' ⟨rfl, rfl⟩
  have hS : ((1 : UInt32) <<< (len - drop)).toNat = 2 ^ (len.toNat - drop.toNat) := by rw [u32_shl1 hb32, u32_sub hdn]
  have hF : ((1 : UInt32) <<< curr).toNat = 2 ^ curr.toNat := u32_shl1 hcurr32
  have hSN : 2 ^ (len.toNat - drop.toNat) * 2 ^ (curr.toNat - (len.toNat - drop.toNat)) = 2 ^ curr.toNat := by
    rw [← Nat.pow_add]; congr 1; omega
  have hhd : (huff >>> drop).toNat = huff.toNat / 2 ^ drop.toNat := u32_shr (by omega)
  have hhdS : huff.toNat / 2 ^ drop.toNat < 2 ^ (len.toNat - drop.toNat) := by
    rw [Nat.div_lt_iff_lt_mul (Nat.pow_pos (by omega)), ← Nat.pow_add, show len.toNat - drop.toNat + drop.toNat = len.toNat by omega,
      hhuff, hlen]
    exact rev_lt _ _
  dsimp only
  have hN1 : 1 ≤ 2 ^ (curr.toNat - (len.toNat - drop.toNat)) := Nat.pow_pos (by omega)
  have hS1 : 1 ≤ 2 ^ (len.toNat - drop.toNat) := Nat.pow_pos (by omega)
  apply Wp.bind' (fill_loop e _ ca (2 ^ (len.toNat - drop.toNat)) (2 ^ (curr.toNat - (len.toNat - drop.toNat))) k
    (huff.toNat / 2 ^ drop.toNat) hnext hS (by rw [hF, hSN]) hN1 hS1 hhd hhdS (show drop.toNat < 32 by omega)
    (by rw [hSN]; omega) hsz)
  rintro s2 h' ⟨ca2, rfl, rfl, hs2, hp1, hp2⟩
  dsimp only
  have hfr : FrameCA e ca ca2 := by
    refine ⟨hs2, fun x hx => hp2 x ?_⟩
    rintro ⟨q', hq', hxq⟩
    have h1 : 2 ^ (len.toNat - drop.toNat) * (q' + 1) ≤ 2 ^ (len.toNat - drop.toNat) * 2 ^ (curr.toNat - (len.toNat - drop.toNat)) :=
      Nat.mul_le_mul_left _ hq'
    rw [Nat.mul_succ] at h1
    rw [hSN] at h1
    omega
  have hl31 : (len - 1).toNat < 32 := by rw [u32_one_sub (by omega)]; omega
  apply Wp.bind' (Q := fun r h' => r = 1 <<< (len - 1) ∧ h' = e.hc ca2) (Wp.pure_eq (shl32_eq hl31) ⟨rfl, rfl⟩)
  rintro incr2 h' ⟨rfl, rfl⟩
  apply Wp.bind' (incr_loop _ (len.toNat - 1) (by omega)
    (by rw [u32_shl1 hl31, u32_one_sub (by omega)]) (e.hc ca2))
  rintro s4 h' ⟨rfl, X, rfl, hX⟩
  dsimp only at hX ⊢
  have hlen1 : len.toNat - 1 = e.l i - 1 := by omega
  rw [hlen1] at hX
  have hXr : X.toNat = incrLoop (rev (e.l i) (e.v i)) (e.l i - 1) := by rw [hX, hhuff]
  -- the continuation, once the new `huff` is known
  have mi1 : ∀ hnew : UInt32, (i + 1 < e.m → hnew.toNat = rev (e.l (i + 1)) (e.v (i + 1))) →
      (i + 1 = e.m → hnew.toNat = 0 ∨ hnew.toNat < 2 ^ curr.toNat) →
      Wp (jp1 e.c (TS.mk hnew sym len curr drop low used (1 <<< curr) 0 X mask left next here count exit)) (e.hc ca2)
        (fun s' h' => ∃ ca', h' = e.hc ca' ∧ FrameCA e ca ca' ∧ StepPost e i s' ca') := by
    intro hnew hA hB
    refine Wp.mono (jp1_wp e i _ ca2 ?_) ?_
    · refine ⟨hi, hex, hsym, hlen, hA, hB, hmask, hcnt, by omega, hTab, ?_⟩
      show ((1 : UInt32) <<< curr).toNat = 2 ^ curr.toNat
      exact hF
    · rintro s' h' ⟨ca', hh, hf, hr⟩
      exact ⟨ca', hh, hfr.trans hf, hr⟩
  have hi1 := e.h_fits
  by_cases hXz : X = 0
  · have hXz' : (X != 0) = false := by simp [hXz]
    rw [if_neg (by simp [hXz])]
    refine mi1 0 (fun hlt => ?_) (fun _ => Or.inl rfl)
    exfalso
    obtain ⟨e', _, hinc, _⟩ := huff_step (f := e.f) (n := e.n) hi1 hlt
    have : X.toNat = 0 := by rw [hXz]; rfl
    have h3 : X.toNat = 2 ^ e' := hXr.trans hinc
    rw [this] at h3
    exact absurd h3.symm (Nat.pos_iff_ne_zero.mp (Nat.pow_pos (by omega)))
  · rw [if_pos (by simpa using hXz)]
    have hXn : X.toNat ≠ 0 := fun h0 => hXz (UInt32.toNat_inj.mp (by rw [h0]; rfl))
    obtain ⟨e', he', hXp⟩ : ∃ e', e' ≤ e.l i - 1 ∧ X.toNat = 2 ^ e' := by
      rcases incrLoop_pow huff.toNat (e.l i - 1) with h0 | ⟨e', he', h1⟩
      · exact absurd (hX.trans h0) hXn
      · exact ⟨e', he', hX.trans h1⟩
    have hX1 : (X - 1).toNat = 2 ^ e' - 1 := by rw [u32_one_sub hXn, hXp]
    have hand : (huff &&& (X - 1)).toNat = huff.toNat % 2 ^ e' := u32_and_mod hX1
    have hmodlt : huff.toNat % 2 ^ e' < 2 ^ e' := Nat.mod_lt _ (Nat.pow_pos (by omega))
    have hp15 : 2 ^ e' ≤ 2 ^ 15 := Nat.pow_le_pow_right (by omega) (by omega)
    have hnewv : ((huff &&& (X - 1)) + X).toNat = huff.toNat % 2 ^ e' + 2 ^ e' := by
      have hlt : (huff &&& (X - 1)).toNat + X.toNat < 2 ^ 32 := by rw [hand, hXp]; omega
      rw [u32_add hlt, hand, hXp]
    refine mi1 _ (fun hlt => ?_) (fun him => ?_)
    · obtain ⟨e2, _, hinc, hrev⟩ := huff_step (f := e.f) (n := e.n) hi1 hlt
      have : 2 ^ e' = 2 ^ e2 := by
        rw [← hXp, hXr]
        exact hinc
      rw [hnewv, this, hhuff]
      exact hrev
    · right
      -- the code is incomplete: its only symbol has length 1
      have hnc : ¬ (Kc e.f e.n 15 = 2 ^ 15) := by
        intro hc
        have := huff_last (f := e.f) (n := e.n) hc (m := i) (by have : e.m = Tc e.f e.n 15 := rfl; omega)
        have h0 : X.toNat = 0 := by rw [hXr]; exact this
        exact hXn h0
      have hmx1 : mxl e.f e.n = 1 := by
        rcases e.h_end with h | h
        · exact absurd h hnc
        · exact h.1
      have hlm : e.l i ≤ e.mx := lenAt_mono (f := e.f) (n := e.n) (show i ≤ Tc e.f e.n 15 - 1 by omega) (by have := e.h_pos; omega)
      have hl1 : e.l i = 1 := by have : e.mx = mxl e.f e.n := rfl; omega
      have hAi : e.l i ≤ e.R := by omega
      obtain ⟨_, _, hcR, _⟩ := hphA hAi
      rw [hnewv]
      have h2 : e' = 0 := by omega
      subst h2
      have := Nat.mod_lt huff.toNat (Nat.pow_pos (a := 2) (n := 0) (by omega))
      have hcpos : 2 ^ 1 ≤ 2 ^ curr.toNat := Nat.pow_le_pow_right (by omega) (by omega)
      simp at this
      omega

theorem hereTop_wp (e : Env) (i : Nat) (s : TS) (ca : Array Code) (h : MI e i s ca) :
    Wp (hereTop e.c s) (e.hc ca) (fun s' h' => ∃ ca', h' = e.hc ca' ∧ FrameCA e ca ca' ∧ StepPost e i s' ca') := by
  have hMI := h
  have hsym : s.sym.toNat = i := h.2.2.1
  have hi : i < e.m := h.1
  have hn288 := e.h_n
  have hTle : e.m ≤ e.n := Tc_le 15 e.n
  have hwlt : e.ow + i < e.wa.size := by have := e.h_wa; omega
  have hw := e.h_wcont i hi
  rw [Array.getElem?_eq_getElem hwlt] at hw
  have hw' : e.wa[e.ow + i]'hwlt = UInt16.ofNat ((wsAux e.f e.n 15).getD i 0) := Option.some.inj hw
  have hx : (wsAux e.f e.n 15).getD i 0 < e.n := ws_getD_lt hi
  generalize (wsAux e.f e.n 15).getD i 0 = x at hw' hx
  have hx16 : x < 2 ^ 16 := by omega
  have hwn : (UInt16.ofNat x).toNat = x := by rw [UInt16.toNat_ofNat', Nat.mod_eq_of_lt hx16]
  have hw32 : (UInt16.ofNat x).toUInt32.toNat = x := by rw [UInt16.toNat_toUInt32, hwn]
  -- the table lookups are in range
  have hidx : x ≥ e.c.match_.toNat →
      x - e.c.match_.toNat < e.c.extra.size ∧ x - e.c.match_.toNat < e.c.base.size := by
    intro hge
    rcases e.h_type with ht | ht | ht
    · obtain ⟨_, _, h3, h4⟩ := e.h_codes ht
      have hm : e.c.match_.toNat = 20 := by rw [h4]; rfl
      omega
    · obtain ⟨h1, h2, h3, h4⟩ := e.h_lens' ht
      have hm : e.c.match_.toNat = 257 := by rw [h4]; rfl
      have hl1 : lbase.size = 31 := rfl
      have hl2 : lext.size = 31 := rfl
      rw [h2, h3, hm] at *
      omega
    · obtain ⟨h1, h2, h3, h4⟩ := e.h_dists ht
      have hm : e.c.match_.toNat = 0 := by rw [h4]; rfl
      have hl1 : dbase.size = 32 := rfl
      have hl2 : dext.size = 32 := rfl
      rw [h2, h3, hm] at *
      omega
  unfold hereTop
  dsimp only
  rw [e.h_work]
  rw [hsym]
  apply Wp.bind' (Q := fun r h' => r = e.wa[e.ow + i]'hwlt ∧ h' = e.hc ca)
    (Wp.of_eq (Ptr.index_ok (e.get_wa ca) hwlt) ⟨rfl, rfl⟩)
  rintro w h' ⟨rfl, rfl⟩
  rw [hw']
  have hjp : ∀ here' : Code, Wp (jp0 e.c { s with here := here' }) (e.hc ca)
      (fun s' h' => ∃ ca', h' = e.hc ca' ∧ FrameCA e ca ca' ∧ StepPost e i s' ca') := fun here' =>
    jp0_wp e i _ ca hMI
  have rd : Wp (Ptr.index (Ptr.ref e.rw e.ow) (i : Int)) (e.hc ca) (fun r h' => r = e.wa[e.ow + i]'hwlt ∧ h' = e.hc ca) :=
    Wp.of_eq (Ptr.index_ok (e.get_wa ca) hwlt) ⟨rfl, rfl⟩
  by_cases h1 : (UInt16.ofNat x).toUInt32 + 1 < e.c.match_
  · rw [if_pos h1]
    try dsimp only
    apply Wp.bind' rd
    rintro w2 h' ⟨rfl, rfl⟩
    rw [hw']
    exact jp0_wp e i _ ca hMI
  · rw [if_neg h1]
    try dsimp only
    apply Wp.bind' rd
    rintro w2 h' ⟨rfl, rfl⟩
    rw [hw']
    by_cases h2 : (UInt16.ofNat x).toUInt32 ≥ e.c.match_
    · rw [if_pos h2]
      have hge : x ≥ e.c.match_.toNat := by
        have := UInt32.le_iff_toNat_le.mp h2; rw [hw32] at this; exact this
      obtain ⟨hx1, hx2⟩ := hidx hge
      have hsb : ((UInt16.ofNat x).toUInt32 - e.c.match_).toNat = x - e.c.match_.toNat := by
        rw [u32_sub (by rw [hw32]; exact hge), hw32]
      apply Wp.bind' rd
      rintro w3 h' ⟨rfl, rfl⟩
      rw [hw']
      have ga : geta e.c.extra ((UInt16.ofNat x).toUInt32 - e.c.match_).toNat = pure (e.c.extra[x - e.c.match_.toNat]'hx1) := by
        rw [hsb]; exact geta_eq hx1
      have gb : geta e.c.base ((UInt16.ofNat x).toUInt32 - e.c.match_).toNat = pure (e.c.base[x - e.c.match_.toNat]'hx2) := by
        rw [hsb]; exact geta_eq hx2
      apply Wp.bind' (Q := fun r h' => r = e.c.extra[x - e.c.match_.toNat]'hx1 ∧ h' = e.hc ca)
        (Wp.pure_eq ga ⟨rfl, rfl⟩)
      rintro ex h' ⟨rfl, rfl⟩
      try dsimp only
      apply Wp.bind' rd
      rintro w4 h' ⟨rfl, rfl⟩
      rw [hw']
      apply Wp.bind' (Q := fun r h' => r = e.c.base[x - e.c.match_.toNat]'hx2 ∧ h' = e.hc ca)
        (Wp.pure_eq gb ⟨rfl, rfl⟩)
      rintro ba h' ⟨rfl, rfl⟩
      try dsimp only
      exact jp0_wp e i _ ca hMI
    · rw [if_neg h2]
      exact jp0_wp e i _ ca hMI

end Zlib.Inftrees.Proofs
