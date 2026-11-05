import ZlibF.Proof.«inftrees.c.step»
import ZlibF.Proof.«inftrees.c.spec»
import ZlibF.Proof.«inftrees.c.link»

namespace Zlib.Inftrees.Proofs
open C Zlib.Inftrees Zlib.Inftrees.Spec

/-! ### `inflate_table` cut at its join points -/

/-- From the declaration of the state of the main loop on. -/
def itTail (type : UInt32) (lens : WPtr) (table : CodePtr) (bits : UInt32) (work : WPtr) (count : Array UInt16)
    (max min root : UInt32) (left : Int32) (base extra : Array UInt16) (match_ : UInt32) :
    M (Int32 × CodePtr × UInt32) := do
  let used ← shl32 1 root
  let s : TS := { huff := 0, sym := 0, len := min, curr := root, drop := 0, low := 0xffffffff, used,
                  min := min, fill := 0, incr := 0, mask := used - 1, left, next := table, here := default,
                  count, exit := 0 }
  if tooBig type used then return (1, table, bits)
  let c : Ctx := { type, lens, work, table, root, max, base, extra, match_ }
  let s ← cwhile (fun s => pure (s.exit == 0, s)) (buildStep c) s
  if s.exit == 2 then return (1, table, bits)
  let mut s := s
  if s.huff != 0 then
    s := { s with here := ⟨64, (s.len - s.drop).toUInt8, 0⟩ }
    storeCode s.next s.huff.toNat s.here
  let table ← table.add s.used.toNat
  return (0, table, root)

/-- From the check of the Kraft sum on. -/
def itB (type : UInt32) (lens : WPtr) (codes : UInt32) (table : CodePtr) (bits : UInt32) (work : WPtr)
    (count : Array UInt16) (max min root : UInt32) : M (Int32 × CodePtr × UInt32) := do
  let offs : Array UInt16 := Array.replicate 16 0
  let (left, bad, _) ← cwhile (fun (left, bad, len) => pure (!bad && len ≤ MAXBITS, (left, bad, len)))
    (fun (left, bad, len) => do
      if left < 0 then ub "left shift of a negative value" else
      let left ← chk32 (left.toInt * 2)
      let cc ← geta count len.toNat
      let left ← chk32 (left.toInt - cc.toNat)
      if left < 0 then pure (left, true, len) else pure (left, bad, len + 1)) ((1 : Int32), false, (1 : UInt32))
  if bad then return (-1, table, bits)
  if left > 0 && (type == CODES || max != 1) then return (-1, table, bits)
  let offs ← seta offs 1 0
  let (_, offs) ← cwhile (fun (len, offs) => pure (len < MAXBITS, (len, offs)))
    (fun (len, offs) => do
      let a ← geta offs len.toNat
      let b ← geta count len.toNat
      pure (len + 1, ← seta offs (len + 1).toNat (a + b))) ((1 : UInt32), offs)
  let (_, offs) ← cwhile (fun (sym, offs) => pure (sym < codes, (sym, offs)))
    (fun (sym, offs) => do
      let l ← lens.index sym.toNat
      if l != 0 then
        let l ← lens.index sym.toNat
        let o ← geta offs l.toNat
        let offs ← seta offs l.toNat (o + 1)
        let q ← work.add o.toNat
        Ptr.store q sym.toUInt16
        pure (sym + 1, offs)
      else pure (sym + 1, offs)) ((0 : UInt32), offs)
  let mut base : Array UInt16 := #[]
  let mut extra : Array UInt16 := #[]
  let mut match_ : UInt32 := 0
  if type == CODES then
    match_ := 20
  else if type == LENS then
    base := lbase; extra := lext; match_ := 257
  else if type == DISTS then
    base := dbase; extra := dext
  itTail type lens table bits work count max min root left base extra match_

/-- From the test `max == 0` on. -/
def itA (type : UInt32) (lens : WPtr) (codes : UInt32) (table : CodePtr) (bits : UInt32) (work : WPtr)
    (count : Array UInt16) (max root : UInt32) : M (Int32 × CodePtr × UInt32) := do
  if max == 0 then
    let here : Code := ⟨64, 1, 0⟩
    Ptr.store table here
    let table ← table.add 1
    Ptr.store table here
    let table ← table.add 1
    return (0, table, 1)
  let (min, _) ← cwhile (fun (min, brk) => pure (!brk && min < max, (min, brk)))
    (fun (min, brk) => do
      if (← geta count min.toNat) != 0 then pure (min, true) else pure (min + 1, brk)) ((1 : UInt32), false)
  let mut root := root
  if root < min then root := min
  itB type lens codes table bits work count max min root

def itTop (type : UInt32) (lens : WPtr) (codes : UInt32) (table : CodePtr) (bits : UInt32) (work : WPtr) :
    M (Int32 × CodePtr × UInt32) := do
  let count : Array UInt16 := Array.replicate 16 0
  let (_, count) ← cwhile (fun (len, count) => pure (len ≤ MAXBITS, (len, count)))
    (fun (len, count) => do pure (len + 1, ← seta count len.toNat 0)) ((0 : UInt32), count)
  let (_, count) ← cwhile (fun (sym, count) => pure (sym < codes, (sym, count)))
    (fun (sym, count) => do
      let l ← lens.index sym.toNat
      let c ← geta count l.toNat
      pure (sym + 1, ← seta count l.toNat (c + 1))) ((0 : UInt32), count)
  let mut root := bits
  let (max, _) ← cwhile (fun (max, brk) => pure (!brk && max ≥ 1, (max, brk)))
    (fun (max, brk) => do
      if (← geta count max.toNat) != 0 then pure (max, true) else pure (max - 1, brk)) (MAXBITS, false)
  if root > max then root := max
  itA type lens codes table bits work count max root

theorem itTail_wp (e : Env) (ca : Array Code) (count : Array UInt16) (bits min : UInt32) (left : Int32)
    (hcnt : CountOK e count 0) (hmin : min.toNat = e.l 0) (hsz : e.oc + e.cap ≤ ca.size) :
    Wp (itTail e.c.type e.c.lens e.c.table bits e.c.work count e.c.max min e.c.root left e.c.base e.c.extra
        e.c.match_) (e.hc ca)
      (fun r h' => ∃ ca', h' = e.hc ca' ∧ FrameCA e ca ca' ∧
        ((r.1 = 0 ∧ ∃ u, u ≤ e.cap ∧ r.2.1 = .ref e.rc (e.oc + u) ∧ r.2.2 = e.c.root) ∨
         (r.1 = 1 ∧ r.2.1 = e.c.table ∧ r.2.2 = bits)) ∧ (r.1 = 1 → e.c.type ≠ CODES)) := by
  have hR1 := e.h_R1
  have hroot := e.h_root
  have hpos := e.h_pos
  have hmxle : e.mx ≤ 15 := by
    have := lenAt_bounds (f := e.f) (n := e.n) (show e.m - 1 < Tc e.f e.n 15 by unfold Env.m; omega)
    exact this.2
  have hRmx := e.h_Rmx
  have hm15 : e.m = Tc e.f e.n 15 := rfl
  have hmx15 : e.mx = mxl e.f e.n := rfl
  have hR32 : e.c.root.toNat < 32 := by omega
  unfold itTail
  apply Wp.bind' (Q := fun r h' => r = 1 <<< e.c.root ∧ h' = e.hc ca) (Wp.pure_eq (shl32_eq hR32) ⟨rfl, rfl⟩)
  rintro used0 h' ⟨rfl, rfl⟩
  have hu0 : ((1 : UInt32) <<< e.c.root).toNat = 2 ^ e.R := by rw [u32_shl1 hR32, hroot]
  by_cases hb : tooBig e.c.type (1 <<< e.c.root) = true
  · rw [if_pos hb]
    exact Wp.pure' ⟨ca, rfl, ⟨rfl, fun _ _ => rfl⟩, Or.inr ⟨rfl, rfl, rfl⟩, fun _ => tooBig_ne hb⟩
  · rw [if_neg hb]
    have hb' : tooBig e.c.type (1 <<< e.c.root) = false := by simpa using hb
    have hu0cap : 2 ^ e.R ≤ e.cap := by
      by_cases hc : e.c.type = CODES
      · obtain ⟨h1, h2, _, _⟩ := e.h_codes hc
        have hcap := e.h_cap
        rw [if_pos hc] at hcap
        have : 2 ^ e.R ≤ 2 ^ 7 := Nat.pow_le_pow_right (by omega) (by omega)
        omega
      · have := tooBig_le e hb' hc
        omega
    have hMI0 : MI e 0 (TS.mk 0 0 min e.c.root 0 0xffffffff (1 <<< e.c.root) min 0 0 ((1 <<< e.c.root) - 1) left
        e.c.table default count 0) ca := by
      refine ⟨hpos, rfl, rfl, hmin, ?_, ?_, hcnt, hsz, ?_⟩
      · show (0 : UInt32).toNat = rev (e.l 0) (e.v 0)
        rw [show e.v 0 = 0 from val_zero hpos, rev_zero]; rfl
      · show ((1 <<< e.c.root) - 1 : UInt32).toNat = 2 ^ e.R - 1
        rw [u32_sub (by rw [hu0]; exact Nat.pow_pos (by omega)), hu0]
        simp [UInt32.toNat_one]
      · refine ⟨⟨0, ?_, ?_⟩, ?_, ?_, ?_, ?_, fun _ => ⟨rfl, rfl, ?_, ?_⟩, fun h => ?_⟩
        · show e.c.table = .ref e.rc (e.oc + 0); rw [e.h_table]; rfl
        · show 0 + 2 ^ e.c.root.toNat = ((1 : UInt32) <<< e.c.root).toNat; rw [hu0, hroot]; omega
        · show ((1 : UInt32) <<< e.c.root).toNat ≤ e.cap; omega
        · show 2 ^ e.R ≤ ((1 : UInt32) <<< e.c.root).toNat; omega
        · show 1 ≤ e.c.root.toNat; omega
        · show e.c.root.toNat ≤ 15; omega
        · show e.c.root.toNat = e.R; omega
        · show ((1 : UInt32) <<< e.c.root).toNat = 2 ^ e.R; omega
        · have := e.h_R0; have : e.l 0 = lenAt e.f e.n 0 := rfl; omega
    have hTle : e.m ≤ e.n := Tc_le 15 e.n
    have hn288 := e.h_n
    apply Wp.bind' (Q := fun s h' => (∃ ca', h' = e.hc ca' ∧ FrameCA e ca ca' ∧ s.exit = 1 ∧ Final e s ∧
          e.oc + e.cap ≤ ca'.size) ∨
        (∃ ca', h' = e.hc ca' ∧ FrameCA e ca ca' ∧ s.exit = 2 ∧ e.c.type ≠ CODES ∧ e.oc + e.cap ≤ ca'.size))
      (Wp.cwhile
        (fun (s : TS) h' => (∃ i ca', h' = e.hc ca' ∧ FrameCA e ca ca' ∧ MI e i s ca') ∨
          (∃ ca', h' = e.hc ca' ∧ FrameCA e ca ca' ∧ s.exit = 1 ∧ Final e s ∧ e.oc + e.cap ≤ ca'.size) ∨
          (∃ ca', h' = e.hc ca' ∧ FrameCA e ca ca' ∧ s.exit = 2 ∧ e.c.type ≠ CODES ∧ e.oc + e.cap ≤ ca'.size))
        (fun (s : TS) => if s.exit = 0 then e.m + 1 - s.sym.toNat else 0) _ ?_ (Or.inl ⟨0, ca, rfl, ⟨rfl, fun _ _ => rfl⟩, hMI0⟩) ?_)
    · rintro s h' hinv
      rcases hinv with ⟨ca', rfl, hf, hx, hfin, hsz'⟩ | ⟨ca', rfl, hf, hx, hnc, hsz'⟩
      · rw [if_neg (by simp [hx])]
        obtain ⟨⟨k, hn, hk⟩, hucap, hh⟩ := hfin
        by_cases hh0 : s.huff = 0
        · rw [if_neg (by simp [hh0])]
          show Wp (do let table ← Ptr.add e.c.table ↑s.used.toNat; pure (0, table, e.c.root)) _ _
          rw [e.h_table]
          apply Wp.bind' (wp_add e ca' e.oc s.used.toNat (by omega))
          rintro q h' ⟨rfl, rfl⟩
          exact Wp.pure' ⟨ca', rfl, hf, Or.inl ⟨rfl, s.used.toNat, hucap, rfl, rfl⟩, fun h => absurd (show (0 : Int32) = 1 from h) (by decide)⟩
        · rw [if_pos (by simpa using hh0)]
          have hhlt : s.huff.toNat < 2 ^ s.curr.toNat := by
            rcases hh with h0 | h0
            · exact absurd (UInt32.toNat_inj.mp (by rw [h0]; rfl)) hh0
            · exact h0
          have hidx : e.oc + k + s.huff.toNat < ca'.size := by
            have := hf.1; omega
          show Wp (do let __r ← storeCode s.next s.huff.toNat ⟨64, (s.len - s.drop).toUInt8, 0⟩
                      let table ← Ptr.add e.c.table ↑s.used.toNat; pure (0, table, e.c.root)) _ _
          unfold storeCode
          rw [hn, e.h_table]
          apply Wp.bind' (Q := fun _ h' => h' = e.hc (ca'.set! (e.oc + k + s.huff.toNat) ⟨64, (s.len - s.drop).toUInt8, 0⟩))
          · apply Wp.bind' (wp_add e ca' (e.oc + k) s.huff.toNat (by omega))
            rintro q h' ⟨rfl, rfl⟩
            refine ⟨(), _, Ptr.store_ok (e.get_hc ca') e.h_ro (by omega), ?_⟩
            rw [Env.hc_hc]
          · rintro _ h' rfl
            apply Wp.bind' (wp_add e _ e.oc s.used.toNat (by rw [Array.size_set!]; omega))
            rintro q h' ⟨rfl, rfl⟩
            refine Wp.pure' ⟨_, rfl, ?_, Or.inl ⟨rfl, s.used.toNat, hucap, rfl, rfl⟩, fun h => absurd (show (0 : Int32) = 1 from h) (by decide)⟩
            refine ⟨by rw [Array.size_set!]; exact hf.1, fun x hx => ?_⟩
            have hne : e.oc + k + s.huff.toNat ≠ x := by omega
            rw [getElem?_set!_ne hne]
            exact hf.2 x hx
      · rw [if_pos (by simp [hx])]
        exact Wp.pure' ⟨ca', rfl, hf, Or.inr ⟨rfl, rfl, rfl⟩, fun _ => hnc⟩
    · rintro s h' hinv
      rcases hinv with ⟨i, ca', rfl, hf, hmi⟩ | ⟨ca', rfl, hf, hx, hfin, hsz'⟩ | ⟨ca', rfl, hf, hx, hnc, hsz'⟩
      · right
        have hex : s.exit = 0 := hmi.2.1
        have hsymi : s.sym.toNat = i := hmi.2.2.1
        have hi : i < e.m := hmi.1
        obtain ⟨s2, h2, hrun, ca2, hh, hf2, hpost⟩ := hereTop_wp e i s ca' hmi
        subst hh
        refine ⟨s, e.hc ca', s2, e.hc ca2, ?_, ?_, ?_, ?_⟩
        · show (pure (s.exit == 0, s) : M _) _ = _
          simp [hex]
        · rw [buildStep_eq]; exact hrun
        · rcases hpost with ⟨him, hMI⟩ | ⟨him, hx, hfin, hsz2⟩ | ⟨hx, hnc, hsz2⟩
          · exact Or.inl ⟨i + 1, ca2, rfl, hf.trans hf2, hMI⟩
          · exact Or.inr (Or.inl ⟨ca2, rfl, hf.trans hf2, hx, hfin, hsz2⟩)
          · exact Or.inr (Or.inr ⟨ca2, rfl, hf.trans hf2, hx, hnc, hsz2⟩)
        · rcases hpost with ⟨him, hMI⟩ | ⟨him, hx, hfin, hsz2⟩ | ⟨hx, hnc, hsz2⟩
          · have h3 : s2.exit = 0 := hMI.2.1
            have h4 : s2.sym.toNat = i + 1 := hMI.2.2.1
            simp only [hex, h3, if_true, hsymi, h4]; omega
          · simp only [hx, hex]; simp; omega
          · simp only [hx, hex]; simp; omega
      · left
        refine ⟨s, e.hc ca', ?_, Or.inl ⟨ca', rfl, hf, hx, hfin, hsz'⟩⟩
        show (pure (s.exit == 0, s) : M _) _ = _
        simp [hx]
      · left
        refine ⟨s, e.hc ca', ?_, Or.inr ⟨ca', rfl, hf, hx, hnc, hsz'⟩⟩
        show (pure (s.exit == 0, s) : M _) _ = _
        simp [hx]
    · dsimp only
      split
      · exact lt_fuel (by omega)
      · exact lt_fuel (by omega)

def kraftCond : Int32 × Bool × UInt32 → M (Bool × (Int32 × Bool × UInt32)) :=
  fun (left, bad, len) => pure (!bad && len ≤ MAXBITS, (left, bad, len))

def kraftBody (count : Array UInt16) : Int32 × Bool × UInt32 → M (Int32 × Bool × UInt32) :=
  fun (left, bad, len) => do
    if left < 0 then ub "left shift of a negative value" else
    let left ← chk32 (left.toInt * 2)
    let cc ← geta count len.toNat
    let left ← chk32 (left.toInt - cc.toNat)
    if left < 0 then pure (left, true, len) else pure (left, bad, len + 1)

theorem i32_lt_zero {x : Int32} : x < 0 ↔ x.toInt < 0 := by
  rw [Int32.lt_iff_toInt_lt, Int32.toInt_zero]

theorem kraftBody_eq (count : Array UInt16) (left : Int32) (bad : Bool) (len : UInt32)
    (hl0 : 0 ≤ left.toInt) (hi : len.toNat < count.size)
    (hr1 : left.toInt * 2 ≤ 2147483647) :
    kraftBody count (left, bad, len) =
      pure (if left.toInt * 2 - (count[len.toNat]).toNat < 0 then
              (Int32.ofInt (left.toInt * 2 - (count[len.toNat]).toNat), true, len)
            else (Int32.ofInt (left.toInt * 2 - (count[len.toNat]).toNat), bad, len + 1)) := by
  simp only [kraftBody]
  have hn : ¬ (left < 0) := by rw [i32_lt_zero]; omega
  rw [if_neg hn]
  have hr2 : -2147483648 ≤ left.toInt * 2 := by omega
  rw [chk32_eq hr2 hr1, M_pure_bind, geta_eq hi, M_pure_bind]
  have hv1 : -2147483648 ≤ (Int32.ofInt (left.toInt * 2)).toInt - (count[len.toNat]).toNat := by
    rw [i32_ofInt_toInt hr2 hr1]; have := UInt16.toNat_lt count[len.toNat]; omega
  have hv2 : (Int32.ofInt (left.toInt * 2)).toInt - (count[len.toNat]).toNat ≤ 2147483647 := by
    rw [i32_ofInt_toInt hr2 hr1]; omega
  rw [chk32_eq hv1 hv2, M_pure_bind]
  rw [i32_ofInt_toInt hr2 hr1]
  have hlt : Int32.ofInt (left.toInt * 2 - (count[len.toNat]).toNat) < 0 ↔ left.toInt * 2 - (count[len.toNat]).toNat < 0 := by
    rw [i32_lt_zero, i32_ofInt_toInt (by have := UInt16.toNat_lt count[len.toNat]; omega) (by omega)]
  by_cases hneg : left.toInt * 2 - (count[len.toNat]).toNat < 0
  · rw [if_pos (hlt.mpr hneg), if_pos hneg]
  · rw [if_neg (fun h => hneg (hlt.mp h)), if_neg hneg]

/-- The Kraft loop of `inflate_table`. -/
theorem kraft_loop (f : Nat → Nat) (n : Nat) (count : Array UInt16) (hs : count.size = 16)
    (hc : ∀ l, 1 ≤ l → l ≤ 15 → (count.getD l 0).toNat = cnt f n l) (h : Heap) :
    Wp (cwhile kraftCond (kraftBody count) ((1 : Int32), false, (1 : UInt32))) h
      (fun r h' => h' = h ∧ ((r.2.1 = true ∧ ¬ Fits f n) ∨
        (r.2.1 = false ∧ Fits f n ∧ r.1.toInt = 2 ^ 15 - (Kc f n 15 : Int)))) := by
  refine Wp.cwhile
    (fun (x : Int32 × Bool × UInt32) h' => h' = h ∧ 1 ≤ x.2.2.toNat ∧ x.2.2.toNat ≤ 16 ∧
      (x.2.1 = false → 0 ≤ x.1.toInt ∧ x.1.toInt = 2 ^ (x.2.2.toNat - 1) - (Kc f n (x.2.2.toNat - 1) : Int) ∧
        ∀ l, 1 ≤ l → l < x.2.2.toNat → Kc f n l ≤ 2 ^ l) ∧
      (x.2.1 = true → ¬ Fits f n))
    (fun (x : Int32 × Bool × UInt32) => if x.2.1 then 0 else 17 - x.2.2.toNat) _ ?_ ?_ ?_
  · rintro ⟨left, bad, len⟩ h' ⟨rfl, hl1, hl2, hnb, hb⟩
    dsimp only at hl1 hl2 hnb hb
    by_cases hc' : (!bad && decide (len ≤ MAXBITS)) = true
    · right
      simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hc'
      obtain ⟨hbad, hle⟩ := hc'
      have hle' : len.toNat ≤ 15 := by
        have := UInt32.le_iff_toNat_le.mp hle; exact this
      obtain ⟨hp, hlv, hfit⟩ := hnb hbad
      have hcnt := hc len.toNat hl1 hle'
      have hlt16 : len.toNat < count.size := by omega
      have hcc : (count[len.toNat]).toNat = cnt f n len.toNat := by
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hlt16] at hcnt; simpa using hcnt
      have hpow : (2:Int) ^ (len.toNat - 1) ≤ 16384 := by
        have h14 : 2 ^ (len.toNat - 1) ≤ 2 ^ 14 := Nat.pow_le_pow_right (by omega) (by omega)
        have : ((2 ^ (len.toNat - 1) : Nat) : Int) ≤ ((2 ^ 14 : Nat) : Int) := Int.ofNat_le.mpr h14
        simpa [Int.natCast_pow] using this
      have hKc := Kc_succ' (f := f) (n := n) hl1
      have hcccast : ((count[len.toNat]).toNat : Int) = (cnt f n len.toNat : Int) := by rw [hcc]
      have hp2 : (2:Int) ^ len.toNat = 2 * 2 ^ (len.toNat - 1) := by
        obtain ⟨r, hr⟩ : ∃ r, len.toNat = r + 1 := ⟨len.toNat - 1, by omega⟩
        rw [hr]; simp [Int.pow_succ, Int.mul_comm]
      have heq := kraftBody_eq count left bad len hp (by omega) (by omega)
      have hbody : kraftBody count (left, bad, len) h' = .ok
          ((if left.toInt * 2 - (count[len.toNat]).toNat < 0 then
              (Int32.ofInt (left.toInt * 2 - (count[len.toNat]).toNat), true, len)
            else (Int32.ofInt (left.toInt * 2 - (count[len.toNat]).toNat), bad, len + 1)), h') := by
        rw [heq]; rfl
      have hcond : kraftCond (left, bad, len) h' = .ok ((true, (left, bad, len)), h') := by
        show (pure ((!bad && decide (len ≤ MAXBITS)), (left, bad, len)) : M _) h' = _
        rw [show ((!bad && decide (len ≤ MAXBITS))) = true from by
          simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq]; exact ⟨hbad, hle⟩]
        rfl
      refine ⟨(left, bad, len), h', _, h', hcond, hbody, ?_, ?_⟩
      · by_cases hneg : left.toInt * 2 - (count[len.toNat]).toNat < 0
        · rw [if_pos hneg]
          refine ⟨rfl, hl1, hl2, fun hx => by simp at hx, fun _ => ?_⟩
          intro hfit'
          have := hfit' len.toNat hl1 hle'
          have h3 : (Kc f n len.toNat : Int) ≤ 2 ^ len.toNat := by exact_mod_cast this
          generalize left.toInt = L at hlv hneg
          generalize (2:Int) ^ (len.toNat - 1) = P at hlv hp2
          generalize (2:Int) ^ len.toNat = Q at hp2 h3
          generalize ((count[len.toNat]).toNat : Int) = cc at hneg hcccast
          omega
        · rw [if_neg hneg]
          have hu : (len + 1).toNat = len.toNat + 1 := u32_succ (by omega)
          refine ⟨rfl, by rw [hu]; omega, by rw [hu]; omega, fun _ => ?_, fun hx => by simp [hbad] at hx⟩
          have hv1 : -2147483648 ≤ left.toInt * 2 - (count[len.toNat]).toNat := by omega
          have hv2 : left.toInt * 2 - (count[len.toNat]).toNat ≤ 2147483647 := by omega
          rw [hu, i32_ofInt_toInt hv1 hv2]
          simp only [Nat.add_sub_cancel]
          refine ⟨by omega, ?_, ?_⟩
          · rw [hcccast] at *
            omega
          · intro l hl1' hl2'
            rcases Nat.lt_or_ge l len.toNat with h4 | h4
            · exact hfit l hl1' h4
            · have hl : l = len.toNat := by omega
              rw [hl]
              have hk : (Kc f n len.toNat : Int) ≤ 2 ^ len.toNat := by
                have hneg' := hneg
                generalize left.toInt = L at hlv hneg'
                generalize (2:Int) ^ (len.toNat - 1) = P at hlv hp2
                generalize (2:Int) ^ len.toNat = Q at hp2 ⊢
                generalize ((count[len.toNat]).toNat : Int) = cc at hneg' hcccast
                omega
              exact_mod_cast hk
      · by_cases hneg : left.toInt * 2 - (count[len.toNat]).toNat < 0
        · rw [if_pos hneg]; simp [hbad]; omega
        · rw [if_neg hneg]
          have hu : (len + 1).toNat = len.toNat + 1 := u32_succ (by omega)
          simp [hbad, hu]; omega
    · left
      have hcond : kraftCond (left, bad, len) h' = .ok ((false, (left, bad, len)), h') := by
        show (pure ((!bad && decide (len ≤ MAXBITS)), (left, bad, len)) : M _) h' = _
        have : ((!bad && decide (len ≤ MAXBITS))) = false := by
          cases hh : ((!bad && decide (len ≤ MAXBITS)))
          · rfl
          · exact absurd hh hc'
        rw [this]; rfl
      refine ⟨(left, bad, len), h', hcond, rfl, ?_⟩
      cases hbad : bad
      · right
        have hn : ¬ (len ≤ MAXBITS) := by
          intro hle; apply hc'; simp [hbad, hle]
        have hn' : 16 ≤ len.toNat := by
          have := (not_congr UInt32.le_iff_toNat_le).mp hn
          have h15 : MAXBITS.toNat = 15 := rfl
          omega
        obtain ⟨hp, hlv, hfit⟩ := hnb hbad
        have h16 : len.toNat = 16 := by omega
        refine ⟨rfl, fun l hl1' hl2' => hfit l hl1' (by omega), ?_⟩
        rw [hlv, h16]
      · left
        exact ⟨rfl, hb hbad⟩
  · refine ⟨rfl, Nat.le_refl _, by decide, fun _ => ⟨by decide, ?_, fun l h1 h2 => by simp at h2; omega⟩, fun hx => by simp at hx⟩
    show ((1 : Int32).toInt) = 2 ^ 0 - (Kc f n 0 : Int)
    have hK0 : Kc f n 0 = 0 := rfl
    rw [hK0]; decide
  · show (if false = true then 0 else 17 - (1 : UInt32).toNat) < fuel
    exact lt_fuel (by decide)

def offsCond : UInt32 × Array UInt16 → M (Bool × (UInt32 × Array UInt16)) :=
  fun (len, offs) => pure (len < MAXBITS, (len, offs))

def offsBody (count : Array UInt16) : UInt32 × Array UInt16 → M (UInt32 × Array UInt16) :=
  fun (len, offs) => do
    let a ← geta offs len.toNat
    let b ← geta count len.toNat
    pure (len + 1, ← seta offs (len + 1).toNat (a + b))

/-- The loop that computes the offsets of the lengths in `work`. -/
theorem offs_loop (f : Nat → Nat) (n : Nat) (hn : n ≤ 288) (count : Array UInt16) (hs : count.size = 16)
    (hc : ∀ l, 1 ≤ l → l ≤ 15 → (count.getD l 0).toNat = cnt f n l) (h : Heap) :
    Wp (cwhile offsCond (offsBody count) ((1 : UInt32), (Array.replicate 16 (0 : UInt16)).set! 1 0)) h
      (fun r h' => h' = h ∧ r.2.size = 16 ∧ ∀ j, 1 ≤ j → j ≤ 15 → (r.2.getD j 0).toNat = Tc f n (j - 1)) := by
  refine Wp.cwhile
    (fun (x : UInt32 × Array UInt16) h' => h' = h ∧ 1 ≤ x.1.toNat ∧ x.1.toNat ≤ 15 ∧ x.2.size = 16 ∧
      ∀ j, 1 ≤ j → j ≤ x.1.toNat → (x.2.getD j 0).toNat = Tc f n (j - 1))
    (fun (x : UInt32 × Array UInt16) => 15 - x.1.toNat) _ ?_ ?_ ?_
  · rintro ⟨len, offs⟩ h' ⟨rfl, hl1, hl2, hsz, hj⟩
    dsimp only at hl1 hl2 hsz hj
    by_cases hlt : len < MAXBITS
    · right
      have hlt' : len.toNat < 15 := by have := UInt32.lt_iff_toNat_lt.mp hlt; exact this
      have hc1 := hc len.toNat hl1 (by omega)
      have hlt16 : len.toNat < count.size := by omega
      have hlt16' : len.toNat < offs.size := by omega
      have hcc : (count[len.toNat]).toNat = cnt f n len.toNat := by
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hlt16] at hc1; simpa using hc1
      have hoo : (offs[len.toNat]).toNat = Tc f n (len.toNat - 1) := by
        have := hj len.toNat hl1 (Nat.le_refl _)
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hlt16'] at this; simpa using this
      have hTs := Tc_succ' (f := f) (n := n) hl1
      have hTle := Tc_le (f := f) len.toNat n
      have hu : (len + 1).toNat = len.toNat + 1 := u32_succ (by omega)
      have hsz2 : (len + 1).toNat < offs.size := by omega
      have hrun : offsBody count (len, offs) = pure (len + 1, offs.set! (len + 1).toNat (offs[len.toNat] + count[len.toNat])) := by
        simp only [offsBody]
        rw [geta_eq hlt16', M_pure_bind, geta_eq hlt16, M_pure_bind, seta_eq hsz2, M_pure_bind]
      have hadd : (offs[len.toNat] + count[len.toNat]).toNat = Tc f n len.toNat := by
        rw [UInt16.toNat_add, hoo, hcc]
        have : Tc f n len.toNat = Tc f n (len.toNat - 1) + cnt f n len.toNat := hTs
        have := Tc_le (f := f) len.toNat n
        rw [Nat.mod_eq_of_lt (by omega)]
        omega
      refine ⟨(len, offs), h', (len + 1, offs.set! (len + 1).toNat (offs[len.toNat] + count[len.toNat])), h', ?_, ?_, ?_, ?_⟩
      · show (pure (decide (len < MAXBITS), (len, offs)) : M _) h' = _
        simp [hlt]
      · rw [hrun]; rfl
      · refine ⟨rfl, by dsimp only; omega, by dsimp only; omega, by dsimp only; rw [Array.size_set!]; exact hsz, ?_⟩
        intro j hj1 hj2
        dsimp only at hj2 ⊢
        rw [hu] at hj2
        rw [getD_set!]
        by_cases hjl : j = len.toNat + 1
        · rw [if_pos ⟨by rw [hu, hjl], hsz2⟩, hadd, hjl]; rfl
        · rw [if_neg (fun hh => hjl (by rw [hu] at hh; omega))]
          exact hj j hj1 (by omega)
      · dsimp only; omega
    · left
      have hn : ¬ (len.toNat < 15) := fun hh => hlt (UInt32.lt_iff_toNat_lt.mpr hh)
      refine ⟨(len, offs), h', ?_, rfl, hsz, ?_⟩
      · show (pure (decide (len < MAXBITS), (len, offs)) : M _) h' = _
        simp [hlt]
      · intro j hj1 hj2
        exact hj j hj1 (by omega)
  · refine ⟨rfl, by decide, by decide, by simp, ?_⟩
    intro j hj1 hj2
    have hj3 : j ≤ 1 := hj2
    have : j = 1 := by omega
    subst this
    show ((Array.replicate 16 (0 : UInt16)).set! 1 0 |>.getD 1 0).toNat = Tc f n 0
    rfl
  · exact lt_fuel (by simp)

theorem wro (h : Heap) (w : WRef) : Space.ro h w = false := by cases w <;> rfl

theorem wput_self {h : Heap} {w : WRef} {a : Array UInt16} (hg : Space.get h w = some a) : Space.put h w a = h := by
  cases w with
  | blk b => simp only [Space.put, Space.get] at *; rw [upd_self _ _ _ hg]
  | dstate_bl_count d =>
    simp only [Space.get, Option.map_eq_some_iff] at hg
    obtain ⟨s, hs, rfl⟩ := hg
    simp only [Space.put, hs]; rw [upd_self _ _ _ hs]
  | istate_lens d =>
    simp only [Space.get, Option.map_eq_some_iff] at hg
    obtain ⟨s, hs, rfl⟩ := hg
    simp only [Space.put, hs]; rw [upd_self _ _ _ hs]
  | istate_work d =>
    simp only [Space.get, Option.map_eq_some_iff] at hg
    obtain ⟨s, hs, rfl⟩ := hg
    simp only [Space.put, hs]; rw [upd_self _ _ _ hs]

theorem cput_self {h : Heap} {r : CodeRef} {a : Array Code} (hg : Space.get h r = some a) : Space.put h r a = h := by
  cases r with
  | istate_codes d =>
    simp only [Space.get, Option.map_eq_some_iff] at hg
    obtain ⟨s, hs, rfl⟩ := hg
    simp only [Space.put, hs]; rw [upd_self _ _ _ hs]
  | st_lenfix => rfl
  | st_distfix => rfl

theorem cnt_zero (f : Nat → Nat) (l : Nat) : cnt f 0 l = 0 := rfl

def sortCond (codes : UInt32) : UInt32 × Array UInt16 → M (Bool × (UInt32 × Array UInt16)) :=
  fun (sym, offs) => pure (sym < codes, (sym, offs))

def sortBody (lens work : WPtr) : UInt32 × Array UInt16 → M (UInt32 × Array UInt16) :=
  fun (sym, offs) => do
    let l ← lens.index sym.toNat
    if l != 0 then
      let l ← lens.index sym.toNat
      let o ← geta offs l.toNat
      let offs ← seta offs l.toNat (o + 1)
      let q ← work.add o.toNat
      Ptr.store q sym.toUInt16
      pure (sym + 1, offs)
    else pure (sym + 1, offs)

/-- What the sort loop has done after it has looked at the symbols below `k`. -/
def SortInv (f : Nat → Nat) (n ow : Nat) (wa : Array UInt16) (k : Nat) (offs : Array UInt16) (wak : Array UInt16) : Prop :=
  offs.size = 16 ∧ (∀ l, 1 ≤ l → l ≤ 15 → (offs.getD l 0).toNat = Tc f n (l - 1) + cnt f k l) ∧
  wak.size = wa.size ∧ (∀ x, (x < ow ∨ ow + n ≤ x) → wak[x]? = wa[x]?) ∧
  (∀ l j, 1 ≤ l → l ≤ 15 → j < cnt f k l →
    wak[ow + Tc f n (l - 1) + j]? = some (UInt16.ofNat ((fl f l k).getD j 0)))

theorem sortInv_skip {f : Nat → Nat} {n ow : Nat} {wa offs wak : Array UInt16} {k : Nat} (hf0 : f k = 0)
    (h : SortInv f n ow wa k offs wak) : SortInv f n ow wa (k + 1) offs wak := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have hc : ∀ l, 1 ≤ l → cnt f (k + 1) l = cnt f k l := by
    intro l hl; rw [cnt_step, if_neg (by omega)]; rfl
  have hfl : ∀ l, 1 ≤ l → fl f l (k + 1) = fl f l k := fun l hl => fl_succ_ne (by omega)
  refine ⟨h1, fun l hl1 hl2 => ?_, h3, h4, fun l j hl1 hl2 hj => ?_⟩
  · rw [hc l hl1]; exact h2 l hl1 hl2
  · rw [hc l hl1] at hj; rw [hfl l hl1]; exact h5 l j hl1 hl2 hj

theorem sortInv_step {f : Nat → Nat} {n ow : Nat} {wa offs wak : Array UInt16} {k l : Nat} (hkn : k < n)
    (hfk : f k = l) (hl1 : 1 ≤ l) (hl2 : l ≤ 15) (hwa : ow + n ≤ wa.size) (hn : n ≤ 288)
    (h : SortInv f n ow wa k offs wak) :
    SortInv f n ow wa (k + 1) (offs.set! l (offs.getD l 0 + 1))
      (wak.set! (ow + (offs.getD l 0).toNat) (UInt16.ofNat k)) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have hoff := h2 l hl1 hl2
  have hj0 : cnt f k l < cnt f n l := cnt_lt hkn hfk
  have hTl := Tc_succ' (f := f) (n := n) hl1
  have hTn := Tc_le (f := f) l n
  have hpos : ow + (offs.getD l 0).toNat < wak.size := by omega
  have hcnew : ∀ l', cnt f (k + 1) l' = cnt f k l' + (if l' = l then 1 else 0) := by
    intro l'; rw [cnt_step]; by_cases h : l' = l
    · rw [if_pos (by omega), if_pos h]
    · rw [if_neg (by omega), if_neg h]
  have hn65 : (offs.getD l 0).toNat + 1 < 65536 := by omega
  have hadd : (offs.getD l 0 + 1).toNat = (offs.getD l 0).toNat + 1 := by
    rw [UInt16.toNat_add]; simp only [UInt16.toNat_one]; exact Nat.mod_eq_of_lt (by omega)
  refine ⟨by rw [Array.size_set!]; exact h1, fun l' hl1' hl2' => ?_, by rw [Array.size_set!]; exact h3, ?_, ?_⟩
  · rw [getD_set!, hcnew]
    by_cases hll : l' = l
    · subst hll
      rw [if_pos ⟨rfl, by omega⟩, hadd, if_pos rfl]; omega
    · rw [if_neg (fun hh => hll hh.1.symm), if_neg hll]; simp only [Nat.add_zero]; exact h2 l' hl1' hl2'
  · intro x hx
    have hne : ow + (offs.getD l 0).toNat ≠ x := by omega
    rw [getElem?_set!_ne hne]; exact h4 x hx
  · intro l' j hl1' hl2' hj
    rw [hcnew] at hj
    have hTs' := Tc_succ' (f := f) (n := n) hl1'
    have hTle' : Tc f n l' ≤ n := Tc_le l' n
    have hcm := cnt_mono (f := f) (l := l') (show k ≤ n by omega)
    have hset : ∀ pos, (wak.set! (ow + (offs.getD l 0).toNat) (UInt16.ofNat k))[pos]? =
        if ow + (offs.getD l 0).toNat = pos then some (UInt16.ofNat k) else wak[pos]? := by
      intro pos
      rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
      by_cases hp : ow + (offs.getD l 0).toNat = pos
      · rw [if_pos hp, if_pos hp, if_pos (by omega)]
      · rw [if_neg hp, if_neg hp]
    by_cases hll : l' = l
    · subst hll
      rw [if_pos rfl] at hj
      by_cases hjj : j = cnt f k l'
      · subst hjj
        rw [hset, if_pos (by omega), fl_getD_new hfk]
      · have hjlt : j < cnt f k l' := by omega
        rw [hset, if_neg (by omega), h5 l' j hl1' hl2' hjlt, fl_getD_old hfk hjlt]
    · rw [if_neg hll] at hj
      simp only [Nat.add_zero] at hj
      have hne : ow + (offs.getD l 0).toNat ≠ ow + Tc f n (l' - 1) + j := by
        rcases Nat.lt_or_gt_of_ne hll with hlt | hgt
        · have m1 := Tc_mono (f := f) (n := n) (show l' ≤ l - 1 by omega)
          omega
        · have m2 := Tc_mono (f := f) (n := n) (show l ≤ l' - 1 by omega)
          omega
      rw [hset, if_neg hne, h5 l' j hl1' hl2' hj, fl_succ_ne (by omega)]

theorem sort_loop (f : Nat → Nat) (n : Nat) (hn : n ≤ 288) (rl rw : WRef) (hne : rw ≠ rl) (ol ow : Nat)
    (la wa : Array UInt16) (codes : UInt32) (hcodes : codes.toNat = n) (h : Heap)
    (hgl : Space.get h rl = some la) (hgw : Space.get h rw = some wa) (hla : ol + n ≤ la.size)
    (hf : ∀ k, f k = (la.getD (ol + k) 0).toNat) (hf15 : ∀ k, k < n → f k ≤ 15) (hwa : ow + n ≤ wa.size)
    (offs0 : Array UInt16) (ho : offs0.size = 16)
    (ho' : ∀ j, 1 ≤ j → j ≤ 15 → (offs0.getD j 0).toNat = Tc f n (j - 1)) :
    Wp (cwhile (sortCond codes) (sortBody (Ptr.ref rl ol) (Ptr.ref rw ow)) ((0 : UInt32), offs0)) h
      (fun r h' => r.1.toNat = n ∧ ∃ wa', h' = Space.put h rw wa' ∧ SortInv f n ow wa n r.2 wa') := by
  refine Wp.cwhile
    (fun (x : UInt32 × Array UInt16) h' => x.1.toNat ≤ n ∧ ∃ wak, h' = Space.put h rw wak ∧ SortInv f n ow wa x.1.toNat x.2 wak)
    (fun (x : UInt32 × Array UInt16) => n - x.1.toNat) _ ?_ ?_ ?_
  · rintro ⟨sym, offs⟩ h' ⟨hsn, wak, rfl, hinv⟩
    dsimp only at hsn hinv
    by_cases hlt : sym < codes
    · right
      have hk : sym.toNat < n := by have := UInt32.lt_iff_toNat_lt.mp hlt; omega
      have hglw : Space.get (Space.put h rw wak) rw = some wak := wget_put_self hgw wak
      have hgll : Space.get (Space.put h rw wak) rl = some la := by rw [wget_put_ne hne]; exact hgl
      have hkl : ol + sym.toNat < la.size := by omega
      have hfk : f sym.toNat = (la[ol + sym.toNat]'hkl).toNat := by
        rw [hf, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hkl]; simp
      have hcond : sortCond codes (sym, offs) (Space.put h rw wak) = .ok ((true, (sym, offs)), Space.put h rw wak) := by
        show (pure (decide (sym < codes), (sym, offs)) : M _) _ = _
        simp [hlt]
      have hw : Wp (sortBody (Ptr.ref rl ol) (Ptr.ref rw ow) (sym, offs)) (Space.put h rw wak)
          (fun r h2 => ∃ wak', h2 = Space.put h rw wak' ∧ r.1.toNat = sym.toNat + 1 ∧
            SortInv f n ow wa (sym.toNat + 1) r.2 wak') := by
        simp only [sortBody]
        apply Wp.bind' (Q := fun r h2 => r = la[ol + sym.toNat]'hkl ∧ h2 = Space.put h rw wak)
          (Wp.of_eq (Ptr.index_ok hgll hkl) ⟨rfl, rfl⟩)
        rintro l h2 ⟨rfl, rfl⟩
        have hu : (sym + 1).toNat = sym.toNat + 1 := u32_succ (by omega)
        by_cases hl0 : (la[ol + sym.toNat]'hkl != 0) = true
        · rw [if_pos hl0]
          have hl0' : f sym.toNat ≠ 0 := by
            rw [hfk]; intro h0
            apply (by simpa using hl0 : ¬ (la[ol + sym.toNat]'hkl = 0))
            exact UInt16.toNat_inj.mp (by rw [h0]; rfl)
          have hf15' := hf15 sym.toNat hk
          apply Wp.bind' (Q := fun r h2 => r = la[ol + sym.toNat]'hkl ∧ h2 = Space.put h rw wak)
            (Wp.of_eq (Ptr.index_ok hgll hkl) ⟨rfl, rfl⟩)
          rintro l2 h2 ⟨rfl, rfl⟩
          have hlt16 : (la[ol + sym.toNat]'hkl).toNat < offs.size := by rw [← hfk, hinv.1]; omega
          apply Wp.bind' (Q := fun r h2 => r = offs[(la[ol + sym.toNat]'hkl).toNat]'hlt16 ∧ h2 = Space.put h rw wak)
            (Wp.pure_eq (geta_eq hlt16) ⟨rfl, rfl⟩)
          rintro o h2 ⟨rfl, rfl⟩
          apply Wp.bind' (Q := fun r h2 => r = offs.set! (la[ol + sym.toNat]'hkl).toNat
              (offs[(la[ol + sym.toNat]'hkl).toNat]'hlt16 + 1) ∧ h2 = Space.put h rw wak)
            (Wp.pure_eq (seta_eq hlt16) ⟨rfl, rfl⟩)
          rintro offs2 h2 ⟨rfl, rfl⟩
          have hog : (offs.getD (f sym.toNat) 0) = offs[(la[ol + sym.toNat]'hkl).toNat]'hlt16 := by
            rw [hfk, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hlt16]; simp
          have hoff := hinv.2.1 (f sym.toNat) (by omega) hf15'
          have hj0 := cnt_lt (f := f) hk rfl
          have hTl := Tc_succ' (f := f) (n := n) (show 1 ≤ f sym.toNat by omega)
          have hTn := Tc_le (f := f) (f sym.toNat) n
          have hobd : ow + (offs[(la[ol + sym.toNat]'hkl).toNat]'hlt16).toNat < wak.size := by
            have := hinv.2.2.1
            rw [← hog]; omega
          apply Wp.bind' (Q := fun q h2 => q = Ptr.ref rw (ow + (offs[(la[ol + sym.toNat]'hkl).toNat]'hlt16).toNat) ∧
              h2 = Space.put h rw wak)
            (Wp.of_eq (Ptr.add_nat_ok hglw (by omega)) ⟨rfl, rfl⟩)
          rintro q h2 ⟨rfl, rfl⟩
          apply Wp.bind' (Q := fun _ h2 => h2 = Space.put h rw
              (wak.set! (ow + (offs[(la[ol + sym.toNat]'hkl).toNat]'hlt16).toNat) sym.toUInt16))
          · refine ⟨(), _, Ptr.store_ok hglw (wro _ _) hobd, ?_⟩
            rw [wput_put]
          · rintro _ h2 rfl
            refine Wp.pure' ⟨_, rfl, hu, ?_⟩
            have hsy : sym.toUInt16 = UInt16.ofNat sym.toNat := by
              apply UInt16.toNat_inj.mp
              rw [UInt32.toNat_toUInt16, UInt16.toNat_ofNat']
            rw [hsy, ← hog]
            have := sortInv_step (f := f) (n := n) (ow := ow) (wa := wa) (offs := offs) (wak := wak) (k := sym.toNat)
              (l := f sym.toNat) hk rfl (by omega) hf15' hwa hn hinv
            show SortInv f n ow wa (sym.toNat + 1) (offs.set! (la[ol + sym.toNat]'hkl).toNat (offs.getD (f sym.toNat) 0 + 1))
              (wak.set! (ow + (offs.getD (f sym.toNat) 0).toNat) (UInt16.ofNat sym.toNat))
            rw [← hfk]
            exact this
        · rw [if_neg hl0]
          have hf0 : f sym.toNat = 0 := by
            have : (la[ol + sym.toNat]'hkl) = 0 := by simpa using hl0
            rw [hfk, this]; rfl
          exact Wp.pure' ⟨wak, rfl, hu, sortInv_skip hf0 hinv⟩
      obtain ⟨s2, h2, hrun, wak', rfl, hs2, hinv'⟩ := hw
      refine ⟨(sym, offs), _, s2, _, hcond, hrun, ⟨by omega, wak', rfl, by rw [hs2]; exact hinv'⟩, ?_⟩
      dsimp only; omega
    · left
      have hsn' : sym.toNat = n := by
        have : ¬ sym.toNat < n := fun hh => hlt (by rw [UInt32.lt_iff_toNat_lt, hcodes]; exact hh)
        omega
      refine ⟨(sym, offs), _, ?_, ⟨hsn', wak, rfl, by have := hinv; rw [hsn'] at this; exact this⟩⟩
      show (pure (decide (sym < codes), (sym, offs)) : M _) _ = _
      simp [hlt]
  · refine ⟨by simp [hcodes], wa, ?_, ?_⟩
    · rw [wput_self hgw]
    · refine ⟨ho, fun l hl1 hl2 => ?_, rfl, fun _ _ => rfl, fun l j _ _ hj => ?_⟩
      · show (offs0.getD l 0).toNat = Tc f n (l - 1) + cnt f 0 l
        rw [cnt_zero]; exact ho' l hl1 hl2
      · have hj' : j < cnt f 0 l := hj
        rw [cnt_zero] at hj'; omega
  · exact lt_fuel (by omega)

theorem ws_getD {f : Nat → Nat} {n i : Nat} (hi : i < Tc f n 15) :
    (wsAux f n 15).getD i 0 = (fl f (lenAt f n i) n).getD (i - Tc f n (lenAt f n i - 1)) 0 := by
  obtain ⟨b1, b2⟩ := lenAt_bounds (f := f) (n := n) hi
  have blk := (lenAt_eq_iff (f := f) (n := n) (l := lenAt f n i) b1 b2 hi).mp rfl
  obtain ⟨rest, h1, _⟩ := wsAux_split (f := f) (n := n) b2
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ, ℓ = lenAt f n i := ⟨_, rfl⟩
  rw [← hℓ] at b1 b2 blk h1 ⊢
  obtain ⟨m, rfl⟩ : ∃ m, ℓ = m + 1 := ⟨ℓ - 1, by omega⟩
  have hA : (wsAux f n m).length = Tc f n m := wsAux_length m
  have hB : (fl f (m + 1) n).length = cnt f n (m + 1) := rfl
  have hT : Tc f n (m + 1) = Tc f n m + cnt f n (m + 1) := rfl
  simp only [Nat.add_sub_cancel] at blk ⊢
  rw [h1, show wsAux f n (m + 1) = wsAux f n m ++ fl f (m + 1) n from rfl, List.append_assoc,
    List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by omega)]
  rw [hA, List.getElem?_append_left (show i - Tc f n m < (fl f (m + 1) n).length by omega)]

/-- What the result code says about the lengths. -/
def RetInfo (type : UInt32) (f : Nat → Nat) (n : Nat) (r : Int32 × CodePtr × UInt32) : Prop :=
  (r.1 = 0 → Acc type f n) ∧ (r.1 = 1 → Acc type f n ∧ type ≠ CODES) ∧ (r.1 = -1 → ¬ Acc type f n)

theorem incomplete_one {f : Nat → Nat} {n : Nat} (hpos : 0 < Tc f n 15) (hfit : Fits f n)
    (hlt : Kc f n 15 < 2 ^ 15) (hmx : mxl f n = 1) : Tc f n 15 = 1 := by
  have hl := lenAt_le_iff (f := f) (n := n) (i := Tc f n 15 - 1) (l := 1) (by omega) (by omega)
  have h1 : Tc f n 15 - 1 < Tc f n 1 := hl.mp (by unfold mxl at hmx; omega)
  have hm := Tc_mono (f := f) (n := n) (show 1 ≤ 15 by omega)
  have hT : Tc f n (1 + 14) = Tc f n 1 := by simp only [Nat.reduceAdd]; omega
  have hK := Kc_gap (f := f) (n := n) 1 14 hT
  have hK1 : Kc f n 1 = cnt f n 1 := by simp [Kc]
  have hT1 : Tc f n 1 = cnt f n 1 := by simp [Tc]
  simp only [Nat.reduceAdd] at hK
  rw [hK1] at hK
  have hfit1 := hfit 1 (by omega) (by omega)
  rw [hK1] at hfit1
  omega

/-- The inputs of the call that `zlib.h` and `inflate.c` allow (the part that lives in the heap). -/
structure CallPre (h : Heap) (type : UInt32) (rl : WRef) (ol : Nat) (codes : UInt32) (rc : CodeRef) (oc : Nat)
    (bits : UInt32) (rw : WRef) (ow : Nat) where
  la : Array UInt16
  wa : Array UInt16
  ca : Array Code
  hty : type = CODES ∨ type = LENS ∨ type = DISTS
  hgl : Space.get h rl = some la
  hgw : Space.get h rw = some wa
  hgc : Space.get h rc = some ca
  hro : Space.ro h rc = false
  hne : rw ≠ rl
  hla : ol + codes.toNat ≤ la.size
  hwa : ow + codes.toNat ≤ wa.size
  hca : oc + capOf type ≤ ca.size
  hf15 : ∀ k, k < codes.toNat → (la.getD (ol + k) 0).toNat ≤ 15
  hcodes : type = CODES → codes.toNat ≤ 19 ∧ (∀ k, k < codes.toNat → (la.getD (ol + k) 0).toNat ≤ 7) ∧ 7 ≤ bits.toNat
  hlens : type = LENS → codes.toNat ≤ 288
  hdists : type = DISTS → codes.toNat ≤ 32

def CallPre.f {h : Heap} {type : UInt32} {rl : WRef} {ol : Nat} {codes : UInt32} {rc : CodeRef} {oc : Nat}
    {bits : UInt32} {rw : WRef} {ow : Nat} (P : CallPre h type rl ol codes rc oc bits rw ow) (k : Nat) : Nat :=
  (P.la.getD (ol + k) 0).toNat

theorem Result.unchanged {h : Heap} {rw : WRef} {rc : CodeRef} {ow oc cap n : Nat} {wa : Array UInt16}
    {ca : Array Code} {table : CodePtr} {bits : UInt32} {r : Int32 × CodePtr × UInt32}
    (hgw : Space.get h rw = some wa) (hgc : Space.get h rc = some ca) (hr : (r.1 = 1 ∨ r.1 = -1) ∧ r.2.1 = table ∧ r.2.2 = bits) :
    Result h rw rc ow oc cap n wa ca table bits r h := by
  refine ⟨wa, ca, ?_, rfl, rfl, fun _ _ => rfl, fun _ _ => rfl, Or.inr hr⟩
  rw [wput_self hgw, cput_self hgc]

theorem itB_wp {h : Heap} {type : UInt32} {rl : WRef} {ol : Nat} {codes : UInt32} {rc : CodeRef} {oc : Nat}
    {bits : UInt32} {rw : WRef} {ow : Nat} (P : CallPre h type rl ol codes rc oc bits rw ow)
    (count : Array UInt16) (max min root : UInt32)
    (hcs : count.size = 16) (hcc : ∀ l, 1 ≤ l → l ≤ 15 → (count.getD l 0).toNat = cnt P.f codes.toNat l)
    (hmax : max.toNat = mxl P.f codes.toNat) (hpos : 0 < Tc P.f codes.toNat 15)
    (hmin : min.toNat = lenAt P.f codes.toNat 0)
    (hr1 : 1 ≤ root.toNat) (hr0 : lenAt P.f codes.toNat 0 ≤ root.toNat) (hrm : root.toNat ≤ mxl P.f codes.toNat)
    (hrC : type = CODES → root.toNat = mxl P.f codes.toNat) :
    Wp (itB type (Ptr.ref rl ol) codes (Ptr.ref rc oc) bits (Ptr.ref rw ow) count max min root) h
      (fun r h' => Result h rw rc ow oc (capOf type) codes.toNat P.wa P.ca (Ptr.ref rc oc) bits r h' ∧
        RetInfo type P.f codes.toNat r) := by
  unfold itB
  apply Wp.bind' (kraft_loop P.f codes.toNat count hcs hcc h)
  rintro ⟨left, bad, len⟩ h' ⟨rfl, hk⟩
  dsimp only at hk ⊢
  by_cases hbad : bad = true
  · rw [if_pos hbad]
    have hnf : ¬ Fits P.f codes.toNat := by
      rcases hk with ⟨_, h2⟩ | ⟨h1, _⟩
      · exact h2
      · exact absurd (hbad.symm.trans h1) (by decide)
    exact Wp.pure' ⟨Result.unchanged P.hgw P.hgc ⟨Or.inr rfl, rfl, rfl⟩,
      fun h => absurd (show (-1 : Int32) = 0 from h) (by decide),
      fun h => absurd (show (-1 : Int32) = 1 from h) (by decide), fun _ hacc => hnf hacc.1⟩
  · rw [if_neg hbad]
    have hbad' : bad = false := by simpa using hbad
    obtain ⟨hfit, hleft⟩ : Fits P.f codes.toNat ∧ left.toInt = 2 ^ 15 - (Kc P.f codes.toNat 15 : Int) := by
      rcases hk with ⟨h1, _⟩ | ⟨_, h2, h3⟩
      · exact absurd h1 hbad
      · exact ⟨h2, h3⟩
    have hK15 := hfit 15 (by omega) (by omega)
    by_cases hg : (decide (left > 0) && (type == CODES || max != 1)) = true
    · rw [if_pos hg]
      have hgl' : left > 0 ∧ (type == CODES || max != 1) = true := by
        simpa [Bool.and_eq_true, decide_eq_true_eq] using hg
      have hl' : 0 < left.toInt := by
        have := Int32.lt_iff_toInt_lt.mp hgl'.1; simpa using this
      have hnacc : ¬ Acc type P.f codes.toNat := by
        rintro ⟨_, h2 | h2 | ⟨hnc, hm1, _⟩⟩
        · omega
        · omega
        · have hmax1 : max = 1 := UInt32.toNat_inj.mp (by rw [hmax, hm1]; rfl)
          have := hgl'.2
          simp [hnc, hmax1] at this
      exact Wp.pure' ⟨Result.unchanged P.hgw P.hgc ⟨Or.inr rfl, rfl, rfl⟩,
        fun h => absurd (show (-1 : Int32) = 0 from h) (by decide),
        fun h => absurd (show (-1 : Int32) = 1 from h) (by decide), fun _ => hnacc⟩
    · rw [if_neg hg]
      have hend : Kc P.f codes.toNat 15 = 2 ^ 15 ∨ (mxl P.f codes.toNat = 1 ∧ Tc P.f codes.toNat 15 = 1 ∧ type ≠ CODES) := by
        by_cases hl : left > 0
        · right
          have hl' : 0 < left.toInt := by
            have := Int32.lt_iff_toInt_lt.mp hl; simpa using this
          have hnc1 : type ≠ CODES := fun ht => hg (by simp [hl, ht])
          have hnc2 : max = 1 := Classical.byContradiction (fun hne => hg (by simp [hl, hne]))
          have hm1 : mxl P.f codes.toNat = 1 := by
            have := congrArg UInt32.toNat hnc2; rw [hmax] at this; simpa using this
          have hlt : Kc P.f codes.toNat 15 < 2 ^ 15 := by
            have : (Kc P.f codes.toNat 15 : Int) < 2 ^ 15 := by omega
            exact_mod_cast this
          exact ⟨hm1, incomplete_one hpos hfit hlt hm1, hnc1⟩
        · left
          have hl' : left.toInt ≤ 0 := by
            have : ¬ (0 < left.toInt) := fun hh => hl (Int32.lt_iff_toInt_lt.mpr (by simpa using hh))
            omega
          have : (2 ^ 15 : Int) ≤ Kc P.f codes.toNat 15 := by omega
          have : 2 ^ 15 ≤ Kc P.f codes.toNat 15 := by exact_mod_cast this
          omega
      have hn288 : codes.toNat ≤ 288 := by
        rcases P.hty with ht | ht | ht
        · have := (P.hcodes ht).1; omega
        · exact P.hlens ht
        · have := P.hdists ht; omega
      rw [seta_eq (by simp)]
      rw [M_pure_bind]
      apply Wp.bind' (offs_loop P.f codes.toNat hn288 count hcs hcc _)
      rintro ⟨len2, offs⟩ h' ⟨rfl, hos, hoj⟩
      dsimp only at hos hoj ⊢
      apply Wp.bind' (sort_loop P.f codes.toNat hn288 rl rw P.hne ol ow P.la P.wa codes rfl _ P.hgl P.hgw P.hla
        (fun k => rfl) P.hf15 P.hwa offs hos hoj)
      rintro ⟨sym, offs'⟩ h2 ⟨hsym, wa1, rfl, hinv⟩
      dsimp only at hinv ⊢
      obtain ⟨_, _, hsz1, hfr1, hcont1⟩ := hinv
      have key : ∀ (base extra : Array UInt16) (match_ : UInt32),
          (type = CODES → match_ = 20) →
          (type = LENS → base = lbase ∧ extra = lext ∧ match_ = 257) →
          (type = DISTS → base = dbase ∧ extra = dext ∧ match_ = 0) →
          Wp (itTail type (Ptr.ref rl ol) (Ptr.ref rc oc) bits (Ptr.ref rw ow) count max min root left base extra match_)
            (Space.put h' rw wa1)
            (fun r h2 => Result h' rw rc ow oc (capOf type) codes.toNat P.wa P.ca (Ptr.ref rc oc) bits r h2 ∧
              RetInfo type P.f codes.toNat r) := by
        intro base extra match_ hC hL hD
        let c0 : Ctx := { type, lens := Ptr.ref rl ol, work := Ptr.ref rw ow, table := Ptr.ref rc oc, root, max, base, extra, match_ }
        let e : Env :=
          { c := c0,
            f := P.f, n := codes.toNat, R := root.toNat, cap := capOf type, rc := rc, oc := oc, «rw» := «rw», ow := ow,
            rl := rl, ol := ol, hb := Space.put h' rw wa1, la := P.la, wa := wa1,
            h_table := rfl, h_lens := rfl, h_work := rfl, h_ro := P.hro,
            h_live := ⟨P.ca, by rw [cget_put_word]; exact P.hgc⟩,
            h_get_la := by rw [wget_put_ne P.hne]; exact P.hgl,
            h_get_wa := wget_put_self P.hgw wa1, h_f := fun k => rfl, h_la := P.hla, h_f15 := P.hf15,
            h_wa := by rw [hsz1]; exact P.hwa,
            h_wcont := fun i hi => by
              have hb := lenAt_bounds (f := P.f) (n := codes.toNat) hi
              have blk := (lenAt_eq_iff (f := P.f) (n := codes.toNat) (l := lenAt P.f codes.toNat i) hb.1 hb.2 hi).mp rfl
              have hlt : i - Tc P.f codes.toNat (lenAt P.f codes.toNat i - 1) < cnt P.f codes.toNat (lenAt P.f codes.toNat i) := by
                have := Tc_succ' (f := P.f) (n := codes.toNat) hb.1
                omega
              have := hcont1 (lenAt P.f codes.toNat i) (i - Tc P.f codes.toNat (lenAt P.f codes.toNat i - 1)) hb.1 hb.2 hlt
              rw [show ow + Tc P.f codes.toNat (lenAt P.f codes.toNat i - 1) + (i - Tc P.f codes.toNat (lenAt P.f codes.toNat i - 1)) = ow + i by omega] at this
              rw [this, ws_getD hi],
            h_n := hn288, h_root := rfl, h_max := hmax, h_R1 := hr1, h_Rmx := hrm, h_R0 := hr0, h_pos := hpos,
            h_fits := hfit, h_end := hend, h_type := P.hty, h_cap := rfl,
            h_codes := fun ht => ⟨by
                have hall := (P.hcodes ht).2.1
                show lenAt P.f codes.toNat (Tc P.f codes.toNat 15 - 1) ≤ 7
                unfold lenAt
                exact hall _ (ws_getD_lt (by omega)), hrC ht, (P.hcodes ht).1, hC ht⟩,
            h_lens' := fun ht => ⟨hn288, hL ht⟩, h_dists := fun ht => ⟨(P.hdists ht), hD ht⟩ }
        have hcnt0 : CountOK e count 0 := ⟨hcs, fun l h1 h2 => by
          rw [hcc l h1 h2]; exact (rem_zero (f := P.f) (n := codes.toNat) h1).symm⟩
        have hhc : e.hc P.ca = Space.put h' rw wa1 :=
          cput_self (by rw [cget_put_word]; exact P.hgc)
        have := itTail_wp e P.ca count bits min left hcnt0 hmin P.hca
        rw [hhc] at this
        refine Wp.mono this ?_
        rintro r h3 ⟨ca', rfl, hf, hr, hrne⟩
        have hacc : Acc type P.f codes.toNat := by
          refine ⟨hfit, ?_⟩
          rcases hend with h | ⟨a, b, c⟩
          · exact Or.inl h
          · exact Or.inr (Or.inr ⟨c, a, b⟩)
        have hr01 : r.1 = 0 ∨ r.1 = 1 := by
          rcases hr with ⟨h0, _⟩ | ⟨h1, _⟩
          · exact Or.inl h0
          · exact Or.inr h1
        refine ⟨⟨wa1, ca', rfl, hsz1, hf.1.trans rfl, hfr1, hf.2, ?_⟩,
          fun _ => hacc, fun h1 => ⟨hacc, hrne h1⟩, fun hm => ?_⟩
        · rcases hr with ⟨h0, u, hu, hr2, _⟩ | ⟨h1, h2, h3⟩
          · exact Or.inl ⟨h0, u, hu, hr2⟩
          · exact Or.inr ⟨Or.inl h1, h2, h3⟩
        · exfalso
          rcases hr01 with h0 | h0 <;> rw [h0] at hm <;> exact absurd hm (by decide)
      rcases P.hty with ht | ht | ht
      · subst ht
        rw [if_pos (by decide)]
        exact key #[] #[] 20 (fun _ => rfl) (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
      · subst ht
        rw [if_neg (by decide), if_pos (by decide)]
        exact key lbase lext 257 (fun h => absurd h (by decide)) (fun _ => ⟨rfl, rfl, rfl⟩) (fun h => absurd h (by decide))
      · subst ht
        rw [if_neg (by decide), if_neg (by decide), if_pos (by decide)]
        exact key dbase dext 0 (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) (fun _ => ⟨rfl, rfl, rfl⟩)

theorem Tc_gap {f : Nat → Nat} {n : Nat} : ∀ a d, (∀ j, a < j → j ≤ a + d → cnt f n j = 0) → Tc f n (a + d) = Tc f n a
  | a, 0, _ => rfl
  | a, d + 1, h => by
    have ih := Tc_gap a d (fun j h1 h2 => h j h1 (by omega))
    have : Tc f n (a + (d + 1)) = Tc f n (a + d) + cnt f n (a + d + 1) := rfl
    rw [this, ih, h (a + d + 1) (by omega) (by omega)]
    rfl

theorem mxl_eq {f : Nat → Nat} {n M : Nat} (hpos : 0 < Tc f n 15) (hM1 : 1 ≤ M) (hM2 : M ≤ 15)
    (hc : cnt f n M ≠ 0) (hgt : ∀ j, M < j → j ≤ 15 → cnt f n j = 0) : mxl f n = M := by
  have hT : Tc f n 15 = Tc f n M := by
    have := Tc_gap (f := f) (n := n) M (15 - M) (fun j h1 h2 => hgt j h1 (by omega))
    rwa [show M + (15 - M) = 15 by omega] at this
  have hTs := Tc_succ' (f := f) (n := n) hM1
  have hi : Tc f n 15 - 1 < Tc f n 15 := by omega
  have := (lenAt_eq_iff (f := f) (n := n) (i := Tc f n 15 - 1) (l := M) hM1 hM2 hi).mpr ⟨by omega, by omega⟩
  exact this

theorem min_facts {f : Nat → Nat} {n : Nat} (hpos : 0 < Tc f n 15) :
    (∀ j, 1 ≤ j → j < lenAt f n 0 → cnt f n j = 0) ∧ cnt f n (lenAt f n 0) ≠ 0 := by
  obtain ⟨b1, b2⟩ := lenAt_bounds (f := f) (n := n) hpos
  have blk := (lenAt_eq_iff (f := f) (n := n) (l := lenAt f n 0) b1 b2 hpos).mp rfl
  have hTs := Tc_succ' (f := f) (n := n) b1
  refine ⟨fun j hj1 hj2 => ?_, by omega⟩
  have hm := Tc_mono (f := f) (n := n) (show j ≤ lenAt f n 0 - 1 by omega)
  have := Tc_succ' (f := f) (n := n) hj1
  omega

def zeroCond : UInt32 × Array UInt16 → M (Bool × (UInt32 × Array UInt16)) :=
  fun (len, count) => pure (len ≤ MAXBITS, (len, count))

def zeroBody : UInt32 × Array UInt16 → M (UInt32 × Array UInt16) :=
  fun (len, count) => do pure (len + 1, ← seta count len.toNat 0)

theorem zero_loop (h : Heap) :
    Wp (cwhile zeroCond zeroBody ((0 : UInt32), Array.replicate 16 (0 : UInt16))) h
      (fun r h' => h' = h ∧ r.2.size = 16 ∧ ∀ l, l < 16 → (r.2.getD l 0).toNat = 0) := by
  refine Wp.cwhile
    (fun (x : UInt32 × Array UInt16) h' => h' = h ∧ x.1.toNat ≤ 16 ∧ x.2.size = 16 ∧ ∀ l, l < 16 → (x.2.getD l 0).toNat = 0)
    (fun (x : UInt32 × Array UInt16) => 16 - x.1.toNat) _ ?_ ?_ ?_
  · rintro ⟨len, count⟩ h' ⟨rfl, hl, hsz, hz⟩
    dsimp only at hl hsz hz
    by_cases hle : len ≤ MAXBITS
    · right
      have hle' : len.toNat ≤ 15 := UInt32.le_iff_toNat_le.mp hle
      have hu : (len + 1).toNat = len.toNat + 1 := u32_succ (by omega)
      have hlt : len.toNat < count.size := by omega
      refine ⟨(len, count), h', (len + 1, count.set! len.toNat 0), h', ?_, ?_, ?_, ?_⟩
      · show (pure (decide (len ≤ MAXBITS), (len, count)) : M _) h' = _
        simp [hle]
      · show (do pure (len + 1, ← seta count len.toNat 0) : M _) h' = _
        rw [seta_eq hlt]; rfl
      · refine ⟨rfl, by dsimp only; omega, by dsimp only; rw [Array.size_set!]; exact hsz, fun l hl2 => ?_⟩
        dsimp only
        rw [getD_set!]
        by_cases hh : len.toNat = l
        · rw [if_pos ⟨hh, hlt⟩]; rfl
        · rw [if_neg (fun hh2 => hh hh2.1)]; exact hz l hl2
      · dsimp only; omega
    · left
      have hn : 16 ≤ len.toNat := by
        have := (not_congr UInt32.le_iff_toNat_le).mp hle
        have h15 : MAXBITS.toNat = 15 := rfl
        omega
      refine ⟨(len, count), h', ?_, rfl, hsz, hz⟩
      show (pure (decide (len ≤ MAXBITS), (len, count)) : M _) h' = _
      simp [hle]
  · refine ⟨rfl, by decide, by simp, fun l hl => ?_⟩
    simp [Array.getD_eq_getD_getElem?, Array.getElem?_replicate, hl]
  · exact lt_fuel (by simp)

def countCond (codes : UInt32) : UInt32 × Array UInt16 → M (Bool × (UInt32 × Array UInt16)) :=
  fun (sym, count) => pure (sym < codes, (sym, count))

def countBody (lens : WPtr) : UInt32 × Array UInt16 → M (UInt32 × Array UInt16) :=
  fun (sym, count) => do
    let l ← lens.index sym.toNat
    let c ← geta count l.toNat
    pure (sym + 1, ← seta count l.toNat (c + 1))

theorem count_loop (f : Nat → Nat) (n : Nat) (hn : n ≤ 288) (rl : WRef) (ol : Nat) (la : Array UInt16)
    (codes : UInt32) (hcodes : codes.toNat = n) (h : Heap) (hgl : Space.get h rl = some la) (hla : ol + n ≤ la.size)
    (hf : ∀ k, f k = (la.getD (ol + k) 0).toNat) (hf15 : ∀ k, k < n → f k ≤ 15)
    (count0 : Array UInt16) (hs0 : count0.size = 16) (hz0 : ∀ l, l < 16 → (count0.getD l 0).toNat = 0) :
    Wp (cwhile (countCond codes) (countBody (Ptr.ref rl ol)) ((0 : UInt32), count0)) h
      (fun r h' => h' = h ∧ r.1.toNat = n ∧ r.2.size = 16 ∧ ∀ l, l < 16 → (r.2.getD l 0).toNat = cnt f n l) := by
  refine Wp.cwhile
    (fun (x : UInt32 × Array UInt16) h' => h' = h ∧ x.1.toNat ≤ n ∧ x.2.size = 16 ∧
      ∀ l, l < 16 → (x.2.getD l 0).toNat = cnt f x.1.toNat l)
    (fun (x : UInt32 × Array UInt16) => n - x.1.toNat) _ ?_ ?_ ?_
  · rintro ⟨sym, count⟩ h' ⟨rfl, hsn, hsz, hcn⟩
    dsimp only at hsn hsz hcn
    by_cases hlt : sym < codes
    · right
      have hk : sym.toNat < n := by have := UInt32.lt_iff_toNat_lt.mp hlt; omega
      have hkl : ol + sym.toNat < la.size := by omega
      have hfk : f sym.toNat = (la[ol + sym.toNat]'hkl).toNat := by
        rw [hf, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hkl]; simp
      have hf15' := hf15 sym.toNat hk
      have hlt16 : (la[ol + sym.toNat]'hkl).toNat < count.size := by rw [← hfk, hsz]; omega
      have hcnt := hcn (la[ol + sym.toNat]'hkl).toNat (by omega)
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hlt16] at hcnt
      simp only [Option.getD_some] at hcnt
      have hcle := cnt_le (f := f) (la[ol + sym.toNat]'hkl).toNat sym.toNat
      have hu : (sym + 1).toNat = sym.toNat + 1 := u32_succ (by omega)
      have hw : Wp (countBody (Ptr.ref rl ol) (sym, count)) h'
          (fun r h2 => h2 = h' ∧ r = (sym + 1, count.set! (la[ol + sym.toNat]'hkl).toNat
            (count[(la[ol + sym.toNat]'hkl).toNat]'hlt16 + 1))) := by
        simp only [countBody]
        apply Wp.bind' (Q := fun r h2 => r = la[ol + sym.toNat]'hkl ∧ h2 = h')
          (Wp.of_eq (Ptr.index_ok hgl hkl) ⟨rfl, rfl⟩)
        rintro l h2 ⟨rfl, hh⟩
        subst h2
        apply Wp.bind' (Q := fun r h2 => r = count[(la[ol + sym.toNat]'hkl).toNat]'hlt16 ∧ h2 = h')
          (Wp.pure_eq (geta_eq hlt16) ⟨rfl, rfl⟩)
        rintro c h2 ⟨rfl, hh⟩
        subst h2
        apply Wp.bind' (Q := fun r h2 => r = count.set! (la[ol + sym.toNat]'hkl).toNat
            (count[(la[ol + sym.toNat]'hkl).toNat]'hlt16 + 1) ∧ h2 = h')
          (Wp.pure_eq (seta_eq hlt16) ⟨rfl, rfl⟩)
        rintro c2 h2 ⟨rfl, hh⟩
        subst h2
        exact Wp.pure' ⟨rfl, rfl⟩
      obtain ⟨r2, h2, hrun, rfl, rfl⟩ := hw
      refine ⟨(sym, count), _, _, _, ?_, hrun, ⟨rfl, by dsimp only; omega, by dsimp only; rw [Array.size_set!]; exact hsz, ?_⟩, by dsimp only; omega⟩
      · show (pure (decide (sym < codes), (sym, count)) : M _) _ = _
        simp [hlt]
      · intro l hl
        dsimp only
        rw [getD_set!, hu, cnt_step]
        have hadd : (count[(la[ol + sym.toNat]'hkl).toNat]'hlt16 + 1).toNat = cnt f sym.toNat (la[ol + sym.toNat]'hkl).toNat + 1 := by
          rw [UInt16.toNat_add]; simp only [UInt16.toNat_one]; rw [hcnt]
          exact Nat.mod_eq_of_lt (by omega)
        by_cases hh : (la[ol + sym.toNat]'hkl).toNat = l
        · rw [if_pos ⟨hh, hlt16⟩, hadd, if_pos (by rw [hfk]; exact hh)]
          rw [hh]
        · rw [if_neg (fun hh2 => hh hh2.1), if_neg (by rw [hfk]; exact hh), Nat.add_zero]
          exact hcn l hl
    · left
      have hsn' : sym.toNat = n := by
        have : ¬ sym.toNat < n := fun hh => hlt (by rw [UInt32.lt_iff_toNat_lt, hcodes]; exact hh)
        omega
      refine ⟨(sym, count), _, ?_, rfl, hsn', hsz, by rw [← hsn']; exact hcn⟩
      show (pure (decide (sym < codes), (sym, count)) : M _) _ = _
      simp [hlt]
  · refine ⟨rfl, by simp, hs0, fun l hl => ?_⟩
    show (count0.getD l 0).toNat = cnt f 0 l
    rw [cnt_zero]; exact hz0 l hl
  · exact lt_fuel (by omega)

def maxCond : UInt32 × Bool → M (Bool × (UInt32 × Bool)) :=
  fun (max, brk) => pure (!brk && max ≥ 1, (max, brk))

def maxBody (count : Array UInt16) : UInt32 × Bool → M (UInt32 × Bool) :=
  fun (max, brk) => do
    if (← geta count max.toNat) != 0 then pure (max, true) else pure (max - 1, brk)

theorem max_loop (f : Nat → Nat) (n : Nat) (count : Array UInt16) (hs : count.size = 16)
    (hc : ∀ l, 1 ≤ l → l ≤ 15 → (count.getD l 0).toNat = cnt f n l) (h : Heap) :
    Wp (cwhile maxCond (maxBody count) (MAXBITS, false)) h
      (fun r h' => h' = h ∧ ((Tc f n 15 = 0 ∧ r.1.toNat = 0) ∨ (0 < Tc f n 15 ∧ r.1.toNat = mxl f n))) := by
  refine Wp.cwhile
    (fun (x : UInt32 × Bool) h' => h' = h ∧ x.1.toNat ≤ 15 ∧
      (x.2 = false → ∀ j, x.1.toNat < j → j ≤ 15 → cnt f n j = 0) ∧
      (x.2 = true → 1 ≤ x.1.toNat ∧ cnt f n x.1.toNat ≠ 0 ∧ ∀ j, x.1.toNat < j → j ≤ 15 → cnt f n j = 0))
    (fun (x : UInt32 × Bool) => if x.2 then 0 else x.1.toNat + 1) _ ?_ ?_ ?_
  · rintro ⟨max, brk⟩ h' ⟨rfl, hm, hnb, hb⟩
    dsimp only at hm hnb hb
    by_cases hcnd : (!brk && decide (max ≥ 1)) = true
    · right
      simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hcnd
      obtain ⟨hbrk, hge⟩ := hcnd
      have hge' : 1 ≤ max.toNat := by
        have := UInt32.le_iff_toNat_le.mp hge; simpa using this
      have hlt16 : max.toNat < count.size := by omega
      have hcm : (count[max.toNat]).toNat = cnt f n max.toNat := by
        have := hc max.toNat hge' hm
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hlt16] at this; simpa using this
      have hcond : maxCond (max, brk) h' = .ok ((true, (max, brk)), h') := by
        show (pure ((!brk && decide (max ≥ 1)), (max, brk)) : M _) h' = _
        rw [show ((!brk && decide (max ≥ 1))) = true from by
          simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq]; exact ⟨hbrk, hge⟩]
        rfl
      by_cases hz : (count[max.toNat] != 0) = true
      · have hbody : maxBody count (max, brk) h' = .ok ((max, true), h') := by
          simp only [maxBody]
          rw [geta_eq hlt16, M_pure_bind, if_pos hz]; rfl
        refine ⟨(max, brk), h', (max, true), h', hcond, hbody, ⟨rfl, hm, fun hx => by simp at hx, fun _ => ⟨hge', ?_, ?_⟩⟩, ?_⟩
        · dsimp only; rw [← hcm]; intro h0; apply (by simpa using hz : ¬ (count[max.toNat] = 0)); exact UInt16.toNat_inj.mp (by rw [h0]; rfl)
        · exact hnb hbrk
        · dsimp only; simp [hbrk]
      · have hbody : maxBody count (max, brk) h' = .ok ((max - 1, brk), h') := by
          simp only [maxBody]
          rw [geta_eq hlt16, M_pure_bind, if_neg hz]; rfl
        have hz0 : cnt f n max.toNat = 0 := by
          rw [← hcm]
          have : count[max.toNat] = 0 := by simpa using hz
          rw [this]; rfl
        have hm1 : (max - 1).toNat = max.toNat - 1 := u32_one_sub (by omega)
        refine ⟨(max, brk), h', (max - 1, brk), h', hcond, hbody, ⟨rfl, by dsimp only; rw [hm1]; omega, fun _ j hj1 hj2 => ?_, fun hx => by simp [hbrk] at hx⟩, ?_⟩
        · dsimp only at hj1
          rw [hm1] at hj1
          by_cases hjj : j = max.toNat
          · rw [hjj]; exact hz0
          · exact hnb hbrk j (by omega) hj2
        · dsimp only; simp [hbrk, hm1]; omega
    · left
      have hcond : maxCond (max, brk) h' = .ok ((false, (max, brk)), h') := by
        show (pure ((!brk && decide (max ≥ 1)), (max, brk)) : M _) h' = _
        have : ((!brk && decide (max ≥ 1))) = false := by
          cases hh : ((!brk && decide (max ≥ 1)))
          · rfl
          · exact absurd hh hcnd
        rw [this]; rfl
      refine ⟨(max, brk), h', hcond, rfl, ?_⟩
      cases hbrk : brk
      · have hmax0 : max.toNat = 0 := by
          have hn : ¬ (max ≥ 1) := fun hh => hcnd (by simp [hbrk, hh])
          have := (not_congr UInt32.le_iff_toNat_le).mp hn
          simp at this; omega
        have hall := hnb hbrk
        left
        refine ⟨?_, hmax0⟩
        have := Tc_gap (f := f) (n := n) 0 15 (fun j h1 h2 => hall j (by omega) (by omega))
        have h0 : Tc f n 0 = 0 := rfl
        simp only [Nat.zero_add] at this
        omega
      · right
        obtain ⟨h1, h2, h3⟩ := hb hbrk
        have hTs := Tc_succ' (f := f) (n := n) h1
        have hmono := Tc_mono (f := f) (n := n) (show max.toNat ≤ 15 by omega)
        have hpos : 0 < Tc f n 15 := by
          have : 0 < cnt f n max.toNat := Nat.pos_of_ne_zero h2
          omega
        refine ⟨hpos, ?_⟩
        exact (mxl_eq hpos h1 hm h2 h3).symm
  · refine ⟨rfl, by decide, fun _ j hj1 hj2 => ?_, fun hx => by simp at hx⟩
    have hM : (MAXBITS, false).fst.toNat = 15 := rfl
    omega
  · show (if false = true then 0 else (MAXBITS, false).fst.toNat + 1) < fuel
    exact lt_fuel (by decide)

def minCond (max : UInt32) : UInt32 × Bool → M (Bool × (UInt32 × Bool)) :=
  fun (min, brk) => pure (!brk && min < max, (min, brk))

def minBody (count : Array UInt16) : UInt32 × Bool → M (UInt32 × Bool) :=
  fun (min, brk) => do
    if (← geta count min.toNat) != 0 then pure (min, true) else pure (min + 1, brk)

theorem min_loop (f : Nat → Nat) (n : Nat) (count : Array UInt16) (hs : count.size = 16)
    (hc : ∀ l, 1 ≤ l → l ≤ 15 → (count.getD l 0).toNat = cnt f n l) (max : UInt32)
    (hmax : max.toNat = mxl f n) (hpos : 0 < Tc f n 15) (h : Heap) :
    Wp (cwhile (minCond max) (minBody count) ((1 : UInt32), false)) h
      (fun r h' => h' = h ∧ r.1.toNat = lenAt f n 0) := by
  obtain ⟨b1, b2⟩ := lenAt_bounds (f := f) (n := n) hpos
  obtain ⟨hz, hnz⟩ := min_facts (f := f) (n := n) hpos
  have hl0mx : lenAt f n 0 ≤ mxl f n := lenAt_mono (f := f) (n := n) (show 0 ≤ Tc f n 15 - 1 by omega) (by omega)
  refine Wp.cwhile
    (fun (x : UInt32 × Bool) h' => h' = h ∧ 1 ≤ x.1.toNat ∧ x.1.toNat ≤ lenAt f n 0 ∧
      (x.2 = true → x.1.toNat = lenAt f n 0))
    (fun (x : UInt32 × Bool) => if x.2 then 0 else lenAt f n 0 + 1 - x.1.toNat) _ ?_ ?_ ?_
  · rintro ⟨min, brk⟩ h' ⟨rfl, hm1, hm2, hb⟩
    dsimp only at hm1 hm2 hb
    by_cases hcnd : (!brk && decide (min < max)) = true
    · right
      simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hcnd
      obtain ⟨hbrk, hlt⟩ := hcnd
      have hlt' : min.toNat < max.toNat := UInt32.lt_iff_toNat_lt.mp hlt
      have hlt16 : min.toNat < count.size := by omega
      have hcm : (count[min.toNat]).toNat = cnt f n min.toNat := by
        have := hc min.toNat hm1 (by omega)
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hlt16] at this; simpa using this
      have hcond : minCond max (min, brk) h' = .ok ((true, (min, brk)), h') := by
        show (pure ((!brk && decide (min < max)), (min, brk)) : M _) h' = _
        rw [show ((!brk && decide (min < max))) = true from by
          simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq]; exact ⟨hbrk, hlt⟩]
        rfl
      by_cases hzz : (count[min.toNat] != 0) = true
      · have hbody : minBody count (min, brk) h' = .ok ((min, true), h') := by
          simp only [minBody]
          rw [geta_eq hlt16, M_pure_bind, if_pos hzz]; rfl
        have hne : cnt f n min.toNat ≠ 0 := by
          rw [← hcm]; intro h0; apply (by simpa using hzz : ¬ (count[min.toNat] = 0))
          exact UInt16.toNat_inj.mp (by rw [h0]; rfl)
        have heq : min.toNat = lenAt f n 0 := by
          apply Classical.byContradiction; intro hh
          exact hne (hz _ hm1 (by omega))
        refine ⟨(min, brk), h', (min, true), h', hcond, hbody, ⟨rfl, hm1, hm2, fun _ => heq⟩, ?_⟩
        dsimp only; simp [hbrk]; omega
      · have hbody : minBody count (min, brk) h' = .ok ((min + 1, brk), h') := by
          simp only [minBody]
          rw [geta_eq hlt16, M_pure_bind, if_neg hzz]; rfl
        have hz0 : cnt f n min.toNat = 0 := by
          rw [← hcm]
          have : count[min.toNat] = 0 := by simpa using hzz
          rw [this]; rfl
        have hlt0 : min.toNat < lenAt f n 0 := by
          apply Classical.byContradiction; intro hh
          have : min.toNat = lenAt f n 0 := by omega
          rw [this] at hz0; exact hnz hz0
        have hu : (min + 1).toNat = min.toNat + 1 := u32_succ (by omega)
        refine ⟨(min, brk), h', (min + 1, brk), h', hcond, hbody, ⟨rfl, by dsimp only; omega, by dsimp only; omega, fun hx => by simp [hbrk] at hx⟩, ?_⟩
        dsimp only; simp [hbrk, hu]; omega
    · left
      have hcond : minCond max (min, brk) h' = .ok ((false, (min, brk)), h') := by
        show (pure ((!brk && decide (min < max)), (min, brk)) : M _) h' = _
        have : ((!brk && decide (min < max))) = false := by
          cases hh : ((!brk && decide (min < max)))
          · rfl
          · exact absurd hh hcnd
        rw [this]; rfl
      refine ⟨(min, brk), h', hcond, rfl, ?_⟩
      cases hbrk : brk
      · have hn : ¬ (min < max) := fun hh => hcnd (by simp [hbrk, hh])
        have := (not_congr UInt32.lt_iff_toNat_lt).mp hn
        show min.toNat = lenAt f n 0
        omega
      · exact hb hbrk
  · have h1 : ((1 : UInt32), false).fst.toNat = 1 := rfl
    exact ⟨rfl, by omega, by omega, fun hx => by simp at hx⟩
  · show (if false = true then 0 else lenAt f n 0 + 1 - ((1 : UInt32), false).fst.toNat) < fuel
    have h1 : ((1 : UInt32), false).fst.toNat = 1 := rfl
    simp only [Bool.false_eq_true, ite_false]
    exact lt_fuel (by omega)

theorem capOf_ge (type : UInt32) : 2 ≤ capOf type := by
  unfold capOf; split <;> (try split) <;> omega

theorem wpC_add {R T : Type} [Space Heap R T] (h : Heap) (r : R) (a : Array T) (off n : Nat)
    (hg : Space.get h r = some a) (hn : off + n ≤ a.size) :
    Wp (Ptr.add (Ptr.ref r off) (n : Int)) h (fun q h' => q = Ptr.ref r (off + n) ∧ h' = h) :=
  Wp.of_eq (Ptr.add_nat_ok hg hn) ⟨rfl, rfl⟩

theorem wpC_store {R T : Type} [Space Heap R T] (h : Heap) (r : R) (a : Array T) (off : Nat) (v : T)
    (hg : Space.get h r = some a) (hro : Space.ro h r = false) (hlt : off < a.size) :
    Wp (Ptr.store (Ptr.ref r off) v) h (fun _ h' => h' = Space.put h r (a.set! off v)) :=
  ⟨(), _, Ptr.store_ok hg hro hlt, rfl⟩

theorem fits_of_zero {f : Nat → Nat} {n : Nat} (hT : Tc f n 15 = 0) : Fits f n := by
  intro l hl1 hl2
  have hm := Tc_mono (f := f) (n := n) hl2
  have := Kc_gap (f := f) (n := n) 0 l (by rw [Nat.zero_add]; show Tc f n l = Tc f n 0; have : Tc f n 0 = 0 := rfl; omega)
  have hK0 : Kc f n 0 = 0 := rfl
  rw [Nat.zero_add, hK0, Nat.mul_zero] at this
  rw [this]; exact Nat.zero_le _

theorem itA_wp {h : Heap} {type : UInt32} {rl : WRef} {ol : Nat} {codes : UInt32} {rc : CodeRef} {oc : Nat}
    {bits : UInt32} {rw : WRef} {ow : Nat} (P : CallPre h type rl ol codes rc oc bits rw ow)
    (count : Array UInt16) (max root : UInt32)
    (hcs : count.size = 16) (hcc : ∀ l, 1 ≤ l → l ≤ 15 → (count.getD l 0).toNat = cnt P.f codes.toNat l)
    (hmaxq : (Tc P.f codes.toNat 15 = 0 ∧ max.toNat = 0) ∨ (0 < Tc P.f codes.toNat 15 ∧ max.toNat = mxl P.f codes.toNat))
    (hroot : root.toNat ≤ max.toNat) (hrC : type = CODES → root.toNat = max.toNat) :
    Wp (itA type (Ptr.ref rl ol) codes (Ptr.ref rc oc) bits (Ptr.ref rw ow) count max root) h
      (fun r h' => Result h rw rc ow oc (capOf type) codes.toNat P.wa P.ca (Ptr.ref rc oc) bits r h' ∧
        RetInfo type P.f codes.toNat r) := by
  unfold itA
  by_cases hm0 : (max == 0) = true
  · rw [if_pos hm0]
    have hcap2 := capOf_ge type
    have hca := P.hca
    show Wp (do Ptr.store (Ptr.ref rc oc) (⟨64, 1, 0⟩ : Code)
                let table ← Ptr.add (Ptr.ref rc oc) 1
                Ptr.store table (⟨64, 1, 0⟩ : Code)
                let table ← Ptr.add table 1
                return ((0 : Int32), table, (1 : UInt32))) _ _
    apply Wp.bind' (Q := fun _ h2 => h2 = Space.put h rc (P.ca.set! oc ⟨64, 1, 0⟩))
      (wpC_store h rc P.ca oc _ P.hgc P.hro (by omega))
    rintro _ h1 rfl
    have hg1 := cget_put_self P.hgc P.hro (P.ca.set! oc (⟨64, 1, 0⟩ : Code))
    apply Wp.bind' (Q := fun q h2 => q = Ptr.ref rc (oc + 1) ∧ h2 = Space.put h rc (P.ca.set! oc ⟨64, 1, 0⟩))
      (wpC_add _ rc _ oc 1 hg1 (by rw [Array.size_set!]; omega))
    rintro q h2 ⟨rfl, rfl⟩
    apply Wp.bind' (Q := fun _ h3 => h3 = Space.put h rc ((P.ca.set! oc ⟨64, 1, 0⟩).set! (oc + 1) ⟨64, 1, 0⟩))
      (by
        have := wpC_store _ rc _ (oc + 1) (⟨64, 1, 0⟩ : Code) hg1 P.hro (by rw [Array.size_set!]; omega)
        refine Wp.mono this ?_
        intro _ h3 hh; rw [hh, cput_put])
    rintro _ h3 rfl
    have hg2 := cget_put_self P.hgc P.hro ((P.ca.set! oc (⟨64, 1, 0⟩ : Code)).set! (oc + 1) (⟨64, 1, 0⟩ : Code))
    apply Wp.bind' (Q := fun q h4 => q = Ptr.ref rc (oc + 1 + 1) ∧ h4 = Space.put h rc ((P.ca.set! oc ⟨64, 1, 0⟩).set! (oc + 1) ⟨64, 1, 0⟩))
      (wpC_add _ rc _ (oc + 1) 1 hg2 (by rw [Array.size_set!, Array.size_set!]; omega))
    rintro q h4 ⟨rfl, rfl⟩
    have hT0 : Tc P.f codes.toNat 15 = 0 := by
      have hm0' : max.toNat = 0 := by
        have : max = 0 := by simpa using hm0
        rw [this]; rfl
      rcases hmaxq with ⟨a, _⟩ | ⟨a, b⟩
      · exact a
      · have := lenAt_bounds (f := P.f) (n := codes.toNat) a
        have h3 : mxl P.f codes.toNat = lenAt P.f codes.toNat (Tc P.f codes.toNat 15 - 1) := rfl
        have := lenAt_bounds (f := P.f) (n := codes.toNat) (show Tc P.f codes.toNat 15 - 1 < Tc P.f codes.toNat 15 by omega)
        omega
    have hacc : Acc type P.f codes.toNat := ⟨fits_of_zero hT0, Or.inr (Or.inl hT0)⟩
    refine Wp.pure' ⟨⟨P.wa, (P.ca.set! oc ⟨64, 1, 0⟩).set! (oc + 1) ⟨64, 1, 0⟩, ?_, rfl, ?_, fun _ _ => rfl, ?_, Or.inl ⟨rfl, 2, hcap2, rfl⟩⟩,
      fun _ => hacc, fun h => absurd (show (0 : Int32) = 1 from h) (by decide),
      fun h => absurd (show (0 : Int32) = -1 from h) (by decide)⟩
    · rw [wput_self P.hgw]
    · simp [Array.size_set!]
    · intro x hx
      have h1 : oc + 1 ≠ x := by omega
      have h2 : oc ≠ x := by omega
      rw [getElem?_set!_ne h1, getElem?_set!_ne h2]
  · rw [if_neg hm0]
    have hm0' : max.toNat ≠ 0 := fun h0 => hm0 (by
      have : max = 0 := UInt32.toNat_inj.mp (by rw [h0]; rfl)
      simp [this])
    obtain ⟨hpos, hmx⟩ : 0 < Tc P.f codes.toNat 15 ∧ max.toNat = mxl P.f codes.toNat := by
      rcases hmaxq with ⟨_, h2⟩ | h2
      · exact absurd h2 hm0'
      · exact h2
    obtain ⟨hl1, hl2⟩ := lenAt_bounds (f := P.f) (n := codes.toNat) hpos
    have hl0mx : lenAt P.f codes.toNat 0 ≤ mxl P.f codes.toNat :=
      lenAt_mono (f := P.f) (n := codes.toNat) (show 0 ≤ Tc P.f codes.toNat 15 - 1 by omega) (by omega)
    apply Wp.bind' (min_loop P.f codes.toNat count hcs hcc max hmx hpos _)
    rintro ⟨min, brk⟩ h' ⟨rfl, hmin⟩
    dsimp only at hmin ⊢
    by_cases hr : root < min
    · rw [if_pos hr]
      have hr' : root.toNat < min.toNat := UInt32.lt_iff_toNat_lt.mp hr
      exact itB_wp P count max min min hcs hcc hmx hpos hmin (by omega) (by omega) (by omega)
        (fun hC => by have := hrC hC; omega)
    · rw [if_neg hr]
      have hr' : min.toNat ≤ root.toNat := by
        have := (not_congr UInt32.lt_iff_toNat_lt).mp hr; omega
      exact itB_wp P count max min root hcs hcc hmx hpos hmin (by omega) (by omega) (by omega)
        (fun hC => by have := hrC hC; omega)

theorem mxl_le7 {f : Nat → Nat} {n : Nat} (hpos : 0 < Tc f n 15) (hall : ∀ k, k < n → f k ≤ 7) : mxl f n ≤ 7 := by
  unfold mxl lenAt
  exact hall _ (ws_getD_lt (by omega))

theorem itTop_wp {h : Heap} {type : UInt32} {rl : WRef} {ol : Nat} {codes : UInt32} {rc : CodeRef} {oc : Nat}
    {bits : UInt32} {rw : WRef} {ow : Nat} (P : CallPre h type rl ol codes rc oc bits rw ow) :
    Wp (itTop type (Ptr.ref rl ol) codes (Ptr.ref rc oc) bits (Ptr.ref rw ow)) h
      (fun r h' => Result h rw rc ow oc (capOf type) codes.toNat P.wa P.ca (Ptr.ref rc oc) bits r h' ∧
        RetInfo type P.f codes.toNat r) := by
  have hn288 : codes.toNat ≤ 288 := by
    rcases P.hty with ht | ht | ht
    · have := (P.hcodes ht).1; omega
    · exact P.hlens ht
    · have := P.hdists ht; omega
  unfold itTop
  apply Wp.bind' (zero_loop h)
  rintro ⟨len, count⟩ h' ⟨rfl, hs, hz⟩
  dsimp only at hs hz ⊢
  apply Wp.bind' (count_loop P.f codes.toNat hn288 rl ol P.la codes rfl _ P.hgl P.hla (fun k => rfl) P.hf15 count hs hz)
  rintro ⟨sym, count2⟩ h2 ⟨rfl, hsym, hs2, hc2⟩
  dsimp only at hs2 hc2 ⊢
  have hcc : ∀ l, 1 ≤ l → l ≤ 15 → (count2.getD l 0).toNat = cnt P.f codes.toNat l := fun l h1 h2 => hc2 l (by omega)
  apply Wp.bind' (max_loop P.f codes.toNat count2 hs2 hcc _)
  rintro ⟨max, brk⟩ h3 ⟨rfl, hmaxq⟩
  dsimp only at hmaxq ⊢
  by_cases hgt : bits > max
  · rw [if_pos hgt]
    exact itA_wp P count2 max max hs2 hcc hmaxq (Nat.le_refl _) (fun _ => rfl)
  · rw [if_neg hgt]
    have hle : bits.toNat ≤ max.toNat := by
      have := (not_congr UInt32.lt_iff_toNat_lt).mp hgt; omega
    exact itA_wp P count2 max bits hs2 hcc hmaxq hle
      (fun hC => by
        obtain ⟨_, h7, hb7⟩ := P.hcodes hC
        rcases hmaxq with ⟨a, b⟩ | ⟨a, b⟩
        · omega
        · have := mxl_le7 (f := P.f) (n := codes.toNat) a h7
          omega)

theorem inflate_table_eq : inflate_table = itTop := rfl

end Zlib.Inftrees.Proofs
