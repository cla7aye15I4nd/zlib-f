import ZlibF.Proof.«inflate.c.misc2»

/-!
# inflate.c: `syncsearch`

The pattern search of `inflateSync`. `syncsearch(have, buf, len)` is a four-state automaton: `got` counts how many bytes
of the pattern `00 00 FF FF` are matched at the end of the input so far. It stops after the byte that completes the
pattern, or at the end of the input. The pure part (`syncStep`, `syncScan`) is the loop of the C function on a list of
bytes; `syncScan_spec` shows what it computes: the position of the first occurrence of the pattern, and, when there is
none, the longest proper prefix of the pattern that ends the input (the state to carry into the next call).
-/

namespace Zlib.Inflate.Spec
open C

/-- The pattern that `inflateSync` looks for: the end of an empty stored block (`00 00` is its length, `FF FF` the
complement), which `deflate` writes at a sync or full flush point. -/
def syncPat : List UInt8 := [0, 0, 255, 255]

/-- One step of the loop of `syncsearch`: the new value of `got` after the byte `b`. -/
def syncStep (got : UInt32) (b : UInt8) : UInt32 :=
  if b.toNat == (if got < 2 then 0 else 0xff) then got + 1 else if b != 0 then 0 else 4 - got

/-- The loop of `syncsearch` on the bytes `bs`, starting with `got`: the final `got` and the number of bytes consumed
(the loop stops after the byte that makes `got` 4, or at the end of the input). -/
def syncScan (got : UInt32) : List UInt8 → UInt32 × Nat
  | [] => (got, 0)
  | b :: bs => if got < 4 then ((syncScan (syncStep got b) bs).1, (syncScan (syncStep got b) bs).2 + 1)
    else (got, 0)

/-- `got` is the state of the search after the bytes `w`: the pattern has not occurred in `w`, and `got` is the length
of the longest proper prefix of the pattern (at most 3 bytes) that ends `w`. -/
def SyncSt (g : UInt32) (w : List UInt8) : Prop :=
  g.toNat < 4 ∧ ¬ syncPat <:+: w ∧ syncPat.take g.toNat <:+ w ∧ ∀ k, k < 4 → syncPat.take k <:+ w → k ≤ g.toNat

/-- The bytes `buf[0 .. len)` of a pointer `buf = .ref r o` into the array `a`. -/
def syncBytes (a : Array UInt8) (o : Nat) (len : UInt32) : List UInt8 := (a.toList.drop o).take len.toNat

/-- The input `p[0 .. len)` that `syncsearch` and `inflateSync` read, as `zlib.h` allows it: `len` readable bytes `bs`
of a byte block of the heap (`o + len` within the block), or `NULL` with `len = 0` (`bs = []`). -/
def SyncIn (h : Heap) (p : BPtr) (len : UInt32) (bs : List UInt8) : Prop :=
  (∃ b a o, p = .ref (.blk b) o ∧ h.bytes b = some a ∧ o + len.toNat ≤ a.size ∧ bs = syncBytes a o len) ∨
  (p = .null ∧ len = 0 ∧ bs = [])

end Zlib.Inflate.Spec

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec

/-! ### The pure part -/

theorem infix_snoc {l w : List UInt8} {b : UInt8} : l <:+: w ++ [b] ↔ l <:+: w ∨ l <:+ w ++ [b] := by
  have e1 : l <:+: w ++ [b] ↔ l.reverse <:+: (w ++ [b]).reverse := List.reverse_infix.symm
  have e2 : l <:+ w ++ [b] ↔ l.reverse <+: (w ++ [b]).reverse := List.reverse_prefix.symm
  have e3 : l <:+: w ↔ l.reverse <:+: w.reverse := List.reverse_infix.symm
  rw [e1, e2, e3, List.reverse_append, List.reverse_singleton, List.singleton_append, List.infix_cons_iff]
  exact Iff.intro (fun h => h.elim Or.inr Or.inl) (fun h => h.elim Or.inr Or.inl)

theorem suffix_snoc {l w : List UInt8} {x b : UInt8} : l ++ [x] <:+ w ++ [b] ↔ x = b ∧ l <:+ w := by
  rw [← List.reverse_prefix, ← List.reverse_prefix (l₁ := l)]
  simp [List.cons_prefix_cons, eq_comm]

theorem suffix_snoc0 {w : List UInt8} {b : UInt8} : [b] <:+ w ++ [b] := List.suffix_append _ _

theorem suffix_snoc1 {w : List UInt8} {x b : UInt8} : [x] <:+ w ++ [b] ↔ x = b := by
  have := @suffix_snoc [] w x b
  simpa using this

/-- Suffix facts used to step the search: the last byte of `w ++ [b]`, and the suffixes `[0]`, `[0,0]`, `[0,0,255]`. -/
theorem sfx1 {w : List UInt8} {b : UInt8} : [0] <:+ w ++ [b] ↔ b = 0 := by
  rw [suffix_snoc1]; exact ⟨fun h => h.symm, fun h => h.symm⟩
theorem sfx2 {w : List UInt8} {b : UInt8} : [0, 0] <:+ w ++ [b] ↔ b = 0 ∧ [0] <:+ w := by
  have := @suffix_snoc [0] w 0 b
  simp only [List.cons_append, List.nil_append] at this
  rw [this]; exact ⟨fun h => ⟨h.1.symm, h.2⟩, fun h => ⟨h.1.symm, h.2⟩⟩
theorem sfx3 {w : List UInt8} {b : UInt8} : [0, 0, 255] <:+ w ++ [b] ↔ b = 255 ∧ [0, 0] <:+ w := by
  have := @suffix_snoc [0, 0] w 255 b
  simp only [List.cons_append, List.nil_append] at this
  rw [this]; exact ⟨fun h => ⟨h.1.symm, h.2⟩, fun h => ⟨h.1.symm, h.2⟩⟩
theorem sfx4 {w : List UInt8} {b : UInt8} : syncPat <:+ w ++ [b] ↔ b = 255 ∧ [0, 0, 255] <:+ w := by
  have := @suffix_snoc [0, 0, 255] w 255 b
  simp only [List.cons_append, List.nil_append] at this
  unfold syncPat
  rw [this]; exact ⟨fun h => ⟨h.1.symm, h.2⟩, fun h => ⟨h.1.symm, h.2⟩⟩

theorem sfx2_1 {w : List UInt8} (h : [0, 0] <:+ w) : [0] <:+ w :=
  List.IsSuffix.trans ⟨[0], rfl⟩ h

theorem sfx3_not1 {w : List UInt8} (h : [0, 0, 255] <:+ w) : ¬ [0] <:+ w := by
  obtain ⟨t, rfl⟩ := h
  intro ⟨s, hs⟩
  have : ([0] : List UInt8) <:+ t ++ [0, 0, 255] := ⟨s, hs⟩
  have e : t ++ [0, 0, 255] = (t ++ [0, 0]) ++ [255] := by simp
  rw [e, sfx1] at this
  exact absurd this (by decide)

theorem sfx3_not2 {w : List UInt8} (h : [0, 0, 255] <:+ w) : ¬ [0, 0] <:+ w :=
  fun h2 => sfx3_not1 h (sfx2_1 h2)

/-- The state description for each value of `got`. -/
theorem syncSt_cases {g : UInt32} {w : List UInt8} (hs : SyncSt g w) :
    (g = 0 ∧ ¬ [0] <:+ w ∧ ¬ [0, 0] <:+ w ∧ ¬ [0, 0, 255] <:+ w) ∨
    (g = 1 ∧ [0] <:+ w ∧ ¬ [0, 0] <:+ w ∧ ¬ [0, 0, 255] <:+ w) ∨
    (g = 2 ∧ [0, 0] <:+ w ∧ ¬ [0, 0, 255] <:+ w) ∨
    (g = 3 ∧ [0, 0, 255] <:+ w) := by
  obtain ⟨hlt, -, hpre, hmax⟩ := hs
  have m1 := hmax 1 (by omega)
  have m2 := hmax 2 (by omega)
  have m3 := hmax 3 (by omega)
  have e1 : syncPat.take 1 = [0] := rfl
  have e2 : syncPat.take 2 = [0, 0] := rfl
  have e3 : syncPat.take 3 = [0, 0, 255] := rfl
  rw [e1] at m1; rw [e2] at m2; rw [e3] at m3
  have hg : g.toNat = 0 ∨ g.toNat = 1 ∨ g.toNat = 2 ∨ g.toNat = 3 := by omega
  rcases hg with hg | hg | hg | hg
  · left
    refine ⟨UInt32.toNat_inj.mp (by simpa using hg), fun h => ?_, fun h => ?_, fun h => ?_⟩
    · have := m1 h; omega
    · have := m2 h; omega
    · have := m3 h; omega
  · right; left
    rw [hg] at hpre
    refine ⟨UInt32.toNat_inj.mp (by simpa using hg), hpre, fun h => ?_, fun h => ?_⟩
    · have := m2 h; omega
    · have := m3 h; omega
  · right; right; left
    rw [hg] at hpre
    refine ⟨UInt32.toNat_inj.mp (by simpa using hg), hpre, fun h => ?_⟩
    have := m3 h; omega
  · right; right; right
    rw [hg] at hpre
    exact ⟨UInt32.toNat_inj.mp (by simpa using hg), hpre⟩

theorem syncSt_mk {g : UInt32} {w : List UInt8}
    (hn : ¬ syncPat <:+: w)
    (hc : (g = 0 ∧ ¬ [0] <:+ w ∧ ¬ [0, 0] <:+ w ∧ ¬ [0, 0, 255] <:+ w) ∨
    (g = 1 ∧ [0] <:+ w ∧ ¬ [0, 0] <:+ w ∧ ¬ [0, 0, 255] <:+ w) ∨
    (g = 2 ∧ [0, 0] <:+ w ∧ ¬ [0, 0, 255] <:+ w) ∨
    (g = 3 ∧ [0, 0, 255] <:+ w)) : SyncSt g w := by
  have e1 : syncPat.take 1 = [0] := rfl
  have e2 : syncPat.take 2 = [0, 0] := rfl
  have e3 : syncPat.take 3 = [0, 0, 255] := rfl
  have e0 : syncPat.take 0 = [] := rfl
  rcases hc with ⟨rfl, a1, a2, a3⟩ | ⟨rfl, a1, a2, a3⟩ | ⟨rfl, a2, a3⟩ | ⟨rfl, a3⟩
  · refine ⟨by decide, hn, ?_, ?_⟩
    · show syncPat.take 0 <:+ w
      rw [e0]; exact List.nil_suffix
    · intro k hk hs
      have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
      rcases this with rfl | rfl | rfl | rfl
      · decide
      · rw [e1] at hs; exact absurd hs a1
      · rw [e2] at hs; exact absurd hs a2
      · rw [e3] at hs; exact absurd hs a3
  · refine ⟨by decide, hn, ?_, ?_⟩
    · show syncPat.take 1 <:+ w
      rw [e1]; exact a1
    · intro k hk hs
      have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
      rcases this with rfl | rfl | rfl | rfl
      · decide
      · decide
      · rw [e2] at hs; exact absurd hs a2
      · rw [e3] at hs; exact absurd hs a3
  · refine ⟨by decide, hn, ?_, ?_⟩
    · show syncPat.take 2 <:+ w
      rw [e2]; exact a2
    · intro k hk hs
      have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
      rcases this with rfl | rfl | rfl | rfl
      · decide
      · decide
      · decide
      · rw [e3] at hs; exact absurd hs a3
  · refine ⟨by decide, hn, ?_, ?_⟩
    · show syncPat.take 3 <:+ w
      rw [e3]; exact a3
    · intro k hk hs
      have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
      rcases this with rfl | rfl | rfl | rfl <;> decide

/-- The search starts in state 0 with nothing read. -/
theorem syncSt_zero : SyncSt 0 [] := by
  refine syncSt_mk (by decide) (Or.inl ⟨rfl, ?_, ?_, ?_⟩)
  · rintro ⟨t, ht⟩; simp at ht
  · rintro ⟨t, ht⟩; simp at ht
  · rintro ⟨t, ht⟩; simp at ht

theorem u8_eq255 {b : UInt8} : b.toNat = 255 ↔ b = 255 := by
  constructor
  · intro h; exact UInt8.toNat_inj.mp (by simpa using h)
  · rintro rfl; rfl

theorem u8_eq0 {b : UInt8} : b.toNat = 0 ↔ b = 0 := by
  constructor
  · intro h; exact UInt8.toNat_inj.mp (by simpa using h)
  · rintro rfl; rfl

/-- **One step.** If the pattern has not occurred in `w` and `got` is the state after `w`, then after the byte `b`: either
the pattern ends here (`syncStep` gives 4 and the pattern is a suffix of `w ++ [b]`), or the pattern has still not
occurred and `syncStep` gives the state after `w ++ [b]`. -/
theorem syncStep_spec {g : UInt32} {w : List UInt8} (hs : SyncSt g w) (b : UInt8) :
    (syncStep g b = 4 ∧ syncPat <:+ w ++ [b]) ∨ (syncStep g b < 4 ∧ SyncSt (syncStep g b) (w ++ [b])) := by
  have hn := hs.2.1
  have hP : syncPat <:+ w ++ [b] ↔ b = 255 ∧ [0, 0, 255] <:+ w := sfx4
  have hI : syncPat <:+: w ++ [b] ↔ syncPat <:+: w ∨ syncPat <:+ w ++ [b] := infix_snoc
  have t1 : [0] <:+ w ++ [b] ↔ b = 0 := sfx1
  have t2 : [0, 0] <:+ w ++ [b] ↔ b = 0 ∧ [0] <:+ w := sfx2
  have t3 : [0, 0, 255] <:+ w ++ [b] ↔ b = 255 ∧ [0, 0] <:+ w := sfx3
  have hno : ¬ syncPat <:+: w ++ [b] ↔ ¬ (b = 255 ∧ [0, 0, 255] <:+ w) := by
    rw [hI, hP]; simp [hn]
  by_cases hb0 : b = 0
  · subst hb0
    have h255 : ¬ ((0 : UInt8) = 255 ∧ [0, 0, 255] <:+ w) := fun h => absurd h.1 (by decide)
    rcases syncSt_cases hs with ⟨rfl, a1, a2, a3⟩ | ⟨rfl, a1, a2, a3⟩ | ⟨rfl, a2, a3⟩ | ⟨rfl, a3⟩
    · have e : syncStep 0 0 = 1 := by decide
      rw [e]; right
      refine ⟨by decide, syncSt_mk (hno.mpr h255) (Or.inr (Or.inl ⟨rfl, t1.mpr rfl, ?_, ?_⟩))⟩
      · rw [t2]; simp [a1]
      · rw [t3]; simp
    · have e : syncStep 1 0 = 2 := by decide
      rw [e]; right
      refine ⟨by decide, syncSt_mk (hno.mpr h255) (Or.inr (Or.inr (Or.inl ⟨rfl, ?_, ?_⟩)))⟩
      · rw [t2]; simp [a1]
      · rw [t3]; simp
    · have e : syncStep 2 0 = 2 := by decide
      rw [e]; right
      refine ⟨by decide, syncSt_mk (hno.mpr h255) (Or.inr (Or.inr (Or.inl ⟨rfl, ?_, ?_⟩)))⟩
      · rw [t2]; exact ⟨rfl, sfx2_1 a2⟩
      · rw [t3]; simp
    · have e : syncStep 3 0 = 1 := by decide
      rw [e]; right
      refine ⟨by decide, syncSt_mk (hno.mpr h255) (Or.inr (Or.inl ⟨rfl, t1.mpr rfl, ?_, ?_⟩))⟩
      · rw [t2]; simp; exact sfx3_not1 a3
      · rw [t3]; simp
  · by_cases hb255 : b = 255
    · subst hb255
      rcases syncSt_cases hs with ⟨rfl, a1, a2, a3⟩ | ⟨rfl, a1, a2, a3⟩ | ⟨rfl, a2, a3⟩ | ⟨rfl, a3⟩
      · have e : syncStep 0 255 = 0 := by decide
        rw [e]; right
        refine ⟨by decide, syncSt_mk (hno.mpr (by simp [a3])) (Or.inl ⟨rfl, ?_, ?_, ?_⟩)⟩
        · rw [t1]; decide
        · rw [t2]; simp
        · rw [t3]; simp [a2]
      · have e : syncStep 1 255 = 0 := by decide
        rw [e]; right
        refine ⟨by decide, syncSt_mk (hno.mpr (by simp [a3])) (Or.inl ⟨rfl, ?_, ?_, ?_⟩)⟩
        · rw [t1]; decide
        · rw [t2]; simp
        · rw [t3]; simp [a2]
      · have e : syncStep 2 255 = 3 := by decide
        rw [e]; right
        refine ⟨by decide, syncSt_mk (hno.mpr (by simp [a3])) (Or.inr (Or.inr (Or.inr ⟨rfl, ?_⟩)))⟩
        rw [t3]; exact ⟨rfl, a2⟩
      · have e : syncStep 3 255 = 4 := by decide
        rw [e]; left
        exact ⟨rfl, hP.mpr ⟨rfl, a3⟩⟩
    · have hb0' : ¬ b.toNat = 0 := fun h => hb0 (u8_eq0.mp h)
      have hb255' : ¬ b.toNat = 255 := fun h => hb255 (u8_eq255.mp h)
      have e : ∀ g : UInt32, syncStep g b = 0 := by
        intro g
        unfold syncStep
        by_cases hg : g < 2
        · simp [hg, hb0, hb0']
        · simp [hg, hb0, hb255']
      have h255 : ¬ (b = 255 ∧ [0, 0, 255] <:+ w) := fun h => hb255 h.1
      have fin : SyncSt 0 (w ++ [b]) := by
        refine syncSt_mk (hno.mpr h255) (Or.inl ⟨rfl, ?_, ?_, ?_⟩)
        · rw [t1]; exact hb0
        · rw [t2]; exact fun h => hb0 h.1
        · rw [t3]; exact fun h => hb255 h.1
      rw [e]; right
      exact ⟨by decide, fin⟩

theorem syncScan_nil (g : UInt32) : syncScan g [] = (g, 0) := rfl

theorem syncScan_cons_lt {g : UInt32} (hg : g < 4) (b : UInt8) (bs : List UInt8) :
    syncScan g (b :: bs) = ((syncScan (syncStep g b) bs).1, (syncScan (syncStep g b) bs).2 + 1) := by
  simp [syncScan, hg]

theorem syncScan_ge {g : UInt32} (hg : ¬ g < 4) (bs : List UInt8) : syncScan g bs = (g, 0) := by
  cases bs <;> simp [syncScan, hg]

theorem syncScan_le (g : UInt32) (bs : List UInt8) : (syncScan g bs).2 ≤ bs.length := by
  induction bs generalizing g with
  | nil => simp [syncScan]
  | cons b bs ih =>
    by_cases hg : g < 4
    · rw [syncScan_cons_lt hg]; simp; exact ih _
    · rw [syncScan_ge hg]; simp

/-- **The search (pure part).** Let `g` be the state after the bytes `w` (`SyncSt`: the pattern `00 00 FF FF` has not
occurred in `w`, and `g` is the longest proper prefix of it that ends `w`). Scanning the bytes `bs` from `g` gives
`(G, L)` with `L ≤ |bs|` and:
* if `G = 4` the pattern was found, and `L` is the number of bytes consumed up to and including its last byte: `L > 0`,
  the pattern ends `w ++ bs[0 .. L)`, and it does not occur in `w ++ bs[0 .. L')` for any `L' < L` (the first
  occurrence);
* otherwise all of `bs` was consumed (`L = |bs|`) and `G` is the state after `w ++ bs`: the pattern has not occurred and
  `G` is the longest proper prefix of the pattern that ends the whole input (the state to carry into the next call). -/
theorem syncScan_spec {g : UInt32} {w : List UInt8} (hs : SyncSt g w) (bs : List UInt8) {G : UInt32} {L : Nat}
    (hr : syncScan g bs = (G, L)) :
    L ≤ bs.length ∧
    (G = 4 → 0 < L ∧ syncPat <:+ w ++ bs.take L ∧ ∀ L', L' < L → ¬ syncPat <:+: w ++ bs.take L') ∧
    (G ≠ 4 → L = bs.length ∧ SyncSt G (w ++ bs)) := by
  induction bs generalizing g w G L with
  | nil =>
    rw [syncScan_nil] at hr
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hr
    refine ⟨Nat.le_refl _, fun h4 => ?_, fun _ => ⟨rfl, by simpa using hs⟩⟩
    have := hs.1; rw [h4] at this; exact absurd this (by decide)
  | cons b bs ih =>
    have hg4 : g < 4 := UInt32.lt_iff_toNat_lt.mpr (by simpa using hs.1)
    rw [syncScan_cons_lt hg4] at hr
    obtain ⟨hG, hL⟩ := Prod.mk.inj hr
    rcases syncStep_spec hs b with ⟨h4, hpat⟩ | ⟨hlt, hs'⟩
    · have hfin : syncScan (syncStep g b) bs = (4, 0) := syncScan_ge (by rw [h4]; decide) bs |>.trans (by rw [h4])
      rw [hfin] at hG hL
      simp only at hG hL
      subst hG; subst hL
      refine ⟨by simp, fun _ => ⟨by simp, by simpa using hpat, ?_⟩, fun h => absurd rfl h⟩
      intro L' hL'
      have : L' = 0 := by omega
      subst this
      simpa using hs.2.1
    · obtain ⟨ih1, ih2, ih3⟩ := ih hs' (show syncScan (syncStep g b) bs = ((syncScan (syncStep g b) bs).1, (syncScan (syncStep g b) bs).2) from rfl)
      rw [← hG, ← hL]
      refine ⟨by simp; omega, fun h4 => ?_, fun h4 => ?_⟩
      · obtain ⟨a1, a2, a3⟩ := ih2 h4
        refine ⟨by omega, ?_, ?_⟩
        · simpa [List.append_assoc] using a2
        · intro L' hL'
          cases L' with
          | zero => simpa using hs.2.1
          | succ j =>
            have := a3 j (by omega)
            simpa [List.append_assoc] using this
      · obtain ⟨a1, a2⟩ := ih3 h4
        refine ⟨by simp; omega, ?_⟩
        simpa [List.append_assoc] using a2

/-- The search finds the pattern exactly when it occurs in the history followed by the new bytes. -/
theorem syncScan_found_iff {g : UInt32} {w : List UInt8} (hs : SyncSt g w) (bs : List UInt8) :
    (syncScan g bs).1 = 4 ↔ syncPat <:+: w ++ bs := by
  obtain ⟨-, h1, h2⟩ := syncScan_spec hs bs rfl
  constructor
  · intro h
    obtain ⟨-, a2, -⟩ := h1 h
    have hin : w ++ bs.take (syncScan g bs).2 <:+: w ++ bs :=
      ⟨[], bs.drop (syncScan g bs).2, by simp [List.append_assoc]⟩
    exact (List.IsSuffix.isInfix a2).trans hin
  · intro h
    refine Classical.byContradiction fun hne => ?_
    exact (h2 hne).2.2.1 (by simpa using h)

/-! ### The loop on the heap -/

theorem syncBytes_length {a : Array UInt8} {o : Nat} {len : UInt32} (hl : o + len.toNat ≤ a.size) :
    (syncBytes a o len).length = len.toNat := by
  simp [syncBytes]; omega

theorem syncBytes_drop {a : Array UInt8} {o : Nat} {len : UInt32} (hl : o + len.toNat ≤ a.size) (n : Nat)
    (hn : n < len.toNat) :
    (syncBytes a o len).drop n = a[o + n]'(by omega) :: (syncBytes a o len).drop (n + 1) := by
  have hn' : n < (syncBytes a o len).length := by rw [syncBytes_length hl]; exact hn
  rw [List.drop_eq_getElem_cons hn']
  congr 1
  simp [syncBytes, List.getElem_take, List.getElem_drop]

theorem syncScan_zero {g G : UInt32} {bs : List UInt8} (h : syncScan g bs = (G, 0)) :
    G = g ∧ (¬ g < 4 ∨ bs = []) := by
  cases bs with
  | nil => simp [syncScan] at h; exact ⟨h.symm, Or.inr rfl⟩
  | cons b bs =>
    by_cases hg : g < 4
    · rw [syncScan_cons_lt hg] at h; simp at h
    · rw [syncScan_ge hg] at h; simp at h; exact ⟨h.symm, Or.inl hg⟩

/-- **`syncsearch`, the loop on the heap.** For a pointer `buf = .ref r o` into a live array `a` with `len` readable
bytes (`o + len ≤ |a|`) the call returns, without a fault and without changing the heap, the number of bytes
consumed and the final `*have`, as the pure loop `syncScan` computes them on the bytes `a[o .. o + len)`. -/
theorem syncsearch_run {h : Heap} {r : BRef} {a : Array UInt8} {o : Nat} {len : UInt32} (g : UInt32)
    (hg : Space.get h r = some a) (hl : o + len.toNat ≤ a.size) :
    syncsearch g (.ref r o) len h =
      .ok ((UInt32.ofNat (syncScan g (syncBytes a o len)).2, (syncScan g (syncBytes a o len)).1), h) := by
  have hL := syncBytes_length hl
  have hlt := len.toNat_lt
  generalize hR : syncScan g (syncBytes a o len) = R
  obtain ⟨G, K⟩ := R
  have hK : K ≤ len.toNat := by
    have := syncScan_le g (syncBytes a o len); rw [hR] at this; simp at this; omega
  let P : Nat → UInt32 × UInt32 → Prop := fun k s =>
    s.1.toNat + k = K ∧ syncScan s.2 ((syncBytes a o len).drop s.1.toNat) = (G, k)
  let Q : UInt32 × UInt32 → Prop := fun s => s.2 = G ∧ s.1.toNat = K
  have key := cwhile_ok (h := h) (σ := UInt32 × UInt32)
    (cond := fun (next, got) => pure (next < len && got < 4, (next, got)))
    (body := fun (next, got) => do
      let b ← index8 (.ref r o) next.toNat
      let got := if b.toNat == (if got < 2 then 0 else 0xff) then got + 1 else if b != 0 then 0 else 4 - got
      pure (next + 1, got)) P Q ?step ?stop (k := K) (s := (0, g)) ⟨by simp, by simpa using hR⟩ (by unfold fuel; omega)
  · obtain ⟨⟨n, gg⟩, hs, hq⟩ := key
    unfold syncsearch
    have hs' : cwhile (σ := UInt32 × UInt32)
        (fun (next, got) => pure (next < len && got < 4, (next, got)))
        (fun (next, got) => do
          let b ← index8 (.ref r o) next.toNat
          let got := if b.toNat == (if got < 2 then 0 else 0xff) then got + 1 else if b != 0 then 0 else 4 - got
          pure (next + 1, got)) (0, g) h = .ok ((n, gg), h) := hs
    simp only [bind_app, pure_app]
    rw [hs']
    obtain ⟨h1, h2⟩ := hq
    try simp only at h1 h2 ⊢
    subst h1
    have : n = UInt32.ofNat K := by rw [← h2]; simp
    subst this
    rfl
  case step =>
    intro k ⟨n, gg⟩ ⟨h1, h2⟩
    simp only at h1 h2
    have hn : n.toNat < len.toNat := by omega
    have hd := syncBytes_drop hl n.toNat hn
    have hg4 : gg < 4 := Classical.byContradiction fun hc => by
      rw [syncScan_ge hc] at h2; simp at h2
    rw [hd, syncScan_cons_lt hg4] at h2
    simp at h2
    refine ⟨(n, gg), (n + 1, syncStep gg a[o + n.toNat]), ?_, ?_, ?_⟩
    · unfold OkOn; simp [UInt32.lt_iff_toNat_lt, hn, hg4]
    · have hb : OkOn h (index8 (.ref r o) n.toNat) a[o + n.toNat] := Ptr.index_ok hg (by omega)
      unfold OkOn at hb ⊢
      simp only [bind_app, hb, pure_app, syncStep]
    · have e : (n + 1).toNat = n.toNat + 1 := by
        rw [UInt32.toNat_add]; simp; omega
      show (n + 1).toNat + k = K ∧ syncScan (syncStep gg a[o + n.toNat]) ((syncBytes a o len).drop (n + 1).toNat) = (G, k)
      rw [e]
      exact ⟨by omega, Prod.ext h2.1 h2.2⟩
  case stop =>
    intro ⟨n, gg⟩ ⟨h1, h2⟩
    try simp only at h1 h2
    obtain ⟨hgG, hor⟩ := syncScan_zero h2
    refine ⟨(n, gg), ?_, hgG.symm, by omega⟩
    unfold OkOn
    rcases hor with hg4 | hd
    · simp [hg4]
    · have : ¬ n.toNat < len.toNat := by
        intro hl'
        have := syncBytes_drop hl n.toNat hl'
        rw [hd] at this; simp at this
      simp [UInt32.lt_iff_toNat_lt, this]

/-- **`syncsearch` on `NULL` with length 0.** The loop test fails at once, `buf` is never read; `*have` is unchanged. -/
theorem syncsearch_null (g : UInt32) (h : Heap) : syncsearch g .null 0 h = .ok ((0, g), h) := by
  have key := cwhile_ok (h := h) (σ := UInt32 × UInt32)
    (cond := fun (next, got) => pure (next < 0 && got < 4, (next, got)))
    (body := fun (next, got) => do
      let b ← index8 .null next.toNat
      let got := if b.toNat == (if got < 2 then 0 else 0xff) then got + 1 else if b != 0 then 0 else 4 - got
      pure (next + 1, got)) (fun k s => k = 0 ∧ s = (0, g)) (fun s => s = (0, g))
    (fun k s ⟨hk, _⟩ => by omega)
    (fun s ⟨_, hs⟩ => ⟨s, by subst hs; unfold OkOn; simp [bind_app, pure_app], hs⟩)
    (k := 0) (s := (0, g)) ⟨rfl, rfl⟩ (by unfold fuel; omega)
  obtain ⟨s, hs, hq⟩ := key
  subst hq
  unfold syncsearch
  simp only [bind_app, pure_app]
  have hs' : cwhile (σ := UInt32 × UInt32)
      (fun (next, got) => pure (next < 0 && got < 4, (next, got)))
      (fun (next, got) => do
        let b ← index8 .null next.toNat
        let got := if b.toNat == (if got < 2 then 0 else 0xff) then got + 1 else if b != 0 then 0 else 4 - got
        pure (next + 1, got)) (0, g) h = .ok ((0, g), h) := hs
  rw [hs']

theorem syncIn_length {h : Heap} {p : BPtr} {len : UInt32} {bs : List UInt8} (I : SyncIn h p len bs) :
    bs.length = len.toNat := by
  rcases I with ⟨b, a, o, rfl, hg, hl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · exact syncBytes_length hl
  · rfl

/-- **`syncsearch`, specification.** Let `g` be the state after the bytes `w` (`SyncSt`; `g = 0` and `w = []` for the
first call). On an input `buf[0 .. len)` (`SyncIn`) the call never faults, does not change the heap, and returns the
number `N` of bytes consumed and the new `*have` `G`:
* `G = 4`: the pattern `00 00 FF FF` was found, `N > 0`, it ends `w ++ buf[0 .. N)` and does not occur in `w ++ buf[0 .. N')` for
  `N' < N` (the first occurrence), and `N ≤ len`;
* `G ≠ 4`: all `len` bytes were consumed and `G` is the state after `w ++ buf[0 .. len)` (the longest proper prefix of
  the pattern that ends the input): the pattern has not occurred and a later call carries on from `G`. -/
theorem syncsearch_spec {h : Heap} {p : BPtr} {len : UInt32} {bs : List UInt8} (I : SyncIn h p len bs)
    {g : UInt32} {w : List UInt8} (hs : SyncSt g w) :
    ∃ N G, syncsearch g p len h = .ok ((N, G), h) ∧ N.toNat ≤ len.toNat ∧
      (G = 4 → 0 < N.toNat ∧ syncPat <:+ w ++ bs.take N.toNat ∧ ∀ L', L' < N.toNat → ¬ syncPat <:+: w ++ bs.take L') ∧
      (G ≠ 4 → N = len ∧ SyncSt G (w ++ bs)) := by
  have hlen := syncIn_length I
  rcases I with ⟨b, a, o, rfl, hg, hl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · refine ⟨UInt32.ofNat (syncScan g (syncBytes a o len)).2, (syncScan g (syncBytes a o len)).1,
      syncsearch_run (r := .blk b) g hg hl, ?_⟩
    obtain ⟨h1, h2, h3⟩ := syncScan_spec hs (syncBytes a o len) rfl
    have hn : (UInt32.ofNat (syncScan g (syncBytes a o len)).2).toNat = (syncScan g (syncBytes a o len)).2 := by
      have := len.toNat_lt
      rw [UInt32.toNat_ofNat_of_lt' (by simp [UInt32.size]; omega)]
    rw [hn]
    refine ⟨by omega, h2, fun hne => ?_⟩
    obtain ⟨e, st⟩ := h3 hne
    refine ⟨?_, st⟩
    apply UInt32.toNat_inj.mp; rw [hn]; omega
  · refine ⟨0, g, syncsearch_null g h, by simp, ?_, ?_⟩
    · intro h4
      have := hs.1; rw [h4] at this; exact absurd this (by decide)
    · intro _; exact ⟨rfl, by simpa using hs⟩

end Zlib.Inflate.Proofs
