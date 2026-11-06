import ZlibF.Proof.«inflate.c.main.table5»

/-!
# inflate.c: `case LENLENS:` as a whole
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec

/-- The state record after both loops of `LENLENS` ran to the end (`M = ncode - have`). -/
def llDone (s : InflateState) (S : List Bool) : InflateState :=
  lzSt (llSt s S (s.ncode.toNat - s.«have».toNat)) (19 - (llSt s S (s.ncode.toNat - s.«have».toNat)).«have».toNat)

theorem llDone_lens (s : InflateState) (S : List Bool) (hnc : s.ncode.toNat ≤ 19) (hhn : s.«have».toNat ≤ s.ncode.toNat) :
    (llDone s S).lens = lensZero (lensRead s.lens s.«have».toNat S (s.ncode.toNat - s.«have».toNat)) s.ncode.toNat
      (19 - s.ncode.toNat) := by
  have h1 := llSt_have s S (s.ncode.toNat - s.«have».toNat) (by omega)
  unfold llDone lzSt llSt
  simp only [llSt] at h1 ⊢
  rw [h1]
  have e : s.«have».toNat + (s.ncode.toNat - s.«have».toNat) = s.ncode.toNat := by omega
  rw [e]

theorem llDone_have (s : InflateState) (S : List Bool) (hnc : s.ncode.toNat ≤ 19) (hhn : s.«have».toNat ≤ s.ncode.toNat) :
    (llDone s S).«have».toNat = 19 := by
  have h1 := llSt_have s S (s.ncode.toNat - s.«have».toNat) (by omega)
  have h2 := lzSt_have (llSt s S (s.ncode.toNat - s.«have».toNat)) (19 - (llSt s S (s.ncode.toNat - s.«have».toNat)).«have».toNat)
    (by omega)
  unfold llDone
  omega

/-- **`case LENLENS:`.** From `have ≤ ncode ≤ 19` (as `TABLE` leaves them, or a resumed call) with the lengths read by earlier calls
being 3-bit values (`Good3`, which holds because `inflate.c` stores only `BITS(3)` there). `M = min (ncode - have) (⌊|S| / 3⌋)`
code-length code lengths are read from the unread stream `S` (three bits each, `grp`) into `lens[order[have + u]]`.

* `M < ncode - have`: the input ran out; `goto inf_leave` with the registers `l'` (all input pulled, fewer than 3 bits left); the
  state record has `have + M` and the `M` lengths.
* `M = ncode - have`: the other lengths are set to 0 (the state `llDone`), `inflate_table(CODES, lens, 19, ...)` is called
  (result `0` or `-1`; `-1` exactly when the 19 lengths are not an acceptable code in the format specification), and then either
  the error "invalid code lengths set" (`BAD`, `break`) or `have = 0`, `mode = CODELENS` and the fall-through into `CODELENS`. -/
theorem inflate_LENLENS_run {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {bs : List UInt8} (hr : c.strm = some r) (hc : c.st = some (.tab zs)) (hz : r.get h = some z)
    (hs : h.istates zs = some s) (hwf : s.WellFormed) (hnc : s.ncode.toNat ≤ 19) (hhn : s.«have».toNat ≤ s.ncode.toNat)
    (hG : Good3 s.lens s.«have».toNat) (B : BitInv h l bs) :
    ∃ l' j, j ≤ bs.length ∧ BitInv h l' (bs.drop j) ∧
      stream l' (bs.drop j) = (stream l bs).drop (3 * min (s.ncode.toNat - s.«have».toNat) ((stream l bs).length / 3)) ∧
      TcRegShape l l' ∧
      (min (s.ncode.toNat - s.«have».toNat) ((stream l bs).length / 3) < s.ncode.toNat - s.«have».toNat →
        l'.have_ = 0 ∧ j = bs.length ∧ l'.bits.toNat < 3 ∧
        runX (inflate_LENLENS c) l h = .ok ((.error Ex.leave, l'), setI h zs
          (llSt s (stream l bs) (min (s.ncode.toNat - s.«have».toNat) ((stream l bs).length / 3))))) ∧
      (min (s.ncode.toNat - s.«have».toNat) ((stream l bs).length / 3) = s.ncode.toNat - s.«have».toNat →
        ∃ (ret : Int32) (wa' : Array UInt16) (ca' : Array Code), wa'.size = 288 ∧ ca'.size = 1444 ∧
          (∀ x, 19 ≤ x → wa'[x]? = s.work[x]?) ∧ (∀ x, 128 ≤ x → ca'[x]? = s.codes[x]?) ∧
          (ret = 0 ∨ ret = -1) ∧
          (ret = -1 ↔ ¬ ZlibF.Spec.Acceptable .codeLength
            (Zlib.Inftrees.Spec.lensList (llDone s (stream l bs)).lens 0 19)) ∧
          (ret = 0 → ∃ u lb, u ≤ 128 ∧ runX (inflate_LENLENS c) l h = runX (inflate_CODELENS c) { l' with ret := 0 }
            (setI h zs (llOkSt zs (llDone s (stream l bs)) u lb wa' ca'))) ∧
          (ret = -1 → ∃ i, strTable[i]? = some "invalid code lengths set" ∧
            runX (inflate_LENLENS c) l h = .ok ((.ok (), { l' with ret := -1 }),
              tcBadHeap (setI h zs (llBadSt zs (llDone s (stream l bs)) wa' ca')) r zs z
                (llBadSt zs (llDone s (stream l bs)) wa' ca') i))) := by
  obtain ⟨hl, hw, hcs⟩ := hwf
  obtain ⟨r1, l', j, hrun1, hj, B', hS', hsh, hl1, hok1⟩ := ll1_run hc hs hl hnc hhn B
  refine ⟨l', j, hj, B', hS', hsh, ?_, ?_⟩
  · intro hlt
    obtain ⟨hr1, h2, h3, h4⟩ := hl1 hlt
    refine ⟨h2, h3, h4, ?_⟩
    rw [inflate_LENLENS_eq, runX_bind, hrun1, hr1]
  · intro heq
    have hr1 := hok1 heq
    obtain ⟨S, hSdef⟩ : ∃ S, S = stream l bs := ⟨_, rfl⟩
    rw [← hSdef] at hrun1 heq ⊢
    rw [heq] at hrun1
    obtain ⟨n, hn⟩ : ∃ n, n = s.ncode.toNat - s.«have».toNat := ⟨_, rfl⟩
    rw [← hn] at hrun1
    have ht1 : (setI h zs (llSt s S n)).istates zs = some (llSt s S n) := by simp
    have hht1 := llSt_have s S n (by omega)
    have hsz1 : (llSt s S n).lens.size = 320 := by simp [llSt, lensRead_size, hl]
    have hlz := lz_run (c := c) (l := l') hc ht1 hsz1 (by omega)
    have hdone : llDone s S = lzSt (llSt s S n) (19 - (llSt s S n).«have».toNat) := by
      unfold llDone; rw [← hn]
    have hmain : runX (inflate_LENLENS c) l h = runX (llTail c) l' (setI h zs (llDone s S)) := by
      rw [inflate_LENLENS_eq, runX_bind, hrun1, hr1]
      simp only []
      rw [runX_bind, hlz, hdone]
      simp only [setI_setI]
    have hgood : Good3 (llDone s S).lens 19 := by
      rw [llDone_lens s S hnc hhn]
      have g1 := lensRead_good (a := s.lens) (i0 := s.«have».toNat) S hG (s.ncode.toNat - s.«have».toNat) (by omega)
      rw [show s.«have».toNat + (s.ncode.toNat - s.«have».toNat) = s.ncode.toNat by omega] at g1
      have g2 := lensZero_good g1 (19 - s.ncode.toNat) (by omega)
      rwa [show s.ncode.toNat + (19 - s.ncode.toNat) = 19 by omega] at g2
    have hwf' : (llDone s S).WellFormed := by
      refine ⟨?_, ?_, ?_⟩
      · rw [llDone_lens s S hnc hhn, lensZero_size, lensRead_size]; exact hl
      · exact hw
      · exact hcs
    have hs' : (setI h zs (llDone s S)).istates zs = some (llDone s S) := by simp
    have hz' : r.get (setI h zs (llDone s S)) = some z := by simpa using hz
    obtain ⟨ret, wa', ca', hwa, hca, hfw, hfc, hret, hacc, hz0, hz1⟩ := llTail_run (c := c) (l := l') hr hc hz' hs' hwf' hgood
    refine ⟨ret, wa', ca', hwa, hca, ?_, ?_, hret, hacc, ?_, ?_⟩
    · intro x hx; rw [hfw x hx]; simp [llDone, lzSt, llSt]
    · intro x hx; rw [hfc x hx]; simp [llDone, lzSt, llSt]
    · intro h0
      obtain ⟨u, lb, hu, hrunu⟩ := hz0 h0
      exact ⟨u, lb, hu, by rw [hmain, hrunu]; simp only [setI_setI]⟩
    · intro h0
      obtain ⟨i, hi, hrunb⟩ := hz1 h0
      refine ⟨i, hi, ?_⟩
      rw [hmain, hrunb]
      simp only [setI_setI]

end Zlib.Inflate.Proofs
