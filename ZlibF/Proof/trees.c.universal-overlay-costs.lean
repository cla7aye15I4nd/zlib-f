import ZlibF.Proof.«trees.c.runs»
import ZlibF.Math.DeflateSymbolMass

/-!
# trees.c: the cost counters at the dynamic choice (for `TinyOverlay`)

`_tr_flush_block` chooses the dynamic block by comparing `opt_len` and `static_len`. To use that
choice, the counters must mean the encoded lengths:

* `opt_len` = the dynamic header (tree description) + the dynamic codes of the symbols + the
  end-of-block code, extra bits included;
* `static_len` = the fixed codes of the symbols + the end-of-block code, extra bits included.

The run-length part: `scan_tree` counts, for every run of code lengths, the bit-length symbols
that `send_tree` emits for that run (`runFreq` against `runBits`). So the cost `build_tree` adds
for the bit-length tree, Σ frequency × (length + extra bits), is exactly the length of what
`send_tree` emits for both trees (`treeBits_length`).
-/

namespace Zlib.Trees.Proofs.Out
open C Zlib.Trees
open ZlibF.Math.DeflateSymbols (mass mass_add mass_congr mass_zero)
set_option autoImplicit false

/-- The extra bits of a bit-length symbol: `REP_3_6` 2, `REPZ_3_10` 3, `REPZ_11_138` 7. -/
def blExtraBits (k : Nat) : Nat := if k = 16 then 2 else if k = 17 then 3 else if k = 18 then 7 else 0

/-- The cost of one bit-length symbol with the code table `blt`: its code length plus its extra bits. -/
def blWeight (blt : Nat → UInt16 × UInt16) (k : Nat) : Nat := (blt k).2.toNat + blExtraBits k

theorem codeBits_length (t : Nat → UInt16 × UInt16) (n : Nat) : (codeBits t n).length = (t n).2.toNat := by
  simp [codeBits, natBits_length]

/-- A frequency concentrated on one symbol. -/
theorem mass_point (f : Nat → Nat) (c a n : Nat) (inside : c < n) :
    mass (fun k => (if k = c then a else 0) * f k) n = a * f c := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [mass]
    by_cases last : c = n
    · subst last
      have zero : mass (fun k => (if k = c then a else 0) * f k) c = 0 := by
        rw [mass_congr (g := fun _ => 0) (fun k lt => by simp [show k ≠ c by omega])]
        exact mass_zero c
      simp [zero]
    · rw [ih (by omega)]
      simp [show n ≠ c from fun e => last e.symm]

theorem mass_mul_add (f g w : Nat → Nat) (n : Nat) :
    mass (fun k => (f k + g k) * w k) n = mass (fun k => f k * w k) n + mass (fun k => g k * w k) n := by
  rw [← mass_add]
  apply mass_congr
  intro k _
  rw [Nat.add_mul]

theorem flatten_replicate_length (l : List Bool) (n : Nat) :
    (List.replicate n l).flatten.length = n * l.length := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate_succ, ih, Nat.succ_mul, Nat.add_comm]

/-- **One run**: what `send_tree` emits for a finished run has the length of the bit-length
symbols `scan_tree` counts for it, each at its code length plus extra bits. -/
theorem runBits_length (blt : Nat → UInt16 × UInt16) (o : Option (Nat × Int × Nat × Nat))
    (small : ∀ cur prev cnt mn, o = some (cur, prev, cnt, mn) → cur ≤ 15) :
    (runBits blt o).length = mass (fun k => runFreq o k * blWeight blt k) 19 := by
  rcases o with _ | ⟨cur, prev, cnt, mn⟩
  · simp only [runBits, runFreq, Nat.zero_mul, List.length_nil]
    exact (mass_zero 19).symm
  have hc : cur ≤ 15 := small cur prev cnt mn rfl
  have ec : blExtraBits cur = 0 := by
    unfold blExtraBits; simp [show cur ≠ 16 by omega, show cur ≠ 17 by omega, show cur ≠ 18 by omega]
  -- the frequency of the run as at most two point masses
  have two : ∀ (A B a b : Nat), A < 19 → B < 19 →
      (∀ k, runFreq (some (cur, prev, cnt, mn)) k = (if k = A then a else 0) + (if k = B then b else 0)) →
      mass (fun k => runFreq (some (cur, prev, cnt, mn)) k * blWeight blt k) 19 =
        a * blWeight blt A + b * blWeight blt B := by
    intro A B a b hA hB freq
    rw [mass_congr (g := fun k => (if k = A then a else 0) * blWeight blt k +
      (if k = B then b else 0) * blWeight blt B * (if k = B then 1 else 0)) (fun k _ => by
        rw [freq k]; by_cases kB : k = B <;> simp [kB, Nat.add_mul])]
    rw [mass_add, mass_point _ A a 19 hA]
    rw [mass_congr (g := fun k => (if k = B then b * blWeight blt B else 0) * 1) (fun k _ => by
      by_cases kB : k = B <;> simp [kB])]
    rw [mass_point (fun _ => 1) B (b * blWeight blt B) 19 hB]
    simp
  by_cases few : cnt < mn
  · rw [two cur 0 cnt 0 (by omega) (by omega) (fun k => by simp [runFreq, few])]
    simp [runBits, few, flatten_replicate_length, codeBits_length, blWeight, ec]
  by_cases nz : cur ≠ 0
  · by_cases newLen : (cur : Int) ≠ prev
    · rw [two cur 16 1 1 (by omega) (by omega) (fun k => by simp [runFreq, few, nz, newLen])]
      simp only [runBits, few, nz, newLen, if_false, if_true, ne_eq, not_false_eq_true, List.length_append,
        codeBits_length, natBits_length]
      have e16 : blExtraBits 16 = 2 := rfl
      simp only [blWeight, ec, e16]
      omega
    · rw [two 16 0 1 0 (by omega) (by omega) (fun k => by simp [runFreq, few, nz, newLen])]
      simp only [runBits, few, nz, newLen, if_false, if_true, ne_eq, not_false_eq_true, List.length_append,
        codeBits_length, natBits_length]
      simp [blWeight, blExtraBits]
  · have z : cur = 0 := by simpa using nz
    by_cases ten : cnt ≤ 10
    · rw [two 17 0 1 0 (by omega) (by omega) (fun k => by simp [runFreq, few, nz, ten])]
      simp [runBits, few, nz, ten, codeBits_length, blWeight, blExtraBits]
    · rw [two 18 0 1 0 (by omega) (by omega) (fun k => by simp [runFreq, few, nz, ten])]
      simp [runBits, few, nz, ten, codeBits_length, blWeight, blExtraBits]

/-- A finished run's length is the length at its index. -/
theorem runStep_cur (L : Nat → Nat) (n : Nat) :
    ∀ cur prev cnt mn, (runStep L n (runAt L n)).2 = some (cur, prev, cnt, mn) → cur = L n := by
  intro cur prev cnt mn e
  unfold runStep at e
  simp only [] at e
  split at e
  · cases e
  · simp only [Option.some.injEq, Prod.mk.injEq] at e
    rw [← e.1, runAt_next]

/-- **The whole tree**: the first `n` iterations of `send_tree` emit as many bits as the
bit-length symbols the first `n` iterations of `scan_tree` count, each at its weight, when the
lengths read are at most 15. -/
theorem treeBits_length (blt : Nat → UInt16 × UInt16) (L : Nat → Nat) (n : Nat)
    (small : ∀ i, i < n → L i ≤ 15) :
    (treeBitsUpTo blt L n).length = mass (fun k => scanFreqUpTo L n k * blWeight blt k) 19 := by
  induction n with
  | zero =>
    simp only [treeBitsUpTo, List.length_nil, scanFreqUpTo, Nat.zero_mul]
    exact (mass_zero 19).symm
  | succ n ih =>
    simp only [treeBitsUpTo, List.length_append, scanFreqUpTo]
    rw [ih (fun i lt => small i (by omega)), mass_mul_add]
    congr 1
    apply runBits_length
    intro cur prev cnt mn e
    rw [runStep_cur L n cur prev cnt mn e]
    exact small n (by omega)

end Zlib.Trees.Proofs.Out
