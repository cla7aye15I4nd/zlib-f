import ZlibF.Proof.«deflate.c.engine.overlay-mem1»

/-!
# deflate.c: the data-tree lengths of a small block are short

At `lit_bufsize = L ≤ 256` every nonzero code length of the prepared trees satisfies
`F(x + 2) ≤ L + 2`: a used code by the Fibonacci bound, a forced leaf because its tree then has two
leaves, both of length 1 (Kraft equality). So the lengths are at most 9 at `L = 128` and at most 11
at `L = 256`, and `scan_tree` never counts the bit-length symbols above them
(`scanFreq_absent`): at `L = 128` the bit-length symbols 10..15 are absent.
-/

namespace Zlib.Trees.Proofs.Out
open ZlibF.Math.DeflateSymbols (mass)

/-- `scan_tree` counts a length symbol only for a length it reads. -/
theorem scanFreq_absent (L : Nat → Nat) (n k : Nat) (low : k < 16) (above : ∀ i, i < n → L i ≠ k) :
    scanFreqUpTo L n k = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [scanFreqUpTo]
    rw [ih (fun i lt => above i (by omega))]
    have cur := runStep_cur L n
    generalize hr : (runStep L n (runAt L n)).2 = o at cur
    rcases o with _ | ⟨c, p, cnt, mn⟩
    · rfl
    · have e := cur c p cnt mn rfl
      have ne : k ≠ c := by rw [e]; exact fun h => above n (by omega) h.symm
      simp [runFreq, ne, show k ≠ 16 by omega, show k ≠ 17 by omega, show k ≠ 18 by omega]

end Zlib.Trees.Proofs.Out

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs (blPrepare BLInput curL same_record_of_runs dynamicHeaderBits sendLengths TK btFreq)
open Zlib.Trees.Proofs.Out (TreesInvAt dcodeN)
open ZlibF.Math.DeflateSymbols
open ZlibF.Math.DeflateOverlayCertificate (kraftTerm)
open ZlibF.Math.DeflateOverlayCertificate128 (isUsed)
open Zlib.Trees.HuffmanAbstract (fib)
set_option autoImplicit false

/-- A sum of terms each at most `c` on the used entries, over exactly two used entries, that
reaches `2c`, has every used term equal to `c`. -/
theorem mass_two_tight (f u : Nat → Nat) (n c : Nat) (each : ∀ v, v < n → f v ≤ c * u v)
    (unit : ∀ v, u v ≤ 1) (two : mass u n = 2) (full : mass f n = 2 * c) :
    ∀ v, v < n → u v = 1 → f v = c := by
  have split : mass (fun v => c * u v) n = mass (fun v => c * u v - f v) n + mass f n := by
    rw [← mass_add]
    apply mass_congr
    intro v hv
    have := each v hv
    omega
  rw [mass_mul_left, two, full] at split
  have zero : mass (fun v => c * u v - f v) n = 0 := by omega
  intro v hv used
  have le := mass_point_le (fun v => c * u v - f v) n v hv
  rw [zero] at le
  have e := each v hv
  simp only [used, Nat.mul_one] at e le
  omega
where
  mass_point_le (g : Nat → Nat) (n v : Nat) (hv : v < n) : g v ≤ mass g n := by
    induction n with
    | zero => omega
    | succ n ih =>
      show g v ≤ mass g n + g n
      by_cases e : v = n
      · subst e; omega
      · have := ih (by omega); omega

theorem fib_le_of_used (f x W : Nat) (pos : 1 ≤ f) (fit : f * fib (x + 1) + fib x ≤ W) : fib (x + 2) ≤ W := by
  have step : fib (x + 2) = fib x + fib (x + 1) := Zlib.Trees.HuffmanAbstract.fib_add_two x
  have : fib (x + 1) ≤ f * fib (x + 1) := Nat.le_mul_of_pos_left _ pos
  omega

/-- **The prepared lengths are short**: every nonzero length `x` read by `scan_tree` has
`F(x + 2) ≤ lit_bufsize + 2` or is 1. -/
theorem prepared_lengths_fib {h : Heap} {ds pb : Nat} {d : DeflateState} {buf : Array UInt8}
    {xs : List Symbol} (trees : TreesInvAt h ds d pb buf) (ledger : SymbolLedger buf d xs)
    (small : d.lit_bufsize.toNat ≤ 256) {mb : Int32} {ready : DeflateState}
    (run : (do blPrepare (some (.tab ds)); Zlib.Trees.build_bl_tree (some (.tab ds))) h =
      .ok (mb, setD h ds ready)) :
    (∀ v, v ≤ ready.l_desc.max_code.toInt.toNat → sendLengths ready .lit v ≠ 0 →
      fib (sendLengths ready .lit v + 2) ≤ d.lit_bufsize.toNat + 2 ∨ sendLengths ready .lit v = 1) ∧
    (∀ v, v ≤ ready.d_desc.max_code.toInt.toNat → sendLengths ready .dist v ≠ 0 →
      fib (sendLengths ready .dist v + 2) ≤ d.lit_bufsize.toNat + 2 ∨ sendLengths ready .dist v = 1) := by
  have capacity : xs.length + 1 ≤ d.lit_bufsize.toNat := by
    have bound := trees.run.sym_next_le
    rw [ledger.count, trees.base.sym_end] at bound
    have low := trees.base.lit_lo
    omega
  have literalMass := ledger_literal_mass ledger
  have distanceMass := ledger_distance_mass ledger
  have budgetL : mass (fun v => (btFreq .lit d v).toNat) 286 + 2 < 1597 := by
    change mass (fun k => (d.dyn_ltree[k]!).fc.toNat) 286 + 2 < 1597
    omega
  have budgetD : mass (fun v => (btFreq .dist d v).toNat) 30 + 2 < 1597 := by
    change mass (fun k => (d.dyn_dtree[k]!).fc.toNat) 30 + 2 < 1597
    omega
  obtain ⟨readyP, prepare, fibL, fibD⟩ := Zlib.Trees.Proofs.bl_prepare_fib_plus trees budgetL budgetD
  obtain ⟨other, otherRun, facts⟩ := Zlib.Trees.Proofs.bl_prepare_length_facts trees
  have e1 : readyP = other := same_record_of_runs prepare otherRun
  subst other
  obtain ⟨other, otherRun, dummyL, dummyD, kraftL, kraftD, usedL, usedD⟩ :=
    Zlib.Trees.Proofs.bl_prepare_leaf_facts trees
  have e2 : readyP = other := same_record_of_runs prepare otherRun
  subst other
  obtain ⟨other, otherRun, twoL, twoD⟩ := Zlib.Trees.Proofs.bl_prepare_two_leaves trees
  have e4 : readyP = other := same_record_of_runs prepare otherRun
  subst other
  obtain ⟨other, otherRun, input, treesR, _bl, _bits⟩ := Zlib.Trees.Proofs.bl_prepare trees
  have e3 : readyP = other := same_record_of_runs prepare otherRun
  subst other
  replace prepare : blPrepare (some (.tab ds)) h = .ok ((), setD h ds readyP) := prepare
  replace treesR : TreesInvAt (setD h ds readyP) ds readyP pb buf := treesR
  obtain ⟨mb', result, run', lDesc, dDesc, lTree, dTree, _treesA, _outputA⟩ :=
    Zlib.Trees.Proofs.build_bl_preserves_source_codes treesR input
  have complete : (do
        Zlib.Trees.Proofs.blPrepare (some (.tab ds))
        Zlib.Trees.build_bl_tree (some (.tab ds))) h = .ok (mb', setD h ds result) := by
    rw [bind_app, prepare]
    simp only [Zlib.Trees.Proofs.setD, setD, upd_upd] at run' ⊢
    exact run'
  have eR : ready = result := same_record_of_runs run complete
  subst eR
  have l286 := input.l286
  have d30 := input.d30
  obtain ⟨WL, weightL, symbolL⟩ := fibL.symbol_fib_plus
  obtain ⟨WD, weightD, symbolD⟩ := fibD.symbol_fib_plus
  change WL ≤ mass (fun v => (d.dyn_ltree[v]!).fc.toNat) 286 + 2 at weightL
  change WD ≤ mass (fun v => (d.dyn_dtree[v]!).fc.toNat) 30 + 2 at weightD
  -- one tree at a time: a used code by Fibonacci, a forced leaf by the two-leaf Kraft equality
  have tree : ∀ (T : Array CtData) (n W : Nat) (freq : Nat → UInt16),
      (∀ v, v < n → (freq v).toNat ≠ 0 →
        (freq v).toNat * fib (curL T v + 1) + fib (curL T v) ≤ W) →
      W ≤ d.lit_bufsize.toNat + 2 →
      (∀ v, v < n → curL T v ≤ 15) →
      Zlib.Trees.Proofs.GB.rs (fun v => if T[v]!.dl.toNat ≠ 0 then 2 ^ (15 - T[v]!.dl.toNat) else 0) n = 2 ^ 15 →
      ((∃ v, v < n ∧ T[v]!.dl.toNat ≠ 0 ∧ freq v = 0) →
        mass (fun v => if T[v]!.dl.toNat ≠ 0 then 1 else 0) n = 2) →
      ∀ v, v < n → curL T v ≠ 0 → fib (curL T v + 2) ≤ d.lit_bufsize.toNat + 2 ∨ curL T v = 1 := by
    intro T n W freq fibs weight len kraft two v hv nz
    by_cases used : freq v = 0
    · right
      have count := two ⟨v, hv, nz, used⟩
      rw [rs_eq_mass] at kraft
      have nz' : T[v]!.dl.toNat ≠ 0 := nz
      have tight := mass_two_tight (fun v => if T[v]!.dl.toNat ≠ 0 then 2 ^ (15 - T[v]!.dl.toNat) else 0)
        (fun v => if T[v]!.dl.toNat ≠ 0 then 1 else 0) n (2 ^ 14)
        (fun w hw => by
          by_cases z : T[w]!.dl.toNat ≠ 0
          · rw [if_pos z, if_pos z, Nat.mul_one]
            exact Nat.pow_le_pow_right (by omega) (by omega)
          · rw [if_neg z, if_neg z]; omega)
        (fun w => by split <;> omega) count (by rw [kraft]) v hv (by rw [if_pos nz'])
      rw [if_pos nz'] at tight
      have lv : T[v]!.dl.toNat ≤ 15 := len v hv
      show T[v]!.dl.toNat = 1
      generalize T[v]!.dl.toNat = x at nz' lv tight ⊢
      rcases x with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | x <;>
        simp at tight nz' lv ⊢
    · left
      have fit := fibs v hv (by intro z; apply used; exact UInt16.toNat_inj.mp (by rw [z]; rfl))
      have := fib_le_of_used _ _ _ (by
        have : (freq v).toNat ≠ 0 := by intro z; apply used; exact UInt16.toNat_inj.mp (by rw [z]; rfl)
        omega) fit
      omega
  have treeL := tree readyP.dyn_ltree 286 WL (btFreq .lit d) (fun v hv nz => by
      have claim := symbolL v hv nz
      dsimp only at claim
      exact claim)
    (by omega) (fun v hv => facts.literal v hv) kraftL (fun ⟨v, hv, nz, z⟩ => twoL ⟨v, hv, nz, z⟩)
  have treeD := tree readyP.dyn_dtree 30 WD (btFreq .dist d) (fun v hv nz => by
      have claim := symbolD v hv nz
      dsimp only at claim
      exact claim)
    (by omega) (fun v hv => facts.distance v hv) kraftD (fun ⟨v, hv, nz, z⟩ => twoD ⟨v, hv, nz, z⟩)
  refine ⟨?_, ?_⟩
  · intro v hv nz
    rw [lDesc] at hv
    have same : sendLengths ready .lit v = curL readyP.dyn_ltree v := by
      simp only [sendLengths, TK.arr, curL]; rw [lTree v hv]
    rw [same] at nz ⊢
    exact treeL v (by omega) nz
  · intro v hv nz
    rw [dDesc] at hv
    have same : sendLengths ready .dist v = curL readyP.dyn_dtree v := by
      simp only [sendLengths, TK.arr, curL]; rw [dTree v hv]
    rw [same] at nz ⊢
    exact treeD v (by omega) nz

/-- **At `lit_bufsize = 128` every length `scan_tree` reads is at most 9.** -/
theorem prepared_lengths_128 {h : Heap} {ds pb : Nat} {d : DeflateState} {buf : Array UInt8}
    {xs : List Symbol} (trees : TreesInvAt h ds d pb buf) (ledger : SymbolLedger buf d xs)
    (size : d.lit_bufsize.toNat = 128) {mb : Int32} {ready : DeflateState}
    (run : (do blPrepare (some (.tab ds)); Zlib.Trees.build_bl_tree (some (.tab ds))) h =
      .ok (mb, setD h ds ready)) :
    (∀ v, v ≤ ready.l_desc.max_code.toInt.toNat → sendLengths ready .lit v ≤ 9) ∧
    (∀ v, v ≤ ready.d_desc.max_code.toInt.toNat → sendLengths ready .dist v ≤ 9) := by
  obtain ⟨lit, dist⟩ := prepared_lengths_fib trees ledger (by omega) run
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, _⟩ :=
    ZlibF.Math.DeflateOverlaySmall.fib_values
  have bound : ∀ x, x ≠ 0 → fib (x + 2) ≤ 130 ∨ x = 1 → x ≤ 9 := by
    intro x nz h
    rcases h with h | h
    · rcases Nat.lt_or_ge x (12 - 2) with lt | ge
      · omega
      · have mono : fib 12 ≤ fib (x + 2) := Zlib.Trees.HuffmanAbstract.fib_mono (by omega)
        omega
    · omega
  refine ⟨fun v hv => ?_, fun v hv => ?_⟩
  · by_cases z : sendLengths ready .lit v = 0
    · omega
    · exact bound _ z (by rw [size] at lit; exact lit v hv z)
  · by_cases z : sendLengths ready .dist v = 0
    · omega
    · exact bound _ z (by rw [size] at dist; exact dist v hv z)

/-- **At `lit_bufsize = 256` every length `scan_tree` reads is at most 11.** -/
theorem prepared_lengths_256 {h : Heap} {ds pb : Nat} {d : DeflateState} {buf : Array UInt8}
    {xs : List Symbol} (trees : TreesInvAt h ds d pb buf) (ledger : SymbolLedger buf d xs)
    (size : d.lit_bufsize.toNat = 256) {mb : Int32} {ready : DeflateState}
    (run : (do blPrepare (some (.tab ds)); Zlib.Trees.build_bl_tree (some (.tab ds))) h =
      .ok (mb, setD h ds ready)) :
    (∀ v, v ≤ ready.l_desc.max_code.toInt.toNat → sendLengths ready .lit v ≤ 11) ∧
    (∀ v, v ≤ ready.d_desc.max_code.toInt.toNat → sendLengths ready .dist v ≤ 11) := by
  obtain ⟨lit, dist⟩ := prepared_lengths_fib trees ledger (by omega) run
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, _⟩ :=
    ZlibF.Math.DeflateOverlaySmall.fib_values
  have bound : ∀ x, x ≠ 0 → fib (x + 2) ≤ 258 ∨ x = 1 → x ≤ 11 := by
    intro x nz h
    rcases h with h | h
    · rcases Nat.lt_or_ge x (14 - 2) with lt | ge
      · omega
      · have mono : fib 14 ≤ fib (x + 2) := Zlib.Trees.HuffmanAbstract.fib_mono (by omega)
        omega
    · omega
  refine ⟨fun v hv => ?_, fun v hv => ?_⟩
  · by_cases z : sendLengths ready .lit v = 0
    · omega
    · exact bound _ z (by rw [size] at lit; exact lit v hv z)
  · by_cases z : sendLengths ready .dist v = 0
    · omega
    · exact bound _ z (by rw [size] at dist; exact dist v hv z)

#print axioms prepared_lengths_128
#print axioms prepared_lengths_256

end Zlib.Deflate.Engine.Proofs
