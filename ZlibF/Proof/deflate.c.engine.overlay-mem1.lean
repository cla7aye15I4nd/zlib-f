import ZlibF.Proof.«deflate.c.engine.overlay-mem2»
import ZlibF.Proof.«deflate.c.engine.overlay-choice-row»
import ZlibF.Proof.«trees.c.overlay-scan-region»
import ZlibF.Proof.«trees.c.build.two-leaves»
import ZlibF.Math.DeflateOverlayCertificate128

/-!
# deflate.c: the overlay room at `memLevel` 1 from the certificate

At `lit_bufsize = 128`, every prepared dynamic block satisfies `H + bitExcess ≤ 999`
(`header_excess_128`), from the header hypothesis `HeaderRefBound128 Δ` with `Δ ≤ 132`: the header
is at most `71 + Δ + refHeaderCost128`, the cost of the scanned bit-length symbols under the
reference code `κ1`. The facts of the run feed the heap-free certificate
(`DeflateOverlayCertificate128`): the region scan (`scan_cost_region`, charges by region), the
choice row (`choice_row`), Kraft and the forced leaves, which are split into three cases (none;
only in the distance tree, which then has two nonzero lengths; in the literal/length tree, which
then has two). The order-free budget follows (`overlay_budget_128`), and so the overlay room
(`dynamic_overlay_128`).
-/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs (blPrepare BLInput curL same_record_of_runs dynamicHeaderBits sendLengths TK btFreq
  fixedLiteralWords)
open Zlib.Trees.Proofs.Out (TreesInvAt dcodeN scanFreqUpTo mass_mul_add ScanCharges regionCharge scan_cost_region)
open ZlibF.Math.DeflateSymbols
open ZlibF.Math.DeflatePush (symbolCost)
open ZlibF.Math.DeflateOverlaySmall (symbol_excess_le_mass literal_end_frequency literal_symbol_count
  match_balance SymbolFibPlus)
open ZlibF.Math.DeflateOverlayCertificate (kraftTerm lengthExtra distanceExtra mass_split)
open ZlibF.Math.DeflateOverlayCertificate128 (refLen1 literalRegionCharge otherRegionCharge literalCharge staticLen
  isUsed certificate_none certificate_dist certificate_lit)
open Zlib.Trees.HuffmanAbstract (fib)
open ZlibF.Math.DeflateSelection (byteCost)
open Zlib.Deflate.Universal.Block (DynamicRoom DynamicOverlay treesInvAt_put)
set_option autoImplicit false

/-- The cost of bit-length symbol `k` under `κ1`, extra bits included. -/
def refWeight1 (k : Nat) : Nat := refLen1 k + Zlib.Trees.Proofs.Out.blExtraBits k

/-- The cost of the bit-length symbols `scan_tree` counts for both trees of `ready`, under `κ1`. -/
def refHeaderCost128 (ready : DeflateState) : Nat :=
  mass (fun k => (scanFreqUpTo (sendLengths ready .lit) (ready.l_desc.max_code.toInt.toNat + 1) k +
    scanFreqUpTo (sendLengths ready .dist) (ready.d_desc.max_code.toInt.toNat + 1) k) * refWeight1 k) 19

/-- **Batch 1's piece at `lit_bufsize = 128` (open)**: the header is at most the `κ1` header plus `Δ`. -/
def HeaderRefBound128 (Δ : Nat) : Prop :=
  ∀ {h : Heap} {ds : Nat} {d : DeflateState} {xs : List Symbol} {mb : Int32} {ready : DeflateState},
    TinyPrepared h ds d xs mb ready → d.lit_bufsize.toNat = 128 →
    (dynamicHeaderBits ready mb).length ≤ 71 + Δ + refHeaderCost128 ready

/-- The region of an entry of the literal/length tree: credit 9 and 1 per zero in the literal
region (0..256), 4 per zero in the length region; the distance tree is one region like the length
region. -/
def literalA (i : Nat) : Nat := if i ≤ 256 then 9 else 0
def literalB (i : Nat) : Nat := if i ≤ 256 then 1 else 4

theorem charges_128 :
    ScanCharges (fun k => 2 * refWeight1 k) otherRegionCharge literalA literalB ∧
    ScanCharges (fun k => 2 * refWeight1 k) otherRegionCharge (fun _ => 0) (fun _ => 4) := by
  have short : ∀ x, 1 ≤ x → x ≤ 15 → 2 * refWeight1 x ≤ otherRegionCharge x := by
    intro x h1 h2
    rcases x with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | x <;>
      simp [refWeight1, refLen1, otherRegionCharge, Zlib.Trees.Proofs.Out.blExtraBits] at h1 h2 ⊢
  have rep : ∀ x, 1 ≤ x → x ≤ 15 → 2 * refWeight1 16 ≤ 3 * otherRegionCharge x := by
    intro x h1 h2
    rcases x with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | x <;>
      simp [refWeight1, refLen1, otherRegionCharge, Zlib.Trees.Proofs.Out.blExtraBits] at h1 h2 ⊢
  have w0 : 2 * refWeight1 0 = 4 := by decide
  have w17 : 2 * refWeight1 17 = 12 := by decide
  have w18 : 2 * refWeight1 18 = 20 := by decide
  refine ⟨⟨short, rep, ?_, ?_, ?_, ?_, ?_⟩, ⟨short, rep, ?_, ?_, ?_, ?_, ?_⟩⟩ <;> intro i <;>
    simp only [literalA, literalB, w0, w17, w18] <;> (try split) <;> omega

/-- The region charge of the literal/length scan is the certificate's literal charge. -/
theorem literal_regionCharge (L : Nat → Nat) (i : Nat) (small : L i ≤ 15) :
    regionCharge L otherRegionCharge literalA literalB i = literalCharge i (L i) := by
  unfold regionCharge literalCharge literalA literalB
  generalize L i = x at small ⊢
  by_cases r : i ≤ 256 <;>
  rcases x with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | x <;>
    simp [r, literalRegionCharge, otherRegionCharge] at small ⊢

theorem distance_regionCharge (L : Nat → Nat) (i : Nat) (small : L i ≤ 15) :
    regionCharge L otherRegionCharge (fun _ => 0) (fun _ => 4) i = otherRegionCharge (L i) := by
  unfold regionCharge
  generalize L i = x at small ⊢
  rcases x with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | x <;>
    simp [otherRegionCharge] at small ⊢

set_option maxRecDepth 10000 in
theorem fixed_static_len : ∀ v : Fin 286, (fixedLiteralWords v.val).2.toNat = staticLen v.val := by
  decide +kernel

theorem isUsed_mass (T : Array CtData) (n : Nat) :
    mass (fun v => isUsed (curL T v)) n = mass (fun v => if (T[v]!).dl.toNat ≠ 0 then 1 else 0) n := by
  apply mass_congr
  intro v _
  simp only [isUsed, curL]
  by_cases z : (T[v]!).dl.toNat = 0 <;> simp [z]

/-- **The certificate on the actual block** at `lit_bufsize = 128`. -/
theorem header_excess_128 {Δ : Nat} (small : Δ ≤ 132) (headerBound : HeaderRefBound128 Δ)
    {h : Heap} {ds : Nat} {d : DeflateState} {xs : List Symbol} {mb : Int32} {ready : DeflateState}
    (prepared : TinyPrepared h ds d xs mb ready) (size : d.lit_bufsize.toNat = 128) :
    (dynamicHeaderBits ready mb).length + Zlib.Trees.Overlay.bitExcess (dynamicSymbolCosts ready xs) ≤ 999 := by
  obtain ⟨pb, buf, trees, ledger⟩ := prepared.base
  have run := prepared.run
  have hdrBound := headerBound prepared size
  have choice := choice_row trees ledger prepared.clear run prepared.header prepared.excess prepared.dynamic
  have capacity : xs.length + 1 ≤ 128 := by
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
  -- the state after both data trees, and its facts
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
  -- the Fibonacci bound with the actual frequencies
  obtain ⟨WL, weightL, symbolL⟩ := fibL.symbol_fib_plus
  obtain ⟨WD, weightD, symbolD⟩ := fibD.symbol_fib_plus
  change WL ≤ mass (fun v => (d.dyn_ltree[v]!).fc.toNat) 286 + 2 at weightL
  change WD ≤ mass (fun v => (d.dyn_dtree[v]!).fc.toNat) 30 + 2 at weightD
  -- the certificate's lengths and frequencies
  let ll : Nat → Nat := fun v => curL readyP.dyn_ltree v
  let dl : Nat → Nat := fun v => curL readyP.dyn_dtree v
  let fl : Nat → Nat := literalFrequency symbolLengthCode xs
  let fd : Nat → Nat := distanceFrequency dcodeN xs
  have freqL : ∀ v, v < 286 → (btFreq .lit d v).toNat = fl v := fun v hv => ledger.literal v hv
  have freqD : ∀ v, v < 30 → (btFreq .dist d v).toNat = fd v := fun v hv => ledger.distance v hv
  have nzL : ∀ v, v < 286 → (btFreq .lit d v ≠ 0 ↔ fl v ≠ 0) := by
    intro v hv
    rw [← freqL v hv]
    constructor
    · intro ne z; apply ne; exact UInt16.toNat_inj.mp (by rw [z]; rfl)
    · intro ne z; apply ne; rw [z]; rfl
  have nzD : ∀ v, v < 30 → (btFreq .dist d v ≠ 0 ↔ fd v ≠ 0) := by
    intro v hv
    rw [← freqD v hv]
    constructor
    · intro ne z; apply ne; exact UInt16.toNat_inj.mp (by rw [z]; rfl)
    · intro ne z; apply ne; rw [z]; rfl
  have dlNz : ∀ (c : CtData), c.dl.toNat ≠ 0 → c.dl ≠ 0 := by
    intro c ne z; apply ne; rw [z]; rfl
  -- the end of block is used, so the literal region ends inside the scanned range
  have eobF := literal_end_frequency symbolLengthCode xs ledger.valid
  have eobUsed : btFreq .lit d 256 ≠ 0 :=
    (nzL 256 (by omega)).mpr (by show literalFrequency symbolLengthCode xs 256 ≠ 0; rw [eobF]; omega)
  have eobLen : 1 ≤ ll 256 := usedL 256 (by omega) eobUsed
  have maxL256 : 256 ≤ readyP.l_desc.max_code.toInt.toNat := facts.literal_used 256 (by omega) eobUsed
  -- the scan of both trees, by region
  have lowL : ∀ i, i ≤ readyP.l_desc.max_code.toInt.toNat → sendLengths ready .lit i = ll i := by
    intro i hi
    simp only [sendLengths, TK.arr, ll, curL]
    rw [lTree i hi]
  have lowD : ∀ i, i ≤ readyP.d_desc.max_code.toInt.toNat → sendLengths ready .dist i = dl i := by
    intro i hi
    simp only [sendLengths, TK.arr, dl, curL]
    rw [dTree i hi]
  have bound16 : ∀ (tk : TK) (n : Nat), sendLengths ready tk n < 2 ^ 16 := by
    intro tk n
    exact UInt16.toNat_lt _
  have keepL : ∀ i, sendLengths ready .lit i = 0 → literalA (i + 1) = literalA i ∧ literalB (i + 1) = literalB i := by
    intro i z
    by_cases e : i = 256
    · subst e
      rw [lowL 256 maxL256] at z
      omega
    · simp only [literalA, literalB]
      by_cases r : i ≤ 255
      · simp [show i + 1 ≤ 256 by omega, show i ≤ 256 by omega]
      · simp [show ¬ (i + 1 ≤ 256) by omega, show ¬ (i ≤ 256) by omega]
  have scanL := scan_cost_region (sendLengths ready .lit) _ _ _ _ charges_128.1 (bound16 .lit) keepL
    (readyP.l_desc.max_code.toInt.toNat + 1)
    (fun i hi => by rw [lowL i (by omega)]; exact facts.literal i (by omega))
  have scanD := scan_cost_region (sendLengths ready .dist) _ _ _ _ charges_128.2 (bound16 .dist)
    (fun _ _ => ⟨rfl, rfl⟩) (readyP.d_desc.max_code.toInt.toNat + 1)
    (fun i hi => by rw [lowD i (by omega)]; exact facts.distance i (by omega))
  have endA : literalA (readyP.l_desc.max_code.toInt.toNat + 1) = 0 := by
    unfold literalA; rw [if_neg (by omega)]
  rw [endA] at scanL
  have chargesL : mass (regionCharge (sendLengths ready .lit) otherRegionCharge literalA literalB)
      (readyP.l_desc.max_code.toInt.toNat + 1) ≤ mass (fun v => literalCharge v (ll v)) 286 := by
    rw [mass_congr (g := fun v => literalCharge v (ll v)) (fun i hi => by
      rw [literal_regionCharge _ i (by rw [lowL i (by omega)]; exact facts.literal i (by omega)), lowL i (by omega)])]
    exact mass_le_of_le _ (by omega)
  have chargesD : mass (regionCharge (sendLengths ready .dist) otherRegionCharge (fun _ => 0) (fun _ => 4))
      (readyP.d_desc.max_code.toInt.toNat + 1) ≤ mass (fun v => otherRegionCharge (dl v)) 30 := by
    rw [mass_congr (g := fun v => otherRegionCharge (dl v)) (fun i hi => by
      rw [distance_regionCharge _ i (by rw [lowD i (by omega)]; exact facts.distance i (by omega)), lowD i (by omega)])]
    exact mass_le_of_le _ (by omega)
  have twice : 2 * refHeaderCost128 ready ≤ mass (fun v => literalCharge v (ll v)) 286 +
      mass (fun v => otherRegionCharge (dl v)) 30 := by
    unfold refHeaderCost128
    rw [lDesc, dDesc, mass_mul_add, Nat.mul_add, ← mass_mul_left, ← mass_mul_left]
    have eL : mass (fun k => 2 * (scanFreqUpTo (sendLengths ready .lit) (readyP.l_desc.max_code.toInt.toNat + 1) k *
        refWeight1 k)) 19 = mass (fun k => scanFreqUpTo (sendLengths ready .lit)
        (readyP.l_desc.max_code.toInt.toNat + 1) k * (2 * refWeight1 k)) 19 := by
      apply mass_congr; intro k _; rw [Nat.mul_left_comm]
    have eD : mass (fun k => 2 * (scanFreqUpTo (sendLengths ready .dist) (readyP.d_desc.max_code.toInt.toNat + 1) k *
        refWeight1 k)) 19 = mass (fun k => scanFreqUpTo (sendLengths ready .dist)
        (readyP.d_desc.max_code.toInt.toNat + 1) k * (2 * refWeight1 k)) 19 := by
      apply mass_congr; intro k _; rw [Nat.mul_left_comm]
    rw [eL, eD]
    omega
  -- the choice row with the certificate's lengths
  have usedLow : ∀ v, v < 286 → fl v ≠ 0 → v ≤ readyP.l_desc.max_code.toInt.toNat := by
    intro v hv used
    exact facts.literal_used v hv ((nzL v hv).mpr used)
  have usedLowD : ∀ v, v < 30 → fd v ≠ 0 → v ≤ readyP.d_desc.max_code.toInt.toNat := by
    intro v hv used
    exact facts.distance_used v hv ((nzD v hv).mpr used)
  have chL : mass (fun v => literalFrequency symbolLengthCode xs v * curL ready.dyn_ltree v) 286 =
      mass (fun v => fl v * ll v) 286 := by
    apply mass_congr
    intro v hv
    by_cases z : fl v = 0
    · show fl v * _ = fl v * _
      rw [z, Nat.zero_mul, Nat.zero_mul]
    · show fl v * curL ready.dyn_ltree v = fl v * curL readyP.dyn_ltree v
      unfold curL
      rw [lTree v (usedLow v hv z)]
  have chD : mass (fun v => distanceFrequency dcodeN xs v * curL ready.dyn_dtree v) 30 =
      mass (fun v => fd v * dl v) 30 := by
    apply mass_congr
    intro v hv
    by_cases z : fd v = 0
    · show fd v * _ = fd v * _
      rw [z, Nat.zero_mul, Nat.zero_mul]
    · show fd v * curL ready.dyn_dtree v = fd v * curL readyP.dyn_dtree v
      unfold curL
      rw [dTree v (usedLowD v hv z)]
  have chS : mass (fun v => literalFrequency symbolLengthCode xs v * (fixedLiteralWords v).2.toNat) 286 =
      mass (fun v => fl v * staticLen v) 286 := by
    apply mass_congr
    intro v hv
    rw [fixed_static_len ⟨v, hv⟩]
  rw [chL, chD, chS] at choice
  -- the excess at the actual lengths
  have costsSame := dynamicSymbolCosts_live_congr ledger facts lTree dTree
  have excess := symbol_excess_le_mass xs (curL readyP.dyn_ltree) (curL readyP.dyn_dtree)
    sourceLiteralExtra sourceDistanceExtra symbolLengthCode dcodeN ledger.valid
    (fun s member => valid_literal_key (ledger.valid s member))
    (fun s member k selected => valid_distance_key (ledger.valid s member) selected)
    (fun v hv _ => facts.literal v hv)
  have tables := extra_tables
  have exL : mass (fun v => literalFrequency symbolLengthCode xs v *
      ZlibF.Math.DeflatePush.literalExcess (curL readyP.dyn_ltree) sourceLiteralExtra v) 286 =
      mass (fun v => fl v * ZlibF.Math.DeflateOverlayCertificate.literalExcess v (ll v)) 286 := by
    apply mass_congr
    intro v hv
    simp only [ZlibF.Math.DeflatePush.literalExcess, ZlibF.Math.DeflateOverlayCertificate.literalExcess, fl, ll]
    by_cases low : v < 257
    · simp [low]
    · simp only [low, if_false]
      rw [tables.1 ⟨v - 257, by omega⟩]
  have exD : mass (fun v => distanceFrequency dcodeN xs v *
      ZlibF.Math.DeflatePush.distanceExcess (curL readyP.dyn_dtree) sourceDistanceExtra v) 30 =
      mass (fun v => fd v * ZlibF.Math.DeflateOverlayCertificate.distanceExcess v (dl v)) 30 := by
    apply mass_congr
    intro v hv
    simp only [ZlibF.Math.DeflatePush.distanceExcess, ZlibF.Math.DeflateOverlayCertificate.distanceExcess, fd, dl]
    rw [tables.2 ⟨v, hv⟩]
  have costs : dynamicSymbolCosts readyP xs = xs.map (symbolCost (curL readyP.dyn_ltree) (curL readyP.dyn_dtree)
      sourceLiteralExtra sourceDistanceExtra symbolLengthCode dcodeN) := rfl
  rw [costsSame, costs]
  rw [exL, exD] at excess
  -- the common facts of the three certificates
  have lenL : ∀ v, v < 286 → ll v ≤ 15 := fun v hv => facts.literal v hv
  have lenD : ∀ v, v < 30 → dl v ≤ 15 := fun v hv => facts.distance v hv
  have kL : mass (fun v => kraftTerm (ll v)) 286 ≤ 2 ^ 15 := by
    rw [rs_eq_mass] at kraftL
    apply Nat.le_of_eq
    rw [← kraftL]
    apply mass_congr
    intro v _
    simp only [kraftTerm, ll, curL]
    by_cases z : (readyP.dyn_ltree[v]!).dl.toNat = 0 <;> simp [z]
  have kD : mass (fun v => kraftTerm (dl v)) 30 ≤ 2 ^ 15 := by
    rw [rs_eq_mass] at kraftD
    apply Nat.le_of_eq
    rw [← kraftD]
    apply mass_congr
    intro v _
    simp only [kraftTerm, dl, curL]
    by_cases z : (readyP.dyn_dtree[v]!).dl.toNat = 0 <;> simp [z]
  have fibL : ∀ v, v < 286 → fl v ≠ 0 → 1 ≤ ll v ∧ fl v * fib (ll v + 1) + fib (ll v) ≤ 130 := by
    intro v hv used
    refine ⟨usedL v hv ((nzL v hv).mpr used), ?_⟩
    have claim := symbolL v hv (by show (btFreq .lit d v).toNat ≠ 0; rw [freqL v hv]; exact used)
    dsimp only at claim
    rw [freqL v hv] at claim
    change fl v * fib (ll v + 1) + fib (ll v) ≤ WL at claim
    omega
  have fibD : ∀ v, v < 30 → fd v ≠ 0 → 1 ≤ dl v ∧ fd v * fib (dl v + 1) + fib (dl v) ≤ 130 := by
    intro v hv used
    refine ⟨usedD v hv ((nzD v hv).mpr used), ?_⟩
    have claim := symbolD v hv (by show (btFreq .dist d v).toNat ≠ 0; rw [freqD v hv]; exact used)
    dsimp only at claim
    rw [freqD v hv] at claim
    change fd v * fib (dl v + 1) + fib (dl v) ≤ WD at claim
    omega
  have symbols : mass (fun v => if v = 256 then 0 else fl v) 286 ≤ 127 := by
    rw [literal_symbol_count symbolLengthCode xs ledger.valid
      (fun s member => valid_literal_key (ledger.valid s member))]
    omega
  have balance := match_balance symbolLengthCode dcodeN xs ledger.valid
    (fun s member => valid_literal_key (ledger.valid s member))
    (fun s member k selected => valid_distance_key (ledger.valid s member) selected)
  have small2L : ∀ v, v < 286 → ll v ≠ 0 → fl v = 0 → v ≤ 2 := by
    intro v hv nonzero zero
    rcases dummyL v hv (dlNz _ nonzero) with used | small
    · exact absurd zero ((nzL v hv).mp used)
    · exact small
  have small2D : ∀ v, v < 30 → dl v ≠ 0 → fd v = 0 → v ≤ 2 := by
    intro v hv nonzero zero
    rcases dummyD v hv (dlNz _ nonzero) with used | small
    · exact absurd zero ((nzD v hv).mp used)
    · exact small
  have hdr : 2 * (dynamicHeaderBits ready mb).length ≤ 2 * (71 + Δ) +
      mass (fun v => literalCharge v (ll v)) 286 + mass (fun v => otherRegionCharge (dl v)) 30 := by omega
  have zeroIff : ∀ (f : Nat → Nat) (v : Nat), (f v = 0 ↔ ¬ (f v ≠ 0)) := fun f v => by omega
  -- the three cases
  by_cases forcedL : ∃ v, v < 286 ∧ ll v ≠ 0 ∧ fl v = 0
  · obtain ⟨v, hv, nz, zero⟩ := forcedL
    have two := twoL ⟨v, hv, nz, by
      have := freqL v hv; rw [zero] at this; exact UInt16.toNat_inj.mp (by rw [this]; rfl)⟩
    rw [← isUsed_mass] at two
    have cert := certificate_lit ll fl dl fd _ Δ (by omega) lenL lenD kL kD fibL fibD small2L small2D
      (Nat.le_of_eq two) eobF symbols balance hdr choice
    omega
  · have noneL : ∀ v, v < 286 → ll v ≠ 0 → fl v = 0 → False := fun v hv nz z => forcedL ⟨v, hv, nz, z⟩
    by_cases forcedD : ∃ v, v < 30 ∧ dl v ≠ 0 ∧ fd v = 0
    · obtain ⟨v, hv, nz, zero⟩ := forcedD
      have two := twoD ⟨v, hv, nz, by
        have := freqD v hv; rw [zero] at this; exact UInt16.toNat_inj.mp (by rw [this]; rfl)⟩
      rw [← isUsed_mass] at two
      have cert := certificate_dist ll fl dl fd _ Δ (by omega) lenL lenD kL kD fibL fibD noneL small2D
        (Nat.le_of_eq two) eobF symbols balance hdr choice
      omega
    · have noneD : ∀ v, v < 30 → dl v ≠ 0 → fd v = 0 → False := fun v hv nz z => forcedD ⟨v, hv, nz, z⟩
      have cert := certificate_none ll fl dl fd _ Δ small lenL lenD kL kD fibL fibD noneL noneD
        eobF symbols balance hdr choice
      omega

/-- **The order-free budget at `memLevel` 1**, from the header bound with `Δ ≤ 132`. -/
theorem overlay_budget_128 {Δ : Nat} (small : Δ ≤ 132) (headerBound : HeaderRefBound128 Δ)
    {h : Heap} {ds : Nat} {d : DeflateState} {xs : List Symbol} {mb : Int32} {ready : DeflateState}
    (prepared : TinyPrepared h ds d xs mb ready) (size : d.lit_bufsize.toNat = 128) :
    OverlayBudget ready mb xs := by
  have bound := header_excess_128 small headerBound prepared size
  have litR : ready.lit_bufsize = d.lit_bufsize := by rw [prepared.frame]
  unfold OverlayBudget
  rw [litR, size]
  omega

/-- **The overlay room at `memLevel` 1**, from the header bound with `Δ ≤ 132`: the premises of
`TinyOverlay` with `lit_bufsize = 128`. -/
theorem dynamic_overlay_128 {Δ : Nat} (small : Δ ≤ 132) (headerBound : HeaderRefBound128 Δ)
    {h : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream} {d : DeflateState} {buf : Array UInt8}
    {xs : List Symbol} (_good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (ledger : SymbolLedger buf d xs) (clear : BlockInit.BlockClear d) (pending : d.pending = 0)
    (bits : d.bi_valid.toInt ≤ 7) (size : d.lit_bufsize.toNat = 128) (z' : ZStream) :
    DynamicOverlay (r.put h z') ds d xs := by
  intro mb ready run frame header excess dynamic
  have treesP := treesInvAt_put (r := r) (z' := z') trees
  have capacity : xs.length + 1 ≤ d.lit_bufsize.toNat := by
    have bound := trees.run.sym_next_le
    rw [ledger.count, trees.base.sym_end] at bound
    have low := trees.base.lit_lo
    omega
  have prepared : TinyPrepared (r.put h z') ds d xs mb ready :=
    ⟨⟨pb, buf, treesP, ledger⟩, clear, by omega, run, frame, header, excess, dynamic⟩
  exact dynamic_room_of_budget frame pending bits capacity (overlay_budget_128 small headerBound prepared size)

#print axioms header_excess_128
#print axioms dynamic_overlay_128

end Zlib.Deflate.Engine.Proofs
