import ZlibF.Proof.«deflate.c.engine.overlay-tiny»
import ZlibF.Proof.«trees.c.build.dummy»
import ZlibF.Proof.«trees.c.overlay-scan-cost»
import ZlibF.Math.DeflateOverlayCertificate

/-!
# deflate.c: the overlay room at `memLevel` 2 from the certificate

At `lit_bufsize = 256`, every prepared dynamic block satisfies

  `71 + refHeaderCost ready + bitExcess ≤ 1852`,

where `refHeaderCost` is the cost of the bit-length symbols `scan_tree` counts for both trees, each
at the reference code `κ0` plus its extra bits (`ref_header_excess_256`). The facts are taken from
the actual run: the lengths and their bounds, Kraft and the forced leaves from `build_tree`, the
Fibonacci bound from the unclamped trees, the symbol counts from the ledger. They feed the
heap-free certificate (`DeflateOverlayCertificate.certificate`) and the per-entry scan bound
(`scan_cost_le`).

The header itself is compared with `refHeaderCost` by one open hypothesis, `HeaderRefBound Δ`:
the header is at most `71 + Δ + refHeaderCost` (Huffman optimality of the bit-length tree against
`κ0`, plus zlib's 7-bit repair). With `Δ ≤ 171` the order-free budget holds
(`overlay_budget_256`), and so the overlay room (`dynamic_overlay_256`).
-/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs (blPrepare BLInput curL same_record_of_runs dynamicHeaderBits sendLengths TK btFreq)
open Zlib.Trees.Proofs.Out (TreesInvAt dcodeN scanFreqUpTo refWeight scan_cost_le mass_mul_add)
open ZlibF.Math.DeflateSymbols
open ZlibF.Math.DeflatePush (symbolCost)
open ZlibF.Math.DeflateOverlaySmall (symbol_excess_le_mass literal_end_frequency literal_symbol_count
  match_balance SymbolFibPlus)
open ZlibF.Math.DeflateOverlayCertificate (entryCost kraftTerm lengthExtra distanceExtra certificate mass_split)
open Zlib.Trees.HuffmanAbstract (fib)
open ZlibF.Math.DeflateSelection (byteCost)
open Zlib.Deflate.Universal.Block (DynamicRoom DynamicOverlay treesInvAt_put)
set_option autoImplicit false

/-- The cost of the bit-length symbols `scan_tree` counts for both trees of `ready`, each at the
reference code `κ0` plus its extra bits. -/
def refHeaderCost (ready : DeflateState) : Nat :=
  mass (fun k => (scanFreqUpTo (sendLengths ready .lit) (ready.l_desc.max_code.toInt.toNat + 1) k +
    scanFreqUpTo (sendLengths ready .dist) (ready.d_desc.max_code.toInt.toNat + 1) k) * refWeight k) 19

set_option maxRecDepth 10000 in
/-- The extra-bit tables of the translation are the certificate's. -/
theorem extra_tables :
    (∀ c : Fin 29, sourceLiteralExtra c.val = lengthExtra c.val) ∧
    (∀ c : Fin 30, sourceDistanceExtra c.val = distanceExtra c.val) := by decide +kernel

theorem rs_eq_mass (f : Nat → Nat) (n : Nat) : Zlib.Trees.Proofs.GB.rs f n = mass f n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Zlib.Trees.Proofs.GB.rs_succ, ih]; rfl

theorem mass_le_of_le (f : Nat → Nat) {n m : Nat} (le : n ≤ m) : mass f n ≤ mass f m := by
  have := mass_split f n (m - n)
  rw [show n + (m - n) = m by omega] at this
  omega

/-- **The certificate on the actual block** at `lit_bufsize = 256`. -/
theorem ref_header_excess_256 {h : Heap} {ds pb : Nat} {d : DeflateState} {buf : Array UInt8}
    {xs : List Symbol} (trees : TreesInvAt h ds d pb buf) (ledger : SymbolLedger buf d xs)
    (size : d.lit_bufsize.toNat = 256) {mb : Int32} {ready : DeflateState}
    (run : (do blPrepare (some (.tab ds)); Zlib.Trees.build_bl_tree (some (.tab ds))) h =
      .ok (mb, setD h ds ready)) :
    71 + refHeaderCost ready + Zlib.Trees.Overlay.bitExcess (dynamicSymbolCosts ready xs) ≤ 1852 := by
  have capacity : xs.length + 1 ≤ 256 := by
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
  have eR : result = ready := same_record_of_runs complete run
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
  have cert := certificate ll fl dl fd
    (fun v hv => facts.literal v hv) (fun v hv => facts.distance v hv)
    (by
      rw [rs_eq_mass] at kraftL
      apply Nat.le_of_eq
      rw [← kraftL]
      apply mass_congr
      intro v _
      simp only [kraftTerm, ll, curL]
      by_cases z : (readyP.dyn_ltree[v]!).dl.toNat = 0 <;> simp [z])
    (by
      rw [rs_eq_mass] at kraftD
      apply Nat.le_of_eq
      rw [← kraftD]
      apply mass_congr
      intro v _
      simp only [kraftTerm, dl, curL]
      by_cases z : (readyP.dyn_dtree[v]!).dl.toNat = 0 <;> simp [z])
    (by
      intro v hv used
      refine ⟨usedL v hv ((nzL v hv).mpr used), ?_⟩
      have claim := symbolL v hv (by show (btFreq .lit d v).toNat ≠ 0; rw [freqL v hv]; exact used)
      dsimp only at claim
      rw [freqL v hv] at claim
      change fl v * fib (ll v + 1) + fib (ll v) ≤ WL at claim
      omega)
    (by
      intro v hv used
      refine ⟨usedD v hv ((nzD v hv).mpr used), ?_⟩
      have claim := symbolD v hv (by show (btFreq .dist d v).toNat ≠ 0; rw [freqD v hv]; exact used)
      dsimp only at claim
      rw [freqD v hv] at claim
      change fd v * fib (dl v + 1) + fib (dl v) ≤ WD at claim
      omega)
    (by
      intro v hv nonzero zero
      rcases dummyL v hv (dlNz _ nonzero) with used | small
      · exact absurd zero ((nzL v hv).mp used)
      · exact small)
    (by
      intro v hv nonzero zero
      rcases dummyD v hv (dlNz _ nonzero) with used | small
      · exact absurd zero ((nzD v hv).mp used)
      · exact small)
    (literal_end_frequency symbolLengthCode xs ledger.valid)
    (by
      rw [literal_symbol_count symbolLengthCode xs ledger.valid
        (fun s member => valid_literal_key (ledger.valid s member))]
      omega)
    (match_balance symbolLengthCode dcodeN xs ledger.valid
      (fun s member => valid_literal_key (ledger.valid s member))
      (fun s member k selected => valid_distance_key (ledger.valid s member) selected))
  -- the scan of both trees is within the entry costs
  have lowL : ∀ i, i ≤ readyP.l_desc.max_code.toInt.toNat → sendLengths result .lit i = ll i := by
    intro i hi
    simp only [sendLengths, TK.arr, ll, curL]
    rw [lTree i hi]
  have lowD : ∀ i, i ≤ readyP.d_desc.max_code.toInt.toNat → sendLengths result .dist i = dl i := by
    intro i hi
    simp only [sendLengths, TK.arr, dl, curL]
    rw [dTree i hi]
  have bound16 : ∀ (tk : TK) (n : Nat), sendLengths result tk n < 2 ^ 16 := by
    intro tk n
    exact UInt16.toNat_lt _
  have scanL := scan_cost_le (sendLengths result .lit) (bound16 .lit) (readyP.l_desc.max_code.toInt.toNat + 1)
    (fun i hi => by rw [lowL i (by omega)]; exact facts.literal i (by omega))
  have scanD := scan_cost_le (sendLengths result .dist) (bound16 .dist) (readyP.d_desc.max_code.toInt.toNat + 1)
    (fun i hi => by rw [lowD i (by omega)]; exact facts.distance i (by omega))
  have entriesL : mass (fun i => entryCost (sendLengths result .lit i)) (readyP.l_desc.max_code.toInt.toNat + 1) ≤
      mass (fun v => entryCost (ll v)) 286 := by
    rw [mass_congr (g := fun v => entryCost (ll v)) (fun i hi => by rw [lowL i (by omega)])]
    exact mass_le_of_le _ (by omega)
  have entriesD : mass (fun i => entryCost (sendLengths result .dist i)) (readyP.d_desc.max_code.toInt.toNat + 1) ≤
      mass (fun v => entryCost (dl v)) 30 := by
    rw [mass_congr (g := fun v => entryCost (dl v)) (fun i hi => by rw [lowD i (by omega)])]
    exact mass_le_of_le _ (by omega)
  have header : refHeaderCost result ≤ mass (fun v => entryCost (ll v)) 286 + mass (fun v => entryCost (dl v)) 30 := by
    unfold refHeaderCost
    rw [lDesc, dDesc, mass_mul_add]
    omega
  -- the excess at the actual lengths
  have agreeL : ∀ i ≤ readyP.l_desc.max_code.toInt.toNat, result.dyn_ltree[i]! = readyP.dyn_ltree[i]! := lTree
  have agreeD : ∀ i ≤ readyP.d_desc.max_code.toInt.toNat, result.dyn_dtree[i]! = readyP.dyn_dtree[i]! := dTree
  have costsSame := dynamicSymbolCosts_live_congr ledger facts agreeL agreeD
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
  omega

/-- **Batch 1's piece (open)**: the header of every prepared block at `lit_bufsize = 256` is at most
the reference-code header plus `Δ`. -/
def HeaderRefBound (Δ : Nat) : Prop :=
  ∀ {h : Heap} {ds : Nat} {d : DeflateState} {xs : List Symbol} {mb : Int32} {ready : DeflateState},
    TinyPrepared h ds d xs mb ready → d.lit_bufsize.toNat = 256 →
    (dynamicHeaderBits ready mb).length ≤ 71 + Δ + refHeaderCost ready

/-- **The order-free budget at `memLevel` 2**, from the header bound with `Δ ≤ 171`. -/
theorem overlay_budget_256 {Δ : Nat} (small : Δ ≤ 171) (headerBound : HeaderRefBound Δ)
    {h : Heap} {ds : Nat} {d : DeflateState} {xs : List Symbol} {mb : Int32} {ready : DeflateState}
    (prepared : TinyPrepared h ds d xs mb ready) (size : d.lit_bufsize.toNat = 256) :
    OverlayBudget ready mb xs := by
  obtain ⟨pb, buf, trees, ledger⟩ := prepared.base
  have bound := ref_header_excess_256 trees ledger size prepared.run
  have hdr := headerBound prepared size
  have litR : ready.lit_bufsize = d.lit_bufsize := by rw [prepared.frame]
  unfold OverlayBudget
  rw [litR, size]
  omega

/-- **The overlay room at `memLevel` 2**, from the header bound with `Δ ≤ 171`: the premises of
`TinyOverlay` with `lit_bufsize = 256`. -/
theorem dynamic_overlay_256 {Δ : Nat} (small : Δ ≤ 171) (headerBound : HeaderRefBound Δ)
    {h : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream} {d : DeflateState} {buf : Array UInt8}
    {xs : List Symbol} (_good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (ledger : SymbolLedger buf d xs) (clear : BlockInit.BlockClear d) (pending : d.pending = 0)
    (bits : d.bi_valid.toInt ≤ 7) (size : d.lit_bufsize.toNat = 256) (z' : ZStream) :
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
  exact dynamic_room_of_budget frame pending bits capacity (overlay_budget_256 small headerBound prepared size)

#print axioms ref_header_excess_256
#print axioms dynamic_overlay_256

end Zlib.Deflate.Engine.Proofs
