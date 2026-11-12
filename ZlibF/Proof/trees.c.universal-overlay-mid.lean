import ZlibF.Proof.«trees.c.universal-overlay-fibplus»
import ZlibF.Proof.«trees.c.universal-flushsafe»
import ZlibF.Proof.«trees.c.universal-spec»

/-!
# trees.c: the dynamic overlay room for `lit_bufsize` 512 and 1024

Batch C of the deflate skeleton. `SmallOverlay` (`trees.c.universal-flushsafe`) asks for the
overlay room of a dynamic block when `lit_bufsize < 2048`. This file proves it for
`lit_bufsize` 512 and 1024 (`memLevel` 3 and 4), and reduces `SmallOverlay` to the
`lit_bufsize < 512` case (`memLevel` 1 and 2), which stays open.

The argument: a block holds at most `lit_bufsize - 1` symbols, so both source trees weigh at
most `lit_bufsize + 2 ≤ 1026 < 1597`. Then `gen_bitlen` never clamps
(`trees.c.universal-overlay-fibplus`), every used symbol keeps `f * F(l + 1) + F(l) ≤ W`, and
the per-code caps of `DeflateOverlaySmall` bound the block excess by 1777 bits (weight at most
514) or 3678 bits (weight at most 1026). With the proved header bound of 2283 bits the order-free
budget `header + excess + 25 ≤ 8 * lit_bufsize` holds: `2283 + 1777 + 25 = 4085 ≤ 4096` and
`2283 + 3678 + 25 = 5986 ≤ 8192`.

Only `TreesInvAt` and the symbol ledger are used, not `DGood`, because the overlay room is
asked for on the heap `r.put h z'` for every stream record `z'`.
-/

namespace Zlib.Trees.Proofs
open C Zlib.Trees
open ZlibF.Math.DeflateSymbols (mass)
set_option autoImplicit false

/-- Literal and distance construction (`blPrepare`) of trees whose leaf mass plus two stays
below 1597: both trees keep the unclamped Fibonacci bound on their original used symbols. -/
theorem bl_prepare_fib_plus {h : Heap} {id b : Nat} {d : DeflateState} {buf : Array UInt8}
    (hI : Out.TreesInvAt h id d b buf)
    (budgetL : mass (fun v => (btFreq .lit d v).toNat) 286 + 2 < 1597)
    (budgetD : mass (fun v => (btFreq .dist d v).toNat) 30 + 2 < 1597) :
    ∃ e : DeflateState, blPrepare (Sp id) h = .ok ((), setD h id e) ∧
      BTFibPlusOrigins .lit 286 d e ∧ BTFibPlusOrigins .dist 30 d e := by
  obtain ⟨aL, lit, hrL, hframeL, fibL⟩ := merge_ws_and
    (ws_build_tree_frame_initialized (h0 := h) .lit hI.base.wf hI.base.static hI.run.to0)
    (ws_build_tree_fib_plus_initialized (h0 := h) .lit hI.base.wf hI.base.static
      hI.run.to0 (Or.inl rfl) budgetL)
  have haL : aL = () := Subsingleton.elim _ _
  subst aL
  rw [setD_self hI.base.dstate] at hrL
  have hIL := hframeL.treesInvAt hI
  have distanceSame : TK.dist.arr lit = TK.dist.arr d := hframeL.other_tree .dist (by decide +kernel)
  have budgetD' : mass (fun v => (btFreq .dist lit v).toNat) 30 + 2 < 1597 := by
    simpa only [btFreq, distanceSame] using budgetD
  obtain ⟨aD, dist, hrD, hframeD, fibD⟩ := merge_ws_and
    (ws_build_tree_frame_initialized (h0 := h) .dist hIL.base.wf hIL.base.static hIL.run.to0)
    (ws_build_tree_fib_plus_initialized (h0 := h) .dist hIL.base.wf hIL.base.static
      hIL.run.to0 (Or.inr rfl) budgetD')
  have haD : aD = () := Subsingleton.elim _ _
  subst aD
  simp only [TK.descRef] at hrL hrD
  have literalSame : TK.lit.arr dist = TK.lit.arr lit := hframeD.other_tree .lit (by decide +kernel)
  refine ⟨dist, ?_, fibL.congr_tree literalSame, fibD.congr_original distanceSame.symm⟩
  have hpL : pLdesc (Sp id) h = .ok (some (.in_dstate_l_desc id), h) := by
    unfold pLdesc
    rw [bind_app, Out.sid_run hI.base.dstate]
    rfl
  have hpD : pDdesc (Sp id) (setD h id lit) =
      .ok (some (.in_dstate_d_desc id), setD h id lit) := by
    unfold pDdesc
    rw [bind_app, Out.sid_run (setD_dstates_same h id lit)]
    rfl
  unfold blPrepare
  rw [bind_app, hpL]
  simp only []
  rw [bind_app, hrL]
  simp only []
  rw [bind_app, hpD]
  exact hrD

end Zlib.Trees.Proofs

namespace Zlib.Deflate.Universal.Block
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Deflate.Engine.Proofs
open Zlib.Trees.Proofs (TK btFreq BTFibPlusOrigins SourceLengthFacts dynamicHeaderBits)
open Zlib.Trees.Proofs.Out (TreesInvAt dcodeN)
open ZlibF.Math.DeflateSymbols
open ZlibF.Math.DeflatePush (symbolCost)
open ZlibF.Math.DeflateOverlaySmall
set_option autoImplicit false

/-- Replacing the stream record leaves the deflate record, the byte blocks and the static
tables alone, so the tree invariant survives. -/
theorem treesInvAt_put {h : Heap} {r : ZStreamRef} {z' : ZStream} {ds pb : Nat} {d : DeflateState}
    {buf : Array UInt8} (trees : TreesInvAt h ds d pb buf) : TreesInvAt (r.put h z') ds d pb buf := by
  have dstates : (r.put h z').dstates = h.dstates := by
    cases r <;> simp only [ZStreamRef.put] <;> split <;> rfl
  have bytes : (r.put h z').bytes = h.bytes := by
    cases r <;> simp only [ZStreamRef.put] <;> split <;> rfl
  have ro : (r.put h z').ro = h.ro := by
    cases r <;> simp only [ZStreamRef.put] <;> split <;> rfl
  have static : (r.put h z').static = h.static := by
    cases r <;> simp only [ZStreamRef.put] <;> split <;> rfl
  obtain ⟨⟨dstate, wf, statics, pbuf, bytesB, rw, size, psize, sym, lo, hi, symEnd, pendingLe⟩, run⟩ := trees
  exact ⟨⟨by rw [dstates]; exact dstate, wf, by rw [static]; exact statics, pbuf,
    by rw [bytes]; exact bytesB, by rw [ro]; exact rw, size, psize, sym, lo, hi, symEnd, pendingLe⟩, run⟩

set_option maxRecDepth 10000 in
/-- The per-code caps summed over the actual extra-bit tables. The kernel checks every entry. -/
theorem small_cap_data :
    mass (fun v => if v < 257 then 0 else lengthCap514 (sourceLiteralExtra (v - 257))) 286 = 749 ∧
    mass (fun v => distanceCap514 (sourceDistanceExtra v)) 30 = 1028 ∧
    mass (fun v => if v < 257 then 0 else lengthCap1026 (sourceLiteralExtra (v - 257))) 286 = 1572 ∧
    mass (fun v => distanceCap1026 (sourceDistanceExtra v)) 30 = 2106 := by decide +kernel

/-- Tree preparation and `build_bl_tree` for a block of at most 1023 symbols: the symbol excess
of the prepared state is at most 3678 bits, and at most 1777 bits for at most 511 symbols. -/
theorem prepared_excess_small {h : Heap} {ds pb : Nat} {d : DeflateState} {buf : Array UInt8}
    {xs : List Symbol} (trees : TreesInvAt h ds d pb buf) (ledger : SymbolLedger buf d xs)
    (fit : xs.length + 3 ≤ 1026) :
    ∃ (mb : Int32) (ready : DeflateState),
      (do Zlib.Trees.Proofs.blPrepare (some (.tab ds)); Zlib.Trees.build_bl_tree (some (.tab ds))) h =
        .ok (mb, setD h ds ready) ∧
      Zlib.Trees.Overlay.bitExcess (dynamicSymbolCosts ready xs) ≤ 3678 ∧
      (xs.length + 3 ≤ 514 → Zlib.Trees.Overlay.bitExcess (dynamicSymbolCosts ready xs) ≤ 1777) := by
  have literalMass := ledger_literal_mass ledger
  have distanceMass := ledger_distance_mass ledger
  have budgetL : mass (fun v => (btFreq .lit d v).toNat) 286 + 2 < 1597 := by
    change mass (fun k => (d.dyn_ltree[k]!).fc.toNat) 286 + 2 < 1597
    omega
  have budgetD : mass (fun v => (btFreq .dist d v).toNat) 30 + 2 < 1597 := by
    change mass (fun k => (d.dyn_dtree[k]!).fc.toNat) 30 + 2 < 1597
    omega
  obtain ⟨ready, prepare, fibL, fibD⟩ := Zlib.Trees.Proofs.bl_prepare_fib_plus trees budgetL budgetD
  obtain ⟨other, otherRun, facts⟩ := Zlib.Trees.Proofs.bl_prepare_length_facts trees
  have same : ready = other := Zlib.Trees.Proofs.same_record_of_runs prepare otherRun
  subst other
  obtain ⟨WL, weightL, symbolL⟩ := fibL.symbol_fib_plus
  obtain ⟨WD, weightD, symbolD⟩ := fibD.symbol_fib_plus
  change WL ≤ mass (fun v => (d.dyn_ltree[v]!).fc.toNat) 286 + 2 at weightL
  change WD ≤ mass (fun v => (d.dyn_dtree[v]!).fc.toNat) 30 + 2 at weightD
  have literalFib : SymbolFibPlus 286 WL (literalFrequency symbolLengthCode xs)
      (Zlib.Trees.Proofs.curL ready.dyn_ltree) := by
    intro v bound nonzero
    have equal : (btFreq .lit d v).toNat = literalFrequency symbolLengthCode xs v := ledger.literal v bound
    have claim := symbolL v bound (by show (btFreq .lit d v).toNat ≠ 0; rw [equal]; exact nonzero)
    dsimp only at claim
    rw [equal] at claim
    exact claim
  have distanceFib : SymbolFibPlus 30 WD (distanceFrequency dcodeN xs)
      (Zlib.Trees.Proofs.curL ready.dyn_dtree) := by
    intro v bound nonzero
    have equal : (btFreq .dist d v).toNat = distanceFrequency dcodeN xs v := ledger.distance v bound
    have claim := symbolD v bound (by show (btFreq .dist d v).toNat ≠ 0; rw [equal]; exact nonzero)
    dsimp only at claim
    rw [equal] at claim
    exact claim
  have data := source_extra_cost_data
  have caps := small_cap_data
  have excessWith := fun (capL capD : Nat → Nat) (CL CD : Nat) literalCap distanceCap literalSum distanceSum =>
    symbol_excess_from_fib_plus xs
      (Zlib.Trees.Proofs.curL ready.dyn_ltree) (Zlib.Trees.Proofs.curL ready.dyn_dtree)
      sourceLiteralExtra sourceDistanceExtra symbolLengthCode dcodeN WL WD capL capD CL CD ledger.valid
      (fun s member => valid_literal_key (ledger.valid s member))
      (fun s member k selected => valid_distance_key (ledger.valid s member) selected)
      (fun c bound => data.1 ⟨c, bound⟩) (fun c bound => data.2.1 ⟨c, bound⟩)
      (fun v bound _nonzero => facts.literal v bound) (fun v bound _nonzero => facts.distance v bound)
      literalFib distanceFib literalCap distanceCap literalSum distanceSum
  have big := excessWith lengthCap1026 distanceCap1026 1572 2106
    (fun f l e length extra weight => length_cap1026 f l e length extra (by omega))
    (fun f l e length extra weight => distance_cap1026 f l e length extra (by omega))
    (Nat.le_of_eq caps.2.2.1) (Nat.le_of_eq caps.2.2.2)
  have small (fewer : xs.length + 3 ≤ 514) := excessWith lengthCap514 distanceCap514 749 1028
    (fun f l e length extra weight => length_cap514 f l e length extra (by omega))
    (fun f l e length extra weight => distance_cap514 f l e length extra (by omega))
    (Nat.le_of_eq caps.1) (Nat.le_of_eq caps.2.1)
  obtain ⟨other, prepared, input, treesR, _bl, _bits⟩ := Zlib.Trees.Proofs.bl_prepare trees
  have sameR : ready = other := Zlib.Trees.Proofs.same_record_of_runs prepare prepared
  subst other
  obtain ⟨mb, result, run, _lDesc, _dDesc, lTree, dTree, _treesA, _outputA⟩ :=
    Zlib.Trees.Proofs.build_bl_preserves_source_codes treesR input
  have costs : dynamicSymbolCosts result xs = dynamicSymbolCosts ready xs :=
    dynamicSymbolCosts_live_congr ledger facts lTree dTree
  have complete : (do
        Zlib.Trees.Proofs.blPrepare (some (.tab ds))
        Zlib.Trees.build_bl_tree (some (.tab ds))) h = .ok (mb, setD h ds result) := by
    rw [bind_app, prepare]
    rw [Zlib.Trees.Proofs.setD_setD] at run
    exact run
  refine ⟨mb, result, complete, ?_, ?_⟩
  · rw [costs]
    exact big
  · intro fewer
    rw [costs]
    exact small fewer

/-- `lit_bufsize` is a power of two (`2 * lit_bufsize = 2^hash_bits`), so between 512 and 2047
it is 512 or 1024. -/
theorem lit_bufsize_mid {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (good : DGood h r ds z d) (lower : 512 ≤ d.lit_bufsize.toNat) (upper : d.lit_bufsize.toNat < 2048) :
    d.lit_bufsize.toNat = 512 ∨ d.lit_bufsize.toNat = 1024 := by
  have lit := good.inv.lit
  have size := good.inv.hsize
  have bitsMax := good.inv.hbits_hi
  generalize d.hash_bits.toNat = k at size bitsMax
  rw [size] at lit
  rcases k with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k <;>
    (try simp only [Nat.reduceAdd, Nat.reducePow] at lit) <;> omega

/-- **F9 for `lit_bufsize` 512 and 1024** (`memLevel` 3 and 4): the dynamic overlay room of
every block, from a drained entry, on the heap with any stream record. -/
theorem dynamic_overlay_mid {h : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream} {d : DeflateState}
    {buf : Array UInt8} {xs : List Symbol}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (ledger : SymbolLedger buf d xs)
    (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7)
    (lower : 512 ≤ d.lit_bufsize.toNat) (upper : d.lit_bufsize.toNat < 2048) (z' : ZStream) :
    DynamicOverlay (r.put h z') ds d xs := by
  intro mb ready run frame header _excess _dynamic
  have capacity : xs.length + 1 ≤ d.lit_bufsize.toNat := by
    have bound := trees.run.sym_next_le
    rw [ledger.count, trees.base.sym_end] at bound
    have lowLit := trees.base.lit_lo
    omega
  have cases := lit_bufsize_mid good lower upper
  obtain ⟨mb2, ready2, run2, big, small⟩ :=
    prepared_excess_small (treesInvAt_put (r := r) (z' := z') trees) ledger (by omega)
  have same : ready = ready2 := Zlib.Trees.Proofs.same_record_of_runs run run2
  subst ready2
  have fields : ready.lit_bufsize = d.lit_bufsize ∧ ready.pending = d.pending ∧
      ready.bi_valid = d.bi_valid := by
    rw [frame]
    exact ⟨rfl, rfl, rfl⟩
  have pendingZero : ready.pending.toNat = 0 := by rw [fields.2.1, pending]; rfl
  have bitsN : ready.bi_valid.toInt.toNat ≤ 7 := by rw [fields.2.2]; omega
  have capacityR : ready.lit_bufsize.toNat = d.lit_bufsize.toNat := by rw [fields.1]
  have costLength : (dynamicSymbolCosts ready xs).length = xs.length := by
    simp only [dynamicSymbolCosts, List.length_map]
  have budget : (dynamicHeaderBits ready mb).length + Zlib.Trees.Overlay.bitExcess (dynamicSymbolCosts ready xs) +
      25 ≤ 8 * ready.lit_bufsize.toNat := by
    rcases cases with equal | equal
    · have bound := small (by omega)
      omega
    · omega
  constructor
  · intro k
    have room := overlay_prefix_of_budget ready.lit_bufsize.toNat ready.bi_valid.toInt.toNat
      (dynamicHeaderBits ready mb).length (dynamicSymbolCosts ready xs) bitsN budget k
    omega
  · have room := overlay_block_of_budget ready.lit_bufsize.toNat ready.bi_valid.toInt.toNat
      (dynamicHeaderBits ready mb).length (dynamicSymbolCosts ready xs) bitsN budget (by omega)
    omega

/-- `SmallOverlay` for `lit_bufsize < 512` only (`memLevel` 1 and 2). Open. -/
def TinyOverlay : Prop :=
  ∀ {h : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream} {d : DeflateState} {buf : Array UInt8}
    {xs : List Symbol},
    DGood h r ds z d → TreesInvAt h ds d pb buf → SymbolLedger buf d xs → d.pending = 0 →
    d.bi_valid.toInt ≤ 7 → d.lit_bufsize.toNat < 512 → ∀ z', DynamicOverlay (r.put h z') ds d xs

/-- The open overlay case reduces to `memLevel` 1 and 2. -/
theorem smallOverlay_of_tiny (tiny : TinyOverlay) : SmallOverlay := by
  intro h r ds pb z d buf xs good trees ledger pending bits upper z'
  by_cases lower : 512 ≤ d.lit_bufsize.toNat
  · exact dynamic_overlay_mid good trees ledger pending bits lower upper z'
  · exact tiny good trees ledger pending bits (by omega) z'

/-- `FlushSafeFrame`, from the open overlay case at `memLevel` 1 and 2. -/
theorem flushSafeFrame_of_tiny (tiny : TinyOverlay) : FlushSafeFrame :=
  flushSafeFrame_of_small (smallOverlay_of_tiny tiny)

/-- Batch B's `FlushSafe`, from the open overlay case at `memLevel` 1 and 2. -/
theorem flushSafe_of_tiny (tiny : TinyOverlay) : Zlib.Deflate.Universal.FlushSafe :=
  flushSafe_of_small (smallOverlay_of_tiny tiny)


/-- **The block flush keeps the deflate invariant** (`flush_block_spec`) for every `memLevel`, from
the open overlay case at `memLevel` 1 and 2; with `lit_bufsize ≥ 512` (`memLevel ≥ 3`) the
premise is not used (`flush_block_spec_mid`). -/
theorem flush_block_spec_of_tiny (tiny : TinyOverlay) {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream}
    {d : DeflateState} (inv : DInv h r ds z d) (buffers : StreamBuffers h r) (out : z.next_out ≠ .null)
    (level : 0 < d.level.toInt) (pending : d.pending = 0) (idle : d.match_available = 0) (last : Bool) :
    ∃ after z' d' produced,
      C.run (FLUSH_BLOCK_ONLY (some (.tab ds)) (if last then 1 else 0)) h = .ok ((), after) ∧
      DInv after r ds z' d' ∧ StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧
      d'.sym_next = 0 := by
  refine flush_block_spec_of_overlay inv buffers out level pending idle ?_ last
  intro xs recorded z'
  obtain ⟨b, a, pbuf, bytes, ledger⟩ := recorded
  obtain ⟨pb, buf, trees⟩ := trees_of_good inv.dgood
  have same : b = pb := by
    have e := trees.base.pbuf; rw [pbuf] at e; cases e; rfl
  subst same
  have sameA : a = buf := Option.some.inj (bytes.symm.trans trees.base.bytes)
  subst sameA
  have bits : d.bi_valid.toInt ≤ 7 := inv.shape.biValid
  by_cases large : 2048 ≤ d.lit_bufsize.toNat
  · have capacity : xs.length + 1 ≤ d.lit_bufsize.toNat := by
      have bound := trees.run.sym_next_le
      rw [ledger.count, trees.base.sym_end] at bound
      have lowLit := trees.base.lit_lo
      omega
    exact dynamic_overlay_large large pending bits capacity
  · exact smallOverlay_of_tiny tiny inv.dgood trees ledger pending bits (by omega) z'

/-- **`flush_block_spec` for `memLevel ≥ 3`** (`lit_bufsize ≥ 512`), with no open premise. -/
theorem flush_block_spec_mid {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream}
    {d : DeflateState} (inv : DInv h r ds z d) (buffers : StreamBuffers h r) (out : z.next_out ≠ .null)
    (level : 0 < d.level.toInt) (pending : d.pending = 0) (idle : d.match_available = 0) (lower : 512 ≤ d.lit_bufsize.toNat) (last : Bool) :
    ∃ after z' d' produced,
      C.run (FLUSH_BLOCK_ONLY (some (.tab ds)) (if last then 1 else 0)) h = .ok ((), after) ∧
      DInv after r ds z' d' ∧ StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧
      d'.sym_next = 0 := by
  refine flush_block_spec_of_overlay inv buffers out level pending idle ?_ last
  intro xs recorded z'
  obtain ⟨b, a, pbuf, bytes, ledger⟩ := recorded
  obtain ⟨pb, buf, trees⟩ := trees_of_good inv.dgood
  have same : b = pb := by
    have e := trees.base.pbuf; rw [pbuf] at e; cases e; rfl
  subst same
  have sameA : a = buf := Option.some.inj (bytes.symm.trans trees.base.bytes)
  subst sameA
  have bits : d.bi_valid.toInt ≤ 7 := inv.shape.biValid
  by_cases large : 2048 ≤ d.lit_bufsize.toNat
  · have capacity : xs.length + 1 ≤ d.lit_bufsize.toNat := by
      have bound := trees.run.sym_next_le
      rw [ledger.count, trees.base.sym_end] at bound
      have lowLit := trees.base.lit_lo
      omega
    exact dynamic_overlay_large large pending bits capacity
  · exact dynamic_overlay_mid inv.dgood trees ledger pending bits lower (by omega) z'

end Zlib.Deflate.Universal.Block
