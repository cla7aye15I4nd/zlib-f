import ZlibF.Math.DeflateSymbolMass
import ZlibF.Proof.«deflate.c.engine.symbol-ledger»

/-! # Actual leaf weights follow from the symbol buffer capacity -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open Zlib.Trees.Proofs.Out (TreesBase dcodeN)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

theorem symbol_length_key_bound {n : Nat} (bound : n < 256) : symbolLengthCode n ≤ 28 := by
  have fit : n < Zlib.Trees.length_code_tab.size := by
    rw [Zlib.Trees.Proofs.Out.length_code_tab_size]
    exact bound
  simpa [symbolLengthCode, fit] using Zlib.Trees.Proofs.Out.length_code_le n bound

theorem symbol_distance_key_bound {n : Nat} (bound : n < 32768) : dcodeN n ≤ 29 := by
  unfold dcodeN
  split
  · rename_i small
    have fit : n < Zlib.Trees.dist_code_tab.size := by
      rw [Zlib.Trees.Proofs.Out.dist_code_tab_size]
      omega
    simpa [fit] using Zlib.Trees.Proofs.Out.dist_code_le n (by omega)
  · have fit : 256 + n / 128 < Zlib.Trees.dist_code_tab.size := by
      rw [Zlib.Trees.Proofs.Out.dist_code_tab_size]
      omega
    simpa [fit] using Zlib.Trees.Proofs.Out.dist_code_le (256 + n / 128) (by omega)

theorem valid_literal_key {s : Symbol} (valid : s.Valid) : s.literalKey symbolLengthCode < 286 := by
  have bound := symbol_length_key_bound valid.2
  have value := valid.2
  unfold Symbol.literalKey
  split <;> omega

theorem valid_distance_key {s : Symbol} (valid : s.Valid) {k : Nat}
    (selected : s.distanceKey dcodeN = some k) : k < 30 := by
  unfold Symbol.distanceKey at selected
  split at selected
  · cases selected
  · rename_i positive
    have bound := symbol_distance_key_bound (n := s.distance - 1) (by have := valid.1; omega)
    simp only [Option.some.injEq] at selected
    omega

/-- Exactly one literal/length leaf is incremented per stored symbol.
The end marker contributes one independently of the symbol list. -/
theorem ledger_literal_mass {buf : Array UInt8} {d : DeflateState} {xs : List Symbol}
    (ledger : SymbolLedger buf d xs) :
    mass (fun k => (d.dyn_ltree[k]!).fc.toNat) 286 = xs.length + 1 := by
  rw [mass_congr ledger.literal]
  exact literal_frequency_mass _ (fun s member => valid_literal_key (ledger.valid s member))

theorem ledger_distance_mass {buf : Array UInt8} {d : DeflateState} {xs : List Symbol}
    (ledger : SymbolLedger buf d xs) :
    mass (fun k => (d.dyn_dtree[k]!).fc.toNat) 30 ≤ xs.length := by
  rw [mass_congr ledger.distance]
  exact distance_frequency_mass _ (fun s member _ selected =>
    valid_distance_key (ledger.valid s member) selected)

/-- The tree-weight premises are consequences of the same real buffer
geometry used by tally. They are not extra caller-supplied weight bounds. -/
theorem ledger_tree_capacity {h : Heap} {ds b : Nat} {d : DeflateState} {buf : Array UInt8}
    {xs : List Symbol} (base : TreesBase h ds d b buf) (ledger : SymbolLedger buf d xs)
    (count : d.sym_next.toNat ≤ d.sym_end.toNat) :
    mass (fun k => (d.dyn_ltree[k]!).fc.toNat) 286 ≤ d.lit_bufsize.toNat ∧
      mass (fun k => (d.dyn_dtree[k]!).fc.toNat) 30 < d.lit_bufsize.toNat := by
  have symbols := ledger.count
  have end_ := base.sym_end
  have low := base.lit_lo
  have literal := ledger_literal_mass ledger
  have distance := ledger_distance_mass ledger
  omega

end Zlib.Deflate.Engine.Proofs
