import ZlibF.Proof.«deflate.c.engine.short-search-frontier»
import ZlibF.Proof.«deflate.c.engine.match-endpoint»

/-! # The EOF insertion reset restores the pending-position boundary -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- The state update written after the slow loop's last deferred byte. -/
def eofInsert (d : DeflateState) : DeflateState :=
  { d with insert := if d.strstart < MIN_MATCH_u - 1 then d.strstart else MIN_MATCH_u - 1 }

/-- The literal settlement preceding the source's final insert write. -/
def slowEofLiteral (s : DeflateStatePtr) : M Unit := do
  let d ← ldDeflateState s
  if d.match_available != 0 then
    let c ← index8 d.window (d.strstart - 1).toNat
    let _ ← tally_lit s c
    wr s (fun d => { d with match_available := 0 })

/-- The complete translated slow function uses this exact EOF state write
in source order, after the real loop and possible deferred literal. -/
theorem deflate_slow_eof_source (s : DeflateStatePtr) (flush : Int32) :
    deflate_slow s flush = (do
      let st ← cwhile forever (deflate_slow_body s flush) {}
      if let some r := st.ret then return r
      slowEofLiteral s
      wr s eofInsert
      finish_tail s flush) := by
  unfold deflate_slow slowEofLiteral eofInsert
  simp only [M_bind_assoc, M_pure_bind, fill_ite_bind]
  rfl

theorem eof_insert_count (d : DeflateState) :
    (eofInsert d).insert.toNat = min d.strstart.toNat 2 := by
  by_cases short : d.strstart < MIN_MATCH_u - 1
  · have small : d.strstart.toNat < 2 := UInt32.lt_iff_toNat_lt.mp short
    simp only [eofInsert, short, ite_true]
    exact (Nat.min_eq_left (by omega)).symm
  · have large : 2 ≤ d.strstart.toNat := by
      have notLt : ¬ d.strstart.toNat < 2 := fun lt => short (UInt32.lt_iff_toNat_lt.mpr lt)
      omega
    simp only [eofInsert, short, ite_false]
    change 2 = min d.strstart.toNat 2
    exact (Nat.min_eq_right large).symm

/-- The saved real insertion frontier supplies the two pending positions
at EOF. No earlier chain frontier is inferred by reversing monotonicity.
This proves the state-write cutpoint, not the full deflate_slow tail. -/
theorem eof_insert_content_boundary {h : Heap} {r : ZStreamRef} {ds origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8}
    (boundary : ContentBoundary h r ds z d input origin base xs)
    (frontier : EndFrontier h d) (empty : d.lookahead = 0) :
    wr (some (.tab ds)) eofInsert h = .ok ((), setD h ds (eofInsert d)) ∧
      ContentBoundary (setD h ds (eofInsert d)) r ds z (eofInsert d) input origin base xs ∧
      EndFrontier (setD h ds (eofInsert d)) (eofInsert d) ∧ ConfigFrame d (eofInsert d) := by
  let result := eofInsert d
  let after := setD h ds result
  have inv : DStInv h ds result :=
    { boundary.good.inv with blocks := boundary.good.inv.blocks_keys rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl }
  have goodA : DGood after r ds z result :=
    boundary.good.setD' (d' := result) rfl boundary.good.live.status inv (by trkeep)
  have chainsA : HeapChains after result result.strstart.toNat :=
    (boundary.chains.at.keep rfl rfl rfl rfl rfl rfl rfl rfl rfl).collapse rfl
  have endA : EndFrontier after result :=
    (frontier.at.keep rfl rfl rfl rfl rfl rfl rfl rfl rfl).collapse rfl
  have pendingA : HeapChains after result (result.strstart.toNat - result.insert.toNat) := by
    have same : result.strstart.toNat - result.insert.toNat = min d.strstart.toNat (fillEnd d - 2) := by
      change d.strstart.toNat - (eofInsert d).insert.toNat = _
      rw [eof_insert_count]
      simp only [fillEnd, empty, show (0 : UInt32).toNat = 0 from rfl, Nat.add_zero]
      omega
    rw [same]
    exact (frontier.at.keep rfl rfl rfl rfl rfl rfl rfl rfl rfl).collapse rfl
  obtain ⟨b, buf, trees, ledger, balance⟩ := boundary.symbols
  have ledgerA : SymbolLedger buf result xs := ledger.keep rfl rfl rfl rfl
  have symbolsA : SymbolBoundary after ds result xs :=
    symbol_boundary_of_ledger goodA trees.base.pbuf trees.base.bytes ledgerA balance
  refine ⟨?_, ?_, endA, rfl⟩
  · simp only [wrD_eq, boundary.good.live.hs]
  · refine ⟨⟨⟨goodA, chainsA, boundary.range, boundary.history, boundary.deferred, symbolsA, boundary.data⟩,
      ?_, pendingA, ?_⟩, boundary.trace, boundary.accounted⟩
    · change (eofInsert d).insert.toNat ≤ d.strstart.toNat
      rw [eof_insert_count]
      exact Nat.min_le_left _ _
    · intro enough
      change 3 ≤ d.lookahead.toNat at enough
      rw [empty] at enough
      change 3 ≤ 0 at enough
      omega

end Zlib.Deflate.Engine.Proofs
