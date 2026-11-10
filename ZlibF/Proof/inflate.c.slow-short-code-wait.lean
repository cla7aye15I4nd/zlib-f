import ZlibF.Proof.«inflate.c.slow-future-query»
import ZlibF.Proof.«inflate.c.slow-future-length-phase»
namespace Zlib.Inflate.Proofs.SlowInputFragment
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inffast.Proofs Zlib.Inffast.Spec
open Zlib.Inftrees Zlib.Inftrees.Spec.DecodeSemantics Zlib.Inftrees.Spec.DecodeSoundness
open SlowSubtablePath
set_option autoImplicit false

/-- If the independent future's valid code does not yet fit, actual root
and linked lookup must wait before dropping either part of the code. -/
theorem lenLookup_short_future {c : Ctx} {h : Heap} {zs : Nat} {s : InflateState}
    {ref : CodeRef} {offset extent : Nat} {ca : Array Code} {L : List Nat}
    {l : IL} {bs : List UInt8} {future input rest : List Bool} {symbol : Nat}
    (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s)
    (pointer : s.lencode = .ref ref offset) (tableGet : Space.get h ref = some ca)
    (safe : LenTableSafe ca offset s.lenbits.toNat)
    (meaning : Zlib.Inftrees.Spec.DecodeTableInvariant.Inv LENS ca offset s.lenbits.toNat extent L)
    (stable : Zlib.Inftrees.Spec.DecodeTableStability.StableQuery LENS ca offset s.lenbits.toNat)
    (B : BitInv h l bs) (source : FutureSource l bs future input)
    (decoded : decodeSym L input = some (symbol, rest)) (valid : ValidSymbol LENS symbol)
    (short : (stream l bs).length < L.getD symbol 0) :
    ∃ regs, InputWait (lenLookup c) h h l bs future input regs := by
  obtain ⟨result, current, used, rootRun, _two, bound, bits, streamEq, shape, count,
    _bitBound, selected, _entryBound, classification, kinds, enough, empty, cursor⟩ :=
    lookup1_len_run_cursor hc hs pointer tableGet safe B
  have currentSource : FutureSource current (bs.drop used) future input := by
    unfold FutureSource
    rw [streamEq]
    exact source
  rcases kinds with normal | stopped
  · have inside : offset + current.hold.toNat % 2 ^ s.lenbits.toNat < ca.size := by
      have extent := meaning.rootTable.2.2.1
      have index := Nat.mod_lt current.hold.toNat (Nat.two_pow_pos s.lenbits.toNat)
      omega
    have cell : ca[offset + current.hold.toNat % 2 ^ s.lenbits.toNat]? = some current.here := by
      rw [selected, codeLookupValue, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem inside, Option.getD_some]
    by_cases link : SlowLenLink current.here
    · have fast := slowLenLink_fast link
      rw [ite_eq_left fast] at classification
      have isLink : Zlib.Inftrees.Spec.Subtable.IsLink LENS current.here = true := by
        simp only [Zlib.Inftrees.Spec.Subtable.IsLink, ite_true, Bool.and_eq_true, bne_iff_ne, beq_iff_eq]
        exact link
      have rootBits := (meaning.subtables _ current.here
        (Nat.mod_lt _ (Nat.two_pow_pos _)) cell isLink).1
      have rootEnough : s.lenbits.toNat ≤ current.bits.toNat := by have := enough normal; omega
      let start := {current with last := current.here}
      have startBits : BitInv h start (bs.drop used) := ⟨bits.have_eq, bits.next, bits.hold_lt⟩
      obtain ⟨result2, regs, used2, subRun, _two2, bound2, bits2, streamEq2, shape2, count2,
        _bitBound2, selected2, _leaf2, _total2, kinds2, enough2, empty2, cursor2⟩ :=
        lookup2_data_run_cursor false current.here hc hs pointer tableGet rfl classification
          (fun _ leaf => leaf.1) startBits
      rcases kinds2 with normal2 | stopped2
      · have currentCell : ca[offset + regs.hold.toNat % 2 ^ s.lenbits.toNat]? = some current.here :=
          root_cell_of_stream rootEnough (by dsimp only [start] at count2; omega) streamEq2 cell
        have finalSource : FutureSource regs ((bs.drop used).drop used2) future input := by
          unfold FutureSource
          rw [streamEq2]
          exact currentSource
        have fitted := fitted_subtable_future meaning stable bits2 finalSource decoded valid
          currentCell isLink selected2 (enough2 normal2)
        have lengthEq : (stream regs ((bs.drop used).drop used2)).length = (stream l bs).length := by
          rw [streamEq2]
          exact congrArg List.length streamEq
        omega
      · have finalBits : BitInv h regs (bs.drop (used + used2)) := by
          simpa only [List.drop_drop, Nat.add_comm] using bits2
        have finalStream : stream regs (bs.drop (used + used2)) = stream l bs := by
          simpa only [List.drop_drop, Nat.add_comm] using streamEq2.trans streamEq
        have totalBound : used + used2 ≤ bs.length := by simp only [List.length_drop] at bound2; omega
        obtain ⟨all, ledger, finalSource, _saved⟩ := wait_source_ledger B totalBound finalBits (empty2 stopped2) finalStream source
        have actual : runX (lenLookup c) l h = .ok ((.error Ex.leave, regs), h) := by
          unfold lenLookup
          rw [runX_bind, rootRun, normal]
          simp only [runX_bind, runX_get]
          rw [lenRootTail_link c current.here link]
          unfold lenSubLookup
          rw [runX_bind, runX_modify]
          change runX (do lookup2 c false; let last := (← get).last; DROPBITS last.bits.toUInt32; let state ← ldInflateState c.st; let back ← chkI32 (state.back.toInt + last.bits.toNat); wrS c.st fun state => {state with back := back}) start h = _
          rw [runX_bind, subRun, stopped2]
        refine ⟨regs, ⟨actual, ?_, empty2 stopped2, ?_, shape.symbol.trans ((by rfl : SymbolRegShape current start).trans shape2.symbol), ?_, ?_⟩⟩
        · simpa only [all, List.drop_length] using finalBits
        · rw [cursor2]
          change inputAdvance current.next used2 = _
          rw [cursor, inputAdvance_add, all]
        · simpa only [all] using ledger
        · simpa only [all, List.drop_length] using finalSource
    · obtain ⟨suffix, query⟩ := ZlibF.Math.InflateHeldBits.padded_query bits.hold_lt meaning.rootTable.2.1
      have heldQuery : tableRead LENS ca offset s.lenbits.toNat
          (Zlib.Inftrees.Spec.DecodeShort.padded (bitsOfNat current.hold.toNat current.bits.toNat)) =
          some (current.here, current.here.bits.toNat) := by
        simp [tableRead, query, cell]
        intro nonzero high
        exact False.elim (link ⟨nonzero, high⟩)
      have fitted := fitted_query_future meaning stable bits currentSource decoded valid heldQuery (enough normal)
      have lengthEq := congrArg List.length streamEq
      omega
  · obtain ⟨all, ledger, finalSource, _saved⟩ := wait_source_ledger B bound bits (empty stopped) streamEq source
    refine ⟨current, ⟨?_, ?_, empty stopped, by simpa only [all] using cursor, shape.symbol,
      by simpa only [all] using ledger, ?_⟩⟩
    · unfold lenLookup
      rw [runX_bind, rootRun, stopped]
    · simpa only [all, List.drop_length] using bits
    · simpa only [all, List.drop_length] using finalSource

#print axioms lenLookup_short_future
end Zlib.Inflate.Proofs.SlowInputFragment
