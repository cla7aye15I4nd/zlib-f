import ZlibF.Proof.«trees.c.emit»
import ZlibF.Proof.«trees.c.monad»

/-! # Aligned length words in the actual stored-block header -/

namespace Zlib.Trees.Proofs.Out
open C Zlib.Trees
set_option autoImplicit false

/-- The real little-endian writer appends exactly sixteen bits at an
aligned output position, retaining all caller and source-tree fields. -/
theorem put_short_emit_aligned {h : Heap} {id b : Nat} {d : DeflateState} {buf : Array UInt8}
    (trees : TreesInvAt h id d b buf) (aligned : d.bi_valid.toInt = 0)
    (room : d.pending.toNat + 2 ≤ buf.size) (word : UInt16) :
    Emit id b (put_short (some (.tab id)) word) h d buf (natBits word.toNat 16) 2 := by
  let next := (buf.set! d.pending.toNat (word &&& 0xff).toUInt8).set!
    (d.pending.toNat + 1) (word >>> 8).toUInt8
  let result : DeflateState := { d with pending := d.pending + 2 }
  have size : next.size = buf.size := by simp only [next, Array.size_set!]
  have pending : result.pending.toNat = d.pending.toNat + 2 := toNat_add_two_u64 trees.base.pending_small
  refine ⟨next, result, put_short_run trees.base room word, ?_, ?_, size, ?_, by omega, by omega,
    d.pending + 2, d.bi_buf, d.bi_valid, d.bi_used, rfl⟩
  · exact ⟨trees.base.step next size result trees.base.wf rfl rfl rfl rfl rfl
      (by change result.pending.toNat ≤ d.pending_buf_size.toNat
          rw [pending, trees.base.psize]; exact room),
      trees.run.ldyn, trees.run.lstat, trees.run.ddyn, trees.run.dstat, trees.run.bldyn, trees.run.blstat,
      trees.run.bi_lo, trees.run.bi_hi, trees.run.bi_buf, trees.run.sym_next_le, trees.run.sym_next_mod⟩
  · unfold outBits
    change bytesBits next result.pending.toNat ++ natBits d.bi_buf.toNat d.bi_valid.toInt.toNat = _
    rw [pending, aligned]
    simp only [Int.toNat_zero, show natBits d.bi_buf.toNat 0 = [] from rfl, List.append_nil]
    rw [bytesBits_two _ _ room, List.append_assoc, natBits_word]
  · intro i outside
    have noFirst : d.pending.toNat ≠ i := by omega
    have noSecond : d.pending.toNat + 1 ≠ i := by omega
    dsimp only [next]
    rw [getD_set_u8, getD_set_u8]
    simp only [noFirst, noSecond, false_and, ite_false]

/-- The checked actual writer identifies its returned state independently
of the more general bit-emission footprint. -/
theorem put_short_result {h : Heap} {id b : Nat} {d result : DeflateState} {buf next : Array UInt8}
    (trees : TreesInvAt h id d b buf) (room : d.pending.toNat + 2 ≤ buf.size) (word : UInt16)
    (run : put_short (some (.tab id)) word h = .ok ((), setD (setB h b next) id result)) :
    result = { d with pending := d.pending + 2 } := by
  have heap := (Prod.mk.inj (Except.ok.inj (run.symm.trans (put_short_run trees.base room word)))).2
  have states := congrArg (fun hp : Heap => hp.dstates id) heap
  exact Option.some.inj (by simpa only [setD_dstates_same] using states)

def storedBlockHeader (s : DeflateStatePtr) (length : UInt64) (last : Int32) : M Unit := do
  send_bits s (← iadd (STORED_BLOCK <<< 1) last) 3
  bi_windup s
  put_short s length.toUInt16
  put_short s (~~~length).toUInt16

/-- The full stored-block translation uses this header before the actual
conditional memcpy and final pending update, in the same source order. -/
theorem stored_block_header_source (s : DeflateStatePtr) (buf : BPtr) (length : UInt64) (last : Int32) :
    «_tr_stored_block» s buf length last = (do
      storedBlockHeader s length last
      if length != 0 then
        let d ← rd s
        let dst ← Ptr.add d.pending_buf (d.pending.toNat : Int)
        memcpyB dst buf length.toNat
      md s fun d => { d with pending := d.pending + length }) := by
  unfold «_tr_stored_block» storedBlockHeader
  simp only [M_bind_assoc, M_pure_bind]

def storedHeaderBits (d : DeflateState) (length : UInt64) (last : Bool) : List Bool :=
  natBits (if last then 1 else 0) 3 ++
    List.replicate ((8 - (d.bi_valid.toInt.toNat + 3) % 8) % 8) false ++
    natBits length.toUInt16.toNat 16 ++ natBits (~~~length).toUInt16.toNat 16

/-- The actual tag, alignment and both length words append the exact
stored header. Starting with at most seven held bits needs at most six
pending bytes. memcpy and its content argument are subsequent obligations. -/
theorem stored_block_header_emit {h : Heap} {id b : Nat} {d : DeflateState} {buf : Array UInt8}
    (trees : TreesInvAt h id d b buf) (bits : d.bi_valid.toInt ≤ 7)
    (room : d.pending.toNat + 6 ≤ buf.size) (length : UInt64) (last : Bool) :
    ∃ next result,
      storedBlockHeader (some (.tab id)) length (if last then 1 else 0) h =
        .ok ((), setD (setB h b next) id result) ∧
      TreesInvAt (setD (setB h b next) id result) id result b next ∧
      outBits next result = outBits buf d ++ storedHeaderBits d length last ∧
      next.size = buf.size ∧ result.bi_valid.toInt = 0 ∧
      result.pending.toNat ≤ d.pending.toNat + 6 ∧ BitsDiff d result := by
  have arith : iadd (STORED_BLOCK <<< 1) (if last then 1 else 0) =
      pure (if last then 1 else 0) := by cases last <;> rfl
  have tagFit : v16 (if last then 1 else 0) < 2 ^ (3 : Int32).toInt.toNat := by
    cases last <;> decide +kernel
  obtain ⟨tagged, tagRun, treesT, outputT, pendingT, wordT, validT, fieldsT⟩ :=
    send_bits_spec_B trees (if last then 1 else 0) 3 (by decide +kernel) (by decide +kernel)
      tagFit (by change d.bi_valid.toInt + 3 ≤ 16; omega)
  have tagWord : v16 (if last then 1 else 0) = if last then 1 else 0 := by cases last <;> rfl
  change outBits buf tagged = outBits buf d ++ natBits (v16 (if last then 1 else 0)) 3 at outputT
  rw [tagWord] at outputT
  have bitLength := congrArg List.length outputT
  simp only [outBits_length, List.length_append, natBits_length, pendingT] at bitLength
  have countT : tagged.bi_valid.toInt.toNat = d.bi_valid.toInt.toNat + 3 := by omega
  have windRoom : 8 * tagged.pending.toNat + tagged.bi_valid.toInt.toNat ≤ 8 * buf.size := by
    rw [pendingT, countT]
    have lower := trees.run.bi_lo
    omega
  obtain ⟨windBuf, wound, windRun, treesW, outputW, zeroW, _wordW, _usedW, sizeW,
    _frameW, _lowerW, upperW, pendingW, usedW, fieldsW⟩ := bi_windup_spec treesT windRoom
  simp only [setB_setD, setD_setD] at windRun treesW
  have roomW : wound.pending.toNat + 2 ≤ windBuf.size := by rw [sizeW]; rw [pendingT] at upperW; omega
  obtain ⟨firstBuf, first, firstRun, treesF, outputF, sizeF, _frameF, _lowerF, upperF, diffF⟩ :=
    put_short_emit_aligned treesW zeroW roomW length.toUInt16
  have fieldsF := put_short_result treesW roomW length.toUInt16 firstRun
  simp only [setB_setD, setB_setB, setD_setD] at firstRun treesF
  have zeroF : first.bi_valid.toInt = 0 := by
    rw [fieldsF]
    exact zeroW
  have roomF : first.pending.toNat + 2 ≤ firstBuf.size := by
    rw [sizeF, sizeW]
    rw [pendingT] at upperW
    omega
  obtain ⟨next, result, secondRun, treesR, outputR, sizeR, _frameR, _lowerR, upperR, diffR⟩ :=
    put_short_emit_aligned treesF zeroF roomF (~~~length).toUInt16
  have fieldsR := put_short_result treesF roomF (~~~length).toUInt16 secondRun
  simp only [setB_setD, setB_setB, setD_setD] at secondRun treesR
  have zeroR : result.bi_valid.toInt = 0 := by
    rw [fieldsR]
    exact zeroF
  have diffT : BitsDiff d tagged := by rw [fieldsT]; exact ⟨d.pending, wordT, validT, d.bi_used, rfl⟩
  have diffW : BitsDiff tagged wound := by rw [fieldsW]; exact ⟨pendingW, 0, 0, usedW, rfl⟩
  refine ⟨next, result, ?_, treesR, ?_, sizeR.trans (sizeF.trans sizeW), zeroR, ?_,
    ((diffT.trans diffW).trans diffF).trans diffR⟩
  · unfold storedBlockHeader
    rw [arith]
    simp only [M_pure_bind, bind_app, pure_app, tagRun, windRun, firstRun, secondRun]
  · rw [outputR, outputF, outputW, outputT, countT]
    simp only [storedHeaderBits, List.append_assoc]
  · rw [pendingT] at upperW
    omega

end Zlib.Trees.Proofs.Out
