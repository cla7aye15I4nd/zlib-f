import ZlibF.Proof.«inflate.c.later-table-counts»
namespace Zlib.Inflate.Proofs.LaterHeader
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inffast.Proofs
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.WrapperGlue Zlib.Inflate.Proofs.HeaderPhaseView Zlib.Inflate.Proofs.CumulativeTableBoundary
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- The two early dynamic-header waits retain real cursors, initialized
state and a causal count/alphabet continuation. No window/output reset. -/
structure EarlyHeaderWait (c : Ctx) (h : Heap) (r : ZStreamRef) (zs : Nat) (z : ZStream)
    (s : InflateState) (l : IL) (bs credited history : List UInt8) where
  regs : IL
  state : InflateState
  heap : Heap
  used : Nat
  bound : used ≤ bs.length
  actual : runX (inflate_TABLE c) l h = .ok ((.error Ex.leave, regs), heap)
  origin : DefaultOriginState heap r zs z state
  buffers : DispatchBuffers heap r regs (bs.drop used)
  frame : HeaderFrame s state
  last : state.last = s.last
  allocator : DefAlloc z
  credit : AdlerCredit z state credited
  dictionary : InflateDictionary heap state history
  bits : regs.bits.toNat ≤ max l.bits.toNat 21
  cursor : regs.next = inputAdvance l.next used
  count : regs.have_.toNat + used = l.have_.toNat
  put : regs.put = l.put
  left : regs.left = l.left
  out : regs.out_ = l.out_
  phase : state.mode = TABLE ∨ state.mode = LENLENS
  tableSource : state.mode = TABLE → stream regs (bs.drop used) = stream l bs
  lensSource : state.mode = LENLENS → ∃ received hlit hdist hclen r1 r2,
    LenlensProgress state regs.hold regs.bits received ∧
    received ++ bytesBits (bs.drop used) = (stream l bs).drop 14 ∧
    readBits 5 (stream l bs) = some (hlit, r1) ∧ readBits 5 r1 = some (hdist, r2) ∧
    readBits 4 r2 = some (hclen, (stream l bs).drop 14) ∧
    state.nlen.toNat = hlit + 257 ∧ state.ndist.toNat = hdist + 1 ∧ state.ncode.toNat = hclen + 4

theorem table_short_wait
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs credited history : List UInt8}
    (E : Env c h r zs z s) (origin : DefaultOriginState h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = TABLE) (allocator : DefAlloc z)
    (credit : AdlerCredit z s credited) (dictionary : InflateDictionary h s history)
    (short : (stream l bs).length < 14) : Nonempty (EarlyHeaderWait c h r zs z s l bs credited history) := by
  obtain ⟨outcome, regs, used, pull, bound, B, source, _count, shape, upper, _same, full, waiting, kinds, cursor⟩ :=
    NEEDBITS_run_cursor buffers.bits 14 (by decide)
  have noNormal : outcome ≠ .ok () := by
    intro normal
    have enough : 14 ≤ regs.bits.toNat := full normal
    have lengths := congrArg List.length source
    rw [tcStream_length B] at lengths
    omega
  have leave := kinds.resolve_left noNormal
  subst outcome
  have packet := buffers.consume origin.good origin.good rfl (fun _ => rfl) (fun _ => rfl) (by rw [shape]; rfl) cursor bound B
  have count : regs.have_.toNat + used = l.have_.toNat := by rw [B.have_eq, buffers.bits.have_eq, List.length_drop]; omega
  refine ⟨⟨regs, s, h, used, bound, CumulativeParser.table_wait_cut l regs pull, origin, packet, rfl, rfl,
    allocator, credit, dictionary, upper, cursor, count, ?_, ?_, ?_, Or.inl mode, fun _ => source, ?_⟩⟩
  · rw [shape]
  · rw [shape]
  · rw [shape]
  · intro impossible
    rw [mode] at impossible
    cases impossible

/-- Actual accepted count reads followed by a short alphabet produce a
real LENLENS wait. Its received-word equality retains all source bits
across future caller buffers, including already-decoded three-bit fields. -/
theorem table_lens_short_wait
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs credited history : List UInt8} {future payload : List Bool} {L D : List Nat}
    (E : Env c h r zs z s) (origin : DefaultOriginState h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = TABLE) (allocator : DefAlloc z)
    (credit : AdlerCredit z s credited) (dictionary : InflateDictionary h s history)
    (available : 14 ≤ (stream l bs).length)
    (header : ZlibF.Math.InflateHuffmanBodyContext.Header 2 (stream l bs ++ future) L D payload) :
    ∃ pulled tableUsed,
      runX (NEEDBITS 14) l h = .ok ((.ok (), pulled), h) ∧ tableUsed ≤ bs.length ∧ BitInv h pulled (bs.drop tableUsed) ∧
      ((stream (tableRegs pulled) (bs.drop tableUsed)).length < 3 * (tableCounts s pulled.hold).ncode.toNat →
        Nonempty (EarlyHeaderWait c h r zs z s l bs credited history)) := by
  obtain ⟨pulled, tableUsed, pull, tableBound, B, full, fields, valid, nextOrigin, nextPacket, seed,
    hlit, hdist, hclen, r1, r2, first, second, third, nlen, ndist, ncode, cut⟩ :=
    table_header_count_source E origin buffers mode available header
  refine ⟨pulled, tableUsed, pull, tableBound, B, ?_⟩
  intro short
  let nextS := {tableCounts s pulled.hold with «have» := 0, mode := LENLENS}
  let nextH := setI h zs nextS
  have nextE : Env c nextH r zs z nextS := ⟨E.strm, E.st, nextOrigin.good.live.hz, nextOrigin.good.live.hs⟩
  have short0 : (stream (tableRegs pulled) (bs.drop tableUsed)).length < 3 * (nextS.ncode.toNat - nextS.«have».toNat) := by
    simpa only [nextS, UInt32.toNat_zero, Nat.sub_zero] using short
  obtain ⟨regs, state, readUsed, bound, actual, current, packet, readFrame, last, savedLit, savedDist, savedCode, stateMode, progress,
    readCursor, readCount, put, left, out, bits⟩ := lenlens_short_source nextE nextOrigin nextPacket rfl seed short0
  have frame0 : HeaderFrame s nextS := rfl
  have frame := frame0.trans readFrame
  have globalBound : tableUsed + readUsed ≤ bs.length := by simp only [List.length_drop] at bound; omega
  obtain ⟨outcome0, pulled0, used0, pull0, _bound0, inv0, _source0, _count0, _shape0, upper0, _same0, _full0, _wait0, _kinds0, tableCursor⟩ :=
    NEEDBITS_run_cursor buffers.bits 14 (by decide)
  rw [pull] at pull0
  cases pull0
  have sameUsed : used0 = tableUsed := by
    have a := inv0.have_eq
    have b := B.have_eq
    simp only [List.length_drop] at a b
    omega
  subst used0
  have dropBits : (tableRegs pulled).bits.toNat = pulled.bits.toNat - 14 := by
    change (pulled.bits - 14).toNat = _
    exact UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr full)
  have tableSource : stream (tableRegs pulled) (bs.drop tableUsed) = (stream l bs).drop 14 := by
    have readWord := ZlibF.Math.CodeLengthPrefix.read_word first
    have word2 := ZlibF.Math.CodeLengthPrefix.read_word second
    have word3 := ZlibF.Math.CodeLengthPrefix.read_word third
    rw [word2.2, word3.2] at readWord
    rw [readWord.2]
    simp only [List.drop_append, bitsOfNat_length, Nat.sub_self, List.drop_eq_nil_of_le (Nat.le_refl _), List.nil_append]
    rfl
  refine ⟨⟨regs, state, setI h zs state, tableUsed + readUsed, globalBound, ?_, ?_, ?_, frame, last,
    allocator, frame.credit credit, frame.dictionary origin.good dictionary, ?_, ?_, ?_, put.trans fields.1,
    left.trans fields.2.1, out.trans fields.2.2, Or.inr stateMode, ?_, ?_⟩⟩
  · simpa only [nextH, setI_setI] using cut.trans actual
  · simpa only [nextH, setI_setI] using current
  · simpa only [nextH, setI_setI, List.drop_drop] using packet
  · rw [dropBits] at bits
    change pulled.bits.toNat ≤ max l.bits.toNat 21 at upper0
    omega
  · rw [readCursor]
    change inputAdvance pulled.next readUsed = _
    rw [tableCursor, inputAdvance_add]
  · have a := B.have_eq
    have b := buffers.bits.have_eq
    change regs.have_.toNat + readUsed = pulled.have_.toNat at readCount
    simp only [List.length_drop] at a
    omega
  · intro impossible
    rw [stateMode] at impossible
    cases impossible
  · intro _
    refine ⟨natBits (tableRegs pulled).bits.toNat (tableRegs pulled).hold.toNat ++ bytesBits ((bs.drop tableUsed).take readUsed), hlit, hdist, hclen, r1, r2, progress, ?_, first, second, ?_, ?_, ?_, ?_⟩
    · rw [← tableSource]
      rw [← List.drop_drop]
      simp only [stream, List.append_assoc]
      rw [← bytesBits_append, List.take_append_drop]
    · rwa [tableSource] at third
    · rw [savedLit]; exact nlen
    · rw [savedDist]; exact ndist
    · rw [savedCode]; exact ncode

#print axioms table_short_wait
#print axioms table_lens_short_wait
end Zlib.Inflate.Proofs.LaterHeader
