import ZlibF.Proof.«inflate.c.later-payload-packet»
namespace Zlib.Inflate.Proofs.LaterHeader
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.WrapperGlue Zlib.Inflate.Proofs.HeaderPhaseView
set_option autoImplicit false
set_option maxHeartbeats 2000000

theorem dynamic_kind_future {h : Heap} {l : IL} {bs : List UInt8} {future payload : List Bool}
    (B : BitInv h l bs) (full : 2 ≤ l.bits.toNat)
    (parsed : readBits 2 (stream l bs ++ future) = some (2, payload)) :
    l.hold.toNat % 4 = 2 ∧ stream {l with hold := l.hold >>> 2, bits := l.bits - 2} bs ++ future = payload := by
  have current := readBits_held_stream l bs 2 full
  have extended := CumulativeTableBoundary.readBits_append current future
  obtain ⟨value, rest⟩ := Prod.mk.inj (Option.some.inj (extended.symm.trans parsed))
  obtain ⟨_bits, remaining, _count⟩ := DROPBITS_inv B 2 full (by decide)
  change stream {l with hold := l.hold >>> 2, bits := l.bits - 2} bs = (stream l bs).drop 2 at remaining
  exact ⟨value, by rw [remaining]; exact rest⟩

theorem typed_dynamic_packet_of_actual
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l regs : IL} {bs : List UInt8} {flag : Int32}
    (E : Env c h r zs z s) (origin : DefaultOriginState h r zs z s)
    (packet : DispatchBuffers h r l bs) (modes : s.mode = TYPE ∨ s.mode = TYPEDO)
    (bits : l.bits.toNat ≤ 39)
    (actual : runX (inflate_TYPEDO c) l h =
      .ok ((.ok (), regs), setI h zs {s with last := flag, mode := TABLE})) :
    ∃ used, used ≤ bs.length ∧
      DefaultOriginState (setI h zs {s with last := flag, mode := TABLE}) r zs z
        {s with last := flag, mode := TABLE} ∧
      DispatchBuffers (setI h zs {s with last := flag, mode := TABLE}) r regs (bs.drop used) ∧
      regs.bits.toNat ≤ 39 ∧ regs.next = inputAdvance l.next used ∧
      regs.have_.toNat + used = l.have_.toNat ∧ regs.put = l.put ∧ regs.left = l.left := by
  obtain ⟨outcome, next, after, stream0, state, used, _consumed, usedBound,
    run, good, _tables, _pending, currentPacket, _sizes, nextCursor, haveCount,
    putCursor, leftCount, _bitCount, bitBound, _static, _frame, _streamFrame, _kinds, _count⟩ :=
    inflate_TYPEDO_boundary E origin.good origin.pending packet origin.globals modes
  have same := Except.ok.inj (actual.symm.trans run)
  cases same
  have streamEq : stream0 = z := Option.some.inj
    (good.live.hz.symm.trans (by simpa only [ZStreamRef.get_setI] using E.hz))
  subst stream0
  have stateEq : state = {s with last := flag, mode := TABLE} :=
    Option.some.inj (good.live.hs.symm.trans (setI_istates_same ..))
  subst state
  have format := origin.toDefaultStateJ.block_format modes
  obtain ⟨outcome1, regs1, after1, z1, s1, run1, current, _modes⟩ :=
    inflate_TYPEDO_default_J E origin.toDefaultDecodeJ packet modes format
  have same1 := Except.ok.inj (actual.symm.trans run1)
  cases same1
  have zEq : z1 = z := Option.some.inj (current.good.live.hz.symm.trans good.live.hz)
  subst z1
  have sEq : s1 = {s with last := flag, mode := TABLE} :=
    Option.some.inj (current.good.live.hs.symm.trans good.live.hs)
  subst s1
  have final := origin.toDefaultStateJ.config_update current ⟨rfl, rfl, rfl, rfl⟩ format
  refine ⟨used, usedBound, origin.block_update final rfl (Or.inl ⟨rfl, rfl⟩),
    currentPacket, ?_, nextCursor, haveCount, putCursor, leftCount⟩
  omega

theorem dynamic_tag_source_producer
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs history credited : List UInt8} {future : List Bool} {final : Nat} {middle bodyInput : List Bool}
    (E : Env c h r zs z s) (origin : DefaultOriginState h r zs z s)
    (packet : DispatchBuffers h r l bs) (modes : s.mode = TYPE ∨ s.mode = TYPEDO)
    (last : s.last = 0) (bits : l.bits.toNat ≤ 39) (credit : AdlerCredit z s credited)
    (dictionary : InflateDictionary h s history)
    (first : readBits 1 (stream l bs ++ future) = some (final, middle))
    (second : readBits 2 middle = some (2, bodyInput)) :
    ∃ outcome pulled used,
      runX (NEEDBITS 3) l h = .ok ((outcome, pulled), h) ∧ used ≤ bs.length ∧
      BitInv h pulled (bs.drop used) ∧ pulled.bits.toNat ≤ 39 ∧
      pulled = {l with next := pulled.next, have_ := pulled.have_, hold := pulled.hold, bits := pulled.bits} ∧
      pulled.next = inputAdvance l.next used ∧ pulled.have_.toNat + used = l.have_.toNat ∧
      (outcome = .ok () ∨ outcome = .error Ex.leave) ∧
      (outcome = .error Ex.leave →
        runX (inflate_TYPEDO c) l h = .ok ((.error Ex.leave, pulled), h) ∧
        stream pulled (bs.drop used) = stream l bs) ∧
      (outcome = .ok () → ∃ regs after state,
        runX (inflate_TYPEDO c) l h = .ok ((.ok (), regs), after) ∧
        after = setI h zs state ∧ BlockHeaderFrame s state ∧
        DefaultOriginState after r zs z state ∧ state.mode = TABLE ∧
        state.last = u2i final.toUInt32 ∧ DispatchBuffers after r regs (bs.drop used) ∧
        regs.bits.toNat ≤ 39 ∧ AdlerCredit z state credited ∧
        InflateDictionary after state history ∧
        regs.next = inputAdvance l.next used ∧ regs.have_.toNat + used = l.have_.toNat ∧
        regs.put = l.put ∧ regs.left = l.left ∧ regs.in_ = l.in_ ∧ regs.out_ = l.out_ ∧
        stream regs (bs.drop used) ++ future = bodyInput) := by
  obtain ⟨outcome, pulled, used, pull, usedBound, inv, source, _bitCount, shape,
    _maxBits, _same, full, _wait, kinds, _cursor⟩ := NEEDBITS_run_cursor packet.bits 3 (by decide)
  have pulledBound : pulled.bits.toNat ≤ 39 := by
    change pulled.bits.toNat ≤ max l.bits.toNat 10 at _maxBits
    omega
  have inputCount : pulled.have_.toNat + used = l.have_.toNat := by
    rw [inv.have_eq, packet.bits.have_eq, List.length_drop]
    omega
  refine ⟨outcome, pulled, used, pull, usedBound, inv, pulledBound, shape, _cursor, inputCount, kinds, ?_, ?_⟩
  · intro wait
    exact ⟨inflate_TYPEDO_wait E l pulled last Ex.leave (by rwa [wait] at pull), source⟩
  · intro normal
    have full3 : 3 ≤ pulled.bits.toNat := full normal
    let firstRegs := {pulled with hold := pulled.hold >>> 1, bits := pulled.bits - 1}
    let regs := {firstRegs with hold := firstRegs.hold >>> 2, bits := firstRegs.bits - 2}
    let state := {s with last := u2i (pulled.hold.toUInt32 &&& ((1 : UInt32) <<< 1 - 1)), mode := TABLE}
    let after := setI h zs state
    obtain ⟨firstInv, firstStream, firstBits⟩ := DROPBITS_inv inv 1 (by change 1 ≤ pulled.bits.toNat; omega) (by decide)
    change BitInv h firstRegs (bs.drop used) at firstInv
    change stream firstRegs (bs.drop used) = (stream pulled (bs.drop used)).drop 1 at firstStream
    change firstRegs.bits.toNat = pulled.bits.toNat - 1 at firstBits
    have actualFirst := readBits_held_stream pulled (bs.drop used) 1 (by omega)
    rw [← firstStream, source] at actualFirst
    have firstExtended := CumulativeTableBoundary.readBits_append actualFirst (future)
    have firstEq := Option.some.inj (firstExtended.symm.trans first)
    have flagValue : pulled.hold.toNat % 2 = final := congrArg Prod.fst firstEq
    have suffix : stream firstRegs (bs.drop used) ++ future = middle := congrArg Prod.snd firstEq
    have secondActual : readBits 2 (stream firstRegs (bs.drop used) ++ future) = some (2, bodyInput) := by
      rw [suffix]; exact second
    obtain ⟨kind, remaining⟩ := dynamic_kind_future firstInv (by omega) secondActual
    have finalBound : final < 2 := (ZlibF.Math.CodeLengthPrefix.read_word first).1
    have flagWord : (pulled.hold.toUInt32 &&& ((1 : UInt32) <<< 1 - 1)) = final.toUInt32 := by
      apply UInt32.toNat_inj.mp
      rw [BITS_toNat pulled 1 (by decide)]
      change pulled.hold.toNat % 2 = final % 2 ^ 32
      rw [Nat.mod_eq_of_lt (by omega : final < 2 ^ 32)]
      exact flagValue
    let midState := {s with last := u2i (pulled.hold.toUInt32 &&& ((1 : UInt32) <<< 1 - 1))}
    have middleEnv : Env c (setI h zs midState) r zs z midState :=
      ⟨E.strm, E.st, by simpa only [ZStreamRef.get_setI] using E.hz, setI_istates_same ..⟩
    have actual : runX (inflate_TYPEDO c) l h = .ok ((.ok (), regs), after) := by
      rw [inflate_TYPEDO_head E l pulled last (by rwa [normal] at pull)]
      have tail := typedoTail_table middleEnv firstRegs kind
      simpa only [after, state, midState, regs, firstRegs, setI_setI] using tail
    obtain ⟨used1, bound1, current, currentPacket, nextBits, nextCursor, haveCount, putCursor, leftCount⟩ :=
      typed_dynamic_packet_of_actual E origin packet modes bits actual
    have count : pulled.have_.toNat + used = l.have_.toNat := by
      rw [inv.have_eq, packet.bits.have_eq, List.length_drop]
      omega
    have usedEq : used1 = used := by
      change pulled.have_.toNat + used1 = l.have_.toNat at haveCount
      omega
    subst used1
    refine ⟨regs, after, state, actual, rfl, rfl, current, rfl, ?_, currentPacket,
      nextBits, credit, HeaderFrame.dictionary origin.good (by rfl) dictionary,
      nextCursor, haveCount, putCursor, leftCount, ?_, ?_, remaining⟩
    · change u2i (pulled.hold.toUInt32 &&& ((1 : UInt32) <<< 1 - 1)) = u2i final.toUInt32
      rw [flagWord]
    all_goals dsimp only [regs, firstRegs]; rw [shape]

#print axioms dynamic_kind_future
#print axioms typed_dynamic_packet_of_actual
#print axioms dynamic_tag_source_producer
end Zlib.Inflate.Proofs.LaterHeader
