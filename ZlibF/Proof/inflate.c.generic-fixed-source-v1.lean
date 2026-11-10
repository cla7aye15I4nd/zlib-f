import ZlibF.Proof.«inflate.c.global-payload-representation»
import ZlibF.Proof.«inffixed.h.fast-flags»
import ZlibF.Proof.«inflate.c.block-source-gate»
import ZlibF.Math.InflateHuffmanBodyContext
import ZlibF.Proof.«inflate.c.header-loop-continuation»

namespace Zlib.Inflate.Proofs.FixedBlockProducer
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.FunctionalEpoch
open Zlib.Inflate.Proofs.WrapperGlue Zlib.Inflate.Proofs.BlockSourceGate
set_option autoImplicit false

/-- A complete real fixed selector retains a pre-existing saved window and
all caller cursors, and installs two actual immutable semantic tables. -/
theorem fixed_selector_complete
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs logical credited : List UInt8}
    (E : Env c h r zs z s) (origin : DefaultOriginState h r zs z s)
    (buffers : DispatchBuffers h r l bs) (modes : s.mode = TYPE ∨ s.mode = TYPEDO)
    (full : 2 ≤ l.bits.toNat) (incoming : l.bits.toNat ≤ 39)
    (kind : l.hold.toNat % 4 = 1) (credit : AdlerCredit z s credited)
    (dictionary : InflateDictionary h s (logical.drop (logical.length - 2 ^ s.wbits.toNat))) :
    let regs := {l with hold := l.hold >>> (2 : UInt32).toUInt64, bits := l.bits - 2}
    let state := {fixedState s with mode := LEN_}
    let after := setI h zs state
    runX (typedoTail c) l h =
      .ok ((if c.flush = Z_TREES then .error Ex.leave else .ok (), regs), after) ∧
    PayloadRepresentation after r zs z state regs bs fixedLitLens fixedDistLens logical ∧
    AdlerCredit z state credited ∧
    Zlib.Inftrees.Spec.FastTableFlags.QueryCompatible LENS Zlib.InffixedH.lenfix 0 9 ∧
    Zlib.Inftrees.Spec.FastTableFlags.QueryCompatible DISTS Zlib.InffixedH.distfix 0 5 ∧
    regs.next = l.next ∧ regs.put = l.put ∧ regs.have_ = l.have_ ∧
    regs.left = l.left ∧ regs.in_ = l.in_ ∧ regs.out_ = l.out_ ∧
    stream regs bs = (stream l bs).drop 2 := by
  dsimp only
  obtain ⟨run, payload, next, put, haveEq, left, out, source⟩ :=
    typedo_fixed_representation E origin buffers modes full incoming kind dictionary
  have creditAfter : AdlerCredit z {fixedState s with mode := LEN_} credited := credit
  obtain ⟨fastLen, fastDist⟩ := Zlib.Inftrees.Proofs.fixed_tables_have_fast_leaf_flags
  exact ⟨run, payload, creditAfter, fastLen, fastDist,
    next, put, haveEq, left, rfl, out, source⟩

#print axioms fixed_selector_complete
end Zlib.Inflate.Proofs.FixedBlockProducer

namespace Zlib.Inflate.Proofs.FixedBlockProducer
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.FunctionalEpoch
open Zlib.Inflate.Proofs.WrapperGlue
set_option autoImplicit false

/-- An independent fixed block tag is consumed by the actual translated
TYPEDO path. Every current buffer size is covered: a split tag waits, while
a complete tag installs both fixed tables and preserves the saved window. -/
theorem fixed_tag_source_producer
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs future logical credited : List UInt8} {final : Nat} {middle bodyInput : List Bool}
    (E : Env c h r zs z s) (origin : DefaultOriginState h r zs z s)
    (packet : DispatchBuffers h r l bs) (modes : s.mode = TYPE ∨ s.mode = TYPEDO)
    (last : s.last = 0) (bits : l.bits.toNat ≤ 39) (credit : AdlerCredit z s credited)
    (dictionary : InflateDictionary h s (logical.drop (logical.length - 2 ^ s.wbits.toNat)))
    (first : readBits 1 (stream l bs ++ bytesBits future) = some (final, middle))
    (second : readBits 2 middle = some (1, bodyInput)) :
    ∃ outcome pulled used,
      runX (NEEDBITS 3) l h = .ok ((outcome, pulled), h) ∧ used ≤ bs.length ∧
      BitInv h pulled (bs.drop used) ∧ pulled.bits.toNat ≤ 39 ∧
      pulled = {l with next := pulled.next, have_ := pulled.have_, hold := pulled.hold, bits := pulled.bits} ∧
      pulled.next = inputAdvance l.next used ∧ pulled.have_.toNat + used = l.have_.toNat ∧
      (outcome = .ok () ∨ outcome = .error Ex.leave) ∧
      (outcome = .error Ex.leave →
        runX (inflate_TYPEDO c) l h = .ok ((.error Ex.leave, pulled), h) ∧
        stream pulled (bs.drop used) = stream l bs) ∧
      (outcome = .ok () → ∃ regs after state exit,
        runX (inflate_TYPEDO c) l h = .ok ((exit, regs), after) ∧
        exit = (if c.flush = Z_TREES then .error Ex.leave else .ok ()) ∧
        after = setI h zs state ∧ state = {fixedState {s with last := u2i final.toUInt32} with mode := LEN_} ∧
        PayloadRepresentation after r zs z state regs (bs.drop used) fixedLitLens fixedDistLens logical ∧
        AdlerCredit z state credited ∧
        Zlib.Inftrees.Spec.FastTableFlags.QueryCompatible LENS Zlib.InffixedH.lenfix 0 9 ∧
        Zlib.Inftrees.Spec.FastTableFlags.QueryCompatible DISTS Zlib.InffixedH.distfix 0 5 ∧
        regs.next = inputAdvance l.next used ∧ regs.have_.toNat + used = l.have_.toNat ∧
        regs.put = l.put ∧ regs.left = l.left ∧ regs.in_ = l.in_ ∧ regs.out_ = l.out_ ∧
        stream regs (bs.drop used) ++ bytesBits future = bodyInput) := by
  obtain ⟨outcome, pulled, used, pull, usedBound, inv, source, _bitCount, shape,
    maxBits, _same, full, _wait, kinds, cursor⟩ := NEEDBITS_run_cursor packet.bits 3 (by decide)
  have pulledBound : pulled.bits.toNat ≤ 39 := by
    change pulled.bits.toNat ≤ max l.bits.toNat 10 at maxBits
    omega
  have inputCount : pulled.have_.toNat + used = l.have_.toNat := by
    rw [inv.have_eq, packet.bits.have_eq, List.length_drop]
    omega
  refine ⟨outcome, pulled, used, pull, usedBound, inv, pulledBound, shape, cursor, inputCount, kinds, ?_, ?_⟩
  · intro wait
    exact ⟨inflate_TYPEDO_wait E l pulled last Ex.leave (by rwa [wait] at pull), source⟩
  · intro normal
    have full3 : 3 ≤ pulled.bits.toNat := full normal
    let firstRegs := {pulled with hold := pulled.hold >>> 1, bits := pulled.bits - 1}
    let midState := {s with last := u2i (pulled.hold.toUInt32 &&& ((1 : UInt32) <<< 1 - 1))}
    let heap1 := setI h zs midState
    obtain ⟨firstInv, firstStream, firstBits⟩ := DROPBITS_inv inv 1 (by change 1 ≤ pulled.bits.toNat; omega) (by decide)
    change BitInv h firstRegs (bs.drop used) at firstInv
    change stream firstRegs (bs.drop used) = (stream pulled (bs.drop used)).drop 1 at firstStream
    change firstRegs.bits.toNat = pulled.bits.toNat - 1 at firstBits
    have actualFirst := readBits_held_stream pulled (bs.drop used) 1 (by change 1 ≤ pulled.bits.toNat; omega)
    rw [source] at actualFirst
    have firstExtended := ZlibF.Spec.Proofs.readBits_append 1 (stream l bs)
      (pulled.hold.toNat % 2 ^ 1) ((stream l bs).drop 1) (bytesBits future) actualFirst
    have firstEq := Option.some.inj (firstExtended.symm.trans first)
    have flagValue : pulled.hold.toNat % 2 = final := by simpa using congrArg Prod.fst firstEq
    have suffix : stream firstRegs (bs.drop used) ++ bytesBits future = middle := by
      rw [firstStream, source]
      exact congrArg Prod.snd firstEq
    have secondActual : readBits 2 (stream firstRegs (bs.drop used) ++ bytesBits future) = some (1, bodyInput) := by
      rw [suffix]; exact second
    obtain ⟨kind, remaining⟩ := fixed_kind_future firstInv (by omega) secondActual
    have finalBound : final < 2 := (ZlibF.Math.CodeLengthPrefix.read_word first).1
    have flagWord : (pulled.hold.toUInt32 &&& ((1 : UInt32) <<< 1 - 1)) = final.toUInt32 := by
      apply UInt32.toNat_inj.mp
      rw [BITS_toNat pulled 1 (by decide)]
      change pulled.hold.toNat % 2 = final % 2 ^ 32
      rw [Nat.mod_eq_of_lt (by omega : final < 2 ^ 32)]
      exact flagValue
    have frame : BlockHeaderFrame s midState := rfl
    have pointers : BlockHeaderPointers s midState := Or.inl ⟨rfl, rfl⟩
    obtain ⟨good1, packet1, sizes1⟩ := block_header_packet origin.good
      (packet.consume origin.good origin.good rfl (fun _ => rfl) (fun _ => rfl)
        (by rw [shape]; rfl) cursor usedBound inv)
      frame pointers origin.good.live.mode firstInv (by rfl)
    have pending1 : DataPendingInvariant midState := by
      apply dataPendingInvariant_idle (s := midState) origin.pending.sane
      rcases modes with mode | mode <;> change s.mode ≠ LENEXT ∧ s.mode ≠ DIST ∧ s.mode ≠ DISTEXT ∧ s.mode ≠ MATCH <;> rw [mode] <;> decide
    have inactive : ¬ DataTableMode midState.mode := by
      rcases modes with mode | mode <;> change ¬DataTableMode s.mode <;> rw [mode] <;> unfold DataTableMode <;> decide
    have format := origin.toDefaultStateJ.block_format modes
    have beforeMode : BlockControlMode midState.mode := modes.elim Or.inl (fun mode => Or.inr (Or.inl mode))
    have decoded := origin.toDefaultDecodeJ.block_update good1
      (dataTableInvariant_inactive inactive) pending1 frame beforeMode format sizes1 rfl
    have currentJ := origin.toDefaultStateJ.config_update decoded ⟨rfl, rfl, rfl, rfl⟩ format
    have midOrigin := origin.block_update currentJ frame pointers
    have middleEnv : Env c heap1 r zs z midState :=
      ⟨E.strm, E.st, by simpa only [heap1, ZStreamRef.get_setI] using E.hz, setI_istates_same ..⟩
    have enough1 : 2 ≤ firstRegs.bits.toNat := by rw [firstBits]; omega
    have firstBound : firstRegs.bits.toNat ≤ 39 := by rw [firstBits]; omega
    have midCredit : AdlerCredit z midState credited := credit
    have midDictionary : InflateDictionary heap1 midState
      (logical.drop (logical.length - 2 ^ midState.wbits.toNat)) :=
      dictionary_block_header origin.good frame dictionary
    obtain ⟨tailRun, payload, creditAfter, fastLen, fastDist, next, put,
      haveEq, left, inEq, outEq, rest⟩ :=
      fixed_selector_complete middleEnv midOrigin packet1 modes enough1 firstBound kind midCredit midDictionary
    have actual := inflate_TYPEDO_head E l pulled last (by rwa [normal] at pull)
    have flagState : midState = {s with last := u2i final.toUInt32} := by
      dsimp only [midState]
      rw [flagWord]
    have actualRun : runX (inflate_TYPEDO c) l h =
        .ok (((if c.flush = Z_TREES then .error Ex.leave else .ok ()),
          {firstRegs with hold := firstRegs.hold >>> (2 : UInt32).toUInt64, bits := firstRegs.bits - 2}),
          setI h zs {fixedState midState with mode := LEN_}) := by
      rw [actual]
      simpa only [heap1, setI_setI] using tailRun
    have finalPayload : PayloadRepresentation (setI h zs {fixedState midState with mode := LEN_})
        r zs z {fixedState midState with mode := LEN_}
        {firstRegs with hold := firstRegs.hold >>> (2 : UInt32).toUInt64, bits := firstRegs.bits - 2}
        (bs.drop used) fixedLitLens fixedDistLens logical := by
      simpa only [heap1, setI_setI] using payload
    have nextEq : firstRegs.next = inputAdvance l.next used := by
      change pulled.next = inputAdvance l.next used
      exact cursor
    have haveCount : firstRegs.have_.toNat + used = l.have_.toNat := by
      change pulled.have_.toNat + used = l.have_.toNat
      exact inputCount
    refine ⟨_, _, _, _, actualRun, rfl, rfl, ?_, finalPayload,
      creditAfter, fastLen, fastDist, ?_, ?_, ?_, ?_, ?_, ?_, remaining⟩
    · rw [flagState]
    · exact next.trans nextEq
    · rw [haveEq]
      exact haveCount
    · rw [put]
      change pulled.put = l.put
      rw [shape]
    · rw [left]
      change pulled.left = l.left
      rw [shape]
    · change pulled.in_ = l.in_
      rw [shape]
    · change pulled.out_ = l.out_
      rw [shape]

#print axioms fixed_tag_source_producer
end Zlib.Inflate.Proofs.FixedBlockProducer

namespace Zlib.Inflate.Proofs.FixedBlockProducer
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.FunctionalEpoch
open Zlib.Inflate.Proofs.WrapperGlue Zlib.Inflate.Proofs.BlockSourceGate
set_option autoImplicit false

/-- The actual dispatch either respects TYPE's block pause, waits for a
split tag, or installs the fixed table pair on a valid independent BTYPE=1.
No current-buffer minimum or first-block condition is imposed. -/
theorem fixed_dispatch_source
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs future logical credited : List UInt8} {final : Nat} {middle bodyInput : List Bool}
    (E : Env c h r zs z s) (origin : DefaultOriginState h r zs z s)
    (packet : DispatchBuffers h r l bs) (modes : s.mode = TYPE ∨ s.mode = TYPEDO)
    (last : s.last = 0) (bits : l.bits.toNat ≤ 39) (credit : AdlerCredit z s credited)
    (dictionary : InflateDictionary h s (logical.drop (logical.length - 2 ^ s.wbits.toNat)))
    (first : readBits 1 (stream l bs ++ bytesBits future) = some (final, middle))
    (second : readBits 2 middle = some (1, bodyInput)) :
    (s.mode = TYPE ∧ (c.flush = Z_BLOCK ∨ c.flush = Z_TREES) ∧
      runX (inflate_dispatch c) l h = .ok ((.error Ex.leave, l), h)) ∨
    (∃ pulled used, used ≤ bs.length ∧
      runX (inflate_dispatch c) l h = .ok ((.error Ex.leave, pulled), h) ∧
      DispatchBuffers h r pulled (bs.drop used) ∧ pulled.bits.toNat ≤ 39 ∧
      stream pulled (bs.drop used) = stream l bs ∧
      pulled.next = inputAdvance l.next used ∧ pulled.have_.toNat + used = l.have_.toNat ∧
      pulled.put = l.put ∧ pulled.left = l.left ∧ pulled.in_ = l.in_ ∧ pulled.out_ = l.out_) ∨
    (∃ regs after state exit used, used ≤ bs.length ∧
      runX (inflate_dispatch c) l h = .ok ((exit, regs), after) ∧
      exit = (if c.flush = Z_TREES then .error Ex.leave else .ok ()) ∧
      after = setI h zs state ∧
      state = {fixedState {s with last := u2i final.toUInt32} with mode := LEN_} ∧
      PayloadRepresentation after r zs z state regs (bs.drop used) fixedLitLens fixedDistLens logical ∧
      AdlerCredit z state credited ∧
      Zlib.Inftrees.Spec.FastTableFlags.QueryCompatible LENS Zlib.InffixedH.lenfix 0 9 ∧
      Zlib.Inftrees.Spec.FastTableFlags.QueryCompatible DISTS Zlib.InffixedH.distfix 0 5 ∧
      regs.next = inputAdvance l.next used ∧ regs.have_.toNat + used = l.have_.toNat ∧
      regs.put = l.put ∧ regs.left = l.left ∧ regs.in_ = l.in_ ∧ regs.out_ = l.out_ ∧
      stream regs (bs.drop used) ++ bytesBits future = bodyInput ∧
      ZlibF.Math.InflateHuffmanBodyContext.Header 1 bodyInput fixedLitLens fixedDistLens bodyInput) := by
  rcases block_dispatch_pause_or_typed E modes with pause | typed
  · exact Or.inl pause
  obtain ⟨outcome, pulled, used, _pull, usedBound, inv, pulledBound, shape, cursor, count,
    kinds, waiting, normal⟩ := fixed_tag_source_producer E origin packet modes last bits credit dictionary first second
  rcases kinds with proceed | leave
  · obtain ⟨regs, after, state, exit, actual, exitEq, afterEq, stateEq, payload,
      currentCredit, fastLen, fastDist, next, haveCount, put, left, inEq, outEq, source⟩ := normal proceed
    exact Or.inr (Or.inr ⟨regs, after, state, exit, used, usedBound, typed.trans actual,
      exitEq, afterEq, stateEq, payload, currentCredit, fastLen, fastDist, next,
      haveCount, put, left, inEq, outEq, source,
      ZlibF.Math.InflateHuffmanBodyContext.Header.fixed bodyInput⟩)
  · obtain ⟨actual, source⟩ := waiting leave
    have currentPacket := packet.consume origin.good origin.good rfl (fun _ => rfl) (fun _ => rfl)
      (by rw [shape]; rfl) cursor usedBound inv
    refine Or.inr (Or.inl ⟨pulled, used, usedBound, typed.trans actual, currentPacket,
      pulledBound, source, cursor, count, ?_, ?_, ?_, ?_⟩)
    all_goals rw [shape]

#print axioms fixed_dispatch_source
end Zlib.Inflate.Proofs.FixedBlockProducer

namespace Zlib.Inflate.Proofs.FixedBlockProducer
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.FunctionalEpoch
open Zlib.Inflate.Proofs.WrapperGlue Zlib.Inflate.Proofs.HeaderSourceTrace
set_option autoImplicit false

/-- The same actual original call reaches a fixed payload cut or exits
through a real TYPE/TREES or split-tag leave. The cut is a finite trace
prefix, so its continuation does not reset loop fuel or assume a callee
return. The independent payload remains available to later token proofs. -/
theorem fixed_source_main_cut
    {c : Ctx} {start : Heap} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs future logical credited : List UInt8} {final : Nat} {middle bodyInput : List Bool}
    (E : Env c h r zs z s) (origin : DefaultOriginState h r zs z s)
    (packet : DispatchBuffers h r l bs) (modes : s.mode = TYPE ∨ s.mode = TYPEDO)
    (last : s.last = 0) (bits : l.bits.toNat ≤ 39) (credit : AdlerCredit z s credited)
    (dictionary : InflateDictionary h s (logical.drop (logical.length - 2 ^ s.wbits.toNat)))
    (mainCut : runX (inflate_run c) IL.init start =
      runX (xwhile (pure true) (inflate_dispatch c)) l h)
    (first : readBits 1 (stream l bs ++ bytesBits future) = some (final, middle))
    (second : readBits 2 middle = some (1, bodyInput)) :
    (∃ pulled used, used ≤ bs.length ∧
      runX (inflate_run c) IL.init start = .ok ((.error Ex.leave, pulled), h) ∧
      DispatchBuffers h r pulled (bs.drop used) ∧ pulled.bits.toNat ≤ 39 ∧
      stream pulled (bs.drop used) = stream l bs ∧
      pulled.next = inputAdvance l.next used ∧ pulled.have_.toNat + used = l.have_.toNat ∧
      pulled.put = l.put ∧ pulled.left = l.left ∧ pulled.in_ = l.in_ ∧ pulled.out_ = l.out_) ∨
    (∃ regs after state used, used ≤ bs.length ∧
      runX (inflate_dispatch c) l h = .ok ((.ok (), regs), after) ∧
      runX (inflate_run c) IL.init start =
        runX (xwhile (pure true) (inflate_dispatch c)) regs after ∧
      state = {fixedState {s with last := u2i final.toUInt32} with mode := LEN_} ∧
      PayloadRepresentation after r zs z state regs (bs.drop used) fixedLitLens fixedDistLens logical ∧
      AdlerCredit z state credited ∧
      Zlib.Inftrees.Spec.FastTableFlags.QueryCompatible LENS Zlib.InffixedH.lenfix 0 9 ∧
      Zlib.Inftrees.Spec.FastTableFlags.QueryCompatible DISTS Zlib.InffixedH.distfix 0 5 ∧
      regs.next = inputAdvance l.next used ∧ regs.have_.toNat + used = l.have_.toNat ∧
      regs.put = l.put ∧ regs.left = l.left ∧ regs.in_ = l.in_ ∧ regs.out_ = l.out_ ∧
      stream regs (bs.drop used) ++ bytesBits future = bodyInput ∧
      ZlibF.Math.InflateHuffmanBodyContext.Header 1 bodyInput fixedLitLens fixedDistLens bodyInput) ∨
    (∃ regs after state used, used ≤ bs.length ∧
      runX (inflate_run c) IL.init start = .ok ((.error Ex.leave, regs), after) ∧
      state = {fixedState {s with last := u2i final.toUInt32} with mode := LEN_} ∧
      PayloadRepresentation after r zs z state regs (bs.drop used) fixedLitLens fixedDistLens logical ∧
      AdlerCredit z state credited ∧
      Zlib.Inftrees.Spec.FastTableFlags.QueryCompatible LENS Zlib.InffixedH.lenfix 0 9 ∧
      Zlib.Inftrees.Spec.FastTableFlags.QueryCompatible DISTS Zlib.InffixedH.distfix 0 5 ∧
      stream regs (bs.drop used) ++ bytesBits future = bodyInput) := by
  rcases fixed_dispatch_source E origin packet modes last bits credit dictionary first second with
    ⟨_type, _pause, actual⟩ | waiting | fixed
  · have loop := xwhile_run_chain (inflate_dispatch c) (fun _ => l) (fun _ => h)
      0 (by unfold fuel; decide) Ex.leave l h (by intro j impossible; omega) actual
    exact Or.inl ⟨l, 0, by omega, mainCut.trans loop,
      by simpa only [List.drop_zero] using packet, bits, by simp only [List.drop_zero],
      (inputAdvance_zero l.next).symm, by omega, rfl, rfl, rfl, rfl⟩
  · obtain ⟨pulled, used, bound, actual, currentPacket, currentBits, source,
      next, count, put, left, inEq, outEq⟩ := waiting
    have loop := xwhile_run_chain (inflate_dispatch c) (fun _ => l) (fun _ => h)
      0 (by unfold fuel; decide) Ex.leave pulled h (by intro j impossible; omega) actual
    exact Or.inl ⟨pulled, used, bound, mainCut.trans loop, currentPacket,
      currentBits, source, next, count, put, left, inEq, outEq⟩
  · obtain ⟨regs, after, state, exit, used, bound, actual, exitEq, afterEq,
      stateEq, payload, currentCredit, fastLen, fastDist, next, count, put, left,
      inEq, outEq, source, header⟩ := fixed
    have current : DefaultOriginState after r zs z state := payload.1
    have currentPacket : DispatchBuffers after r regs (bs.drop used) := payload.2.1
    have currentBits : regs.bits.toNat ≤ 39 := payload.2.2.1
    have currentEnv : Env c after r zs z state :=
      ⟨E.strm, E.st, current.good.live.hz, current.good.live.hs⟩
    by_cases trees : c.flush = Z_TREES
    · have leaveRun : runX (inflate_dispatch c) l h = .ok ((.error Ex.leave, regs), after) := by
        simpa only [exitEq, trees, ite_true] using actual
      have loop := xwhile_run_chain (inflate_dispatch c) (fun _ => l) (fun _ => h)
        0 (by unfold fuel; decide) Ex.leave regs after (by intro j impossible; omega) leaveRun
      exact Or.inr (Or.inr ⟨regs, after, state, used, bound, mainCut.trans loop,
        stateEq, payload, currentCredit, fastLen, fastDist, source⟩)
    · have stepRun : runX (inflate_dispatch c) l h = .ok ((.ok (), regs), after) := by
        simpa only [exitEq, trees, ite_false] using actual
      have continuation := loop_prefix_continuation E origin packet bits currentEnv current
        currentPacket currentBits (.step .begin stepRun)
      exact Or.inr (Or.inl ⟨regs, after, state, used, bound, stepRun,
        mainCut.trans continuation, stateEq, payload, currentCredit,
        fastLen, fastDist, next, count, put, left, inEq, outEq, source, header⟩)

#print axioms fixed_source_main_cut
end Zlib.Inflate.Proofs.FixedBlockProducer
