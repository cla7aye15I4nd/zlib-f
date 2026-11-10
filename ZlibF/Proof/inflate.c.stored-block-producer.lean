import ZlibF.Proof.«inflate.c.stored-generic-phase»
import ZlibF.Proof.«inflate.c.block-source-gate»

namespace Zlib.Inflate.Proofs.StoredBlockProducer
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.StoredHistory Zlib.Inflate.Proofs.WrapperGlue
open Zlib.Inflate.Proofs.StoredGeneric Zlib.Inflate.Proofs.BlockSourceGate
set_option autoImplicit false

/-- A stored selector changes no byte of the saved chronological window. -/
theorem retained_dictionary_block_header {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s state : InflateState} {history : List UInt8}
    (good : Good h r zs z s) (frame : BlockHeaderFrame s state)
    (dictionary : InflateDictionary h s history) :
    InflateDictionary (setI h zs state) state history := by
  rcases dictionary with ⟨zero, empty⟩ | ⟨ref, off, a, window, get, bound, values⟩
  · exact Or.inl ⟨by rw [frame]; exact zero, empty⟩
  · rcases good.inv.win.block with null | ⟨b, bytes, ptr, _get, _ro, _size⟩
    · rw [null] at window
      cases window
    · rw [ptr] at window
      cases window
      refine Or.inr ⟨.blk b, 0, a, ?_, ?_, ?_, ?_⟩
      · rw [frame]; exact ptr
      · simpa only [Space.get, BRef.get_blk, setI] using get
      · rw [frame]; exact bound
      · rw [frame]; exact values

/-- Independent type-zero bits over the real held/current/future stream
produce the actual selector guard and remaining source after DROPBITS2. -/
theorem stored_kind_future
    {h : Heap} {l : IL} {bs : List UInt8} {future payload : List Bool}
    (B : BitInv h l bs) (full : 2 ≤ l.bits.toNat)
    (parsed : readBits 2 (stream l bs ++ future) = some (0, payload)) :
    l.hold.toNat % 4 = 0 ∧
      stream {l with hold := l.hold >>> 2, bits := l.bits - 2} bs ++ future = payload := by
  have current := readBits_held_stream l bs 2 full
  have extended := stored_readBits_append current future
  obtain ⟨value, rest⟩ := Prod.mk.inj (Option.some.inj (extended.symm.trans parsed))
  obtain ⟨_bits, remaining, _count⟩ := DROPBITS_inv B 2 full (by decide)
  change stream {l with hold := l.hold >>> 2, bits := l.bits - 2} bs = (stream l bs).drop 2 at remaining
  exact ⟨value, by rw [remaining]; exact rest⟩

/-- The real type-zero selector produces the shared origin/byte packet
and exact retained logical window. It has no output-capacity or flush
restriction, and preserves the current Adler credit and output cursors. -/
theorem typedo_stored_representation
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs logical credited : List UInt8}
    (E : Env c h r zs z s) (origin : DefaultOriginState h r zs z s)
    (buffers : DispatchBuffers h r l bs) (modes : s.mode = TYPE ∨ s.mode = TYPEDO)
    (full : 2 ≤ l.bits.toNat) (incoming : l.bits.toNat ≤ 39)
    (kind : l.hold.toNat % 4 = 0) (credit : AdlerCredit z s credited)
    (dictionary : InflateDictionary h s (logical.drop (logical.length - 2 ^ s.wbits.toNat))) :
    let regs := {l with hold := l.hold >>> 2, bits := l.bits - 2}
    let state := {s with mode := STORED}
    let after := setI h zs state
    runX (typedoTail c) l h = .ok ((.ok (), regs), after) ∧
    DefaultOriginState after r zs z state ∧ DispatchBuffers after r regs bs ∧
    regs.bits.toNat ≤ 39 ∧ AdlerCredit z state credited ∧
    InflateDictionary after state (logical.drop (logical.length - 2 ^ state.wbits.toNat)) ∧
    regs.next = l.next ∧ regs.put = l.put ∧ regs.have_ = l.have_ ∧
    regs.left = l.left ∧ regs.in_ = l.in_ ∧ regs.out_ = l.out_ ∧
    stream regs bs = (stream l bs).drop 2 := by
  dsimp only
  let regs := {l with hold := l.hold >>> 2, bits := l.bits - 2}
  let state := {s with mode := STORED}
  let after := setI h zs state
  have frame : BlockHeaderFrame s state := rfl
  have pointers : BlockHeaderPointers s state := Or.inl ⟨rfl, rfl⟩
  obtain ⟨bits, remaining, bitCount⟩ := DROPBITS_inv buffers.bits 2 full (by decide)
  obtain ⟨good, packet, sizes⟩ := block_header_packet origin.good buffers frame pointers
    (by change HEAD ≤ STORED ∧ STORED ≤ SYNC; decide) bits (by rfl)
  have tables : DataTableInvariant after state :=
    dataTableInvariant_inactive (by change ¬DataTableMode STORED; unfold DataTableMode; decide)
  have pending := block_header_pending origin.pending frame (Or.inl rfl)
  have format := origin.toDefaultStateJ.block_format modes
  have current := origin.toDefaultDecodeJ.block_update good tables pending frame
    (Or.inr (Or.inr (Or.inl rfl))) format sizes rfl
  have final := origin.toDefaultStateJ.config_update current (by exact ⟨rfl, rfl, rfl, rfl⟩) format
  have finalOrigin := origin.block_update final frame pointers
  have finalDictionary : InflateDictionary after state
      (logical.drop (logical.length - 2 ^ state.wbits.toNat)) := retained_dictionary_block_header origin.good frame dictionary
  refine ⟨typedoTail_stored E l kind, finalOrigin, packet, ?_, credit, finalDictionary,
    rfl, rfl, rfl, rfl, rfl, rfl, remaining⟩
  change (l.bits - 2).toNat ≤ 39
  rw [bitCount]
  omega

#print axioms retained_dictionary_block_header
#print axioms stored_kind_future
#print axioms typedo_stored_representation
end Zlib.Inflate.Proofs.StoredBlockProducer

namespace Zlib.Inflate.Proofs.StoredBlockProducer
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.StoredHistory Zlib.Inflate.Proofs.WrapperGlue
open Zlib.Inflate.Proofs.StoredGeneric Zlib.Inflate.Proofs.BlockSourceGate
set_option autoImplicit false

/-- An observed actual stored TYPEDO source cut obtains its origin and
packet from the proved complete translated TYPEDO boundary. These facts
are conclusions of execution, never a callee contract assumption. -/
theorem typed_stored_packet_of_actual
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l regs : IL} {bs : List UInt8} {flag : Int32}
    (E : Env c h r zs z s) (origin : DefaultOriginState h r zs z s)
    (packet : DispatchBuffers h r l bs) (modes : s.mode = TYPE ∨ s.mode = TYPEDO)
    (bits : l.bits.toNat ≤ 39)
    (actual : runX (inflate_TYPEDO c) l h =
      .ok ((.ok (), regs), setI h zs {s with last := flag, mode := STORED})) :
    ∃ used, used ≤ bs.length ∧
      DefaultOriginState (setI h zs {s with last := flag, mode := STORED}) r zs z
        {s with last := flag, mode := STORED} ∧
      DispatchBuffers (setI h zs {s with last := flag, mode := STORED}) r regs (bs.drop used) ∧
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
  have stateEq : state = {s with last := flag, mode := STORED} :=
    Option.some.inj (good.live.hs.symm.trans (setI_istates_same ..))
  subst state
  have format := origin.toDefaultStateJ.block_format modes
  obtain ⟨outcome1, regs1, after1, z1, s1, run1, current, _modes⟩ :=
    inflate_TYPEDO_default_J E origin.toDefaultDecodeJ packet modes format
  have same1 := Except.ok.inj (actual.symm.trans run1)
  cases same1
  have zEq : z1 = z := Option.some.inj (current.good.live.hz.symm.trans good.live.hz)
  subst z1
  have sEq : s1 = {s with last := flag, mode := STORED} :=
    Option.some.inj (current.good.live.hs.symm.trans good.live.hs)
  subst s1
  have final := origin.toDefaultStateJ.config_update current ⟨rfl, rfl, rfl, rfl⟩ format
  refine ⟨used, usedBound, origin.block_update final rfl (Or.inl ⟨rfl, rfl⟩),
    currentPacket, ?_, nextCursor, haveCount, putCursor, leftCount⟩
  omega

#print axioms typed_stored_packet_of_actual
end Zlib.Inflate.Proofs.StoredBlockProducer

namespace Zlib.Inflate.Proofs.StoredBlockProducer
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.StoredHistory Zlib.Inflate.Proofs.WrapperGlue
open Zlib.Inflate.Proofs.StoredGeneric Zlib.Inflate.Proofs.BlockSourceGate
set_option autoImplicit false

/-- Generic real TYPEDO tag consumption from independent current/future
bits. This covers held bits and every current input size. A split tag
waits without inventing a new source; a complete tag derives the literal
stored selector and produces the actual origin/window/output packet.
The old logical history and Adler credit may contain earlier blocks. -/
theorem stored_tag_source_producer
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs future logical credited : List UInt8} {final : Nat} {middle bodyInput : List Bool}
    (E : Env c h r zs z s) (origin : DefaultOriginState h r zs z s)
    (packet : DispatchBuffers h r l bs) (modes : s.mode = TYPE ∨ s.mode = TYPEDO)
    (last : s.last = 0) (bits : l.bits.toNat ≤ 39) (credit : AdlerCredit z s credited)
    (dictionary : InflateDictionary h s (logical.drop (logical.length - 2 ^ s.wbits.toNat)))
    (first : readBits 1 (stream l bs ++ bytesBits future) = some (final, middle))
    (second : readBits 2 middle = some (0, bodyInput)) :
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
        DefaultOriginState after r zs z state ∧ state.mode = STORED ∧
        state.last = u2i final.toUInt32 ∧ DispatchBuffers after r regs (bs.drop used) ∧
        regs.bits.toNat ≤ 39 ∧ AdlerCredit z state credited ∧
        InflateDictionary after state (logical.drop (logical.length - 2 ^ state.wbits.toNat)) ∧
        regs.next = inputAdvance l.next used ∧ regs.have_.toNat + used = l.have_.toNat ∧
        regs.put = l.put ∧ regs.left = l.left ∧ regs.in_ = l.in_ ∧ regs.out_ = l.out_ ∧
        stream regs (bs.drop used) ++ bytesBits future = bodyInput) := by
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
    let state := {s with last := u2i (pulled.hold.toUInt32 &&& ((1 : UInt32) <<< 1 - 1)), mode := STORED}
    let after := setI h zs state
    obtain ⟨firstInv, firstStream, firstBits⟩ := DROPBITS_inv inv 1 (by change 1 ≤ pulled.bits.toNat; omega) (by decide)
    change BitInv h firstRegs (bs.drop used) at firstInv
    change stream firstRegs (bs.drop used) = (stream pulled (bs.drop used)).drop 1 at firstStream
    change firstRegs.bits.toNat = pulled.bits.toNat - 1 at firstBits
    have actualFirst := readBits_held_stream pulled (bs.drop used) 1 (by omega)
    rw [← firstStream, source] at actualFirst
    have firstExtended := stored_readBits_append actualFirst (bytesBits future)
    have firstEq := Option.some.inj (firstExtended.symm.trans first)
    have flagValue : pulled.hold.toNat % 2 = final := congrArg Prod.fst firstEq
    have suffix : stream firstRegs (bs.drop used) ++ bytesBits future = middle := congrArg Prod.snd firstEq
    have secondActual : readBits 2 (stream firstRegs (bs.drop used) ++ bytesBits future) = some (0, bodyInput) := by
      rw [suffix]; exact second
    obtain ⟨kind, remaining⟩ := stored_kind_future firstInv (by omega) secondActual
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
      have tail := typedoTail_stored middleEnv firstRegs kind
      simpa only [after, state, midState, regs, firstRegs, setI_setI] using tail
    obtain ⟨used1, bound1, current, currentPacket, nextBits, nextCursor, haveCount, putCursor, leftCount⟩ :=
      typed_stored_packet_of_actual E origin packet modes bits actual
    have count : pulled.have_.toNat + used = l.have_.toNat := by
      rw [inv.have_eq, packet.bits.have_eq, List.length_drop]
      omega
    have usedEq : used1 = used := by
      change pulled.have_.toNat + used1 = l.have_.toNat at haveCount
      omega
    subst used1
    refine ⟨regs, after, state, actual, rfl, rfl, current, rfl, ?_, currentPacket,
      nextBits, credit, retained_dictionary_block_header origin.good (by rfl) dictionary,
      nextCursor, haveCount, putCursor, leftCount, ?_, ?_, remaining⟩
    · change u2i (pulled.hold.toUInt32 &&& ((1 : UInt32) <<< 1 - 1)) = u2i final.toUInt32
      rw [flagWord]
    all_goals dsimp only [regs, firstRegs]; rw [shape]

#print axioms stored_tag_source_producer
end Zlib.Inflate.Proofs.StoredBlockProducer

namespace Zlib.Inflate.Proofs.StoredBlockProducer
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.StoredHistory Zlib.Inflate.Proofs.WrapperGlue
open Zlib.Inflate.Proofs.StoredGeneric Zlib.Inflate.Proofs.BlockSourceGate
set_option autoImplicit false

/-- A source-derived entry observation. Its origin, saved window, source
meaning and output cursor all refer to the same actual stored dispatch. -/
def StoredBlockEntry (c : Ctx) (h : Heap) (r : ZStreamRef) (zs : Nat) (z : ZStream)
    (s : InflateState) (l : IL) (bs future dictionary prior payload logical credited : List UInt8)
    (final : Nat) (rest : List Bool) : Prop :=
  ∃ regs after state used,
    used ≤ bs.length ∧ runX (inflate_dispatch c) l h = .ok ((.ok (), regs), after) ∧
    after = setI h zs state ∧ BlockHeaderFrame s state ∧
    DefaultOriginState after r zs z state ∧ state.mode = STORED ∧ state.last = u2i final.toUInt32 ∧
    DispatchBuffers after r regs (bs.drop used) ∧ regs.bits.toNat ≤ 39 ∧ AdlerCredit z state credited ∧
    InflateDictionary after state (logical.drop (logical.length - 2 ^ state.wbits.toNat)) ∧
    regs.next = inputAdvance l.next used ∧ regs.have_.toNat + used = l.have_.toNat ∧
    regs.put = l.put ∧ regs.left = l.left ∧ regs.in_ = l.in_ ∧ regs.out_ = l.out_ ∧
    Body dictionary 0 prior (stream regs (bs.drop used) ++ bytesBits future) rest (prior ++ payload)

/-- Valid independent stored-block bits yield an actual TYPE/TYPEDO
pause, a genuine split-tag wait, or a same-call STORED entry carrying
its full independent Body and actual saved history. The prefix may follow
any number of earlier blocks; neither first-call zero output nor a final
single-block witness is assumed. -/
theorem stored_dispatch_body_source
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs future dictionary prior payload logical credited : List UInt8}
    {final : Nat} {middle bodyInput rest : List Bool}
    (E : Env c h r zs z s) (origin : DefaultOriginState h r zs z s)
    (packet : DispatchBuffers h r l bs) (modes : s.mode = TYPE ∨ s.mode = TYPEDO)
    (last : s.last = 0) (bits : l.bits.toNat ≤ 39) (credit : AdlerCredit z s credited)
    (saved : InflateDictionary h s (logical.drop (logical.length - 2 ^ s.wbits.toNat)))
    (first : readBits 1 (stream l bs ++ bytesBits future) = some (final, middle))
    (second : readBits 2 middle = some (0, bodyInput))
    (body : Body dictionary 0 prior bodyInput rest (prior ++ payload)) :
    (s.mode = TYPE ∧ (c.flush = Z_BLOCK ∨ c.flush = Z_TREES) ∧
      runX (inflate_dispatch c) l h = .ok ((.error Ex.leave, l), h)) ∨
    (∃ pulled used, used ≤ bs.length ∧
      runX (inflate_dispatch c) l h = .ok ((.error Ex.leave, pulled), h) ∧
      DispatchBuffers h r pulled (bs.drop used) ∧ pulled.bits.toNat ≤ 39 ∧
      stream pulled (bs.drop used) = stream l bs ∧
      pulled.next = inputAdvance l.next used ∧ pulled.have_.toNat + used = l.have_.toNat ∧
      pulled.put = l.put ∧ pulled.left = l.left ∧ pulled.in_ = l.in_ ∧ pulled.out_ = l.out_) ∨
    StoredBlockEntry c h r zs z s l bs future dictionary prior payload logical credited final rest := by
  rcases block_dispatch_pause_or_typed E modes with pause | typed
  · exact Or.inl pause
  obtain ⟨outcome, pulled, used, _pull, usedBound, inv, pulledBound, shape, cursor, count, kinds, waiting, normal⟩ :=
    stored_tag_source_producer E origin packet modes last bits credit saved first second
  rcases kinds with proceed | leave
  · obtain ⟨regs, after, state, actual, afterEq, frame, current, mode, flag, currentPacket,
      currentBits, currentCredit, currentSaved, next, haveCount, put, left, in_, out_, source⟩ := normal proceed
    exact Or.inr (Or.inr ⟨regs, after, state, used, usedBound, typed.trans actual, afterEq,
      frame, current, mode, flag, currentPacket, currentBits, currentCredit, currentSaved,
      next, haveCount, put, left, in_, out_, by rwa [source]⟩)
  · obtain ⟨actual, source⟩ := waiting leave
    have currentPacket := packet.consume origin.good origin.good rfl (fun _ => rfl) (fun _ => rfl)
      (by rw [shape]; rfl) cursor usedBound inv
    refine Or.inr (Or.inl ⟨pulled, used, usedBound, typed.trans actual, currentPacket,
      pulledBound, source, cursor, count, ?_, ?_, ?_, ?_⟩)
    all_goals rw [shape]

#print axioms stored_dispatch_body_source
end Zlib.Inflate.Proofs.StoredBlockProducer

namespace Zlib.Inflate.Proofs.StoredBlockProducer
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.StoredHistory Zlib.Inflate.Proofs.WrapperGlue
open Zlib.Inflate.Proofs.StoredGeneric Zlib.Inflate.Proofs.BlockSourceGate
set_option autoImplicit false

/-- The exact actual header/COPY observation produced by the closed
stored consumer. This is a proof-only result package, not a public premise. -/
def StoredHeaderObservation (c : Ctx) (h : Heap) (r : ZStreamRef) (zs : Nat) (z : ZStream)
    (s : InflateState) (l : IL) (bs future dictionary prior payload credited : List UInt8)
    (rest : List Bool) : Prop :=
  ∃ outcome current used,
    runX (do BYTEBITS; NEEDBITS 32) l h = .ok ((outcome, current), h) ∧
    used ≤ bs.length ∧ BitInv h current (bs.drop used) ∧ current.bits.toNat % 8 = 0 ∧
    ((outcome = .error Ex.leave ∧
      runX (inflate_STORED c) l h = .ok ((.error Ex.leave, current), h) ∧
      Body dictionary 0 prior (stream current (bs.drop used) ++ bytesBits future) rest (prior ++ payload)) ∨
     (outcome = .ok () ∧
      let ready := {s with length := current.hold.toUInt32 &&& 0xffff, mode := COPY_}
      let after := setI h zs ready
      let regs := {current with hold := 0, bits := 0}
      DefaultOriginState after r zs z ready ∧ DispatchBuffers after r regs (bs.drop used) ∧
      ready.length.toNat = payload.length ∧ AdlerCredit z ready credited ∧
      readBytes payload.length (bytesBits (bs.drop used ++ future)) = some (payload, rest) ∧
      ((c.flush == Z_TREES) = true ∧
        runX (inflate_STORED c) l h = .ok ((.error Ex.leave, regs), after) ∨
       (c.flush == Z_TREES) = false ∧
        StoredPayloadObservation (inflate_COPY_ c) after r zs z regs (bs.drop used) future payload credited rest ∧
        runX (inflate_STORED c) l h = runX (inflate_COPY_ c) regs after)))

/-- The source-produced TYPE entry continues to real LEN/NLEN parsing
and inline COPY with arbitrary current/future input and output space.
Every intermediate relation is obtained from the independent Body and
actual tag execution. Existing logical history is retained unchanged by
header processing; the copied payload prefix is provided by the result. -/
theorem StoredBlockEntry.header_consumer
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs future dictionary prior payload logical credited : List UInt8}
    {final : Nat} {rest : List Bool}
    (E : Env c h r zs z s)
    (entry : StoredBlockEntry c h r zs z s l bs future dictionary prior payload logical credited final rest) :
    ∃ regs after state used,
      used ≤ bs.length ∧ runX (inflate_dispatch c) l h = .ok ((.ok (), regs), after) ∧
      DefaultOriginState after r zs z state ∧ state.mode = STORED ∧ state.last = u2i final.toUInt32 ∧
      DispatchBuffers after r regs (bs.drop used) ∧ regs.bits.toNat ≤ 39 ∧
      AdlerCredit z state credited ∧
      InflateDictionary after state (logical.drop (logical.length - 2 ^ state.wbits.toNat)) ∧
      regs.next = inputAdvance l.next used ∧ regs.have_.toNat + used = l.have_.toNat ∧
      regs.put = l.put ∧ regs.left = l.left ∧ regs.in_ = l.in_ ∧ regs.out_ = l.out_ ∧
      StoredHeaderObservation c after r zs z state regs (bs.drop used) future dictionary prior payload credited rest := by
  obtain ⟨regs, after, state, used, bound, actual, _heap, _frame, origin, mode, flag,
    packet, bits, credit, saved, next, haveCount, put, left, in_, out_, body⟩ := entry
  have currentEnv : Env c after r zs z state := ⟨E.strm, E.st, origin.good.live.hz, origin.good.live.hs⟩
  exact ⟨regs, after, state, used, bound, actual, origin, mode, flag, packet, bits, credit,
    saved, next, haveCount, put, left, in_, out_,
    stored_generic_phase_consumer currentEnv origin packet mode bits credit body⟩

#print axioms StoredBlockEntry.header_consumer
end Zlib.Inflate.Proofs.StoredBlockProducer
