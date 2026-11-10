import ZlibF.Proof.«inflate.c.stored-entry-path»
import ZlibF.Proof.Format.Deflate

namespace Zlib.Inflate.Proofs.StoredGeneric
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.StoredHistory Zlib.Inflate.Proofs.WrapperGlue
set_option autoImplicit false
/-- Every initial segment of a successful independent byte read has the
same payload prefix and a genuine remaining reader continuation. -/
theorem readBytes_take_continuation {n : Nat} {inp rest : List Bool} {bytes : List UInt8}
    (whole : readBytes n inp = some (bytes, rest)) (m : Nat) (bound : m ≤ n) :
    ∃ middle, readBytes m inp = some (bytes.take m, middle) ∧
      readBytes (n - m) middle = some (bytes.drop m, rest) := by
  induction m generalizing n inp bytes rest with
  | zero => exact ⟨inp, rfl, by simpa only [Nat.sub_zero, List.drop_zero] using whole⟩
  | succ m ih =>
    cases n with
    | zero => omega
    | succ n =>
      cases first : readBits 8 inp with
      | none => simp only [readBytes, first, reduceCtorEq] at whole
      | some pair =>
        rcases pair with ⟨value, next⟩
        cases tail : readBytes n next with
        | none => simp only [readBytes, first, tail, reduceCtorEq] at whole
        | some pair =>
          rcases pair with ⟨more, after⟩
          simp only [readBytes, first, tail, Option.some.injEq, Prod.mk.injEq] at whole
          rcases whole with ⟨rfl, rfl⟩
          obtain ⟨middle, prefixRead, restRead⟩ := ih tail (by omega)
          refine ⟨middle, ?_, ?_⟩
          · simp only [readBytes, first, List.take_succ_cons, prefixRead]
          · simpa only [Nat.succ_sub_succ_eq_sub, List.drop_succ_cons] using restRead

/-- Actual available source bytes are the corresponding independent
stored payload prefix even when the remainder is supplied in future calls. -/
theorem stored_available_prefix
    {bs future payload : List UInt8} {rest : List Bool} {n m : Nat}
    (whole : readBytes n (bytesBits (bs ++ future)) = some (payload, rest))
    (payloadBound : m ≤ n) (available : m ≤ bs.length) :
    bs.take m = payload.take m ∧
      readBytes (n - m) (bytesBits (bs.drop m ++ future)) = some (payload.drop m, rest) := by
  obtain ⟨middle, first, second⟩ := readBytes_take_continuation whole m payloadBound
  have actual := stored_readBytes_prefix bs m available (bytesBits future)
  simp only [bytesBits_eq_bytesToBits] at actual
  rw [bytesBits_append] at first
  have same := Option.some.inj (actual.symm.trans first)
  refine ⟨congrArg Prod.fst same, ?_⟩
  have suffix : bytesBits (bs.drop m) ++ bytesBits future = middle := congrArg Prod.snd same
  rw [← suffix, ← bytesBits_append] at second
  exact second

#print axioms readBytes_take_continuation
#print axioms stored_available_prefix
end Zlib.Inflate.Proofs.StoredGeneric

namespace Zlib.Inflate.Proofs.StoredGeneric
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.StoredHistory Zlib.Inflate.Proofs.WrapperGlue
set_option autoImplicit false
/-- Actual stored-header parsing is compatible with every future byte
suffix, including a split LEN/NLEN. Waiting retains a valid independent
stored body. A complete header derives its real length/complement from
that body and exposes inline COPY_ on arbitrary output capacity. -/
theorem stored_header_phase_consumer
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs future payload dictionary prior credited : List UInt8} {rest : List Bool}
    (E : Env c h r zs z s) (initial : DefaultOriginState h r zs z s)
    (packet : DispatchBuffers h r l bs) (mode : s.mode = STORED) (bits : l.bits.toNat ≤ 39)
    (credit : AdlerCredit z s credited)
    (format : Body dictionary 0 prior (stream l bs ++ bytesBits future) rest (prior ++ payload)) :
    ∃ outcome current used,
      runX (do BYTEBITS; NEEDBITS 32) l h = .ok ((outcome, current), h) ∧
      used ≤ bs.length ∧ BitInv h current (bs.drop used) ∧ current.bits.toNat % 8 = 0 ∧
      (outcome = .error Ex.leave →
        runX (inflate_STORED c) l h = .ok ((.error Ex.leave, current), h) ∧
        Body dictionary 0 prior (stream current (bs.drop used) ++ bytesBits future) rest (prior ++ payload)) ∧
      (outcome = .ok () →
        let ready := {s with length := current.hold.toUInt32 &&& 0xffff, mode := COPY_}
        let after := setI h zs ready
        let regs := {current with hold := 0, bits := 0}
        DefaultOriginState after r zs z ready ∧ DispatchBuffers after r regs (bs.drop used) ∧
        ready.length.toNat = payload.length ∧ AdlerCredit z ready credited ∧
        readBytes payload.length (bytesBits (bs.drop used ++ future)) = some (payload, rest) ∧
        runX (inflate_STORED c) l h =
          runX (if c.flush == Z_TREES then (throw Ex.leave : X Unit) else inflate_COPY_ c) regs after) := by
  obtain ⟨len, nlen, firstRest, dataBits, bytes, readLen, readNlen, complement, readPayload, output⟩ :=
    stored_body_reads format
  have payloadEq : payload = bytes := List.append_cancel_left output
  subst bytes
  have payloadLength : payload.length = len := readBytes_extent readPayload
  let whole := stream l bs
  have totalMod : (whole ++ bytesBits future).length % 8 = whole.length % 8 := by
    rw [List.length_append, bytesBits_length]
    omega
  have alignedWhole : (whole ++ bytesBits future).drop ((whole ++ bytesBits future).length % 8) =
      whole.drop (whole.length % 8) ++ bytesBits future := by
    rw [totalMod, List.drop_append_of_le_length (by omega)]
  change readBits 16 ((whole ++ bytesBits future).drop ((whole ++ bytesBits future).length % 8)) = _ at readLen
  rw [alignedWhole] at readLen
  obtain ⟨outcome, current, used, macroRun, usedBound, inv, source, wait, ready⟩ :=
    stored_STORED_header_prefix E initial packet mode bits
  have alignedBits : current.bits.toNat % 8 = 0 := by
    have lengths := congrArg List.length source
    rw [tcStream_length inv, List.length_drop, tcStream_length packet.bits] at lengths
    simp only [List.length_drop] at lengths
    have originalLength := tcStream_length packet.bits
    omega
  have wholeSource : stream current (bs.drop used) ++ bytesBits future =
      whole.drop (whole.length % 8) ++ bytesBits future := by rw [source]
  refine ⟨outcome, current, used, macroRun, usedBound, inv, alignedBits, ?_, ?_⟩
  · intro waiting
    refine ⟨wait waiting, ?_⟩
    have currentMod : (stream current (bs.drop used) ++ bytesBits future).length % 8 = 0 := by
      rw [List.length_append, tcStream_length inv, bytesBits_length]
      omega
    refine Body.stored (len := len) (nlen := nlen) (r1 := firstRest) (r2 := dataBits)
      (r3 := rest) (bs := payload) ?_ readNlen complement readPayload
    rw [currentMod, List.drop_zero, wholeSource]
    exact readLen
  · intro normal
    obtain ⟨word, actualLen, actualNlen, actualRest, first, second, lenBound, nlenBound,
      accepted, enter⟩ := ready normal
    have firstExtended := stored_readBits_append first (bytesBits future)
    have firstEq := Option.some.inj (readLen.symm.trans firstExtended)
    have lenEq : len = actualLen := congrArg Prod.fst firstEq
    have restEq : firstRest = actualRest ++ bytesBits future := congrArg Prod.snd firstEq
    subst actualLen
    have secondExtended := stored_readBits_append second (bytesBits future)
    rw [restEq] at readNlen
    have secondEq := Option.some.inj (readNlen.symm.trans secondExtended)
    have nlenEq : nlen = actualNlen := congrArg Prod.fst secondEq
    have dataEq : dataBits = bytesBits (bs.drop used) ++ bytesBits future := congrArg Prod.snd secondEq
    subst actualNlen
    obtain ⟨currentJ, currentPacket, actualLength, actualRun⟩ := enter complement
    refine ⟨currentJ, currentPacket, actualLength.trans payloadLength.symm,
      adlerCredit_decode credit (by rfl), ?_, actualRun⟩
    rw [← payloadLength, dataEq, ← bytesBits_append] at readPayload
    exact readPayload

#print axioms stored_header_phase_consumer
end Zlib.Inflate.Proofs.StoredGeneric

namespace Zlib.Inflate.Proofs.StoredGeneric
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.StoredHistory Zlib.Inflate.Proofs.WrapperGlue
set_option autoImplicit false
/-- Arbitrary-capacity inline COPY_ executes the real branch, rather than
assuming a chosen return mode. Its output is the independent stored
payload prefix and its remaining source is a genuine byte-reader suffix.
A complete copy exposes TYPE only on the subsequent zero-COPY dispatch. -/
theorem stored_payload_phase_consumer
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs future payload credited : List UInt8} {rest : List Bool}
    (E : Env c h r zs z s) (initial : DefaultOriginState h r zs z s)
    (packet : DispatchBuffers h r l bs) (mode : s.mode = COPY_)
    (length : s.length.toNat = payload.length) (credit : AdlerCredit z s credited)
    (source : readBytes payload.length (bytesBits (bs ++ future)) = some (payload, rest)) :
    ∃ outcome regs after state made,
      made ≤ bs.length ∧ made ≤ payload.length ∧
      runX (inflate_COPY_ c) l h = .ok ((outcome, regs), after) ∧
      DefaultOriginState after r zs z state ∧ DispatchBuffers after r regs (bs.drop made) ∧
      Bytes after l.put made (payload.take made) ∧
      BufferFrame h after (fun b => StreamRoot r b ∨ b = zs) [⟨l.put, made⟩] ∧
      regs.next = inputAdvance l.next made ∧ regs.have_.toNat + made = l.have_.toNat ∧
      regs.put = inputAdvance l.put made ∧ regs.left.toNat + made = l.left.toNat ∧
      regs.bits = l.bits ∧ regs.hold = l.hold ∧
      state.length.toNat + made = payload.length ∧ AdlerCredit z state credited ∧
      readBytes (payload.length - made) (bytesBits (bs.drop made ++ future)) =
        some (payload.drop made, rest) ∧
      ((outcome = .error Ex.leave ∧ made = 0 ∧ state.mode = COPY) ∨
       (outcome = .ok () ∧ made = 0 ∧ state.mode = TYPE) ∨
       (outcome = .ok () ∧ 0 < made ∧ state.mode = COPY)) := by
  obtain ⟨outcome, regs, after, state, made, bound, run, good, tables, pending,
    currentPacket, sizes, frame, next, haveCount, put, leftCount, bits, hold, kinds, static, _shape⟩ :=
    inflate_COPY_start_boundary_frame E initial.good initial.pending packet mode
  have copied := stored_COPY_start_payload_of_run E initial.good packet run leftCount
  have debt := copied.2.2 state good.live.hs
  have payloadBound : made ≤ payload.length := by omega
  obtain ⟨prefixEq, continuation⟩ := stored_available_prefix source payloadBound bound
  have modes : StoredExitMode state.mode := by
    rcases kinds with ⟨_, _, stateEq⟩ | ⟨_, _, type⟩ | ⟨_, _, copying, _⟩
    · rw [stateEq]; exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (Or.inl type)))
    · exact Or.inr (Or.inr (Or.inl copying))
  have currentJ := initial.toDefaultStateJ.stored_update (Or.inr (Or.inl mode))
    good tables pending frame modes sizes static
  have origin := inflate_dispatch_default_origin_state E initial packet
    ((inflate_dispatch_COPY_start E l mode).trans run) currentJ
  refine ⟨outcome, regs, after, state, made, bound, payloadBound, run, origin, currentPacket,
    ?_, inflate_COPY_start_frame_of_run E initial.good packet run leftCount,
    next, haveCount, put, leftCount, bits, hold, debt.trans length,
    adlerCredit_decode credit frame, continuation, ?_⟩
  · rw [← prefixEq]; exact copied.1
  · rcases kinds with ⟨exit, zero, stateEq⟩ | ⟨exit, zero, type⟩ | ⟨exit, positive, copying, _⟩
    · exact Or.inl ⟨exit, zero, by rw [stateEq]⟩
    · exact Or.inr (Or.inl ⟨exit, zero, type⟩)
    · exact Or.inr (Or.inr ⟨exit, positive, copying⟩)

#print axioms stored_payload_phase_consumer
end Zlib.Inflate.Proofs.StoredGeneric

namespace Zlib.Inflate.Proofs.StoredGeneric
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.StoredHistory Zlib.Inflate.Proofs.WrapperGlue
set_option autoImplicit false
/-- An execution observation, collecting the actual stored-prefix output,
not a callee specification supplied as an assumption. -/
def StoredPayloadObservation (program : X Unit) (h : Heap) (r : ZStreamRef) (zs : Nat)
    (z : ZStream) (l : IL) (bs future payload credited : List UInt8) (rest : List Bool) : Prop :=
  ∃ outcome regs after state made,
    made ≤ bs.length ∧ made ≤ payload.length ∧
    runX program l h = .ok ((outcome, regs), after) ∧
    DefaultOriginState after r zs z state ∧ DispatchBuffers after r regs (bs.drop made) ∧
    Bytes after l.put made (payload.take made) ∧
    BufferFrame h after (fun b => StreamRoot r b ∨ b = zs) [⟨l.put, made⟩] ∧
    regs.next = inputAdvance l.next made ∧ regs.have_.toNat + made = l.have_.toNat ∧
    regs.put = inputAdvance l.put made ∧ regs.left.toNat + made = l.left.toNat ∧
    regs.bits = l.bits ∧ regs.hold = l.hold ∧
    state.length.toNat + made = payload.length ∧ AdlerCredit z state credited ∧
    readBytes (payload.length - made) (bytesBits (bs.drop made ++ future)) =
      some (payload.drop made, rest) ∧
    ((outcome = .error Ex.leave ∧ made = 0 ∧ state.mode = COPY) ∨
     (outcome = .ok () ∧ made = 0 ∧ state.mode = TYPE) ∨
     (outcome = .ok () ∧ 0 < made ∧ state.mode = COPY))

/-- Closed generic STORED consumer. No choice of output capacity or next
mode is required. Incomplete LEN/NLEN waits with the independent body
unchanged. Z_TREES performs its real pre-copy return. Every other flush
executes inline COPY_ and yields exact payload/source/counter facts.
The final equality is an actual source cut for embedding in the ongoing
main while; it does not restart the private loop or claim public return. -/
theorem stored_generic_phase_consumer
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs future payload dictionary prior credited : List UInt8} {rest : List Bool}
    (E : Env c h r zs z s) (initial : DefaultOriginState h r zs z s)
    (packet : DispatchBuffers h r l bs) (mode : s.mode = STORED) (bits : l.bits.toNat ≤ 39)
    (credit : AdlerCredit z s credited)
    (format : Body dictionary 0 prior (stream l bs ++ bytesBits future) rest (prior ++ payload)) :
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
          runX (inflate_STORED c) l h = runX (inflate_COPY_ c) regs after))) := by
  obtain ⟨outcome, current, used, headerRun, usedBound, inv, alignment, waiting, normal⟩ :=
    stored_header_phase_consumer E initial packet mode bits credit format
  refine ⟨outcome, current, used, headerRun, usedBound, inv, alignment, ?_⟩
  have kinds : outcome = .ok () ∨ outcome = .error Ex.leave := by
    obtain ⟨aligned, _, _⟩ := BYTEBITS_inv packet.bits
    obtain ⟨value, regs, count, pull, _, _, _, _, _, _, _, _, _, allowed, _⟩ :=
      NEEDBITS_run_cursor aligned 32 (by decide)
    have actual : runX (do BYTEBITS; NEEDBITS 32) l h = .ok ((value, regs), h) := by
      rw [runX_bind, BYTEBITS_run]
      exact pull
    have eq := congrArg (fun p => p.1.1) (Except.ok.inj (headerRun.symm.trans actual))
    change outcome = value at eq
    rw [eq]
    exact allowed
  rcases kinds with normalKind | waitKind
  · subst outcome
    obtain ⟨currentJ, currentPacket, length, currentCredit, source, sourceCut⟩ := normal rfl
    refine Or.inr ⟨rfl, currentJ, currentPacket, length, currentCredit, source, ?_⟩
    by_cases trees : (c.flush == Z_TREES) = true
    · exact Or.inl ⟨trees, by simpa only [trees, ↓reduceIte, runX_throw] using sourceCut⟩
    · have notTrees : (c.flush == Z_TREES) = false := Bool.eq_false_iff.mpr trees
      have readyEnv : Env c (setI h zs {s with length := current.hold.toUInt32 &&& 0xffff, mode := COPY_}) r zs z
          {s with length := current.hold.toUInt32 &&& 0xffff, mode := COPY_} :=
        ⟨E.strm, E.st, currentJ.good.live.hz, currentJ.good.live.hs⟩
      exact Or.inr ⟨notTrees,
        stored_payload_phase_consumer readyEnv currentJ currentPacket rfl length currentCredit source,
        by simpa only [notTrees, Bool.false_eq_true, ↓reduceIte] using sourceCut⟩
  · exact Or.inl ⟨waitKind, waiting waitKind⟩

#print axioms stored_generic_phase_consumer
end Zlib.Inflate.Proofs.StoredGeneric

namespace Zlib.Inflate.Proofs.StoredGeneric
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.StoredHistory Zlib.Inflate.Proofs.WrapperGlue
set_option autoImplicit false
/-- The header macro's consumed count comes from its actual input cursor.
Alignment and LEN/NLEN reading never move the output cursor or alter the
initial per-call input/output counters. -/
theorem stored_header_actual_metadata
    {h : Heap} {l current : IL} {bs : List UInt8} {used : Nat} {outcome : Except Ex Unit}
    (packet : BitInv h l bs) (bound : used ≤ bs.length)
    (currentPacket : BitInv h current (bs.drop used))
    (actual : runX (do BYTEBITS; NEEDBITS 32) l h = .ok ((outcome, current), h)) :
    current.next = inputAdvance l.next used ∧ current.have_.toNat + used = l.have_.toNat ∧
    current.put = l.put ∧ current.left = l.left ∧ current.in_ = l.in_ ∧ current.out_ = l.out_ ∧
    current.bits.toNat = (bytebits l).bits.toNat + 8 * used := by
  obtain ⟨aligned, _, _⟩ := BYTEBITS_inv packet
  obtain ⟨value, regs, count, pull, countBound, inv, _, bitCount, shape, _, _, _, _, _, cursor⟩ :=
    NEEDBITS_run_cursor aligned 32 (by decide)
  have expected : runX (do BYTEBITS; NEEDBITS 32) l h = .ok ((value, regs), h) := by
    rw [runX_bind, BYTEBITS_run]
    exact pull
  have same : current = regs := congrArg (fun p => p.1.2) (Except.ok.inj (actual.symm.trans expected))
  subst regs
  have countEq : count = used := by
    have a := inv.have_eq
    have b := currentPacket.have_eq
    simp only [List.length_drop] at a b
    omega
  subst count
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, bitCount⟩
  · exact cursor
  · have a := currentPacket.have_eq
    have b := packet.have_eq
    simp only [List.length_drop] at a
    omega
  all_goals rw [shape]; rfl

#print axioms stored_header_actual_metadata
end Zlib.Inflate.Proofs.StoredGeneric
