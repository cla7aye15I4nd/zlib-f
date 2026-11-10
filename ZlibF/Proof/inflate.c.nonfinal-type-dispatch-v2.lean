import ZlibF.Proof.«inflate.c.whole-epoch-terminal-dispatch-v4»
import ZlibF.Proof.«inflate.c.generic-fixed-source-v1»
import ZlibF.Proof.«inflate.c.global-fixed-ledger-join»
import ZlibF.Proof.«inflate.c.later-dynamic-entry»
import ZlibF.Proof.«inflate.c.header-code-source-credit»

namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.BlockSourceGate
set_option autoImplicit false

#print axioms CallFacts.advance_main
end Zlib.Inflate.Proofs.WholeEpoch

namespace Zlib.Inflate.Proofs.WholeEpoch
open ZlibF.Spec Zlib.Inflate.Proofs
set_option autoImplicit false

theorem tag_three_word (n : Nat) :
    readBits 1 (natBits 3 n) = some (n % 2, natBits 2 (n / 2)) ∧
    readBits 2 (natBits 2 (n / 2)) = some ((n / 2) % 4, []) ∧
    (natBits 3 n).length = 3 := by
  constructor
  · simp only [natBits, readBits]
    by_cases low : n % 2 = 1 <;> simp [low] <;> omega
  constructor
  · simp only [natBits, readBits]
    by_cases low : n / 2 % 2 = 1 <;> by_cases high : n / 2 / 2 % 2 = 1 <;> simp [low,high] <;> omega
  · exact natBits_length 3 n

#print axioms tag_three_word
end Zlib.Inflate.Proofs.WholeEpoch

namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.FunctionalEpoch
set_option autoImplicit false

/-- NEEDBITS3 does not consume a block bit or touch output. Its actual
pulled bytes extend only the caller input index and held-word ledger. -/
theorem CallFacts.tag_refill_frame
    {c : Ctx} {entryHeap h : Heap} {r : ZStreamRef} {zs : Nat} {entryZ z : ZStream}
    {s : InflateState} {l pulled : IL} {base : DataLog} {raw : List UInt8} {used : Nat}
    (before : CallFacts c entryHeap h r zs entryZ z s l base raw)
    (bound : used ≤ (raw.drop before.used).length)
    (B : BitInv h pulled ((raw.drop before.used).drop used))
    (source : stream pulled ((raw.drop before.used).drop used) = stream l (raw.drop before.used))
    (shape : pulled = {l with next := pulled.next, have_ := pulled.have_, hold := pulled.hold, bits := pulled.bits})
    (cursor : pulled.next = inputAdvance l.next used) :
    let usedTotal := before.used + used
    usedTotal ≤ raw.length ∧
    DispatchBuffers h r pulled (raw.drop usedTotal) ∧
    pulled.next = inputAdvance entryZ.next_in usedTotal ∧
    pulled.have_.toNat + usedTotal = entryZ.avail_in.toNat ∧
    pulled.put = inputAdvance entryZ.next_out before.emitted.length ∧
    pulled.left.toNat + before.emitted.length = entryZ.avail_out.toNat ∧
    pulled.in_ = entryZ.avail_in ∧ pulled.out_ = l.out_ ∧
    CausalInput.Credited (base.input ++ raw.take usedTotal) before.word pulled.bits pulled.hold := by
  dsimp only
  have usedBound : before.used + used ≤ raw.length := by
    have old := before.usedBound
    rw [List.length_drop] at bound
    omega
  have count : pulled.have_.toNat + used = l.have_.toNat := by
    rw [B.have_eq, before.buffers.bits.have_eq, List.length_drop]
    omega
  have packet := before.buffers.consume before.origin.good before.origin.good rfl
    (fun _ => rfl) (fun _ => rfl) (by rw [shape]; rfl) cursor bound B
  have packetTotal : DispatchBuffers h r pulled (raw.drop (before.used + used)) := by
    simpa only [List.drop_drop] using packet
  have nextTotal : pulled.next = inputAdvance entryZ.next_in (before.used + used) := by
    rw [cursor, before.next, inputAdvance_add]
  have haveTotal : pulled.have_.toNat + (before.used + used) = entryZ.avail_in.toNat := by
    have old := before.haveCount
    omega
  have held := held_pull_cut source
  have credited : CausalInput.Credited (base.input ++ raw.take (before.used + used))
      before.word pulled.bits pulled.hold := by
    have sourceCredit : natBits l.bits.toNat l.hold.toNat ++ bytesBits ((raw.drop before.used).take used) =
        [] ++ natBits pulled.bits.toNat pulled.hold.toNat := by
      simpa only [List.nil_append] using held.symm
    have app := before.credited.append sourceCredit
    simpa only [List.take_add, List.append_assoc, List.append_nil] using app
  refine ⟨usedBound, packetTotal, nextTotal, haveTotal, ?_, ?_, ?_, ?_, credited⟩
  · rw [shape]
    exact before.put
  · rw [shape]
    exact before.leftCount
  · rw [shape]
    exact before.registers.inputStart
  · rw [shape]

#print axioms CallFacts.tag_refill_frame
end Zlib.Inflate.Proofs.WholeEpoch

namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs
set_option autoImplicit false

structure TagData (log : DataLog) (s : InflateState) (wire : List Bool) where
  wrapper : Wrapper log.dictionary
  previous : List Bool
  mode : s.mode = TYPE ∨ s.mode = TYPEDO
  last : s.last = 0
  context : BlocksPrefix wrapper.dictionary previous log.output
  anchor : wire = bytesBits wrapper.bytes ++ previous

/-- The only source phase compatible with a non-final TYPE/TYPEDO state
is the original tag phase. This extracts existing provenance, not an
assumed next block kind. -/
theorem SourcePhase4.tag_data {log : DataLog} {s : InflateState} {wire : List Bool}
    (phase : SourcePhase4 log s wire) (mode : s.mode = TYPE ∨ s.mode = TYPEDO)
    (last : s.last = 0) : Nonempty (TagData log s wire) := by
  cases phase with
  | legacy prior =>
    cases prior with
    | tag w word modes final context anchor =>
      exact ⟨⟨w, word, modes, final, context, anchor⟩⟩
    | afterBlocks modes final body => exact False.elim (final last)
    | _ =>
      rcases mode with selected | selected <;>
        simp_all [HEAD, DICTID, DICT, TYPE, TYPEDO, TABLE, LENLENS, CODELENS,
          STORED, COPY_, COPY, LEN_, LEN, LENEXT, DIST, DISTEXT, LIT, MATCH,
          BAD, MEM, DONE]
  | rawStored block stored _ _ _ _ =>
    rcases mode with selected | selected <;> rw [selected] at stored <;> cases stored
  | uncheckedMatch matching _ =>
    rcases mode with selected | selected <;> rw [selected] at matching <;> cases matching
  | memory prior previous _ frame =>
    rw [frame] at mode
    rcases mode with selected | selected <;> change MEM = _ at selected <;> cases selected

#print axioms SourcePhase4.tag_data
end Zlib.Inflate.Proofs.WholeEpoch

namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs
set_option autoImplicit false

/-- A completed real three-bit word extends the existing causal Blocks
prefix with its exact BFINAL and BTYPE; no validity of later bits is used. -/
def TagData.block_start {log : DataLog} {s : InflateState} {wire : List Bool}
    (tagged : TagData log s wire) (heldWord : Nat) : BlockStart log.dictionary :=
  let parsed := tag_three_word heldWord
  { wrapper := tagged.wrapper
    previous := tagged.previous
    before := log.output
    context := tagged.context
    tag := natBits 3 heldWord
    middle := natBits 2 (heldWord / 2)
    last := heldWord % 2
    kind := (heldWord / 2) % 4
    tagSize := parsed.2.2
    finalRead := parsed.1
    typeRead := parsed.2.1
    finalBound := by omega }

#print axioms TagData.block_start
end Zlib.Inflate.Proofs.WholeEpoch

namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs
set_option autoImplicit false

/-- The actual NEEDBITS3 source observer identifies the next block tag
without asking for a selected kind or any future valid stream. -/
theorem CallFacts.actual_tag_observation
    {c : Ctx} {entryHeap h : Heap} {r : ZStreamRef} {zs : Nat} {entryZ z : ZStream}
    {s : InflateState} {l : IL} {base : DataLog} {raw : List UInt8}
    (before : CallFacts c entryHeap h r zs entryZ z s l base raw)
    (tagged : TagData (sourceLog (callLog base raw before.used before.emitted)) (leaveState s l) before.word) :
    ∃ outcome pulled used,
      runX (NEEDBITS 3) l h = .ok ((outcome, pulled), h) ∧
      used ≤ (raw.drop before.used).length ∧
      BitInv h pulled ((raw.drop before.used).drop used) ∧
      pulled.bits.toNat ≤ 39 ∧
      pulled = {l with next := pulled.next, have_ := pulled.have_, hold := pulled.hold, bits := pulled.bits} ∧
      pulled.next = inputAdvance l.next used ∧
      stream pulled ((raw.drop before.used).drop used) = stream l (raw.drop before.used) ∧
      (outcome = .ok () ∨ outcome = .error Ex.leave) ∧
      (outcome = .ok () →
        let tag := tagged.block_start pulled.hold.toNat
        3 ≤ pulled.bits.toNat ∧
        (stream l (raw.drop before.used)).take 3 = tag.tag ∧
        tag.kind = (pulled.hold.toNat / 2) % 4 ∧
        tag.last = pulled.hold.toNat % 2 ∧
        tag.before = base.output ++ before.emitted ∧
        tag.previous = tagged.previous ∧
        tag.wrapper = tagged.wrapper) := by
  obtain ⟨outcome, pulled, used, pull, bound, inv, source, _count, shape, maximum,
    _identity, full, _short, kinds, cursor⟩ := NEEDBITS_run_cursor before.buffers.bits 3 (by decide)
  have small : pulled.bits.toNat ≤ 39 := by
    have initialBound := before.bits
    change pulled.bits.toNat ≤ max l.bits.toNat 10 at maximum
    omega
  refine ⟨outcome, pulled, used, pull, bound, inv, small, shape, cursor, source, kinds, ?_⟩
  intro normal
  dsimp only
  have full3 : 3 ≤ pulled.bits.toNat := full normal
  have headPrefix : (stream l (raw.drop before.used)).take 3 = natBits 3 pulled.hold.toNat := by
    rw [← source, stream, List.take_append_of_le_length (by rw [natBits_length]; exact full3)]
    exact natBits_take _ _ _ full3
  exact ⟨full3, headPrefix, rfl, rfl, rfl, rfl, rfl⟩

#print axioms CallFacts.actual_tag_observation
end Zlib.Inflate.Proofs.WholeEpoch

namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs
set_option autoImplicit false

/-- Literal translation of all four BTYPE cases after the real NEEDBITS3
success. This does not assume a chosen kind or a valid future block. -/
theorem actual_typed_tag_cases
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l pulled : IL} (E : Env c h r zs z s) (last : s.last = 0)
    (pull : runX (NEEDBITS 3) l h = .ok ((.ok (), pulled), h)) :
    let firstRegs := {pulled with hold := pulled.hold >>> 1, bits := pulled.bits - 1}
    let midState := {s with last := u2i (pulled.hold.toUInt32 &&& ((1 : UInt32) <<< 1 - 1))}
    let regs := {firstRegs with hold := firstRegs.hold >>> 2, bits := firstRegs.bits - 2}
    (((pulled.hold.toNat / 2) % 4 = 0 ∧
      runX (inflate_TYPEDO c) l h = .ok ((.ok (), regs), setI h zs {midState with mode := STORED})) ∨
     ((pulled.hold.toNat / 2) % 4 = 1 ∧
      runX (inflate_TYPEDO c) l h = .ok (((if c.flush = Z_TREES then .error Ex.leave else .ok ()), regs), setI h zs {fixedState midState with mode := LEN_})) ∨
     ((pulled.hold.toNat / 2) % 4 = 2 ∧
      runX (inflate_TYPEDO c) l h = .ok ((.ok (), regs), setI h zs {midState with mode := TABLE})) ∨
     ((pulled.hold.toNat / 2) % 4 = 3 ∧
      ∃ i, strTable[i]? = some "invalid block type" ∧
        runX (inflate_TYPEDO c) l h = .ok ((.ok (), regs), badHeap h r zs z midState i))) := by
  dsimp only
  let firstRegs := {pulled with hold := pulled.hold >>> 1, bits := pulled.bits - 1}
  let midState := {s with last := u2i (pulled.hold.toUInt32 &&& ((1 : UInt32) <<< 1 - 1))}
  let regs := {firstRegs with hold := firstRegs.hold >>> 2, bits := firstRegs.bits - 2}
  have env : Env c (setI h zs midState) r zs z midState :=
    ⟨E.strm, E.st, by simpa only [ZStreamRef.get_setI] using E.hz, setI_istates_same ..⟩
  have kind : firstRegs.hold.toNat % 4 = (pulled.hold.toNat / 2) % 4 := by
    change (pulled.hold >>> 1).toNat % 4 = _
    rw [show (1 : UInt64) = (1 : UInt32).toUInt64 from rfl, shr64_toNat pulled.hold 1 (by decide)]
    rfl
  have head := inflate_TYPEDO_head E l pulled last pull
  have bound : (pulled.hold.toNat / 2) % 4 < 4 := Nat.mod_lt _ (by decide)
  by_cases k0 : (pulled.hold.toNat / 2) % 4 = 0
  · left
    refine ⟨k0, ?_⟩
    rw [head]
    have tail := typedoTail_stored env firstRegs (by rw [kind]; exact k0)
    simpa only [firstRegs, midState, regs, setI_setI] using tail
  by_cases k1 : (pulled.hold.toNat / 2) % 4 = 1
  · right; left
    refine ⟨k1, ?_⟩
    rw [head]
    by_cases trees : c.flush = Z_TREES
    · have tail := typedoTail_fixed_trees env firstRegs (by rw [kind]; exact k1) trees
      simpa only [firstRegs, midState, regs, setI_setI, trees, ite_true] using tail
    · have tail := typedoTail_fixed env firstRegs (by rw [kind]; exact k1) trees
      simpa only [firstRegs, midState, regs, setI_setI, trees, ite_false] using tail
  by_cases k2 : (pulled.hold.toNat / 2) % 4 = 2
  · right; right; left
    refine ⟨k2, ?_⟩
    rw [head]
    have tail := typedoTail_table env firstRegs (by rw [kind]; exact k2)
    simpa only [firstRegs, midState, regs, setI_setI] using tail
  · right; right; right
    have k3 : (pulled.hold.toNat / 2) % 4 = 3 := by omega
    obtain ⟨i, string, tail⟩ := typedoTail_bad env firstRegs (by rw [kind]; exact k3)
    refine ⟨k3, i, string, ?_⟩
    rw [head]
    simpa only [firstRegs, midState, regs, badHeap, ZStreamRef.put_setI, setI_setI] using tail

#print axioms actual_typed_tag_cases
end Zlib.Inflate.Proofs.WholeEpoch

namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs
set_option autoImplicit false

/-- A real short BTYPE read exits with the original tag phase; bytes fetched
into the held word are credited, but no tag bit has yet been consumed. -/
theorem EpochCallCut4.nonfinal_tag_wait
    {c : Ctx} {entryHeap h : Heap} {r : ZStreamRef} {zs : Nat} {entryZ z : ZStream}
    {s : InflateState} {l pulled : IL} {base : DataLog} {raw : List UInt8} {used : Nat}
    (before : EpochCallCut4 c entryHeap h r zs entryZ z s l base raw)
    (modes : s.mode = TYPE ∨ s.mode = TYPEDO) (last : s.last = 0)
    (typed : runX (inflate_dispatch c) l h = runX (inflate_TYPEDO c) l h)
    (pull : runX (NEEDBITS 3) l h = .ok ((.error Ex.leave, pulled), h))
    (bound : used ≤ (raw.drop before.facts.used).length)
    (B : BitInv h pulled ((raw.drop before.facts.used).drop used))
    (source : stream pulled ((raw.drop before.facts.used).drop used) =
      stream l (raw.drop before.facts.used))
    (shape : pulled = {l with next := pulled.next, have_ := pulled.have_, hold := pulled.hold, bits := pulled.bits})
    (cursor : pulled.next = inputAdvance l.next used)
    (small : pulled.bits.toNat ≤ 39) : Nonempty (DispatchResult4 before) := by
  let cut := before.facts
  have actual : runX (inflate_dispatch c) l h = .ok ((.error Ex.leave, pulled), h) :=
    typed.trans (inflate_TYPEDO_wait cut.env l pulled last Ex.leave pull)
  have tag := before.phase.tag_data modes last
  obtain ⟨⟨wrapper, word, _mode, _last, context, anchor⟩⟩ := tag
  obtain ⟨usedBound, packet, next, haveCount, put, leftCount, in_, out_, credit⟩ :=
    cut.tag_refill_frame bound B source shape cursor
  let nextPhase : SourcePhase4
      (sourceLog (callLog base raw (cut.used + used) cut.emitted))
      (leaveState s pulled) cut.word :=
    .legacy (.tag wrapper word modes last context anchor)
  let nextFacts : TerminalFacts4 c entryHeap h r zs entryZ z s pulled base raw Ex.leave := {
    used := cut.used + used
    usedBound := usedBound
    emitted := cut.emitted
    word := cut.word
    env := cut.env
    origin := cut.origin
    allocator := cut.allocator
    wrapperOrigins := cut.wrapperOrigins
    main := cut.exit_main actual
    buffers := packet
    bits := small
    next := next
    haveCount := haveCount
    put := put
    leftCount := leftCount
    credited := credit
    window := cut.window
    physical := by
      intro dest off array pointer get
      apply cut.physical dest off array
      · rw [shape] at pointer
        exact pointer
      · exact get
    checksum := by
      intro lower upper
      obtain ⟨count, old⟩ := cut.checksum lower upper
      refine ⟨count, ⟨old.count, old.checksum, ?_, ?_⟩⟩
      · rw [shape]; exact old.pending
      · rw [shape]; exact old.physical
    registers := ⟨by rw [shape]; exact cut.registers.inputStart, by
      intro selected
      rw [shape]
      exact cut.registers.noHeaderOutput selected⟩
    outputStart := by
      intro early
      exact out_.trans (cut.outputStart early)
    normalRet := by
      intro early
      rw [shape]
      exact cut.normalRet (UInt32.le_iff_toNat_le.mpr
        (Nat.le_of_lt (UInt32.lt_iff_toNat_lt.mp early)))
    allocationOracle := cut.allocationOracle
  }
  exact ⟨.stopped h z s pulled Ex.leave actual
    ⟨nextFacts, nextPhase, ⟨trivial, trivial⟩, trivial⟩⟩

#print axioms EpochCallCut4.nonfinal_tag_wait
end Zlib.Inflate.Proofs.WholeEpoch

namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs
set_option autoImplicit false

/-- The three bits consumed by the actual selector are exactly the next
credited source word; this uses the incoming wrapper and block context. -/
theorem TagData.block_start_anchor {log : DataLog} {s : InflateState} {wire : List Bool}
    (tagged : TagData log s wire) (heldWord : Nat) :
    wire ++ (tagged.block_start heldWord).tag = (tagged.block_start heldWord).prefix ∧
    (tagged.block_start heldWord).before = log.output := by
  constructor
  · simpa only [TagData.block_start, BlockStart.prefix, List.append_assoc] using
      congrArg (fun x => x ++ natBits 3 heldWord) tagged.anchor
  · rfl

#print axioms TagData.block_start_anchor
end Zlib.Inflate.Proofs.WholeEpoch

namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.FunctionalEpoch
set_option autoImplicit false

/-- The two real DROPBITS operations consume exactly the selected BFINAL
and BTYPE word. This is the common bit ledger for all four actual branches. -/
theorem tag_drop_credit
    {h : Heap} {pulled : IL} {bs input : List UInt8} {word : List Bool}
    (B : BitInv h pulled bs) (full : 3 ≤ pulled.bits.toNat)
    (credit : CausalInput.Credited input word pulled.bits pulled.hold) :
    let first := {pulled with hold := pulled.hold >>> 1, bits := pulled.bits - 1}
    let regs := {first with hold := first.hold >>> 2, bits := first.bits - 2}
    BitInv h regs bs ∧
    stream regs bs = (stream pulled bs).drop 3 ∧
    CausalInput.Credited input (word ++ natBits 3 pulled.hold.toNat) regs.bits regs.hold ∧
    regs.bits.toNat ≤ pulled.bits.toNat := by
  dsimp only
  let first := {pulled with hold := pulled.hold >>> 1, bits := pulled.bits - 1}
  let regs := {first with hold := first.hold >>> 2, bits := first.bits - 2}
  obtain ⟨firstInv, firstSource, firstBits⟩ := DROPBITS_inv B 1 (by change 1 ≤ pulled.bits.toNat; omega) (by decide)
  change BitInv h first bs at firstInv
  change stream first bs = (stream pulled bs).drop 1 at firstSource
  change first.bits.toNat = pulled.bits.toNat - 1 at firstBits
  obtain ⟨secondInv, secondSource, secondBits⟩ := DROPBITS_inv firstInv 2 (by change 2 ≤ first.bits.toNat; omega) (by decide)
  change BitInv h regs bs at secondInv
  change stream regs bs = (stream first bs).drop 2 at secondSource
  have source : stream regs bs = (stream pulled bs).drop 3 := by
    rw [secondSource, firstSource, List.drop_drop]
  have held := held_drop_cut full source
  have take : (natBits pulled.bits.toNat pulled.hold.toNat).take 3 = natBits 3 pulled.hold.toNat :=
    natBits_take _ _ _ full
  have split : natBits pulled.bits.toNat pulled.hold.toNat =
      natBits 3 pulled.hold.toNat ++ natBits regs.bits.toNat regs.hold.toNat := by
    calc
      natBits pulled.bits.toNat pulled.hold.toNat =
          (natBits pulled.bits.toNat pulled.hold.toNat).take 3 ++
          (natBits pulled.bits.toNat pulled.hold.toNat).drop 3 :=
            (List.take_append_drop 3 _).symm
      _ = _ := by rw [take, ← held]
  have sourceCredit : CausalInput.Credited input
      (word ++ natBits 3 pulled.hold.toNat) regs.bits regs.hold := by
    have old := credit
    change bytesBits input = word ++ natBits pulled.bits.toNat pulled.hold.toNat at old
    change bytesBits input = (word ++ natBits 3 pulled.hold.toNat) ++
      natBits regs.bits.toNat regs.hold.toNat
    rw [old, split, List.append_assoc]
  have small : regs.bits.toNat ≤ pulled.bits.toNat := by
    change (first.bits - 2).toNat ≤ pulled.bits.toNat
    rw [secondBits, firstBits]
    omega
  exact ⟨secondInv, source, sourceCredit, small⟩

#print axioms tag_drop_credit
end Zlib.Inflate.Proofs.WholeEpoch
