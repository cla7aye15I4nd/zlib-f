import ZlibF.Proof.«inflate.c.whole-stored-v4-legacy»

namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.FunctionalTrailer
set_option autoImplicit false
set_option maxHeartbeats 2200000

/-- BYTEBITS is identity at an actually aligned local bit count. -/
theorem bytebits_aligned_identity (l : IL) (aligned : l.bits.toNat % 8 = 0) : bytebits l = l := by
  have mask : l.bits &&& 7 = 0 := UInt32.toNat_inj.mp ((and7_toNat l).trans aligned)
  simp only [bytebits, mask, UInt32.sub_zero, show (0 : UInt32).toUInt64 = (0 : UInt64) from rfl, UInt64.shiftRight_zero]

/-- The literal initial BYTEBITS is idempotent, so its inline source
normalization does not consume a dispatcher or mainwhile trip. -/
theorem stored_bytebits_source_cut
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8} (E : Env c h r zs z s) (B : BitInv h l bs) (mode : s.mode = STORED) :
    runX (inflate_dispatch c) l h = runX (inflate_dispatch c) (bytebits l) h := by
  obtain ⟨_inv, _source, aligned⟩ := BYTEBITS_inv B
  have idempotent := bytebits_aligned_identity (bytebits l) aligned
  rw [inflate_dispatch_STORED E l mode, inflate_dispatch_STORED E (bytebits l) mode]
  unfold inflate_STORED
  simp only [runX_bind, BYTEBITS_run, idempotent]

/-- Actual inline equality transports a v4 result, including terminals,
without running a new public call or inventing a semantic phase. -/
def DispatchResult4.prepend_inline
    {c : Ctx} {entryHeap h heap : Heap} {r : ZStreamRef} {zs : Nat}
    {entryZ z nextZ : ZStream} {s state : InflateState} {l regs : IL} {base : DataLog} {raw : List UInt8}
    {before : EpochCallCut4 c entryHeap h r zs entryZ z s l base raw}
    {next : EpochCallCut4 c entryHeap heap r zs entryZ nextZ state regs base raw}
    (same : runX (inflate_dispatch c) l h = runX (inflate_dispatch c) regs heap)
    (result : DispatchResult4 next) : DispatchResult4 before := by
  cases result with
  | progress after stream state final actual next => exact .progress after stream state final (same.trans actual) next
  | stopped after stream state final exit actual next => exact .stopped after stream state final exit (same.trans actual) next

/-- A rawStored source point executes the literal alignment prefix before
using the checked aligned STORED/LEN/COPY producer. The discarded bits
are real credited source padding and remain attached to the same block. -/
theorem EpochCallCut4.raw_stored_dispatch
    {c : Ctx} {entryHeap h : Heap} {r : ZStreamRef} {zs : Nat} {entryZ z : ZStream}
    {s : InflateState} {l : IL} {base : DataLog} {raw : List UInt8}
    (before : EpochCallCut4 c entryHeap h r zs entryZ z s l base raw)
    (block : BlockStart (sourceLog (callLog base raw before.facts.used before.facts.emitted)).dictionary)
    (mode : s.mode = STORED) (kind : block.kind = 0)
    (last : s.last = Int32.ofNat block.last) (anchor : before.facts.word = block.prefix)
    (output : (sourceLog (callLog base raw before.facts.used before.facts.emitted)).output = block.before) :
    Nonempty (DispatchResult4 before) := by
  let facts := before.facts
  let regs := bytebits l
  let padding := (natBits l.bits.toNat l.hold.toNat).take (l.bits.toNat % 8)
  have within : l.bits.toNat % 8 ≤ (natBits l.bits.toNat l.hold.toNat).length := by
    rw [natBits_length]
    exact Nat.mod_le _ _
  have paddingSize : padding.length = l.bits.toNat % 8 := by
    simp only [padding, List.length_take, Nat.min_eq_left within]
  have short : padding.length < 8 := by rw [paddingSize]; exact Nat.mod_lt _ (by decide)
  obtain ⟨inv, dropped, aligned⟩ := BYTEBITS_inv facts.buffers.bits
  have held : natBits regs.bits.toNat regs.hold.toNat = (natBits l.bits.toNat l.hold.toNat).drop (l.bits.toNat % 8) := by
    dsimp only [stream] at dropped
    rw [List.drop_append_of_le_length within] at dropped
    exact List.append_cancel_right dropped
  have split : natBits l.bits.toNat l.hold.toNat = padding ++ natBits regs.bits.toNat regs.hold.toNat := by
    rw [held]
    exact (List.take_append_drop _ _).symm
  have credited : CausalInput.Credited (base.input ++ raw.take facts.used) (facts.word ++ padding) regs.bits regs.hold := by
    have source := facts.credited
    change bytesBits (base.input ++ raw.take facts.used) = facts.word ++ natBits l.bits.toNat l.hold.toNat at source
    change bytesBits (base.input ++ raw.take facts.used) = (facts.word ++ padding) ++ natBits regs.bits.toNat regs.hold.toNat
    rw [source, split, List.append_assoc]
  have buffers : DispatchBuffers h r regs (raw.drop facts.used) :=
    ⟨facts.buffers.input,
      ⟨facts.buffers.output.range, facts.buffers.output.nonnull, facts.buffers.output.count, facts.buffers.output.produced⟩,
      facts.buffers.separate, inv⟩
  have small : regs.bits.toNat ≤ 39 := by
    have count := UInt32.toNat_sub_of_le l.bits (l.bits &&& 7) (UInt32.le_iff_toNat_le.mpr (and7_le l))
    change (l.bits - (l.bits &&& 7)).toNat ≤ 39
    rw [count]
    have old := facts.bits
    omega
  have same := stored_bytebits_source_cut facts.env facts.buffers.bits mode
  have main := facts.main.trans (while_inline_cut facts.env facts.origin facts.buffers facts.bits
    facts.env facts.origin buffers small same)
  let phase : SourcePhase (sourceLog (callLog base raw facts.used facts.emitted)) (leaveState s regs) (facts.word ++ padding) :=
    .stored block padding mode kind short aligned last (by rw [anchor]) output
  have checksum : TYPE ≤ s.mode → s.mode ≤ DONE → ∃ count, OutputCredit h z s regs base.output facts.emitted count := by
    intro lower upper
    obtain ⟨count, ledger⟩ := facts.checksum lower upper
    exact ⟨count, ⟨ledger.count, ledger.checksum, ledger.pending, ledger.physical⟩⟩
  have call : CallCut c entryHeap h r zs entryZ z s regs base raw :=
    ⟨facts.used, facts.usedBound, facts.emitted, facts.word ++ padding, facts.env, facts.origin, facts.allocator,
      facts.wrapperOrigins, main, buffers, small, facts.next, facts.haveCount, facts.put, facts.leftCount,
      credited, phase, True.intro, facts.window, facts.physical, checksum⟩
  let prepared : EpochCallCut c entryHeap h r zs entryZ z s regs base raw :=
    ⟨⟨call, ⟨facts.registers.inputStart, facts.registers.noHeaderOutput⟩⟩,
      facts.outputStart, facts.normalRet, facts.allocationOracle⟩
  obtain ⟨result⟩ := prepared.stored_dispatch mode
  let prepared4 := prepared.upgrade (prepared.framed.cut.phase.reversible_of_not_codes (by change s.mode ≠ CODELENS; rw [mode]; decide))
  have lifted : DispatchResult4 prepared4 := stored_result_upgrade prepared4 prepared (Or.inl mode) result
  exact ⟨lifted.prepend_inline same⟩

/-- Complete v4 STORED case: both saved/aligned header reads and the real
pre-BYTEBITS block entry construct their entire actual dispatcher result. -/
theorem EpochCallCut4.stored_dispatch
    {c : Ctx} {entryHeap h : Heap} {r : ZStreamRef} {zs : Nat} {entryZ z : ZStream}
    {s : InflateState} {l : IL} {base : DataLog} {raw : List UInt8}
    (before : EpochCallCut4 c entryHeap h r zs entryZ z s l base raw)
    (mode : s.mode = STORED) : Nonempty (DispatchResult4 before) := by
  cases selected : before.phase
  case legacy phase => exact before.legacy_stored_dispatch phase selected mode
  case rawStored block kind output current last anchor =>
    exact before.raw_stored_dispatch block mode kind last anchor output
  all_goals
    clear selected
    exfalso
    simp_all [leaveState, STORED, MATCH, MEM]

#print axioms bytebits_aligned_identity
#print axioms stored_bytebits_source_cut
#print axioms DispatchResult4.prepend_inline
#print axioms EpochCallCut4.raw_stored_dispatch
#print axioms EpochCallCut4.stored_dispatch
end Zlib.Inflate.Proofs.WholeEpoch
