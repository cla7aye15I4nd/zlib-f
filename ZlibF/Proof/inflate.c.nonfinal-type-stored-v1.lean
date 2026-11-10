import ZlibF.Proof.«inflate.c.nonfinal-type-normal-factory»

namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs
set_option autoImplicit false

/-- The literal BFINAL bit written by TYPEDO agrees with the independent
three-bit BlockStart, including the UInt32 mask and signed state field. -/
theorem tag_last_eq (pulled : IL) :
    u2i (pulled.hold.toUInt32 &&& ((1 : UInt32) <<< 1 - 1)) =
      Int32.ofNat (pulled.hold.toNat % 2) := by
  unfold u2i
  have bits : (pulled.hold.toUInt32 &&& ((1 : UInt32) <<< 1 - 1)).toNat =
      pulled.hold.toNat % 2 := by
    simpa only [UInt32.toNat_ofNat] using BITS_toNat pulled 1 (by decide)
  rw [bits]
  rfl

#print axioms tag_last_eq
end Zlib.Inflate.Proofs.WholeEpoch

namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs
set_option autoImplicit false

/-- A selected literal BTYPE0 reaches the real pre-BYTEBITS STORED cut.
No alignment, body-length, or future-input assumption is made. -/
theorem EpochCallCut4.nonfinal_tag_stored
    {c : Ctx} {entryHeap h : Heap} {r : ZStreamRef} {zs : Nat} {entryZ z : ZStream}
    {s : InflateState} {l pulled : IL} {base : DataLog} {raw : List UInt8} {used : Nat}
    (before : EpochCallCut4 c entryHeap h r zs entryZ z s l base raw)
    (modes : s.mode = TYPE ∨ s.mode = TYPEDO) (last : s.last = 0)
    (typed : runX (inflate_dispatch c) l h = runX (inflate_TYPEDO c) l h)
    (pull : runX (NEEDBITS 3) l h = .ok ((.ok (), pulled), h))
    (bound : used ≤ (raw.drop before.facts.used).length)
    (B : BitInv h pulled ((raw.drop before.facts.used).drop used))
    (source : stream pulled ((raw.drop before.facts.used).drop used) =
      stream l (raw.drop before.facts.used))
    (shape : pulled = {l with next := pulled.next, have_ := pulled.have_, hold := pulled.hold, bits := pulled.bits})
    (cursor : pulled.next = inputAdvance l.next used)
    (small : pulled.bits.toNat ≤ 39) (full : 3 ≤ pulled.bits.toNat)
    (kind : (pulled.hold.toNat / 2) % 4 = 0) :
    Nonempty (DispatchResult4 before) := by
  let cut := before.facts
  obtain ⟨tagged⟩ := before.phase.tag_data modes last
  let block := tagged.block_start pulled.hold.toNat
  let first := {pulled with hold := pulled.hold >>> 1, bits := pulled.bits - 1}
  let regs := {first with hold := first.hold >>> 2, bits := first.bits - 2}
  let mid := {s with last := u2i (pulled.hold.toUInt32 &&& ((1 : UInt32) <<< 1 - 1))}
  let state := {mid with mode := STORED}
  obtain ⟨run, _rest⟩ :
      runX (inflate_TYPEDO c) l h = .ok ((.ok (), regs), setI h zs state) ∧ True := by
    have all := actual_typed_tag_cases cut.env last pull
    change (_ ∧ _) ∨ (_ ∧ _) ∨ (_ ∧ _) ∨ (_ ∧ _) at all
    rcases all with stored | fixed | dynamic | bad
    · exact ⟨stored.2, trivial⟩
    · exact False.elim (by rcases fixed with ⟨k, _⟩; omega)
    · exact False.elim (by rcases dynamic with ⟨k, _⟩; omega)
    · exact False.elim (by rcases bad with ⟨k, _⟩; omega)
  have actual : runX (inflate_dispatch c) l h = .ok ((.ok (), regs), setI h zs state) := typed.trans run
  obtain ⟨totalBound, packet, nextTotal, countTotal, putTotal, leftTotal, in_, out_, creditPulled⟩ :=
    cut.tag_refill_frame bound B source shape cursor
  obtain ⟨inv, sourceAfter, creditAfter, bitsBound⟩ := tag_drop_credit B full creditPulled
  have frame : BlockHeaderFrame s state := rfl
  have high : DICT < state.mode := by change DICT < STORED; decide
  have regNext : regs.next = inputAdvance l.next used := by change pulled.next = _; exact cursor
  have regCount : regs.have_.toNat + used = l.have_.toNat := by
    change pulled.have_.toNat + used = l.have_.toNat
    have old := cut.haveCount
    omega
  have regSmall : regs.bits.toNat ≤ 39 := by
    change regs.bits.toNat ≤ pulled.bits.toNat at bitsBound
    omega
  have regPut : regs.put = l.put := by change pulled.put = l.put; rw [shape]
  have regLeft : regs.left = l.left := by change pulled.left = l.left; rw [shape]
  have regIn : regs.in_ = l.in_ := by change pulled.in_ = l.in_; rw [shape]
  have regOut : regs.out_ = l.out_ := by change pulled.out_ = l.out_; rw [shape]
  have regRet : regs.ret = l.ret := by change pulled.ret = l.ret; rw [shape]
  obtain ⟨facts, factsUsed, factsEmitted, factsWord⟩ := cut.block_header_no_output modes frame high actual bound regNext regCount
    regPut regLeft regIn regOut regRet regSmall creditAfter
  have blockLast : state.last = Int32.ofNat block.last := by
    change u2i (pulled.hold.toUInt32 &&& ((1 : UInt32) <<< 1 - 1)) =
      Int32.ofNat (pulled.hold.toNat % 2)
    exact tag_last_eq pulled
  have blockAnchor : facts.word = block.prefix := by
    rw [factsWord]
    exact (tagged.block_start_anchor pulled.hold.toNat).1
  have blockOutput : (sourceLog (callLog base raw facts.used facts.emitted)).output = block.before := by
    rw [factsEmitted]
    exact (tagged.block_start_anchor pulled.hold.toNat).2
  let phase : SourcePhase4 (sourceLog (callLog base raw facts.used facts.emitted))
      (leaveState state regs) facts.word :=
    .rawStored block rfl kind blockLast blockAnchor blockOutput
  let nextCut : EpochCallCut4 c entryHeap (setI h zs state) r zs entryZ z state regs base raw :=
    ⟨facts, phase, trivial⟩
  exact ⟨.progress (setI h zs state) z state regs actual nextCut⟩

#print axioms EpochCallCut4.nonfinal_tag_stored
end Zlib.Inflate.Proofs.WholeEpoch
