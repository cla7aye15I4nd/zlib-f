import ZlibF.Proof.«inflate.c.later-dynamic-tag»
namespace Zlib.Inflate.Proofs.LaterHeader
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.WrapperGlue Zlib.Inflate.Proofs.BlockSourceGate Zlib.Inflate.Proofs.HeaderSourceTrace
open ZlibF.Math.InflateHuffmanBodyContext
set_option autoImplicit false
set_option maxHeartbeats 2000000

structure DynamicBlockEntry (c : Ctx) (h : Heap) (r : ZStreamRef) (zs : Nat) (z : ZStream)
    (s : InflateState) (l : IL) (bs : List UInt8) (future payload : List Bool) (L D : List Nat)
    (credited history : List UInt8) (final : Nat) where
  regs : IL
  state : InflateState
  used : Nat
  bound : used ≤ bs.length
  origin : DefaultOriginState (setI h zs state) r zs z state
  buffers : DispatchBuffers (setI h zs state) r regs (bs.drop used)
  mode : state.mode = TABLE
  frame : BlockHeaderFrame s state
  last : state.last = u2i final.toUInt32
  finalBound : final < 2
  allocator : DefAlloc z
  credit : AdlerCredit z state credited
  dictionary : InflateDictionary (setI h zs state) state history
  bits : regs.bits.toNat ≤ 39
  cursor : regs.next = inputAdvance l.next used
  count : regs.have_.toNat + used = l.have_.toNat
  put : regs.put = l.put
  left : regs.left = l.left
  in_ : regs.in_ = l.in_
  out : regs.out_ = l.out_
  firstRest : List Bool
  bodyInput : List Bool
  first : readBits 1 (stream l bs ++ future) = some (final, firstRest)
  second : readBits 2 firstRest = some (2, bodyInput)
  source : stream regs (bs.drop used) ++ future = bodyInput
  header : Header 2 (stream regs (bs.drop used) ++ future) L D payload
  actual : runX (inflate_dispatch c) l h = .ok ((.ok (), regs), setI h zs state)

/-- Arbitrary TYPE/TYPEDO input and flush selects its exact documented
pause, a genuine split-tag wait, or an initialized dynamic TABLE source.
The validity premise describes only the header, never a complete payload. -/
theorem dynamic_dispatch_header_source
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs credited history : List UInt8} {future payload middle bodyInput : List Bool} {L D : List Nat} {final : Nat}
    (E : Env c h r zs z s) (origin : DefaultOriginState h r zs z s)
    (buffers : DispatchBuffers h r l bs) (modes : s.mode = TYPE ∨ s.mode = TYPEDO)
    (last : s.last = 0) (bits : l.bits.toNat ≤ 39) (allocator : DefAlloc z)
    (credit : AdlerCredit z s credited) (dictionary : InflateDictionary h s history)
    (first : readBits 1 (stream l bs ++ future) = some (final, middle))
    (second : readBits 2 middle = some (2, bodyInput)) (header : Header 2 bodyInput L D payload) :
    (s.mode = TYPE ∧ (c.flush = Z_BLOCK ∨ c.flush = Z_TREES) ∧ runX (inflate_dispatch c) l h = .ok ((.error Ex.leave, l), h)) ∨
    (∃ regs used, used ≤ bs.length ∧ runX (inflate_dispatch c) l h = .ok ((.error Ex.leave, regs), h) ∧
      DispatchBuffers h r regs (bs.drop used) ∧ regs.bits.toNat ≤ 39 ∧ stream regs (bs.drop used) = stream l bs ∧
      regs.next = inputAdvance l.next used ∧ regs.have_.toNat + used = l.have_.toNat ∧
      regs.put = l.put ∧ regs.left = l.left ∧ regs.in_ = l.in_ ∧ regs.out_ = l.out_) ∨
    Nonempty (DynamicBlockEntry c h r zs z s l bs future payload L D credited history final) := by
  rcases block_dispatch_pause_or_typed E modes with pause | typed
  · exact Or.inl pause
  obtain ⟨outcome, pulled, used, _pull, usedBound, inv, pulledBound, shape, cursor, count, kinds, waiting, normal⟩ :=
    dynamic_tag_source_producer E origin buffers modes last bits credit dictionary first second
  rcases kinds with proceed | leave
  · obtain ⟨regs, after, state, actual, afterEq, frame, current, mode, flag, packet, nextBits, nextCredit, saved,
      next, haveCount, put, left, in_, out_, source⟩ := normal proceed
    subst after
    exact Or.inr (Or.inr ⟨⟨regs, state, used, usedBound, current, packet, mode, frame, flag,
      (ZlibF.Math.CodeLengthPrefix.read_word first).1, allocator, nextCredit, saved, nextBits, next, haveCount,
      put, left, in_, out_, middle, bodyInput, first, second, source, by rwa [source], typed.trans actual⟩⟩)
  · obtain ⟨actual, source⟩ := waiting leave
    have currentPacket := buffers.consume origin.good origin.good rfl (fun _ => rfl) (fun _ => rfl)
      (by rw [shape]; rfl) cursor usedBound inv
    refine Or.inr (Or.inl ⟨pulled, used, usedBound, typed.trans actual, currentPacket, pulledBound, source, cursor, count, ?_, ?_, ?_, ?_⟩)
    all_goals rw [shape]

/-- The source-produced TABLE state is the same real main-loop suffix.
No fuel restart or artificial public TYPE return is introduced. -/
theorem DynamicBlockEntry.main_cut
    {c : Ctx} {h callHeap : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs credited history : List UInt8} {future payload : List Bool} {L D : List Nat} {final : Nat}
    (E : Env c h r zs z s) (origin : DefaultOriginState h r zs z s) (buffers : DispatchBuffers h r l bs)
    (incoming : l.bits.toNat ≤ 39)
    (main : runX (inflate_run c) IL.init callHeap = runX (xwhile (pure true) (inflate_dispatch c)) l h)
    (e : DynamicBlockEntry c h r zs z s l bs future payload L D credited history final) :
    runX (inflate_run c) IL.init callHeap = runX (xwhile (pure true) (inflate_dispatch c)) e.regs (setI h zs e.state) := by
  have currentE : Env c (setI h zs e.state) r zs z e.state := ⟨E.strm, E.st, e.origin.good.live.hz, e.origin.good.live.hs⟩
  exact main.trans (loop_prefix_continuation E origin buffers incoming currentE e.origin e.buffers e.bits (.step .begin e.actual))

theorem final_flag_toInt {final : Nat} (bound : final < 2) : (u2i final.toUInt32).toInt = (final : Int) := by
  have cases : final = 0 ∨ final = 1 := by omega
  rcases cases with rfl | rfl <;> decide

#print axioms dynamic_dispatch_header_source
#print axioms DynamicBlockEntry.main_cut
#print axioms final_flag_toInt
end Zlib.Inflate.Proofs.LaterHeader
