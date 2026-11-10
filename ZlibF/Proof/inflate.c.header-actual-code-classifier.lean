import ZlibF.Proof.«inflate.c.later-header-exhaustive»
import ZlibF.Proof.«inflate.c.code-length-classified»
namespace Zlib.Inflate.Proofs.ActualHeader
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.HeaderPhaseView
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- One actual reader observation, including rejected and partial input.
All heap, state, buffer and branch facts are produced by translated code.
The only semantic alphabet input is actual CODES constructor Contents. -/
structure CodeReadObservation (c : Ctx) (h : Heap) (r : ZStreamRef) (zs : Nat) (z : ZStream)
    (s : InflateState) (l : IL) (bs : List UInt8) (alphabet : List Nat) where
  outcome : Except Ex Unit
  regs : IL
  heap : Heap
  streamZ : ZStream
  state : InflateState
  used : Nat
  bound : used ≤ bs.length
  read : runX (clRead c) l h = .ok ((outcome, regs), heap)
  origin : DefaultOriginState heap r zs streamZ state
  buffers : DispatchBuffers heap r regs (bs.drop used)
  full : ClReadResultFull h r z zs s l bs outcome regs heap
  cursor : regs.next = inputAdvance l.next used
  count : regs.have_.toNat + used = l.have_.toNat
  put : regs.put = l.put
  left : regs.left = l.left
  out : regs.out_ = l.out_
  bits : regs.bits.toNat ≤ max l.bits.toNat 21
  modes : state.mode = CODELENS ∨ state.mode = BAD
  complete : outcome = .ok () → state.mode = BAD ∨ state.«have».toNat = state.nlen.toNat + state.ndist.toNat
  format :
    (state.mode = CODELENS ∧ (∀ length ∈ alphabet, length = 0) ∧
      actualLengthPrefix state = List.replicate state.«have».toNat 0 ∧
      (outcome = .ok () → state.«have».toNat = s.nlen.toNat + s.ndist.toNat)) ∨
    ((state.mode ≠ BAD → ∃ consumed, stream l bs = consumed ++ stream regs (bs.drop used) ∧
      ZlibF.Math.CodeLengthPrefix.Trace alphabet (s.nlen.toNat + s.ndist.toNat) (actualLengthPrefix s) consumed (actualLengthPrefix state)) ∧
      (outcome = .ok () → state.mode ≠ BAD → CodeLens alphabet (s.nlen.toNat + s.ndist.toNat) (actualLengthPrefix s)
        (stream l bs) (stream regs (bs.drop used)) (actualLengthPrefix state)))
  grammar : outcome = .ok () → state.mode = CODELENS →
    ((∀ length ∈ alphabet, length = 0) ∧ actualLengthPrefix state = List.replicate state.«have».toNat 0 ∧
      ∃ i, runX (clTail c) regs heap = .ok ((.ok (), regs), tcBadHeap heap r zs streamZ state i)) ∨
    CodeLens alphabet (s.nlen.toNat + s.ndist.toNat) (actualLengthPrefix s) (stream l bs)
      (stream regs (bs.drop used)) (actualLengthPrefix state)
  source : runX (inflate_CODELENS c) l h = match outcome with
    | .error exit => .ok ((.error exit, regs), heap)
    | .ok () => runX (clTail c) regs heap

/-- Automatic actual CODELENS branch classification with no Header,
CodeLens, valid-future, successful-read or constructor-return premise.
The lower literal count and empty-prefix component are initialized source
facts from real TABLE/CODES and are retained by actual waiting reads. -/
theorem code_read_classifier
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8} {alphabet : List Nat}
    (E : Env c h r zs z s) (origin : DefaultOriginState h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = CODELENS)
    (literalCount : 256 < s.nlen.toNat)
    (contents : Zlib.Inftrees.Proofs.CodeLengthContents s.codes 0 s.lenbits.toNat alphabet)
    (emptyPrefix : (∀ length ∈ alphabet, length = 0) → actualLengthPrefix s = List.replicate s.«have».toNat 0) :
    Nonempty (CodeReadObservation c h r zs z s l bs alphabet) := by
  obtain ⟨outcome, regs, after, state, used, read, full, get, bound, B, format⟩ :=
    clRead_contents_format E.strm E.st E.hz E.hs origin.good.inv.wf.1 mode origin.lengths contents emptyPrefix buffers.bits
  obtain ⟨outcome0, regs0, after0, stream0, state0, used0, bound0, read0, current,
    _config, packet, _sizes, cursor, count, put, left, out, bits, _budget, modes, complete⟩ :=
    clRead_default_state_complete E origin.toDefaultStateJ buffers mode
  rw [read] at read0
  cases read0
  have sameState : state0 = state := Option.some.inj (current.good.live.hs.symm.trans get)
  subst state0
  have sameUsed : used0 = used := by
    have a := packet.bits.have_eq
    have b := B.have_eq
    simp only [List.length_drop] at a b
    omega
  subst used0
  have nextOrigin := origin.of_field_frame current (originFieldFrameX_clRead r c E.strm _ _ _ _ _ read)
  refine ⟨⟨outcome, regs, after, stream0, state, used, bound, read, nextOrigin, packet, full,
    cursor, count, put, left, out, bits, modes, complete, format, ?_, ?_⟩⟩
  · intro normal code
    rcases format with empty | ordinary
    · obtain ⟨_mode, _allzero, zeros, done⟩ := empty
      have haveBound : 256 < state.«have».toNat := by have := done normal; omega
      have env : Env c after r zs stream0 state := ⟨E.strm, E.st, current.good.live.hz, get⟩
      exact Or.inl ⟨_allzero, zeros, clTail_zero_prefix env.strm env.st env.hz env.hs current.good.inv.wf.1 code haveBound zeros⟩
    · exact Or.inr (ordinary.2 normal (by rw [code]; decide))
  · cases outcome with
    | error exit => simpa only [inflate_CODELENS_eq, runX_bind, read]
    | ok unit =>
      cases unit
      simpa only [inflate_CODELENS_eq, runX_bind, read]

#print axioms code_read_classifier
end Zlib.Inflate.Proofs.ActualHeader
