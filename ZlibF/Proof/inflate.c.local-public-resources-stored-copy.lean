import ZlibF.Proof.«inflate.c.local-public-resources-slow-output»
import ZlibF.Proof.«inflate.c.stored-output-exact-frame»

namespace Zlib.Inflate.Local
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- Attach the exact caller interval to the actual stored-copy execution.
The zero-length and stalled cases retain an empty output frame. -/
theorem inflate_COPY_frame_of_run {c : Ctx} {l regs : IL} {h after : Heap} {cutoff : Nat}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8}
    {outcome : Except Ex Unit} {made : Nat}
    (E : Env c h r zs z s) (good : LocalGood h cutoff r zs z s)
    (buffers : DispatchBuffers h r l bs)
    (run : runX (inflate_COPY c) l h = .ok ((outcome, regs), after))
    (count : regs.left.toNat + made = l.left.toNat) :
    BufferFrame h after (fun b => StreamRoot r b ∨ b = zs) [⟨l.put, made⟩] := by
  obtain ⟨dest, output, oo, put, outputGet, write, outputRoom, _, _, _⟩ :=
    callerRange_slow_output good l buffers.output.range buffers.output.nonnull
      buffers.output.count buffers.output.produced
  by_cases done : s.length = 0
  · have actual := inflate_COPY_done E l done
    have same := Except.ok.inj (actual.symm.trans run)
    cases same
    have zero : made = 0 := by change l.left.toNat + made = l.left.toNat at count; omega
    subst made
    exact (fast_terminal_buffer_frame E.hz E.hs [⟨l.put, 0⟩]).1
  · let n := copyAmt s.length l.have_ l.left
    obtain ⟨_, inputBound, outputBound⟩ := copyAmt_le s.length l.have_ l.left
    change n.toNat ≤ l.have_.toNat at inputBound
    change n.toNat ≤ l.left.toNat at outputBound
    by_cases stall : n = 0
    · have actual := inflate_COPY_leave E l done stall
      have same := Except.ok.inj (actual.symm.trans run)
      cases same
      have zero : made = 0 := by change l.left.toNat + made = l.left.toNat at count; omega
      subst made
      rw [put]
      exact BufferFrame.singleton_refl outputGet write
    · have positive : 0 < n.toNat := by
        have nonzero : n.toNat ≠ 0 := fun zero => stall (UInt32.toNat_inj.mp zero)
        omega
      have nonempty : bs ≠ [] := by
        intro empty
        have eq := buffers.bits.have_eq
        rw [empty] at eq
        simp only [List.length_nil] at eq
        omega
      obtain ⟨source, input, io, next, inputGet, inputRoom, _⟩ := buffers.bits.next.resolve_left nonempty
      have inputFit : io + n.toNat ≤ input.size := by
        have eq := buffers.bits.have_eq
        omega
      have outputFit : oo + n.toNat ≤ output.size := by omega
      have separate : dest ≠ source ∨ oo + n.toNat ≤ io ∨ io + n.toNat ≤ oo := by
        have sep := buffers.separate
        rw [next, put] at sep
        rcases sep with empty | empty | different | before | later
        · omega
        · omega
        · exact Or.inl (Ne.symm different)
        · exact Or.inr (Or.inr (by omega))
        · exact Or.inr (Or.inl (by omega))
      have actual := inflate_COPY_views_run E l done stall next put inputGet outputGet write
        inputFit outputFit separate
      have same := Except.ok.inj (actual.symm.trans run)
      cases same
      have madeEq : made = n.toNat := by
        change (l.left - n).toNat + made = l.left.toNat at count
        rw [UInt32.toNat_sub_of_le _ _ outputBound] at count
        omega
      subst made
      rw [put]
      apply output_state_segment_buffer_frame E.hz E.hs outputGet write (size_copyRange ..)
        { s with length := s.length - n }
      intro j outside
      rw [copyRange_getElem? output input oo io n.toNat outputFit inputFit j]
      exact if_neg (by omega)

/-- Complete COPY returns with its exact output prefix frame and the same
produced count as its actual caller cursors and remaining-output field. -/
theorem inflate_COPY_exact_frame {c : Ctx} {l : IL} {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {bs : List UInt8}
    (E : Env c h r zs z s) (good : LocalGood h cutoff r zs z s) (pending : DataPendingInvariant s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = COPY) :
    ∃ outcome regs after state made,
      runX (inflate_COPY c) l h = .ok ((outcome, regs), after) ∧
      LocalGood after cutoff r zs z state ∧ regs.left.toNat + made = l.left.toNat ∧
      regs.put = inputAdvance l.put made ∧
      BufferFrame h after (fun b => StreamRoot r b ∨ b = zs) [⟨l.put, made⟩] := by
  obtain ⟨outcome, regs, after, state, made, _, run, current, _, _, _, _, _, _, _, put, count, _⟩ :=
    inflate_COPY_boundary_frame E good pending buffers mode
  exact ⟨outcome, regs, after, state, made, run, current, count, put,
    inflate_COPY_frame_of_run E good buffers run count⟩

#print axioms inflate_COPY_frame_of_run
#print axioms inflate_COPY_exact_frame
end Zlib.Inflate.Local
