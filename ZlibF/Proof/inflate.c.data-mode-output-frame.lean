import ZlibF.Proof.«inflate.c.pending-output-exact-frame»
import ZlibF.Proof.«inflate.c.pending-dispatch»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Every actual data-mode dispatch has the exact frame of its produced
output prefix. All pending lengths/distances come from the mode clauses
of the established default invariant, not extra public caller assumptions. -/
theorem inflate_dispatch_data_exact_frame
    {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : DataTableMode s.mode) :
    ∃ outcome regs after stream state made,
      runX (inflate_dispatch c) l h = .ok ((outcome, regs), after) ∧
      Good after r zs stream state ∧ regs.left.toNat + made = l.left.toNat ∧
      regs.put = inputAdvance l.put made ∧
      BufferFrame h after (fun b => StreamRoot r b ∨ b = zs) [⟨l.put, made⟩] := by
  have tables := invariant.tables mode
  rcases mode with start | len | lenext | dist | distext | matching | literal
  · obtain ⟨outcome, regs, after, stream, state, made, run, current, count, put, frame⟩ :=
      inflate_LEN_start_exact_frame E invariant buffers start
    exact ⟨outcome, regs, after, stream, state, made,
      (inflate_dispatch_LEN_start E l start).trans run, current, count, put, frame⟩
  · obtain ⟨outcome, regs, after, stream, state, made, run, current, count, put, frame⟩ :=
      inflate_LEN_exact_frame E invariant buffers len
    exact ⟨outcome, regs, after, stream, state, made,
      (inflate_dispatch_LEN E l len).trans run, current, count, put, frame⟩
  · obtain ⟨outcome, regs, after, stream, state, made, run, current, count, put, frame⟩ :=
      inflate_LENEXT_exact_frame E invariant.good tables buffers invariant.pending lenext
    exact ⟨outcome, regs, after, stream, state, made,
      (inflate_dispatch_LENEXT E l lenext).trans run, current, count, put, frame⟩
  · obtain ⟨outcome, regs, after, stream, state, made, run, current, count, put, frame⟩ :=
      inflate_DIST_exact_frame E invariant.good tables buffers invariant.pending dist
    exact ⟨outcome, regs, after, stream, state, made,
      (inflate_dispatch_DIST E l dist).trans run, current, count, put, frame⟩
  · obtain ⟨outcome, regs, after, stream, state, made, run, current, count, put, frame⟩ :=
      inflate_DISTEXT_exact_frame E invariant.good tables buffers invariant.pending distext
    exact ⟨outcome, regs, after, stream, state, made,
      (inflate_dispatch_DISTEXT E l distext).trans run, current, count, put, frame⟩
  · have safe := invariant.pending.matching matching
    obtain ⟨outcome, regs, after, stream, state, made, run, current, count, put, frame⟩ :=
      inflate_MATCH_exact_frame E invariant.good tables buffers matching safe.1 safe.2.2.2
        (by rw [invariant.pending.sane]; decide)
    exact ⟨outcome, regs, after, stream, state, made,
      (inflate_dispatch_MATCH E l matching).trans run, current, count, put, frame⟩
  · obtain ⟨outcome, regs, after, state, made, run, current, count, put, frame⟩ :=
      inflate_LIT_exact_frame E invariant.good tables buffers
    exact ⟨outcome, regs, after, z, state, made,
      (inflate_dispatch_LIT E l literal).trans run, current, count, put, frame⟩

#print axioms inflate_dispatch_data_exact_frame
end Zlib.Inflate.Proofs
