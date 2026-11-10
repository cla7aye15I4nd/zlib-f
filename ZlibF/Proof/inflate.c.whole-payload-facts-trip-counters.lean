import ZlibF.Proof.«inflate.c.whole-payload-facts-trip-ledgers»
import ZlibF.Proof.«inflate.c.payload-counter-source»
namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.PayloadCounters
set_option autoImplicit false

/-- All seven actual payload branches preserve the input/output start
counters and return register, including RESTORE/full fast callee/LOAD. -/
theorem PayloadTrip4.counters
    {c : Ctx} {entryHeap h after : Heap} {r : ZStreamRef} {zs : Nat}
    {entryZ z : ZStream} {s : InflateState} {l regs : IL} {base : DataLog} {raw : List UInt8}
    {outcome : Except Ex Unit} {before : CallFacts c entryHeap h r zs entryZ z s l base raw}
    (trip : PayloadTrip4 before after regs outcome) (mode : DataTableMode s.mode) :
    regs.in_ = l.in_ ∧ regs.out_ = l.out_ ∧ regs.ret = l.ret := by
  have E := before.env
  have actual := trip.actual
  have frame : counterFields regs = counterFields l := by
    rcases mode with selected | selected | selected | selected | selected | selected | selected
    · rw [inflate_dispatch_LEN_start E l selected] at actual
      exact counterBaseX_inflate_LEN_ (counterFields l) c l h outcome regs after rfl actual
    · rw [inflate_dispatch_LEN E l selected] at actual
      exact counterBaseX_inflate_LEN (counterFields l) c l h outcome regs after rfl actual
    · rw [inflate_dispatch_LENEXT E l selected] at actual
      exact counterBaseX_inflate_LENEXT (counterFields l) c l h outcome regs after rfl actual
    · rw [inflate_dispatch_DIST E l selected] at actual
      exact counterBaseX_inflate_DIST (counterFields l) c l h outcome regs after rfl actual
    · rw [inflate_dispatch_DISTEXT E l selected] at actual
      exact counterBaseX_inflate_DISTEXT (counterFields l) c l h outcome regs after rfl actual
    · rw [inflate_dispatch_MATCH E l selected] at actual
      exact counterBaseX_inflate_MATCH (counterFields l) c l h outcome regs after rfl actual
    · rw [inflate_dispatch_LIT E l selected] at actual
      exact counterBaseX_inflate_LIT (counterFields l) c l h outcome regs after rfl actual
  simpa only [counterFields, Prod.mk.injEq] using frame

#print axioms PayloadTrip4.counters
end Zlib.Inflate.Proofs.WholeEpoch
