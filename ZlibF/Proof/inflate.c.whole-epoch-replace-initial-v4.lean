import ZlibF.Proof.«inflate.c.whole-epoch-dispatch-interface-v4»

namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs
set_option autoImplicit false

/-- Inline source normalization changes no mainwhile trip. A produced
result transfers using the exact same first dispatcher execution and the
same original entry heap, rather than an assumed functional contract. -/
theorem DispatchResult4.replace_initial
    {c : Ctx} {entryHeap h heap : Heap} {r : ZStreamRef} {zs : Nat}
    {entryZ z stream : ZStream} {s state : InflateState} {l regs : IL}
    {base : DataLog} {raw : List UInt8}
    {before : EpochCallCut4 c entryHeap h r zs entryZ z s l base raw}
    {next : EpochCallCut4 c entryHeap heap r zs entryZ stream state regs base raw}
    (result : DispatchResult4 next)
    (same : runX (inflate_dispatch c) l h = runX (inflate_dispatch c) regs heap) :
    Nonempty (DispatchResult4 before) := by
  cases result with
  | progress after current final locals actual cut =>
    exact ⟨.progress after current final locals (same.trans actual) cut⟩
  | stopped after current final locals exit actual cut =>
    exact ⟨.stopped after current final locals exit (same.trans actual) cut⟩

#print axioms DispatchResult4.replace_initial
end Zlib.Inflate.Proofs.WholeEpoch
