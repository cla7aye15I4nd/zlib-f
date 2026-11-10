import ZlibF.Proof.«inflate.c.whole-epoch-ready-fast-entry»
import ZlibF.Proof.«inflate.c.whole-epoch-fast-observation»
namespace Zlib.Inflate.Proofs.FunctionalEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs
set_option autoImplicit false

/-- The named fast packet belongs to the real LEN dispatcher. RESTORE,
the callee and LOAD are the same translated run, not a callee contract. -/
theorem FastCommittedCallCut.dispatch_run
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {slow : IL} {bs : List UInt8} {L D : List Nat} {dict past current : List UInt8}
    (cut : FastCommittedCallCut c h r zs z s slow bs L D dict past current)
    (E : Env c h r zs z s) (mode : s.mode = LEN)
    (fast : (slow.have_ >= 6 && slow.left >= 258 && slow.bits < 8) = true) :
    runX (inflate_dispatch c) slow h = .ok ((.ok (), cut.loaded), cut.loadedHeap) := by
  rw [inflate_dispatch_LEN E slow mode]
  have execution : Zlib.Inffast.inflate_fast c.strm slow.out_ cut.restored = .ok ((), cut.finished) := by
    rw [cut.envStrm]
    exact cut.callRun
  have prefixRun : runX (inflate_LEN c) slow h = runX (inflateAfterFast c) slow cut.finished := by
    unfold inflate_LEN
    rw [runX_bind, runX_get]
    simp only [fast, ↓reduceIte]
    rw [runX_bind, cut.restoreRun]
    simp only []
    rw [runX_bind, runX_lift_ok execution]
    rfl
  exact prefixRun.trans cut.loadRun

#print axioms FastCommittedCallCut.dispatch_run
end Zlib.Inflate.Proofs.FunctionalEpoch
