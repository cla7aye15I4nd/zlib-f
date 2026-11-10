import ZlibF.Proof.«inflate.c.header-code-source-trace»
namespace Zlib.Inflate.Proofs.ActualHeader
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs
set_option autoImplicit false
set_option maxHeartbeats 1500000

/-- Actual CODES construction establishes the reader alphabet, and real
read/public/caller events preserve that exact constructor meaning. -/
theorem CodeSourceTrace.contents
    {r : ZStreamRef} {zs : Nat} {h : Heap} {z : ZStream} {s : InflateState} {l : IL}
    {bs : List UInt8} {alphabet : List Nat} (trace : CodeSourceTrace r zs h z s l bs alphabet) :
    Zlib.Inftrees.Proofs.CodeLengthContents s.codes 0 s.lenbits.toNat alphabet := by
  induction trace with
  | seed counts event => exact event.contents
  | read previous event mode ordinary ih =>
    obtain ⟨state0, _used, get, _bound, _bits, _shape, _upper, frame, _rest⟩ := event.full.1
    have stateEq : state0 = event.state := Option.some.inj (get.symm.trans event.origin.good.live.hs)
    rw [← stateEq, frame]
    exact ih
  | resume previous leave publicGet publicStream caller callerGet callerStream loaded inputBytes lit dist values codes rootBits haveEq ih =>
    rw [codes, rootBits]
    exact ih

/-- The separately malformed empty alphabet retains only actual zero
lengths through its real waits. No successful syntax is invented for it. -/
theorem CodeSourceTrace.empty_zero
    {r : ZStreamRef} {zs : Nat} {h : Heap} {z : ZStream} {s : InflateState} {l : IL}
    {bs : List UInt8} {alphabet : List Nat} (trace : CodeSourceTrace r zs h z s l bs alphabet) :
    (∀ length ∈ alphabet, length = 0) → actualLengthPrefix s = List.replicate s.«have».toNat 0 := by
  induction trace with
  | seed counts event =>
    intro _zero
    rw [event.empty, event.written]
    rfl
  | read previous event mode ordinary ih =>
    intro zero
    exact False.elim (ordinary zero)
  | resume previous leave publicGet publicStream caller callerGet callerStream loaded inputBytes lit dist values codes rootBits haveEq ih =>
    intro zero
    rw [values, haveEq]
    exact ih zero

/-- The next actual reader observation is produced from the trace's
constructor provenance. No installed-table or valid-future oracle is an
input to this continuation. -/
theorem CodeSourceTrace.read_observation
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8} {alphabet : List Nat}
    (trace : CodeSourceTrace r zs h z s l bs alphabet)
    (E : Env c h r zs z s) (origin : DefaultOriginState h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = CODELENS) :
    Nonempty (CodeReadObservation c h r zs z s l bs alphabet) := by
  obtain ⟨data⟩ := trace.prefix
  have lower : 256 < s.nlen.toNat := by rw [data.literalCount]; omega
  exact code_read_classifier E origin buffers mode lower trace.contents trace.empty_zero

#print axioms CodeSourceTrace.contents
#print axioms CodeSourceTrace.empty_zero
#print axioms CodeSourceTrace.read_observation
end Zlib.Inflate.Proofs.ActualHeader
