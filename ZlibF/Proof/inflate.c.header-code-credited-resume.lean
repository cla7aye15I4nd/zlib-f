import ZlibF.Proof.«inflate.c.header-code-trace-progress»
import ZlibF.Proof.«inflate.c.global-credited-input-rebuffer»
namespace Zlib.Inflate.Proofs.ActualHeader
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs
set_option autoImplicit false
set_option maxHeartbeats 1500000

/-- Resume the actual header trace using the shared exact public input
ledger. Rebuffer's private-state and credited-word preservation are
proved by CausalInput; LOAD is executed on that same returned heap. -/
theorem CodeSourceTrace.resume_credited
    {c : Ctx} {h publicHeap callerHeap : Heap} {r : ZStreamRef} {zs : Nat}
    {z callerZ : ZStream} {s : InflateState} {l : IL} {bs input : List UInt8}
    {alphabet : List Nat} {rc : Int32} {log : DataLog} {word : List Bool}
    (trace : CodeSourceTrace r zs h z s l bs alphabet)
    (root : c.strm = some r) (stateRoot : c.st = some (.tab zs))
    (leave : C.run (inflate_leave c l) h = .ok (rc, publicHeap))
    (source : CausalInput.AtPublic publicHeap r log word) (owner : source.zs = zs)
    (lit : source.state.nlen = s.nlen) (dist : source.state.ndist = s.ndist)
    (values : actualLengthPrefix source.state = actualLengthPrefix s)
    (codes : source.state.codes = s.codes) (rootBits : source.state.lenbits = s.lenbits)
    (haveEq : source.state.«have» = s.«have»)
    (edit : Rebuffer publicHeap callerHeap r) (streamGet : r.get callerHeap = some callerZ)
    (inputBytes : Bytes callerHeap callerZ.next_in callerZ.avail_in.toNat input) :
    ∃ next : CausalInput.AtPublic callerHeap r log word,
      next.zs = zs ∧ next.state = source.state ∧ next.z = callerZ ∧
      ∃ regs, runX (LOAD c.strm c.st) IL.init callerHeap = .ok ((.ok (), regs), callerHeap) ∧
        CodeSourceTrace r zs callerHeap callerZ source.state regs input alphabet := by
  obtain ⟨next, sameOwner, sameState, _streamFields⟩ := source.rebuffer_same edit
  have nextOwner : next.zs = zs := sameOwner.trans owner
  have nextZ : next.z = callerZ := Option.some.inj (next.good.live.hz.symm.trans streamGet)
  have callerGood : Good callerHeap r zs callerZ source.state := by
    have good := next.good
    rw [nextOwner, sameState, nextZ] at good
    exact good
  have publicGet : publicHeap.istates zs = some source.state := by
    rw [← owner]; exact source.good.live.hs
  have env : Env c callerHeap r zs callerZ source.state := ⟨root, stateRoot, streamGet, callerGood.live.hs⟩
  let regs := {IL.init with put := callerZ.next_out, left := callerZ.avail_out, next := callerZ.next_in, have_ := callerZ.avail_in, hold := source.state.hold, bits := source.state.bits}
  have loaded : runX (LOAD c.strm c.st) IL.init callerHeap = .ok ((.ok (), regs), callerHeap) := LOAD_run env IL.init
  exact ⟨next, nextOwner, sameState, nextZ, regs, loaded,
    .resume trace leave publicGet source.good.live.hz edit callerGood.live.hs streamGet loaded inputBytes lit dist values codes rootBits haveEq⟩

#print axioms CodeSourceTrace.resume_credited
end Zlib.Inflate.Proofs.ActualHeader
