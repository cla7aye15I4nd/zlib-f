import ZlibF.Proof.«inflate.c.whole-epoch-entry-invariant»
import ZlibF.Proof.«inflate.c.whole-dictionary-ready-call-cut»
namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.HeaderSourceTrace
set_option autoImplicit false

/-- A terminal proof packet carries the actual run result. A direct
NEED_DICT return is never restarted as a live dispatch loop. Credit is
still internal until the real leave/free publication is executed. -/
structure EpochCallExit (c : Ctx) (entryHeap h : Heap) (r : ZStreamRef) (zs : Nat)
    (entryZ z : ZStream) (s : InflateState) (l : IL) (base : DataLog) (raw : List UInt8) (exit : Ex) where
  terminal : WholeWrapper.WrapperTerminal c entryHeap h r zs entryZ z s l base raw exit
  outputStart : s.mode < CHECK → l.out_ = entryZ.avail_out
  normalRet : s.mode < CHECK → l.ret = Z_OK
  allocationOracle : h.allocOk = entryHeap.allocOk

/-- A produced conclusion of one actual dispatcher proof. These are not
public-history constructors and are never added as caller assumptions. -/
inductive DispatchResult {c : Ctx} {entryHeap h : Heap} {r : ZStreamRef} {zs : Nat}
    {entryZ z : ZStream} {s : InflateState} {l : IL} {base : DataLog} {raw : List UInt8}
    (_before : EpochCallCut c entryHeap h r zs entryZ z s l base raw) : Type
  | progress (after : Heap) (stream : ZStream) (state : InflateState) (regs : IL)
      (actual : runX (inflate_dispatch c) l h = .ok ((.ok (), regs), after))
      (next : EpochCallCut c entryHeap after r zs entryZ stream state regs base raw) : DispatchResult _before
  | stopped (after : Heap) (stream : ZStream) (state : InflateState) (regs : IL) (exit : Ex)
      (actual : runX (inflate_dispatch c) l h = .ok ((.error exit, regs), after))
      (next : EpochCallExit c entryHeap after r zs entryZ stream state regs base raw exit) : DispatchResult _before

/-- A verified normal source trip advances the exact same actual whole
mainwhile. Both bounded loops are supplied by existing proved safety. -/
theorem EpochCallCut.advance_main
    {c : Ctx} {entryHeap h after : Heap} {r : ZStreamRef} {zs : Nat}
    {entryZ z stream : ZStream} {s state : InflateState} {l regs : IL} {base : DataLog} {raw bs : List UInt8}
    (before : EpochCallCut c entryHeap h r zs entryZ z s l base raw)
    (E : Env c after r zs stream state) (origin : DefaultOriginState after r zs stream state)
    (buffers : DispatchBuffers after r regs bs) (bits : regs.bits.toNat ≤ 39)
    (actual : runX (inflate_dispatch c) l h = .ok ((.ok (), regs), after)) :
    runX (inflate_run c) IL.init entryHeap = runX (xwhile (pure true) (inflate_dispatch c)) regs after := by
  exact before.framed.cut.main.trans
    (loop_prefix_continuation before.framed.cut.env before.framed.cut.origin before.framed.cut.buffers
      before.framed.cut.bits E origin buffers bits (.step .begin actual))

/-- The actual terminating dispatcher trip closes the same mainwhile,
including literal return exceptions and ordinary inf_leave. -/
theorem EpochCallCut.exit_main
    {c : Ctx} {entryHeap h after : Heap} {r : ZStreamRef} {zs : Nat}
    {entryZ z : ZStream} {s : InflateState} {l regs : IL} {base : DataLog} {raw : List UInt8} {exit : Ex}
    (before : EpochCallCut c entryHeap h r zs entryZ z s l base raw)
    (actual : runX (inflate_dispatch c) l h = .ok ((.error exit, regs), after)) :
    runX (inflate_run c) IL.init entryHeap = .ok ((.error exit, regs), after) := by
  exact before.framed.cut.main.trans
    (WholeWrapper.wrapper_loop_terminal before.framed.cut.env before.framed.cut.origin
      before.framed.cut.buffers before.framed.cut.bits actual)

#print axioms EpochCallCut.advance_main
#print axioms EpochCallCut.exit_main
end Zlib.Inflate.Proofs.WholeEpoch
