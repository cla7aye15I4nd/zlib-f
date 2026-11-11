import ZlibF.Proof.«inflate.c.direct-terminal-dispatch»
import ZlibF.Proof.«inflate.c.loop-control-post»
import ZlibF.Proof.«inflate.c.default-view-run»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

def RegisterBindings (z : ZStream) (l : IL) : Prop :=
  l.next = z.next_in ∧ l.have_ = z.avail_in ∧ l.put = z.next_out ∧ l.left = z.avail_out

/-- An error-terminal state can only still carry the original stream and
bindings. Every normal actual iteration has a mode below both terminals. -/
def TerminalLoopInv (c : Ctx) (r : ZStreamRef) (zs : Nat) (initial : ZStream) (l : IL) (h : Heap) : Prop :=
  ∃ z s bs, DefaultStateJ h r zs z s ∧ HeaderLocal c h r s l ∧ DispatchBuffers h r l bs ∧ l.bits.toNat ≤ 39 ∧
    (s.mode = MEM ∨ s.mode = SYNC → r.get h = some initial ∧ RegisterBindings initial l)

def TerminalDirectPost (r : ZStreamRef) (zs : Nat) (initial : ZStream)
    (exit : Ex) (l : IL) (h : Heap) : Prop :=
  ∀ code, exit = .ret code → (code = Z_MEM_ERROR ∨ code = Z_STREAM_ERROR) →
    r.get h = some initial ∧ RegisterBindings initial l ∧
      ∃ s, h.istates zs = some s ∧
        ((s.mode = MEM ∧ code = Z_MEM_ERROR) ∨ (s.mode = SYNC ∧ code = Z_STREAM_ERROR))

theorem inflate_dispatch_terminal_loop_step
    {c : Ctx} {r : ZStreamRef} {zs : Nat} {initial : ZStream}
    (root : c.strm = some r) (state : c.st = some (.tab zs))
    (l : IL) (h : Heap) (outcome : Except Ex Unit) (regs : IL) (after : Heap)
    (current : TerminalLoopInv c r zs initial l h)
    (run : runX (inflate_dispatch c) l h = .ok ((outcome, regs), after)) :
    match outcome with
    | .ok () => TerminalLoopInv c r zs initial regs after
    | .error exit => TerminalDirectPost r zs initial exit regs after := by
  obtain ⟨stream, privateState, bs, invariant, local_, buffers, incoming, terminalBindings⟩ := current
  have env : Env c h r zs stream privateState :=
    ⟨root, state, invariant.good.live.hz, invariant.good.live.hs⟩
  cases outcome with
  | ok value =>
    cases value
    obtain ⟨outcome, nextRegs, nextHeap, nextZ, nextS, used, made, _, source, final,
      ⟨rest, _, packet⟩, _, _, _, _, _, bits, finalLocal, _⟩ :=
      inflate_dispatch_default_view_state_rank env invariant buffers local_ incoming
    have same := Except.ok.inj (source.symm.trans run)
    cases same
    have low := inflate_dispatch_normal_low env invariant buffers local_ incoming run final.good.live.hs
    refine ⟨nextZ, nextS, rest, final, finalLocal, packet, bits, ?_⟩
    intro terminal
    rcases terminal with memory | sync
    · rw [memory] at low
      exact False.elim ((by decide : ¬ MEM < MEM) low)
    · rw [sync] at low
      exact False.elim ((by decide : ¬ SYNC < MEM) low)
  | error exit =>
    intro code selected wanted
    subst exit
    obtain ⟨modes, regsEq, heapEq⟩ :=
      inflate_dispatch_direct_terminal env invariant buffers local_ incoming run wanted
    have terminal : privateState.mode = MEM ∨ privateState.mode = SYNC := by
      rcases modes with memory | sync
      · exact Or.inl memory.1
      · exact Or.inr sync.1
    obtain ⟨streamGet, bindings⟩ := terminalBindings terminal
    rw [regsEq, heapEq]
    exact ⟨streamGet, bindings, privateState, invariant.good.live.hs, modes⟩

/-- The actual complete mode loop retains original stream data on direct
MEM/STREAM returns. No termination or callee contract is assumed. -/
theorem inflate_default_terminal_loop
    {c : Ctx} {r : ZStreamRef} {zs : Nat} {initial : ZStream}
    {l regs : IL} {h after : Heap} {exit : Ex}
    (root : c.strm = some r) (state : c.st = some (.tab zs))
    (current : TerminalLoopInv c r zs initial l h)
    (run : runX (xwhile (pure true) (inflate_dispatch c)) l h = .ok ((.error exit, regs), after)) :
    TerminalDirectPost r zs initial exit regs after := by
  apply xwhile_success_control_post _ _ ?_ current run
  intro before heap outcome finalRegs finalHeap valid source
  have result := inflate_dispatch_terminal_loop_step root state before heap outcome
    finalRegs finalHeap valid source
  cases outcome with
  | ok value =>
    cases value
    exact result
  | error stopped => exact result

/-- Actual public-body entry establishes the terminal binding relation.
The whole loop then preserves the exact original stream on both direct
terminal error returns, including original public total counters. -/
theorem inflate_run_terminal_direct
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {regs : IL} {code : Int32}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : StreamBuffers h r) (nonnull : z.next_out ≠ .null)
    (inputValid : z.next_in = .null → z.avail_in = 0)
    (local_ : HeaderLocal c h r s (dispatchRegs z s))
    (run : runX (inflate_run c) IL.init h = .ok ((.error (.ret code), regs), after))
    (wanted : code = Z_MEM_ERROR ∨ code = Z_STREAM_ERROR) :
    r.get after = some z ∧ RegisterBindings z regs ∧
      ∃ state, after.istates zs = some state ∧
        ((state.mode = MEM ∧ code = Z_MEM_ERROR) ∨ (state.mode = SYNC ∧ code = Z_STREAM_ERROR)) := by
  obtain ⟨entryHeap, entryState, bs, cut, current, env, packet, bits, entrySizes, entryFrame, entryHeapEq,
    entryStateEq⟩ := inflate_run_default_view_entry E invariant buffers nonnull inputValid
  have entryLocal := inflate_run_entry_local invariant current entrySizes entryFrame entryHeapEq entryStateEq local_
  have start : TerminalLoopInv c r zs z (dispatchRegs z entryState) entryHeap :=
    ⟨z, entryState, bs, current, entryLocal, packet, bits, fun _ => ⟨env.hz, rfl, rfl, rfl, rfl⟩⟩
  rw [cut] at run
  exact inflate_default_terminal_loop E.strm E.st start run code rfl wanted

#print axioms inflate_run_terminal_direct
end Zlib.Inflate.Proofs
