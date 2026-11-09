import ZlibF.Proof.«inflate.c.local-public-state»
import ZlibF.Proof.«inflate.c.header-output-frame»

namespace Zlib.Inflate.Local
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

theorem bufferFrame_live_refl {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (hz : r.get h = some z) (hs : h.istates zs = some s)
    (regions : List Region) : BufferFrame h h (fun b => StreamRoot r b ∨ b = zs) regions := by
  have same : setI (r.put h z) zs s = h := by rw [ZStreamRef.put_self hz, tcSetI_same hs]
  simpa only [same] using (fastWriteback_heap_frame hz hs z s regions).1

/-- The actual zlib header suffix only changes stream/state records.
Each refusal and the accepted header use their real translated runs. -/
theorem headDefaultCheck_output_frame {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l regs : IL} {outcome : Except Ex Unit}
    (E : Env c h r zs z s) (wbits : s.wbits = 15)
    (run : runX (headDefaultCheck c s l) l h = .ok ((outcome, regs), after))
    (regions : List Region) : BufferFrame h after (fun b => StreamRoot r b ∨ b = zs) regions := by
  by_cases header : headHeaderRejected s l = true
  · obtain ⟨i, actual⟩ := headDefaultCheck_bad_header E l header
    have heapEq : after = badHeap h r zs z s i :=
      congrArg Prod.snd (Except.ok.inj (run.symm.trans actual))
    rw [heapEq]
    exact (badHeap_buffer_frame E.hz E.hs i regions).1
  have headerFalse : headHeaderRejected s l = false := by cases test : headHeaderRejected s l <;> simp_all
  by_cases method : headMethodRejected l = true
  · obtain ⟨i, actual⟩ := headDefaultCheck_bad_method E l headerFalse method
    have heapEq : after = badHeap h r zs z s i :=
      congrArg Prod.snd (Except.ok.inj (run.symm.trans actual))
    rw [heapEq]
    exact (badHeap_buffer_frame E.hz E.hs i regions).1
  have methodFalse : headMethodRejected l = false := by cases test : headMethodRejected l <;> simp_all
  by_cases window : 15 < (headWindowRegs l).len.toNat
  · obtain ⟨i, actual⟩ := headDefaultCheck_bad_window E l headerFalse methodFalse window
    have heapEq : after = badHeap h r zs z s i :=
      congrArg Prod.snd (Except.ok.inj (run.symm.trans actual))
    rw [heapEq]
    exact (badHeap_buffer_frame E.hz E.hs i regions).1
  · have actual := headDefaultCheck_accept E l headerFalse methodFalse (by omega) wbits
    have heapEq : after = setI (r.put h { z with adler := 1 }) zs (headDefaultState s l) :=
      congrArg Prod.snd (Except.ok.inj (run.symm.trans actual))
    rw [heapEq]
    exact (fastWriteback_heap_frame E.hz E.hs { z with adler := 1 } (headDefaultState s l) regions).1

/-- Every actual HEAD admitted by J, including raw recovery and disabled
validation, has no caller-byte effect. The public output interval is empty. -/
theorem inflate_HEAD_output_frame {c : Ctx} {h after : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l regs : IL} {outcome : Except Ex Unit} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : LocalStateJ h cutoff r zs z s)
    (buffers : DispatchBuffers h r l bs)
    (run : runX (inflate_HEAD c) l h = .ok ((outcome, regs), after))
    (regions : List Region) : BufferFrame h after (fun b => StreamRoot r b ∨ b = zs) regions := by
  rcases invariant.wrapper with raw | wrapped
  · have actual := inflate_HEAD_raw_run E l raw
    have heapEq : after = setI h zs { s with mode := TYPEDO } :=
      congrArg Prod.snd (Except.ok.inj (run.symm.trans actual))
    rw [heapEq]
    have frame := (fastWriteback_heap_frame E.hz E.hs z { s with mode := TYPEDO } regions).1
    simpa only [ZStreamRef.put_self E.hz] using frame
  · obtain ⟨result, current, _, _, _, _, _, _, _, _, cut, _⟩ :=
      inflate_HEAD_zlib_window_prefix_count E buffers.bits wrapped invariant.header
    rw [cut] at run
    cases result with
    | error exit =>
      cases run
      exact bufferFrame_live_refl E.hz E.hs regions
    | ok value =>
      cases value
      exact headDefaultCheck_output_frame E invariant.window run regions

/-- The actual default HEAD dispatch has zero output with the exact empty
output frame, using the same returned cursors and private state. -/
theorem inflate_dispatch_HEAD_exact_frame
    {c : Ctx} {l : IL} {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : LocalStateJ h cutoff r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = HEAD) (incoming : l.bits.toNat ≤ 39) :
    ∃ outcome regs after stream state made,
      runX (inflate_dispatch c) l h = .ok ((outcome, regs), after) ∧
      LocalGood after cutoff r zs stream state ∧ regs.left.toNat + made = l.left.toNat ∧
      regs.put = inputAdvance l.put made ∧
      BufferFrame h after (fun b => StreamRoot r b ∨ b = zs) [⟨l.put, made⟩] := by
  obtain ⟨outcome, regs, after, stream, state, _, _, run, current, _, _, _, _, put, left, _⟩ :=
    inflate_dispatch_HEAD_state_rank E invariant buffers mode incoming
  refine ⟨outcome, regs, after, stream, state, 0, run, current.good,
    by rw [left]; rfl, by rw [put, inputAdvance_zero], ?_⟩
  exact inflate_HEAD_output_frame E invariant buffers
    ((inflate_dispatch_HEAD E l mode).symm.trans run) [⟨l.put, 0⟩]

/-- DONE, BAD, MEM and SYNC dispatch writes no heap object. Direct returns
and ordinary leave preserve the same exact empty output frame. -/
theorem inflate_dispatch_terminal_exact_frame
    {c : Ctx} {l : IL} {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState}
    (E : Env c h r zs z s) (good : LocalGood h cutoff r zs z s) (mode : TerminalMode s.mode) :
    ∃ outcome regs after stream state made,
      runX (inflate_dispatch c) l h = .ok ((outcome, regs), after) ∧
      LocalGood after cutoff r zs stream state ∧ regs.left.toNat + made = l.left.toNat ∧
      regs.put = inputAdvance l.put made ∧
      BufferFrame h after (fun b => StreamRoot r b ∨ b = zs) [⟨l.put, made⟩] := by
  refine ⟨terminalExit s.mode, terminalRegs s.mode l, h, z, s, 0,
    inflate_dispatch_terminal_run E l mode, good, ?_, ?_, bufferFrame_live_refl E.hz E.hs _⟩
  · unfold terminalRegs
    repeat' first | split | rfl
  · rw [inputAdvance_zero]
    unfold terminalRegs
    repeat' first | split | rfl

#print axioms inflate_HEAD_output_frame
#print axioms inflate_dispatch_HEAD_exact_frame
#print axioms inflate_dispatch_terminal_exact_frame
end Zlib.Inflate.Local
