import ZlibF.Proof.«inflate.c.block-type»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The four terminal/error modes have distinct source exit conventions. -/
def TerminalMode (mode : UInt32) : Prop :=
  mode = DONE ∨ mode = BAD ∨ mode = MEM ∨ mode = SYNC

def terminalRegs (mode : UInt32) (l : IL) : IL :=
  if mode = DONE then { l with ret := Z_STREAM_END }
  else if mode = BAD then { l with ret := Z_DATA_ERROR } else l

def terminalExit (mode : UInt32) : Except Ex Unit :=
  if mode = DONE ∨ mode = BAD then .error Ex.leave
  else if mode = MEM then .error (Ex.ret Z_MEM_ERROR) else .error (Ex.ret Z_STREAM_ERROR)

/-- The actual switch distinguishes ordinary leave from direct API returns.
It writes no heap memory in any terminal/error mode. -/
theorem inflate_dispatch_terminal_run {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (E : Env c h r zs z s) (l : IL) (mode : TerminalMode s.mode) :
    runX (inflate_dispatch c) l h = .ok ((terminalExit s.mode, terminalRegs s.mode l), h) := by
  unfold inflate_dispatch
  rw [runX_bind, runX_rdS E]
  rcases mode with mode | mode | mode | mode
  all_goals with_reducible simp [mode, HEAD, FLAGS, TIME, OS, EXLEN, EXTRA, NAME, COMMENT, HCRC, DICTID, DICT,
    TYPE, TYPEDO, STORED, COPY_, COPY, TABLE, LENLENS, CODELENS, LEN_, LEN, LENEXT, DIST, DISTEXT,
    MATCH, LIT, CHECK, LENGTH, DONE, BAD, MEM, SYNC, inflate_DONE, terminalExit, terminalRegs,
    runX_bind, runX_modify, runX_throw]

/-- Terminal/error dispatch retains the complete buffer relation and all
current state clauses on the original heap. No parser fields are assumed
usable after an error, and MEM/SYNC bypass ordinary inf_leave accounting. -/
theorem inflate_dispatch_terminal_boundary {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (good : Good h r zs z s) (pending : DataPendingInvariant s)
    (buffers : DispatchBuffers h r l bs) (mode : TerminalMode s.mode) :
    runX (inflate_dispatch c) l h = .ok ((terminalExit s.mode, terminalRegs s.mode l), h) ∧
      Good h r zs z s ∧ DataTableInvariant h s ∧ DataPendingInvariant s ∧
      DispatchBuffers h r (terminalRegs s.mode l) bs ∧
      (terminalRegs s.mode l).bits = l.bits ∧ (terminalRegs s.mode l).hold = l.hold := by
  have frame : ∀ field, terminalRegs s.mode l = field →
      field.next = l.next ∧ field.have_ = l.have_ ∧ field.put = l.put ∧ field.left = l.left ∧
      field.out_ = l.out_ ∧ field.bits = l.bits ∧ field.hold = l.hold := by
    intro field equal
    subst field
    unfold terminalRegs
    split
    · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨next, haveCount, put, left, out, bits, hold⟩ := frame (terminalRegs s.mode l) rfl
  have inv : BitInv h (terminalRegs s.mode l) bs := by
    refine ⟨by rw [haveCount]; exact buffers.bits.have_eq, ?_, ?_⟩
    · rw [next]
      exact buffers.bits.next
    · rw [hold, bits]
      exact buffers.bits.hold_lt
  have packet : DispatchBuffers h r (terminalRegs s.mode l) bs := by
    simpa only [List.drop_zero] using buffers.advance_both good good rfl (ByteViewSizes.refl h)
      (fun _ => rfl) (regs := terminalRegs s.mode l) (used := 0) (made := 0)
      (by rw [next, inputAdvance_zero]) (by rw [haveCount]; rfl)
      (by rw [put, inputAdvance_zero]) (by rw [left]; rfl) out
      (by simpa only [List.drop_zero] using inv)
  have tables : DataTableInvariant h s := by
    apply dataTableInvariant_inactive
    rcases mode with mode | mode | mode | mode <;> rw [mode] <;> unfold DataTableMode <;> decide
  exact ⟨inflate_dispatch_terminal_run E l mode, good, tables, pending, packet, bits, hold⟩

end Zlib.Inflate.Proofs
