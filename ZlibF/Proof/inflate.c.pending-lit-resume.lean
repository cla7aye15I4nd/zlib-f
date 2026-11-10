import ZlibF.Proof.«inflate.c.slow-input-fragment»
import ZlibF.Proof.«inflate.c.data-dispatch»

namespace Zlib.Inflate.Proofs.PendingLiteral
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.SlowInputFragment
set_option autoImplicit false

/-- A pending literal with exhausted output takes the actual leave exit.
The heap, scalar records, bit source and pending symbol remain identical. -/
theorem literal_wait
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8} {future residual : List Bool} {symbol : Nat}
    (E : Env c h r zs z s) (good : Good h r zs z s) (tables : DataTablesSafe h s)
    (buffers : DispatchBuffers h r l bs) (source : FutureSource l bs future residual)
    (mode : s.mode = LIT) (length : s.length.toNat = symbol) (small : symbol < 256)
    (empty : l.left = 0) :
    runX (inflate_LIT c) l h = .ok ((.error Ex.leave, l), h) ∧
      runX (inflate_dispatch c) l h = .ok ((.error Ex.leave, l), h) ∧
      Good h r zs z s ∧ DataTablesSafe h s ∧ DispatchBuffers h r l bs ∧
      FutureSource l bs future residual ∧ s.mode = LIT ∧ s.length.toNat = symbol ∧ symbol < 256 := by
  have run := inflate_LIT_full c l h empty
  exact ⟨run, (inflate_dispatch_LIT E l mode).trans run, good, tables, buffers, source, mode, length, small⟩

/-- Positive output resumes a real pending literal through the actual
LIT dispatch. The caller supplies ordinary buffer ownership/ranges only;
the actual generic byte-view write, output observation and final buffers
are derived, even for disjoint slices in one byte object. -/
theorem literal_resume
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8} {future residual : List Bool} {symbol : Nat}
    (E : Env c h r zs z s) (good : Good h r zs z s) (tables : DataTablesSafe h s)
    (buffers : DispatchBuffers h r l bs) (source : FutureSource l bs future residual)
    (mode : s.mode = LIT) (length : s.length.toNat = symbol) (small : symbol < 256)
    (room : l.left ≠ 0) :
    ∃ dest off array regs after state,
      l.put = .ref dest off ∧ Space.get h dest = some array ∧ Space.ro h dest = false ∧ off < array.size ∧
      runX (inflate_LIT c) l h = .ok ((.ok (), regs), after) ∧
      runX (inflate_dispatch c) l h = .ok ((.ok (), regs), after) ∧
      after = setI (Space.put h dest (array.set! off symbol.toUInt8)) zs state ∧
      state = { s with mode := LEN } ∧ Good after r zs z state ∧ DataTablesSafe after state ∧
      DispatchBuffers after r regs bs ∧ ByteViewSizes h after ∧ after.static = h.static ∧ DecodeStateFrame s state ∧ EmitRegFrame l regs ∧
      regs.put = inputAdvance l.put 1 ∧ regs.left.toNat + 1 = l.left.toNat ∧
      regs.next = l.next ∧ regs.have_ = l.have_ ∧ regs.hold = l.hold ∧ regs.bits = l.bits ∧
      stream regs bs = stream l bs ∧ FutureSource regs bs future residual ∧
      state.length = s.length ∧ state.was = s.was ∧ state.back = s.back ∧
      Space.get after dest = some (array.set! off symbol.toUInt8) ∧ Space.ro after dest = false ∧
      Bytes after l.put 1 [symbol.toUInt8] ∧ symbol < 256 ∧
      (array.set! off symbol.toUInt8).size = array.size ∧
      ∀ i, i < array.size → i ≠ off → (array.set! off symbol.toUInt8)[i]? = array[i]? := by
  obtain ⟨dest, array, off, put, get, write, capacity, _, _, _⟩ :=
    callerRange_slow_output good l buffers.output.range buffers.output.nonnull buffers.output.count buffers.output.produced
  have positive : 0 < l.left.toNat := by
    have nonzero : l.left.toNat ≠ 0 := fun zero => room (UInt32.toNat_inj.mp zero)
    omega
  have fit : off < array.size := by omega
  have byte : s.length.toUInt8 = symbol.toUInt8 := by rw [← length]; rfl
  let regs : IL := { l with put := .ref dest (off + 1), left := l.left - 1 }
  let state := { s with mode := LEN }
  let after := setI (Space.put h dest (array.set! off symbol.toUInt8)) zs state
  have run : runX (inflate_LIT c) l h = .ok ((.ok (), regs), after) := by
    have actual := inflate_LIT_view_run E room put get write fit
    simpa only [byte] using actual
  obtain ⟨outcome, actualRegs, actualHeap, actualState, actualRun, current, currentTables,
    finalBuffers, sizes, stateFrame, regFrame, alternatives⟩ := inflate_LIT_dispatch E good tables buffers
  have equal := Except.ok.inj (actualRun.symm.trans run)
  cases equal
  have stateGet : after.istates zs = some state := by simp only [after, setI_istates_same]
  have stateEq : actualState = state := Option.some.inj (current.live.hs.symm.trans stateGet)
  subst actualState
  have getAfter : Space.get after dest = some (array.set! off symbol.toUInt8) := by
    rw [byte_view_get_setI]
    exact byte_view_get_put get write _
  have writeAfter : Space.ro after dest = false := by
    rw [byte_view_ro_setI, byte_view_ro_write]
    exact write
  have leftCount : regs.left.toNat + 1 = l.left.toNat := by
    change (l.left - 1).toNat + 1 = l.left.toNat
    rw [UInt32.toNat_sub_of_le _ _ positive]
    change l.left.toNat - 1 + 1 = l.left.toNat
    omega
  have output : Bytes after l.put 1 [symbol.toUInt8] := by
    refine Or.inr ⟨dest, off, array.set! off symbol.toUInt8, put, getAfter, by simp; omega, ?_⟩
    rw [take_succ_drop (array.set! off symbol.toUInt8) off 0 (by simp; omega)]
    simp
  refine ⟨dest, off, array, regs, after, state, put, get, write, fit, run,
    (inflate_dispatch_LIT E l mode).trans run, rfl, rfl, current, currentTables,
    finalBuffers, sizes, by simp only [after, setI, byte_view_put_static], stateFrame, regFrame, ?_, leftCount, rfl, rfl, rfl, rfl,
    rfl, source, rfl, rfl, rfl, getAfter, writeAfter, output, small, by simp, ?_⟩
  · rw [put]
    rfl
  · intro i bound different
    simp [Array.set!, Ne.symm different]

#print axioms literal_wait
#print axioms literal_resume
end Zlib.Inflate.Proofs.PendingLiteral

namespace Zlib.Inflate.Proofs.PendingLiteral
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.SlowInputFragment
set_option autoImplicit false

/-- Completing a pending literal yields its original independent token
event, rather than reusing the completed token as a new pending phase.
The represented suffix and arbitrary future input remain unchanged. -/
theorem literal_resume_event
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs dict history : List UInt8} {future input rest : List Bool} {symbol : Nat} {L D : List Nat}
    (E : Env c h r zs z s) (good : Good h r zs z s) (tables : DataTablesSafe h s)
    (buffers : DispatchBuffers h r l bs) (source : FutureSource l bs future rest)
    (mode : s.mode = LIT) (length : s.length.toNat = symbol) (small : symbol < 256)
    (decoded : decodeSym L input = some (symbol, rest)) (room : l.left ≠ 0) :
    ∃ regs after state,
      runX (inflate_dispatch c) l h = .ok ((.ok (), regs), after) ∧
      Good after r zs z state ∧ DataTablesSafe after state ∧ DispatchBuffers after r regs bs ∧
      ByteViewSizes h after ∧ after.static = h.static ∧ state = {s with mode := LEN} ∧
      regs.put = inputAdvance l.put 1 ∧ regs.left.toNat + 1 = l.left.toNat ∧
      regs.next = l.next ∧ regs.have_ = l.have_ ∧ regs.hold = l.hold ∧ regs.bits = l.bits ∧
      FutureSource regs bs future rest ∧ Bytes after l.put 1 [symbol.toUInt8] ∧
      Token.Step L D dict history input rest (history ++ [symbol.toUInt8]) false ∧
      (∀ tail output, Symbols L D dict (history ++ [symbol.toUInt8]) rest tail output →
        Symbols L D dict history input tail output) := by
  obtain ⟨dest, off, array, regs, after, state, _put, _get, _write, _fit,
    _litRun, dispatch, _heap, stateEq, current, currentTables, nextBuffers, sizes, static,
    _stateFrame, _regFrame, put, left, next, have_, hold, bits, _stream, nextSource,
    _length, _was, _back, _finalGet, _finalWrite, observed, _small, _size, _outside⟩ :=
    literal_resume E good tables buffers source mode length small room
  have token : Token.Step L D dict history input rest (history ++ [symbol.toUInt8]) false :=
    .literal decoded small
  exact ⟨regs, after, state, dispatch, current, currentTables, nextBuffers, sizes, static,
    stateEq, put, left, next, have_, hold, bits, nextSource, observed, token,
    fun tail output continuation => (Token.step_composes_symbols L D dict history input rest
      (history ++ [symbol.toUInt8]) false token).2 rfl tail output continuation⟩

#print axioms literal_resume_event
end Zlib.Inflate.Proofs.PendingLiteral
