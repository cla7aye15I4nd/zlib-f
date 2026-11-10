import ZlibF.Proof.«inflate.c.fast-view-loop-bit-account-invariant»
import ZlibF.Proof.«inflate.c.fast-view-dolen-end-invariant»
import ZlibF.Proof.«inflate.c.fast-view-dodist-invalid-invariant»
import ZlibF.Proof.«inflate.c.fast-view-dolen-invalid-invariant»
import ZlibF.Proof.«inflate.c.fast-view-invalid-invariant»
import ZlibF.Proof.«inflate.c.fast-view-dolen-root-terminals-invariant»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- A decoder branch that reads no input byte and only consumes held bits
retains the call-entry input account, including when it breaks the loop. -/
theorem FastInputAccount.no_pull
    {ctx : FastLoopContext} {startOff startBits : Nat}
    {before after : Zlib.Inffast.L}
    (account : FastInputAccount ctx startOff startBits before)
    (cursor : after.in_ = before.in_)
    (bits : after.bits.toNat ≤ before.bits.toNat) :
    FastInputAccount ctx startOff startBits after := by
  obtain ⟨off, beforeCursor, lower, budget⟩ := account
  exact ⟨off, cursor.trans beforeCursor, lower, by omega⟩

/-- The exact bit-stream relation supplies the bit bound for a no-pull
branch. This applies to terminal and invalid table leaves regardless of
their `broke` flag. -/
theorem FastInputAccount.no_pull_from_stream
    {ctx : FastLoopContext} {startOff startBits : Nat}
    {beforeHeap afterHeap : Heap}
    {slow slowFinal : IL} {bs : List UInt8}
    {before after : Zlib.Inffast.L} {consumed : Nat}
    (account : FastInputAccount ctx startOff startBits before)
    (beforePacket : FastInputPacket beforeHeap slow bs before)
    (afterPacket : FastInputPacket afterHeap slowFinal bs after)
    (cursor : after.in_ = before.in_)
    (source : stream slowFinal bs =
      (stream slow bs).drop consumed) :
    FastInputAccount ctx startOff startBits after := by
  have upper : slowFinal.bits.toNat ≤ slow.bits.toNat := by
    have bound := fast_stream_drop_bit_upper
      (used := 0) (by omega) source
    simpa using bound
  apply account.no_pull cursor
  rw [afterPacket.bits, beforePacket.bits]
  exact upper

/-- A branch with an exact read count and source-bit relation retains the
same call-entry account. The read count can include refills before a later
error `break`. -/
theorem FastInputAccount.advance_from_stream
    {ctx : FastLoopContext} {startOff startBits off used consumed : Nat}
    {beforeHeap afterHeap : Heap} {slow slowFinal : IL}
    {bs : List UInt8} {before after : Zlib.Inffast.L}
    (account : FastInputAccount ctx startOff startBits before)
    (beforePacket : FastInputPacket beforeHeap slow bs before)
    (afterPacket : FastInputPacket afterHeap slowFinal
      (bs.drop used) after)
    (beforeCursor : before.in_ = .ref ctx.inputRef off)
    (afterCursor : after.in_ = .ref ctx.inputRef (off + used))
    (usedBound : used ≤ bs.length)
    (source : stream slowFinal (bs.drop used) =
      (stream slow bs).drop consumed) :
    FastInputAccount ctx startOff startBits after := by
  obtain ⟨oldOff, oldCursor, lower, budget⟩ := account
  have same : oldOff = off := by
    rw [beforeCursor] at oldCursor
    cases oldCursor
    rfl
  subst oldOff
  have upper := fast_stream_drop_bit_upper usedBound source
  refine ⟨off + used, afterCursor, by omega, ?_⟩
  rw [← afterPacket.bits, ← beforePacket.bits] at upper
  omega

/-- One translated input pull advances the cursor and retains the
call-entry account, ready to compose with any later break leaf. -/
theorem FastInputAccount.after_pull
    {ctx : FastLoopContext} {startOff startBits off : Nat}
    {h : Heap} {slow : IL} {b : UInt8} {bs : List UInt8}
    {before : Zlib.Inffast.L}
    (account : FastInputAccount ctx startOff startBits before)
    (packet : FastInputPacket h slow (b :: bs) before)
    (small : slow.bits.toNat ≤ 22)
    (cursor : before.in_ = .ref ctx.inputRef off) :
    ∃ fastNext slowNext,
      C.run (Zlib.Inffast.pull before) h = .ok (fastNext, h) ∧
      FastInputPacket h slowNext bs fastNext ∧
      FastInputAccount ctx startOff startBits fastNext ∧
      stream slowNext bs = stream slow (b :: bs) := by
  obtain ⟨next, fastNext, slowNext, pullRun, nextEq,
    slowEq, fastEq, nextPacket, streamEq⟩ :=
    packet.pull small
  have nextCursor : fastNext.in_ =
      .ref ctx.inputRef (off + 1) := by
    rw [nextPacket.cursor, slowEq, pulled, nextEq]
    have old : slow.next = .ref ctx.inputRef off :=
      packet.cursor.symm.trans cursor
    rw [old]
    rfl
  have nextAccount : FastInputAccount ctx startOff
      startBits fastNext := by
    exact account.advance_from_stream (used := 1)
      (consumed := 0) packet nextPacket cursor nextCursor
      (by simp) (by simpa using streamEq)
  exact ⟨fastNext, slowNext, pullRun, nextPacket,
    nextAccount, streamEq⟩

/-- The fast body's initial two-pull refill carries the account to the
root lookup. Both reads are real translated `pull` executions. -/
theorem FastInputAccount.after_two_pulls
    {ctx : FastLoopContext} {startOff startBits off : Nat}
    {h : Heap} {slow : IL}
    {first second : UInt8} {rest : List UInt8}
    {before : Zlib.Inffast.L}
    (account : FastInputAccount ctx startOff startBits before)
    (packet : FastInputPacket h slow
      (first :: second :: rest) before)
    (small : slow.bits.toNat < 15)
    (cursor : before.in_ = .ref ctx.inputRef off) :
    ∃ (fast1 fast2 : Zlib.Inffast.L) (slow2 : IL),
      C.run (Zlib.Inffast.pull before) h = .ok (fast1, h) ∧
      C.run (Zlib.Inffast.pull fast1) h = .ok (fast2, h) ∧
      FastInputPacket h slow2 rest fast2 ∧
      FastInputAccount ctx startOff startBits fast2 ∧
      fast2.in_ = .ref ctx.inputRef (off + 2) ∧
      stream slow2 rest = stream slow
        (first :: second :: rest) := by
  obtain ⟨next1, fast1, slow1, pull1, next1Eq,
    slow1Eq, _, packet1, stream1⟩ :=
    packet.pull (by omega)
  have cursor1 : fast1.in_ =
      .ref ctx.inputRef (off + 1) := by
    rw [packet1.cursor, slow1Eq, pulled, next1Eq]
    have old : slow.next = .ref ctx.inputRef off :=
      packet.cursor.symm.trans cursor
    rw [old]
    rfl
  have account1 : FastInputAccount ctx startOff
      startBits fast1 := by
    exact account.advance_from_stream (used := 1)
      (consumed := 0) packet packet1 cursor cursor1
      (by simp) (by simpa using stream1)
  have small1 : slow1.bits.toNat ≤ 22 := by
    rw [slow1Eq]
    change (slow.bits + 8).toNat ≤ 22
    have count := u32_add8 slow.bits (by omega)
    omega
  obtain ⟨next2, fast2, slow2, pull2, next2Eq,
    slow2Eq, _, packet2, stream2⟩ :=
    packet1.pull small1
  have cursor2 : fast2.in_ =
      .ref ctx.inputRef (off + 2) := by
    rw [packet2.cursor, slow2Eq, pulled, next2Eq]
    rw [packet1.cursor] at cursor1
    rw [cursor1]
    rfl
  have account2 : FastInputAccount ctx startOff
      startBits fast2 := by
    exact account1.advance_from_stream (used := 1)
      (consumed := 0) packet1 packet2 cursor1 cursor2
      (by simp) (by simpa using stream2)
  refine ⟨fast1, fast2, slow2, pull1, pull2,
    packet2, account2, ?_, ?_⟩
  · simpa only [Nat.add_assoc] using cursor2
  · rw [stream2, stream1]

/-- The actual end-of-block leaf preserves call-entry input accounting
through its `break`, since it consumes bits but reads no byte. -/
theorem FastInputPacket.dolen_end_leaf_account_default_state
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {ctx : FastLoopContext} {startOff startBits : Nat}
    (packet : FastInputPacket h slow bs l)
    (account : FastInputAccount ctx startOff startBits l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow bs)
    (statePtr : c.state = some (.tab zs))
    (mode : DataTableMode s.mode)
    {codeRef : CodeRef} {codes : Array Code} {index : Nat}
    (herePtr : l.here = .ref codeRef index)
    (codesGet : Space.get h codeRef = some codes)
    (codeIndex : index < codes.size)
    (codeBits : codes[index].bits.toNat ≤ slow.bits.toNat)
    (codeWidth : codes[index].bits.toNat ≤ 15)
    (nonzero : codes[index].op ≠ 0)
    (notBase : (codes[index].op.toUInt32 &&& 16 != 0) = false)
    (notLink : (codes[index].op.toUInt32 &&& 64 == 0) = false)
    (endCode : (codes[index].op.toUInt32 &&& 32 != 0) = true) :
    ∃ result slowNext,
      C.run (Zlib.Inffast.dolen c l) h =
        .ok (result, setI h zs { s with mode := TYPE }) ∧
      result.broke = true ∧
      FastInputAccount ctx startOff startBits result ∧
      FastInputPacket (setI h zs { s with mode := TYPE })
        slowNext bs result := by
  obtain ⟨result, slowNext, run, broke, _, cursor, _,
    nextPacket, _, _, _, source⟩ :=
    packet.dolen_end_leaf_default_state invariant buffers
      statePtr mode herePtr codesGet codeIndex codeBits
      codeWidth nonzero notBase notLink endCode
  refine ⟨result, slowNext, run, broke, ?_, nextPacket⟩
  exact account.no_pull_from_stream packet nextPacket cursor source

/-- The real one-pass `dolen` loop retains the same account when it exits
on an end-of-block code. -/
theorem FastInputPacket.dolen_root_end_loop_account_default_state
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {ctx : FastLoopContext} {startOff startBits : Nat}
    (packet : FastInputPacket h slow bs l)
    (account : FastInputAccount ctx startOff startBits l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow bs)
    (statePtr : c.state = some (.tab zs))
    (mode : DataTableMode s.mode)
    {codeRef : CodeRef} {codes : Array Code} {index : Nat}
    (herePtr : l.here = .ref codeRef index)
    (codesGet : Space.get h codeRef = some codes)
    (codeIndex : index < codes.size)
    (codeBits : codes[index].bits.toNat ≤ slow.bits.toNat)
    (codeWidth : codes[index].bits.toNat ≤ 15)
    (nonzero : codes[index].op ≠ 0)
    (notBase : (codes[index].op.toUInt32 &&& 16 != 0) = false)
    (notLink : (codes[index].op.toUInt32 &&& 64 == 0) = false)
    (endCode : (codes[index].op.toUInt32 &&& 32 != 0) = true) :
    ∃ result slowNext,
      C.run (cdoWhile (Zlib.Inffast.dolen c)
        (fun current => pure (current.againL, current)) l) h =
        .ok (result, setI h zs { s with mode := TYPE }) ∧
      result.broke = true ∧
      FastInputAccount ctx startOff startBits result ∧
      FastInputPacket (setI h zs { s with mode := TYPE })
        slowNext bs result ∧
      DefaultStateJ (setI h zs { s with mode := TYPE })
        r zs z { s with mode := TYPE } ∧
      DispatchBuffers (setI h zs { s with mode := TYPE })
        r slowNext bs := by
  obtain ⟨result, slowNext, leafRun, broke, againL,
    cursor, _, nextPacket, nextState, nextBuffers,
    _, source⟩ :=
    packet.dolen_end_leaf_default_state invariant buffers
      statePtr mode herePtr codesGet codeIndex codeBits
      codeWidth nonzero notBase notLink endCode
  refine ⟨result, slowNext, dolen_loop_one leafRun againL,
    broke, ?_, nextPacket, nextState, nextBuffers⟩
  exact account.no_pull_from_stream packet nextPacket cursor source

/-- An invalid distance table leaf also keeps the input account through
its translated error `break`. -/
theorem FastInputPacket.dodist_invalid_leaf_account_default_state
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {ctx : FastLoopContext} {startOff startBits : Nat}
    (packet : FastInputPacket h slow bs l)
    (account : FastInputAccount ctx startOff startBits l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow bs)
    (streamPtr : c.strm = some r)
    (statePtr : c.state = some (.tab zs))
    {codeRef : CodeRef} {codes : Array Code} {index : Nat}
    (herePtr : l.here = .ref codeRef index)
    (codesGet : Space.get h codeRef = some codes)
    (codeIndex : index < codes.size)
    (codeBits : codes[index].bits.toNat ≤ slow.bits.toNat)
    (codeWidth : codes[index].bits.toNat ≤ 15)
    (notBase : (codes[index].op.toUInt32 &&& 16 != 0) = false)
    (notLink : (codes[index].op.toUInt32 &&& 64 == 0) = false) :
    ∃ result after slowNext,
      C.run (Zlib.Inffast.dodist c l) h = .ok (result, after) ∧
      result.broke = true ∧
      FastInputAccount ctx startOff startBits result ∧
      FastInputPacket after slowNext bs result := by
  obtain ⟨i, after, result, slowNext, run, _, broke,
    _, cursor, _, nextPacket, _, _, _, source⟩ :=
    packet.dodist_invalid_leaf_default_state invariant
      buffers streamPtr statePtr herePtr codesGet codeIndex
      codeBits codeWidth notBase notLink
  refine ⟨result, after, slowNext, run, broke, ?_,
    nextPacket⟩
  exact account.no_pull_from_stream packet nextPacket cursor source

/-- The real one-pass `dodist` loop retains the account on an invalid
distance root code. -/
theorem FastInputPacket.dodist_root_invalid_loop_account_default_state
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {ctx : FastLoopContext} {startOff startBits : Nat}
    (packet : FastInputPacket h slow bs l)
    (account : FastInputAccount ctx startOff startBits l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow bs)
    (streamPtr : c.strm = some r)
    (statePtr : c.state = some (.tab zs))
    {codeRef : CodeRef} {codes : Array Code} {index : Nat}
    (herePtr : l.here = .ref codeRef index)
    (codesGet : Space.get h codeRef = some codes)
    (codeIndex : index < codes.size)
    (codeBits : codes[index].bits.toNat ≤ slow.bits.toNat)
    (codeWidth : codes[index].bits.toNat ≤ 15)
    (notBase : (codes[index].op.toUInt32 &&& 16 != 0) = false)
    (notLink : (codes[index].op.toUInt32 &&& 64 == 0) = false) :
    ∃ result after slowNext,
      C.run (cdoWhile (Zlib.Inffast.dodist c)
        (fun current => pure (current.againD, current)) l) h =
        .ok (result, after) ∧
      result.broke = true ∧
      FastInputAccount ctx startOff startBits result ∧
      FastInputPacket after slowNext bs result := by
  obtain ⟨i, after, result, slowNext, leafRun, _, broke,
    againD, cursor, _, nextPacket, _, _, _, source⟩ :=
    packet.dodist_invalid_leaf_default_state invariant
      buffers streamPtr statePtr herePtr codesGet codeIndex
      codeBits codeWidth notBase notLink
  have cond :
      (fun q : Zlib.Inffast.L =>
        (pure (q.againD, q) : M (Bool × Zlib.Inffast.L)))
        result after = .ok ((false, result), after) := by
    simp [againD]
  have loop := Zlib.Inffast.Proofs.cdoWhile_one
    (body := Zlib.Inffast.dodist c)
    (cond := fun q => (pure (q.againD, q) :
      M (Bool × Zlib.Inffast.L))) leafRun cond
  refine ⟨result, after, slowNext, loop, broke, ?_,
    nextPacket⟩
  exact account.no_pull_from_stream packet nextPacket cursor source

/-- An invalid literal/length table leaf retains the account through
its translated error `break`. -/
theorem FastInputPacket.dolen_invalid_leaf_account_default_state
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {ctx : FastLoopContext} {startOff startBits : Nat}
    (packet : FastInputPacket h slow bs l)
    (account : FastInputAccount ctx startOff startBits l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow bs)
    (streamPtr : c.strm = some r)
    (statePtr : c.state = some (.tab zs))
    {codeRef : CodeRef} {codes : Array Code} {index : Nat}
    (herePtr : l.here = .ref codeRef index)
    (codesGet : Space.get h codeRef = some codes)
    (codeIndex : index < codes.size)
    (codeBits : codes[index].bits.toNat ≤ slow.bits.toNat)
    (codeWidth : codes[index].bits.toNat ≤ 15)
    (nonzero : codes[index].op ≠ 0)
    (notBase : (codes[index].op.toUInt32 &&& 16 != 0) = false)
    (notLink : (codes[index].op.toUInt32 &&& 64 == 0) = false)
    (notEnd : (codes[index].op.toUInt32 &&& 32 != 0) = false) :
    ∃ result after slowNext,
      C.run (Zlib.Inffast.dolen c l) h = .ok (result, after) ∧
      result.broke = true ∧
      FastInputAccount ctx startOff startBits result ∧
      FastInputPacket after slowNext bs result := by
  obtain ⟨i, after, result, slowNext, run, _, broke,
    _, cursor, _, nextPacket, _, _, _, source⟩ :=
    packet.dolen_invalid_leaf_default_state invariant
      buffers streamPtr statePtr herePtr codesGet codeIndex
      codeBits codeWidth nonzero notBase notLink notEnd
  refine ⟨result, after, slowNext, run, broke, ?_,
    nextPacket⟩
  exact account.no_pull_from_stream packet nextPacket cursor source

/-- The real one-pass `dolen` loop retains the account when it exits on
an invalid length code. -/
theorem FastInputPacket.dolen_root_invalid_loop_account_default_state
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {ctx : FastLoopContext} {startOff startBits : Nat}
    (packet : FastInputPacket h slow bs l)
    (account : FastInputAccount ctx startOff startBits l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow bs)
    (streamPtr : c.strm = some r)
    (statePtr : c.state = some (.tab zs))
    {codeRef : CodeRef} {codes : Array Code} {index : Nat}
    (herePtr : l.here = .ref codeRef index)
    (codesGet : Space.get h codeRef = some codes)
    (codeIndex : index < codes.size)
    (codeBits : codes[index].bits.toNat ≤ slow.bits.toNat)
    (codeWidth : codes[index].bits.toNat ≤ 15)
    (nonzero : codes[index].op ≠ 0)
    (notBase : (codes[index].op.toUInt32 &&& 16 != 0) = false)
    (notLink : (codes[index].op.toUInt32 &&& 64 == 0) = false)
    (notEnd : (codes[index].op.toUInt32 &&& 32 != 0) = false) :
    ∃ result after slowNext,
      C.run (cdoWhile (Zlib.Inffast.dolen c)
        (fun current => pure (current.againL, current)) l) h =
        .ok (result, after) ∧
      result.broke = true ∧
      FastInputAccount ctx startOff startBits result ∧
      FastInputPacket after slowNext bs result ∧
      DispatchBuffers after r slowNext bs ∧
      ∃ i, DefaultStateJ after r zs
        { z with msg := .ref (.str i) 0 }
        { s with mode := BAD } := by
  obtain ⟨i, after, result, slowNext, leafRun, _, broke,
    againL, cursor, _, nextPacket, nextState,
    nextBuffers, _, source⟩ :=
    packet.dolen_invalid_leaf_default_state invariant
      buffers streamPtr statePtr herePtr codesGet codeIndex
      codeBits codeWidth nonzero notBase notLink notEnd
  refine ⟨result, after, slowNext,
    dolen_loop_one leafRun againL, broke, ?_, nextPacket,
    nextBuffers, i, nextState⟩
  exact account.no_pull_from_stream packet nextPacket cursor source

/-- The actual distance-too-far branch does not read input or change the
held-bit count before its error `break`. -/
theorem FastInputPacket.copyMatch_invalid_account_default_state
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {ctx : FastLoopContext} {startOff startBits : Nat}
    (packet : FastInputPacket h slow bs l)
    (account : FastInputAccount ctx startOff startBits l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow bs)
    (streamPtr : c.strm = some r)
    (statePtr : c.state = some (.tab zs))
    (windowBranch : l.dist > l.op)
    (invalidBack : l.dist - l.op > c.whave)
    {dest : BRef} {output : Array UInt8}
    (outputGet : Space.get h dest = some output)
    (outputWrite : Space.ro h dest = false) :
    ∃ after,
      C.run (Zlib.Inffast.copyMatch c l) h =
        .ok ({ l with op := l.dist - l.op, broke := true }, after) ∧
      FastInputAccount ctx startOff startBits
        { l with op := l.dist - l.op, broke := true } := by
  obtain ⟨i, after, run, _, _, _, _, _, _, _⟩ :=
    packet.copyMatch_invalid_default_state invariant buffers
      streamPtr statePtr windowBranch invalidBack
      outputGet outputWrite
  exact ⟨after, run,
    account.no_pull rfl (Nat.le_refl _)⟩

end Zlib.Inflate.Proofs
