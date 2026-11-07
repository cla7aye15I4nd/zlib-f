import ZlibF.Proof.«deflate.c.engine.header-caller»

/-! # The first actual default public compressor call before block output

This supporting path emits the wrapper header and executes the selected
strategy on the same heap. The full public target is unchanged.
-/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

theorem stream_accounting_trans {a b c : ZStream} {used1 used2 produced1 produced2 : Nat}
    (one : StreamAccounting a b used1 produced1) (two : StreamAccounting b c used2 produced2) :
    StreamAccounting a c (used1 + used2) (produced1 + produced2) := by
  rcases one with ⟨boundIn1, boundOut1, input1, output1, inPtr1, outPtr1, state1, alloc1, free1, opaque1, reserved1⟩
  rcases two with ⟨boundIn2, boundOut2, input2, output2, inPtr2, outPtr2, state2, alloc2, free2, opaque2, reserved2⟩
  refine ⟨by omega, by omega, by omega, by omega, ?_, ?_, state2.trans state1,
    alloc2.trans alloc1, free2.trans free1, opaque2.trans opaque1, reserved2.trans reserved1⟩
  · rw [inPtr2, inPtr1, advance_add]
  · rw [outPtr2, outPtr1, advance_add]

theorem caller_raw_output {h : Heap} {r : ZStreamRef} {ds ob oo : Nat}
    {z : ZStream} {d : DeflateState} (good : DGood h r ds z d) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo) :
    ∃ output, h.bytes ob = some output ∧ h.ro ob = false ∧ oo + z.avail_out.toNat ≤ output.size ∧
      ¬ DeflateOwned ds d ob := by
  obtain ⟨old, getter, _input, output, _separate⟩ := buffers
  have equal : old = z := Option.some.inj (getter.symm.trans good.live.hz)
  subst old
  rw [pointer] at output
  rcases output with null | ⟨_bytes, writable, outside⟩
  · cases null
  · rcases writable rfl with ⟨null, _⟩ | ⟨ref, off, array, ptr, get, ro, bound⟩
    · cases null
    · have same : ref = .blk ob ∧ off = oo := by simpa only [Ptr.ref.injEq] using ptr.symm
      rcases same with ⟨refEq, offEq⟩
      subst ref off
      exact ⟨array, get, ro, bound, fun mine => outside ob rfl ((stream_owned_deflate good ob).mpr mine)⟩

/-- `int ZEXPORT deflate(z_streamp strm, int flush)` (empty data tail).
After a complete zlib header, empty input and lookahead return Z_OK
without executing a strategy or emitting block bits on Z_NO_FLUSH. -/
theorem public_default_empty_data {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (good : DGood h r ds z d) (status : d.status = BUSY_STATE) (empty : z.avail_in = 0)
    (look : d.lookahead = 0) :
    publicDataTail (some r) (some (.tab ds)) Z_NO_FLUSH h = .ok (Z_OK, h) := by
  unfold publicDataTail
  simp only [bind_app, pure_app, rdD_eq, good.live.hs, status,
    show (BUSY_STATE == GZIP_STATE) = false from by decide,
    show (BUSY_STATE == EXTRA_STATE) = false from by decide,
    show (BUSY_STATE == NAME_STATE) = false from by decide,
    show (BUSY_STATE == COMMENT_STATE) = false from by decide,
    show (BUSY_STATE == HCRC_STATE) = false from by decide,
    Bool.false_eq_true, ite_false, ldDeflateState_tab good.live.hs, zrd_eq, good.live.hz,
    empty, look, show ((0 : UInt32) != 0) = false from rfl,
    show (Z_NO_FLUSH != Z_NO_FLUSH) = false from rfl, Bool.false_and, Bool.false_or,
    show (Z_NO_FLUSH != Z_FINISH) = true from rfl, ite_true]

set_option maxHeartbeats 2500000 in
/-- `int ZEXPORT deflate(z_streamp strm, int flush)`.
The first default level-six Z_NO_FLUSH call emits its complete two-byte
header, executes the selected slow strategy and accepts all input before
block output. Explicit internal path restrictions are raw output, at
least three output bytes and the current block's byte budget. Empty input
is included. This supporting theorem does not replace Goal.deflate. -/
theorem public_default_first_before_block_output {h : Heap} {r : ZStreamRef} {ds ob oo : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8}
    (initial : EngineStart h r ds z d) (level : d.level = 6)
    (boundary : ContentBoundary h r ds z d input 0 0 []) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo) (outputRoom : 3 ≤ z.avail_out.toNat)
    (valid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (capacity : 3 * (fillEnd d + z.avail_in.toNat + 1) < d.sym_end.toNat) :
    ∃ used after z' result ys extended nextOrigin,
      deflate (some r) Z_NO_FLUSH h = .ok (Z_OK, after) ∧
      ContentBoundary after r ds z' result extended nextOrigin 0 ys ∧ StreamBuffers after r ∧
      StreamAccounting z z' used 2 ∧ used = z.avail_in.toNat ∧ z'.avail_in = 0 ∧
      result.lookahead.toNat < 262 ∧ nextOrigin + fillEnd result = fillEnd d + used ∧
      expandSymbols ys (inputPrefix extended 0) =
        inputPrefix extended (nextOrigin + result.strstart.toNat - pendingCredit result) ∧
      ∃ written, after.bytes ob = some written ∧ written[oo]? = some 120 ∧ written[oo + 1]? = some 156 := by
  obtain ⟨output, outGet, outRw, outBound, outside⟩ := caller_raw_output initial.good buffers pointer
  obtain ⟨oldD, pb, buf, trees⟩ := initial.good.trees
  have sameD : oldD = d := Option.some.inj (trees.base.dstate.symm.trans initial.good.live.hs)
  subst oldD
  have separate : ob ≠ pb := by
    intro same
    subst ob
    exact outside (Or.inr (Or.inr (Or.inr (Or.inr trees.base.pbuf))))
  have room : 2 ≤ buf.size := by have size := trees.base.size; have lo := trees.base.lit_lo; omega
  have first := public_default_header_complete initial level trees.base.pbuf trees.base.bytes room trees.base.rw
    pointer outGet outRw separate outBound (by omega) valid
  let header := headerCompleteHeap h r ds pb ob oo z d buf output
  let zh := headerCompleteStream z ob oo
  let dh := headerCompleteState d
  have content : ContentBoundary header r ds zh dh input 0 0 [] :=
    header_complete_content boundary trees.base.pbuf trees.base.bytes outGet outside
  have buffer : StreamBuffers header r :=
    header_complete_buffers initial.good buffers trees.base.bytes outGet separate pointer (by omega)
  have accounting : StreamAccounting z zh 0 2 := header_complete_accounting pointer (by omega)
  have positive : zh.avail_out ≠ 0 := by
    intro zero
    have count := accounting.2.2.2.1
    rw [zero] at count
    change 0 + 2 = z.avail_out.toNat at count
    omega
  have inputValid : zh.avail_in ≠ 0 → zh.next_in ≠ .null := valid
  have headerWritten := header_complete_prefix h r ds pb ob oo z d buf output room (by omega)
  by_cases empty : z.avail_in = 0
  · have stop := public_default_empty_data content.good rfl empty initial.lookahead
    refine ⟨0, header, zh, dh, [], input, 0, first.trans stop, content, buffer, accounting, ?_, empty, ?_, by simp [dh, headerCompleteState, fillEnd], content.expands, headerWritten⟩
    · rw [empty]; rfl
    · change d.lookahead.toNat < 262
      rw [initial.lookahead]
      decide
  · obtain ⟨used, after, z', result, ys, extended, nextOrigin, run, contentA, buffersA, accountA,
      _storage, _fields, _agrees, _symbols, endpoint, expands, usedAll, emptyA, shortA⟩ :=
      public_default_data_before_block content rfl level initial.strategy initial.wrap buffer positive inputValid
        (Or.inl empty) (by simpa [dh, zh, headerCompleteState, headerCompleteStream, pendingStream, fillEnd] using capacity)
    have total := stream_accounting_trans accounting accountA
    obtain ⟨written, getWritten, byte0, byte1⟩ := headerWritten
    have preserved : after.bytes ob = some written :=
      (_storage.bytes ob outside).trans getWritten
    exact ⟨used, after, z', result, ys, extended, nextOrigin, first.trans run, contentA, buffersA,
      by simpa only [Nat.zero_add, Nat.add_zero] using total, usedAll, emptyA, shortA, by simpa [dh, headerCompleteState, fillEnd] using endpoint, expands, written, preserved, byte0, byte1⟩

/-- The first-call endpoint result retains its exact statement. -/
theorem public_default_first_before_block_endpoint {h : Heap} {r : ZStreamRef} {ds ob oo : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8}
    (initial : EngineStart h r ds z d) (level : d.level = 6)
    (boundary : ContentBoundary h r ds z d input 0 0 []) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo) (outputRoom : 3 ≤ z.avail_out.toNat)
    (valid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (capacity : 3 * (fillEnd d + z.avail_in.toNat + 1) < d.sym_end.toNat) :
    ∃ used after z' result ys extended nextOrigin,
      deflate (some r) Z_NO_FLUSH h = .ok (Z_OK, after) ∧
      ContentBoundary after r ds z' result extended nextOrigin 0 ys ∧ StreamBuffers after r ∧
      StreamAccounting z z' used 2 ∧ used = z.avail_in.toNat ∧ z'.avail_in = 0 ∧
      result.lookahead.toNat < 262 ∧ nextOrigin + fillEnd result = fillEnd d + used ∧
      expandSymbols ys (inputPrefix extended 0) =
        inputPrefix extended (nextOrigin + result.strstart.toNat - pendingCredit result) := by
  obtain ⟨used, after, z', result, ys, extended, nextOrigin, run, content, buffer, account, allInput,
    empty, short, endpoint, expands, _written⟩ :=
    public_default_first_before_block_output initial level boundary buffers pointer outputRoom valid capacity
  exact ⟨used, after, z', result, ys, extended, nextOrigin, run, content, buffer, account, allInput,
    empty, short, endpoint, expands⟩

/-- The earlier first-call result retains its exact statement. -/
theorem public_default_first_before_block {h : Heap} {r : ZStreamRef} {ds ob oo : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8}
    (initial : EngineStart h r ds z d) (level : d.level = 6)
    (boundary : ContentBoundary h r ds z d input 0 0 []) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo) (outputRoom : 3 ≤ z.avail_out.toNat)
    (valid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (capacity : 3 * (fillEnd d + z.avail_in.toNat + 1) < d.sym_end.toNat) :
    ∃ used after z' result ys extended nextOrigin,
      deflate (some r) Z_NO_FLUSH h = .ok (Z_OK, after) ∧
      ContentBoundary after r ds z' result extended nextOrigin 0 ys ∧ StreamBuffers after r ∧
      StreamAccounting z z' used 2 ∧ used = z.avail_in.toNat ∧ z'.avail_in = 0 ∧
      result.lookahead.toNat < 262 ∧
      expandSymbols ys (inputPrefix extended 0) =
        inputPrefix extended (nextOrigin + result.strstart.toNat - pendingCredit result) := by
  obtain ⟨used, after, z', result, ys, extended, nextOrigin, run, content, buffer, account, allInput,
    empty, short, _endpoint, expands⟩ :=
    public_default_first_before_block_endpoint initial level boundary buffers pointer outputRoom valid capacity
  exact ⟨used, after, z', result, ys, extended, nextOrigin, run, content, buffer, account, allInput, empty, short, expands⟩

end Zlib.Deflate.Engine.Proofs
