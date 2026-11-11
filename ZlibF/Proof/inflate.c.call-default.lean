import ZlibF.Proof.«inflate.c.invariant-bridge»
import ZlibF.Proof.«inflate.c.origin-fields-memory-contract»
import ZlibF.Proof.«inflate.c.default-error-clauses»
import ZlibF.Proof.«inflate.c.output-frame-footprint-compose»

/-!
# inflate.c: one `inflate` call in the default configuration

`InflateCall` is the conclusion of `Goal.inflate` with `Good` strengthened to
the history invariant on the returned state. In the default configuration
(zlib or raw wrapper, a fixed window width; the requested width and wrapper
may differ, since `inflate` does not read them), a call whose entry checks pass and that does not start in
`SYNC` satisfies it. The proof combines the default memory contract, the
origin facts and the error clauses; no callee contract is assumed.
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The conclusion of `Goal.inflate`, with the invariant on the returned state. -/
def InflateCall (h : Heap) (r : ZStreamRef) (i : Nat) (z : ZStream) (s : InflateState)
    (flush : Int32) : Prop :=
  ∃ rc after z' s' used out,
    C.run (Zlib.Inflate.inflate (some r) flush) h = .ok (rc, after) ∧
    InflateInv after r i z' s' ∧ StreamAccounting z z' used out.length ∧
    Bytes after z.next_out out.length out ∧
    (rc = Z_OK ∨ rc = Z_STREAM_END ∨ rc = Z_NEED_DICT ∨ rc = Z_STREAM_ERROR ∨
     rc = Z_DATA_ERROR ∨ rc = Z_MEM_ERROR ∨ rc = Z_BUF_ERROR) ∧
    (rc = Z_OK → (used ≠ 0 ∨ out ≠ []) ∧ flush ≠ Z_FINISH) ∧
    (rc = Z_STREAM_ERROR ↔
      z.next_out = .null ∨ (z.next_in = .null ∧ z.avail_in ≠ 0) ∨ s.mode = SYNC) ∧
    (rc = Z_STREAM_ERROR → z' = z ∧ s' = s ∧ used = 0 ∧ out = []) ∧
    (rc = Z_BUF_ERROR → (used = 0 ∧ out = []) ∨ flush = Z_FINISH) ∧
    (z.avail_in ≠ 0 → z.avail_out ≠ 0 → flush ≠ Z_BLOCK → flush ≠ Z_TREES →
      rc = Z_BUF_ERROR → used ≠ 0 ∨ out ≠ []) ∧
    (rc = Z_STREAM_END → s'.mode = DONE) ∧
    (rc = Z_NEED_DICT → s'.mode = DICT) ∧
    (rc = Z_DATA_ERROR → s'.mode = BAD) ∧
    (rc = Z_MEM_ERROR → s'.mode = MEM ∧ z'.total_in = z.total_in ∧ z'.total_out = z.total_out) ∧
    (rc = Z_OK ∨ rc = Z_STREAM_END ∨ rc = Z_DATA_ERROR ∨ rc = Z_BUF_ERROR →
      z'.total_in = z.total_in + UInt64.ofNat used ∧
      z'.total_out = z.total_out + UInt64.ofNat out.length) ∧
    BufferFrame h after
      (fun b => StreamRoot r b ∨ InflateOwned i s b ∨ s.head = some (.tab b))
      (⟨z.next_out, out.length⟩ :: HeaderRegions h s.head) ∧
    LiveChange h after (fun b => InflateOwned i s' b ∧ ¬ h.live b) (fun _ => False)

/-- The caller premises of one call, with the platform object-size limit. -/
structure CallPremises (h : Heap) (r : ZStreamRef) : Prop where
  platform : ZlibF.PlatformMemory.ByteObjectsFit h
  buffers : StreamBuffers h r
  header : ActiveHeader h r

/-- The default configuration after entry: the default memory contract,
the origin facts, and the error clauses. -/
theorem inflate_call_default {h : Heap} {r : ZStreamRef} {i : Nat} {z : ZStream} {s : InflateState}
    (current : InflateInv h r i z s) (caller : CallPremises h r) (flush : Int32)
    (config : DefaultConfig s)
    (accepted : z.next_out ≠ .null ∧ (z.next_in = .null → z.avail_in = 0) ∧ s.mode ≠ SYNC) :
    InflateCall h r i z s flush := by
  have origin := current.to_origin config caller.platform
  obtain ⟨rc, after, stream, state, used, output, run, next, finalAllocator, _, accounting,
    bytes, totals, progress, codes, memoryTotals, modes, frame, ledger⟩ :=
    inflate_default_origin_public_memory_contract origin current.alloc caller.buffers flush
  obtain ⟨rc2, after2, stream2, state2, used2, made2, run2, next2, accounting2, notStream,
    buffer, moving⟩ :=
    inflate_default_view_public_error_clauses origin.toDefaultStateJ current.alloc
      caller.buffers flush accepted.1 accepted.2.1 accepted.2.2
  have same := Except.ok.inj (run2.symm.trans run)
  cases same
  have sameZ : stream2 = stream := Option.some.inj (next2.good.live.hz.symm.trans next.good.live.hz)
  subst stream2
  have usedEq : used2 = used := by
    have one := accounting.2.2.1
    have two := accounting2.2.2.1
    omega
  have madeEq : made2 = output.length := by
    have one := accounting.2.2.2.1
    have two := accounting2.2.2.2.1
    omega
  subst used2 made2
  have header : s.head = none := origin.header
  refine ⟨rc, after, stream, state, used, output, run, InflateInv.of_origin next finalAllocator,
    accounting, bytes, codes, progress, ⟨fun e => absurd e notStream, ?_⟩,
    fun e => absurd e notStream, ?_, ?_, modes.1, modes.2.1, modes.2.2.1,
    fun e => ⟨modes.2.2.2 e, (memoryTotals e).1, (memoryTotals e).2⟩, totals, ?_, ledger⟩
  · intro refused
    exfalso
    rcases refused with output | ⟨input, pending⟩ | sync
    · exact accepted.1 output
    · exact pending (accepted.2.1 input)
    · exact accepted.2.2 sync
  · intro buffered
    rcases buffer buffered with ⟨none, empty⟩ | finish
    · exact Or.inl ⟨none, List.eq_nil_of_length_eq_zero empty⟩
    · exact Or.inr finish
  · intro input space notBlock notTrees buffered
    rcases moving input space notBlock notTrees buffered with consumed | made
    · exact Or.inl consumed
    · exact Or.inr (fun empty => made (by rw [empty]; rfl))
  · rw [header]
    exact inflate_buffer_frame_mono frame
      (fun b changed => changed.elim Or.inl (fun owned => Or.inr (Or.inl owned)))

#print axioms inflate_call_default
end Zlib.Inflate.Proofs
