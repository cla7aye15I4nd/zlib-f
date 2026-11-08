import ZlibF.Proof.«deflate.c.engine.loop-phase»
import ZlibF.Proof.«deflate.c.engine.pending-resume»

/-! # Actual pending publication returns a continuing or output-full phase -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt)
set_option autoImplicit false

/-- `local void flush_pending(z_streamp strm)`.
The real bit flush and pending copy retain configuration. If caller output
space remains, complete bytes are drained and the pending cursor is at its
base. Zero-copy and short-output cases are proved from actual execution. -/
theorem pending_publication_phase_execution {h : Heap} {r : ZStreamRef} {ds pb ob oo : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) (pointer : z.next_out = .ref (.blk ob) oo)
    (cursor : d.pending_out = d.pending_buf)
    (room : 8 * d.pending.toNat + d.bi_valid.toInt.toNat ≤ 8 * buf.size) :
    ∃ after z' result,
      flush_pending (some r) h = .ok ((), after) ∧ DGood after r ds z' result ∧ StreamBuffers after r ∧
      ConfigFrame d result ∧ result.bi_valid.toInt < 8 ∧
      (0 < z'.avail_out.toNat → PublishReady result) := by
  obtain ⟨next, prepared, _bitRun, goodP, treesP, _bitStream, low, size, diff, _pendingCount, _validCount, sameRun⟩ :=
    flush_pending_prepare good trees cursor room
  let ready := setD (Zlib.Trees.Proofs.Out.setB h pb next) ds prepared
  have buffersP : StreamBuffers ready r := output_bits_buffers good buffers cursor trees.base.bytes size diff treesP
  have cursorP : prepared.pending_out = prepared.pending_buf := by
    obtain ⟨_, _, _, _, fields⟩ := diff
    rw [fields]
    exact cursor
  obtain ⟨_pb, produced, after, z', result, _written, _remaining, _base, run, goodA, buffersA,
    account, _sizes, _storage, count, left, lowA, fields, reset, _bytes, _pending, _output⟩ :=
    flush_pending_resume_raw_bits goodP buffersP pointer low (pending_bits_base treesP cursorP)
  have configP := ConfigFrame.bits diff
  have configA : ConfigFrame prepared result := by rw [fields]; rfl
  refine ⟨after, z', result, sameRun.trans run, goodA, buffersA, configP.trans configA, lowA, ?_⟩
  intro space
  have available := account.2.2.2.1
  have drained : result.pending.toNat = 0 := by omega
  have pendingZero : result.pending = 0 := by
    apply UInt64.toNat_inj.mp
    exact drained
  refine ⟨pendingZero, ?_, lowA⟩
  by_cases moved : 0 < produced
  · exact reset moved drained
  · have zero : produced = 0 := by omega
    have noCopy : pendingLen prepared.pending z.avail_out = 0 := by
      apply UInt32.toNat_inj.mp
      change (pendingLen prepared.pending z.avail_out).toNat = 0
      rw [pendingLen_value]
      omega
    have zeroRun := flush_pending_low_zero goodP.live.hz goodP.live.zst goodP.live.hs low noCopy
    have heapEq : ready = after := (Prod.mk.inj (Except.ok.inj (zeroRun.symm.trans run))).2
    have liveA : ready.dstates ds = some result := by rw [heapEq]; exact goodA.live.hs
    have stateEq : result = prepared := Option.some.inj (liveA.symm.trans goodP.live.hs)
    rw [stateEq]
    exact cursorP

/-- The proved phase applies to any actual successful publication run.
Heap determinism identifies both the state record and the returned stream. -/
theorem pending_publication_run_phase {h after : Heap} {r : ZStreamRef} {ds pb ob oo : Nat}
    {z z' : ZStream} {d result : DeflateState} {buf : Array UInt8}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) (pointer : z.next_out = .ref (.blk ob) oo)
    (cursor : d.pending_out = d.pending_buf)
    (room : 8 * d.pending.toNat + d.bi_valid.toInt.toNat ≤ 8 * buf.size)
    (run : flush_pending (some r) h = .ok ((), after))
    (live : after.dstates ds = some result) (stream : r.get after = some z') :
    ConfigFrame d result ∧ result.bi_valid.toInt < 8 ∧ (0 < z'.avail_out.toNat → PublishReady result) := by
  obtain ⟨otherHeap, otherZ, otherD, otherRun, otherGood, _buffersA, config, low, phase⟩ :=
    pending_publication_phase_execution good trees buffers pointer cursor room
  have heapEq : otherHeap = after := (Prod.mk.inj (Except.ok.inj (otherRun.symm.trans run))).2
  rw [heapEq] at otherGood
  have stateEq : otherD = result := Option.some.inj (otherGood.live.hs.symm.trans live)
  have streamEq : otherZ = z' := Option.some.inj (otherGood.live.hz.symm.trans stream)
  rw [← stateEq, ← streamEq]
  exact ⟨config, low, phase⟩

end Zlib.Deflate.Engine.Proofs
