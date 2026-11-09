import ZlibF.Proof.«deflate.c.engine.pending-resume»
import ZlibF.Proof.«deflate.c.engine.flush-size»

/-! # Exact byte potential through resumed pending publication -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- Real low-bit pending publication transfers its exact byte potential
to the caller, even at an advanced pending cursor and zero output room.
No pending byte is counted twice after a partial drain. The observed run
is identified with the already proved actual zero/nonzero executions. -/
theorem flush_pending_run_byte_potential {h after : Heap} {r : ZStreamRef} {ds ob oo produced : Nat}
    {z z' : ZStream} {d result : DeflateState}
    (good : DGood h r ds z d) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo) (low : d.bi_valid.toInt < 8)
    (observed : flush_pending (some r) h = .ok ((), after))
    (live : after.dstates ds = some result) (stream : r.get after = some z')
    (account : StreamAccounting z z' 0 produced) :
    produced + result.pending.toNat + (result.bi_valid.toInt.toNat + 7) / 8 =
      d.pending.toNat + (d.bi_valid.toInt.toNat + 7) / 8 ∧
    FlushWorkFrame d result ∧
    (ShortCandidateQuality d → ShortCandidateQuality result) ∧
    (StoredSourceFloor d → StoredSourceFloor result) := by
  obtain ⟨w, p, q, pb, blocks⟩ := good.inv.blocks
  obtain ⟨buf, get, size⟩ := blocks.ba
  obtain ⟨offset, cursor, bound⟩ := blocks.pout
  have sourceBound : offset + d.pending.toNat ≤ buf.size := by
    rw [size, ← blocks.psize]; exact bound
  have pending := pending_bits_slice cursor get sourceBound
  obtain ⟨_pendingId, amount, middle, nextZ, nextD, _written, _remaining, _base, run, goodA, _buffersA,
    accountA, _sizesA, _storageA, _copied, left, _lowA, fields, _emptyCursor, _bytes, _pendingA, _wire⟩ :=
    flush_pending_resume_raw_bits good buffers pointer low pending
  have heaps : middle = after := (Prod.mk.inj (Except.ok.inj (run.symm.trans observed))).2
  rw [heaps] at goodA
  have streams : nextZ = z' := Option.some.inj (goodA.live.hz.symm.trans stream)
  have states : nextD = result := Option.some.inj (goodA.live.hs.symm.trans live)
  rw [streams] at accountA
  have amounts : amount = produced := by
    have first := accountA.2.2.2.1
    have second := account.2.2.2.1
    omega
  rw [states, amounts] at left
  rw [states] at fields
  have bits : result.bi_valid = d.bi_valid := by rw [fields]
  refine ⟨by rw [bits]; omega, ?_, ?_, ?_⟩
  · rw [fields]; rfl
  · intro candidate
    rw [fields]
    exact candidate
  · intro floor
    rw [fields]
    exact floor

end Zlib.Deflate.Engine.Proofs
