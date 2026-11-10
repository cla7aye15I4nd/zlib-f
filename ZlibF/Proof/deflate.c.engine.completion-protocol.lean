import ZlibF.Proof.«deflate.c.engine.encoding-data-history»
import ZlibF.Proof.«deflate.c.engine.finishing-new-input»

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- This necessary protocol fact is derived from actual default histories.
It does not assert that such a finishing history exists or refute the
complete public completion target on its own. -/
theorem DefaultDataTrace.finished_new_input_not_end
    {h : Heap} {r : ZStreamRef} {log : DataLog} {ds ob oo : Nat}
    {z : ZStream} {d : DeflateState} {input : List UInt8}
    (history : DefaultDataTrace r h log) (good : DGood h r ds z d)
    (status : d.status = FINISH_STATE) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo) (output : 0 < z.avail_out.toNat)
    (nonempty : z.avail_in ≠ 0) (snapshot : Bytes h z.next_in z.avail_in.toNat input) :
    ¬ ∃ after, C.run (deflate (some r) Z_FINISH) h = .ok (Z_STREAM_END, after) := by
  obtain ⟨ds0, z0, d0, config, protocol⟩ := history.protocol
  have sameZ : z0 = z := Option.some.inj (protocol.good.live.hz.symm.trans good.live.hz)
  subst z0
  have sameDS : ds0 = ds := by
    simpa only [protocol.good.live.zst, Option.some.injEq, StateRef.deflate.injEq] using good.live.zst
  subst ds0
  have sameD : d0 = d := Option.some.inj (protocol.good.live.hs.symm.trans good.live.hs)
  subst d0
  have finishing : FinishingPhase d config := by
    rcases protocol.phase with ⟨_, _, _, start, _⟩ | ⟨_, _, _, _, _, busy⟩ | phase
    · exact False.elim ((by decide : INIT_STATE ≠ FINISH_STATE) (start.status.symm.trans status))
    · exact False.elim ((by decide : BUSY_STATE ≠ FINISH_STATE) (busy.symm.trans status))
    · exact phase
  have valid : z.avail_in ≠ 0 → z.next_in ≠ .null := by
    intro count null
    rcases snapshot with zero | ⟨ref, offset, array, ptr, _⟩
    · exact count (UInt32.toNat_inj.mp zero.2.1)
    · rw [null] at ptr
      cases ptr
  obtain ⟨produced, rc, computed, z', result, run, _goodA, _buffersA, _account,
      allowed, _phaseA, _lastA, _inputA, _exhausted⟩ :=
    public_default_finishing_new_input good buffers finishing pointer valid nonempty output
      protocol.lower protocol.upper
  rintro ⟨after, ended⟩
  have code : rc = Z_STREAM_END := (Prod.mk.inj (Except.ok.inj (run.symm.trans ended))).1
  rcases allowed with ok | refused
  · exact (by decide : Z_OK ≠ Z_STREAM_END) (ok.symm.trans code)
  · exact (by decide : Z_BUF_ERROR ≠ Z_STREAM_END) (refused.symm.trans code)

end Zlib.Deflate.Engine.Proofs
