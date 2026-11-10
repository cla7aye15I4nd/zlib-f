import ZlibF.Proof.«deflate.c.engine.public-finish-phase»
import ZlibF.Proof.«deflate.c.engine.finish-entry»

/-! # The actual public FINISH entry continues after a partial pending phase -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- A live represented stream has a concrete pending bit sequence at its current cursor. -/
theorem good_pending_bits {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (good : DGood h r ds z d) : ∃ bits, PendingBits h d bits := by
  obtain ⟨w, p, q, pb, blocks⟩ := good.inv.blocks
  obtain ⟨buf, get, size⟩ := blocks.ba
  obtain ⟨po, cursor, bound⟩ := blocks.pout
  exact ⟨_, pending_bits_slice cursor get (by rw [size, ← blocks.psize]; exact bound)⟩

/-- The accepted entry uses the actual pending run, then reaches the
header/data tail when caller output remains. No callee contract is assumed. -/
theorem public_pending_finish_continue {h middle : Heap} {r : ZStreamRef} {ds : Nat}
    {z zm : ZStream} {d result : DeflateState}
    (good : DGood h r ds z d) (goodM : DGood middle r ds zm result)
    (out : z.next_out ≠ .null) (positive : z.avail_out ≠ 0)
    (input : z.avail_in ≠ 0 → z.next_in ≠ .null) (pending : d.pending ≠ 0)
    (run : flush_pending (some r) (setD h ds { d with last_flush := Z_FINISH }) = .ok ((), middle))
    (remaining : zm.avail_out ≠ 0) (finishedInput : result.status = FINISH_STATE → zm.avail_in = 0) :
    deflate (some r) Z_FINISH h =
      publicZlibHeader (some r) (some (.tab ds))
        (publicDataTail (some r) (some (.tab ds)) Z_FINISH) middle := by
  have inputs : (z.avail_in != 0 && z.next_in == .null) = false := by
    by_cases empty : z.avail_in = 0
    · simp [empty]
    · simp [input empty]
  have finishInput : (result.status == FINISH_STATE && zm.avail_in != 0) = false := by
    by_cases status : result.status = FINISH_STATE
    · simp [status, finishedInput status]
    · simp [status]
  have checked := stateCheck_live good.live
  rw [public_deflate_source]
  simp only [bind_app, pure_app, checked, show ((0 : Int32) != 0) = false from rfl,
    show (Z_FINISH > Z_BLOCK) = False from by decide, show (Z_FINISH < 0) = False from by decide,
    decide_false, Bool.false_or, Bool.false_eq_true, ite_false,
    zrd_eq, good.live.hz, good.live.zst, castDeflateState,
    ldZStream_ok good.live.hz, ldDeflateState_tab good.live.hs,
    show (z.next_out == .null) = false from beq_eq_false_iff_ne.mpr out,
    inputs, show (Z_FINISH != Z_FINISH) = false from rfl, Bool.and_false, Bool.or_false,
    show (z.avail_out == 0) = false from beq_eq_false_iff_ne.mpr positive,
    wrD_eq, good.live.hs, show (d.pending != 0) = true from bne_iff_ne.mpr pending,
    ite_true, run, goodM.live.hz,
    show (zm.avail_out == 0) = false from beq_eq_false_iff_ne.mpr remaining,
    rdD_eq, goodM.live.hs, finishInput]

/-- Exhausted pending publication returns before any new strategy or trailer. -/
theorem public_pending_finish_exhausted {h middle : Heap} {r : ZStreamRef} {ds : Nat}
    {z zm : ZStream} {d result : DeflateState}
    (good : DGood h r ds z d) (goodM : DGood middle r ds zm result)
    (out : z.next_out ≠ .null) (positive : z.avail_out ≠ 0)
    (input : z.avail_in ≠ 0 → z.next_in ≠ .null) (pending : d.pending ≠ 0)
    (run : flush_pending (some r) (setD h ds { d with last_flush := Z_FINISH }) = .ok ((), middle))
    (exhausted : zm.avail_out = 0) :
    deflate (some r) Z_FINISH h = .ok (Z_OK, setD middle ds { result with last_flush := -1 }) := by
  have inputs : (z.avail_in != 0 && z.next_in == .null) = false := by
    by_cases empty : z.avail_in = 0
    · simp [empty]
    · simp [input empty]
  have checked := stateCheck_live good.live
  rw [public_deflate_source]
  simp only [bind_app, pure_app, checked, show ((0 : Int32) != 0) = false from rfl,
    show (Z_FINISH > Z_BLOCK) = False from by decide, show (Z_FINISH < 0) = False from by decide,
    decide_false, Bool.false_or, Bool.false_eq_true, ite_false,
    zrd_eq, good.live.hz, good.live.zst, castDeflateState,
    ldZStream_ok good.live.hz, ldDeflateState_tab good.live.hs,
    show (z.next_out == .null) = false from beq_eq_false_iff_ne.mpr out,
    inputs, show (Z_FINISH != Z_FINISH) = false from rfl, Bool.and_false, Bool.or_false,
    show (z.avail_out == 0) = false from beq_eq_false_iff_ne.mpr positive,
    wrD_eq, good.live.hs, show (d.pending != 0) = true from bne_iff_ne.mpr pending,
    ite_true, run, goodM.live.hz, exhausted, BEq.rfl, goodM.live.hs]

/-- BUSY states skip the zlib header statements on every continuation. -/
theorem public_busy_header_skip {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (good : DGood h r ds z d) (status : d.status = BUSY_STATE) :
    publicZlibHeader (some r) (some (.tab ds))
      (publicDataTail (some r) (some (.tab ds)) Z_FINISH) h =
      publicDataTail (some r) (some (.tab ds)) Z_FINISH h := by
  unfold publicZlibHeader
  simp only [bind_app, pure_app, rdD_eq, good.live.hs, status,
    show (BUSY_STATE == INIT_STATE) = false from rfl, Bool.false_and, Bool.false_eq_true, ite_false]

end Zlib.Deflate.Engine.Proofs
