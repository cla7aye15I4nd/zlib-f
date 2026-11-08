import ZlibF.Proof.«deflate.c.engine.pending-counters»
import ZlibF.Proof.«deflate.c.engine.trailer-output»

/-! # The actual one-time zlib trailer has exact counters -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Actual one-time trailer queuing and publication have exact total effects. -/
theorem zlib_trailer_counter_execution {h : Heap} {r : ZStreamRef} {ds pb ob oo : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo) (wrap : d.wrap = 1)
    (pending : d.pending = 0) (cursor : d.pending_out = d.pending_buf) (bits : d.bi_valid.toInt = 0) :
    ∃ produced after z' result,
      publicFinishTail (some r) (some (.tab ds)) Z_FINISH h =
        .ok ((if result.pending != 0 then Z_OK else Z_STREAM_END), after) ∧
      DGood after r ds z' result ∧ StreamAccounting z z' 0 produced ∧
      z'.total_in = z.total_in ∧ z'.total_out = z.total_out + UInt64.ofNat produced := by
  let next := zlibTrailerBuffer buf z.adler
  let emitted := { d with pending := 4 }
  let ready := setD (Zlib.Trees.Proofs.Out.setB h pb next) ds emitted
  obtain ⟨write, goodE, treesE, buffersE, sizesE, storageE, values⟩ :=
    zlib_trailer_write (ob := ob) good trees buffers pending cursor
  obtain ⟨output, getOutput, writable, outputBound, outside⟩ := caller_raw_output goodE buffersE pointer
  have separate : ob ≠ pb := by
    intro same
    subst ob
    exact outside (Or.inr (Or.inr (Or.inr (Or.inr treesE.base.pbuf))))
  obtain ⟨produced, middle, z', result, written, remaining, flush, goodM, account, sizesM,
    amount, left, fields, bytesM, pendingM, outputM, storageM⟩ :=
    flush_pending_low_raw_bits_storage goodE treesE (by change d.bi_valid.toInt < 8; omega)
      cursor pointer getOutput writable separate outputBound
  have wrapM : result.wrap = 1 := by rw [fields]; exact wrap
  have bitsM : result.bi_valid.toInt = 0 := by rw [fields]; exact bits
  let final := setD middle ds { result with wrap := -1 }
  have goodF := trailer_wrap_good goodM wrapM
  have effects := flush_pending_low_run_counter_effects goodE buffersE pointer (by change d.bi_valid.toInt < 8; omega)
    flush goodM.live.hz account
  have run : publicFinishTail (some r) (some (.tab ds)) Z_FINISH h =
      .ok ((if result.pending != 0 then Z_OK else Z_STREAM_END), final) := by
    have getW : rd (some (.tab ds)) (·.wrap) h = .ok (1, h) := by
      simp only [rdD_eq, good.live.hs, wrap]
    have getWM : rd (some (.tab ds)) (·.wrap) middle = .ok (1, middle) := by
      simp only [rdD_eq, goodM.live.hs, wrapM]
    have negative : ineg (1 : Int32) = pure (-1) := by rfl
    unfold publicFinishTail
    simp only [bind_app, pure_app, show (Z_FINISH != Z_FINISH) = false from rfl,
      Bool.false_eq_true, ite_false, getW,
      show ¬ (1 : Int32) ≤ 0 from by decide, show ((1 : Int32) == 2) = false from rfl,
      write, flush, getWM, show (1 : Int32) > 0 from by decide,
      ite_true, negative, wrD_eq, goodM.live.hs]
    simp only [rdD_eq, setD_dstates_same]
    rfl
  exact ⟨produced, final, z', { result with wrap := -1 }, run, goodF, account, effects⟩

end Zlib.Deflate.Engine.Proofs
