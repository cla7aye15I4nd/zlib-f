import ZlibF.Proof.«deflate.c.engine.ordinary-output-interval»
import ZlibF.Proof.«deflate.c.engine.public-request-full-storage»

/-! # Exact caller output intervals for public header, pending and trailer publication -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- The complete actual header heap changes only its two-byte caller interval. -/
theorem header_complete_output_effect {h : Heap} {r : ZStreamRef} {ds pb ob oo : Nat}
    {z : ZStream} {d : DeflateState} {buf output : Array UInt8}
    (get : h.bytes ob = some output) (bound : oo + 2 ≤ output.size) :
    RawOutputInterval h (headerCompleteHeap h r ds pb ob oo z d buf output) ob oo 2 := by
  intro before getBefore
  have same : before = output := Option.some.inj (getBefore.symm.trans get)
  subst before
  refine ⟨copyRange output (zlibHeaderBytes buf) oo 0 2, ?_, size_copyRange _ _ _ _ _, ?_⟩
  · simp only [headerCompleteHeap, setD_bytes, ZStreamRef.put_bytes, headerCompleteBytes, upd_same]
  · intro j _range outside
    rw [getElem?_copyRange output (zlibHeaderBytes buf) oo 0 2 j bound, ite_eq_right outside]

/-- Splitting the actual header changes only its single produced caller byte. -/
theorem header_one_output_effect {h : Heap} {r : ZStreamRef} {ds pb ob oo : Nat}
    {z : ZStream} {d : DeflateState} {buf output : Array UInt8}
    (get : h.bytes ob = some output) (bound : oo + 1 ≤ output.size) :
    RawOutputInterval h (headerOneHeap h r ds pb ob oo z d buf output) ob oo 1 := by
  intro before getBefore
  have same : before = output := Option.some.inj (getBefore.symm.trans get)
  subst before
  refine ⟨copyRange output (zlibHeaderBytes buf) oo 0 1, ?_, size_copyRange _ _ _ _ _, ?_⟩
  · simp only [headerOneHeap, setD_bytes, ZStreamRef.put_bytes, headerOneBytes, upd_same]
  · intro j _range outside
    rw [getElem?_copyRange output (zlibHeaderBytes buf) oo 0 1 j bound, ite_eq_right outside]

/-- Actual low-bit pending publication preserves its exact accounted caller interval. -/
theorem flush_pending_low_run_output_effect {h after : Heap} {r : ZStreamRef} {ds ob oo produced : Nat}
    {z z' : ZStream} {d : DeflateState}
    (good : DGood h r ds z d) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo) (low : d.bi_valid.toInt < 8)
    (run : flush_pending (some r) h = .ok ((), after)) (live : r.get after = some z')
    (account : StreamAccounting z z' 0 produced) : RawOutputInterval h after ob oo produced := by
  intro before getBefore
  exact flush_pending_low_run_output_interval good buffers pointer low run live account getBefore

/-- Actual bit preparation and pending publication preserve their exact accounted caller interval. -/
theorem flush_pending_run_output_effect {h after : Heap} {r : ZStreamRef} {ds pb ob oo produced : Nat}
    {z z' : ZStream} {d : DeflateState} {buf : Array UInt8}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) (pointer : z.next_out = .ref (.blk ob) oo)
    (cursor : d.pending_out = d.pending_buf)
    (room : 8 * d.pending.toNat + d.bi_valid.toInt.toNat ≤ 8 * buf.size)
    (run : flush_pending (some r) h = .ok ((), after)) (live : r.get after = some z')
    (account : StreamAccounting z z' 0 produced) : RawOutputInterval h after ob oo produced := by
  intro before getBefore
  exact flush_pending_run_output_interval good trees buffers pointer cursor room run live account getBefore

/-- Actual one-time trailer queuing and publication return exact counters and their exact caller output interval. -/
theorem zlib_trailer_output_execution {h : Heap} {r : ZStreamRef} {ds pb ob oo : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo) (wrap : d.wrap = 1)
    (pending : d.pending = 0) (cursor : d.pending_out = d.pending_buf) (bits : d.bi_valid.toInt = 0) :
    ∃ produced after z' result,
      publicFinishTail (some r) (some (.tab ds)) Z_FINISH h =
        .ok ((if result.pending != 0 then Z_OK else Z_STREAM_END), after) ∧
      DGood after r ds z' result ∧ StreamAccounting z z' 0 produced ∧
      z'.total_in = z.total_in ∧ z'.total_out = z.total_out + UInt64.ofNat produced ∧ RawOutputInterval h after ob oo produced := by
  let next := zlibTrailerBuffer buf z.adler
  let emitted := { d with pending := 4 }
  let ready := setD (Zlib.Trees.Proofs.Out.setB h pb next) ds emitted
  obtain ⟨write, goodE, treesE, buffersE, sizesE, storageE, values⟩ :=
    zlib_trailer_write (ob := pb) good trees buffers pending cursor
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
  have prefixEffect : RawOutputInterval h ready ob oo 0 :=
    .of_private_frame good buffers pointer (storageE.pending_private_frame trees.base.pbuf)
  have middleEffect := flush_pending_low_run_output_effect goodE buffersE pointer
    (by change d.bi_valid.toInt < 8; omega) flush goodM.live.hz account
  have beforeFinal : RawOutputInterval h middle ob oo produced := by
    simpa only [Nat.zero_add] using prefixEffect.trans middleEffect
  have tailEffect : RawOutputInterval middle final ob (oo + produced) 0 := .of_same rfl
  have effect : RawOutputInterval h final ob oo produced := by
    simpa only [Nat.add_zero] using beforeFinal.trans tailEffect
  exact ⟨produced, final, z', { result with wrap := -1 }, run, goodF, account, effects.1, effects.2, effect⟩

end Zlib.Deflate.Engine.Proofs
