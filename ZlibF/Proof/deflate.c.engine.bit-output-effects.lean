import ZlibF.Proof.«deflate.c.engine.pending-block-output»
import ZlibF.Proof.«deflate.c.engine.public-output-interval-prefix»
import ZlibF.Proof.«deflate.c.engine.pending-counters»
import ZlibF.Proof.«deflate.c.engine.output-full-storage»

/-! # Private bit output and actual pending publication retain exact effects -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
open Zlib.Trees.Proofs.Out (TreesInvAt BitsDiff)
set_option autoImplicit false

/-- Concrete private bit-buffer replacement followed by actual pending
publication has exact counters, caller interval and allocation footprint.
The caller proves its concrete bit-writer execution and room separately. -/
theorem bit_output_pending_effects {h : Heap} {r : ZStreamRef} {ds pb ob oo : Nat}
    {z : ZStream} {d middle : DeflateState} {buf next : Array UInt8}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo) (cursor : d.pending_out = d.pending_buf)
    (size : next.size = buf.size) (fields : BitsDiff d middle)
    (treesM : TreesInvAt (setD (Zlib.Trees.Proofs.Out.setB h pb next) ds middle) ds middle pb next)
    (room : 8 * middle.pending.toNat + middle.bi_valid.toInt.toNat ≤ 8 * next.size) :
    ∃ produced after z' result,
      flush_pending (some r) (setD (Zlib.Trees.Proofs.Out.setB h pb next) ds middle) = .ok ((), after) ∧
      DGood after r ds z' result ∧ StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧
      z'.total_in = z.total_in ∧ z'.total_out = z.total_out + UInt64.ofNat produced ∧
      RawOutputInterval h after ob oo produced ∧ Shape h after ∧
      Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b ∨ b = ob) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧ after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  let marker := setD (Zlib.Trees.Proofs.Out.setB h pb next) ds middle
  have goodM := output_bits_good good cursor trees.base.bytes size fields treesM
  have buffersM := output_bits_buffers good buffers cursor trees.base.bytes size fields treesM
  have cursorM : middle.pending_out = middle.pending_buf := by
    obtain ⟨_, _, _, _, eq⟩ := fields
    rw [eq]; exact cursor
  obtain ⟨produced, after, z', result, _written, _remaining, run, goodA, buffersA, account,
      _sizes, storageA, _count, _remainingCount, _low, _validCount, _fieldsA, _bytes, _pending, _bits⟩ :=
    flush_pending_raw_bits goodM treesM buffersM pointer cursorM room
  have totals := flush_pending_run_counter_effects goodM treesM buffersM pointer cursorM room run goodA.live.hz account
  have intervalA := flush_pending_run_output_effect goodM treesM buffersM pointer cursorM room run goodA.live.hz account
  obtain ⟨_output, _getOut, _writable, _bound, outside⟩ := caller_raw_output good buffers pointer
  have separate : ob ≠ pb := by
    intro same; subst ob
    exact outside (Or.inr (Or.inr (Or.inr (Or.inr trees.base.pbuf))))
  have intervalM : RawOutputInterval h marker ob oo 0 := .of_same (by
    simp only [marker, setD_bytes, Zlib.Trees.Proofs.Out.setB, upd_ne _ _ _ _ separate])
  have interval : RawOutputInterval h after ob oo produced := by
    simpa only [Nat.add_zero, Nat.zero_add] using intervalM.trans intervalA
  have storageM := output_bits_storage (r := r) (ob := ob) (result := middle) (next := next) good.live.hs trees.base.bytes
  have storage := storageM.trans storageA
  exact ⟨produced, after, z', result, run, goodA, buffersA, account, totals.1, totals.2,
    interval, storage.shape, storage.private_frame trees.base.pbuf, full_shape_live_change storage.shape,
    storage.nalloc, storage.nextBlk⟩

end Zlib.Deflate.Engine.Proofs
