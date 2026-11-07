import ZlibF.Proof.«deflate.c.engine.counter-effects»
import ZlibF.Proof.«deflate.c.engine.public-first-no-flush-buffered»

/-! # Exact counter effects of complete and split first headers -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Any bounded actual pending record update has its natural byte count. -/
theorem pending_stream_accounting {z : ZStream} {ob oo : Nat} (n : UInt32)
    (pointer : z.next_out = .ref (.blk ob) oo) (bound : n.toNat ≤ z.avail_out.toNat) :
    StreamAccounting z (pendingStream z (.ref (.blk ob) (oo + n.toNat)) n) 0 n.toNat := by
  dsimp only [StreamAccounting, pendingStream]
  refine ⟨by omega, bound, by simp, ?_, (advance_zero _).symm, ?_, rfl, rfl, rfl, rfl, rfl⟩
  · rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr bound)]
    omega
  · simp only [pointer, advance]

/-- Header publication uses exactly the same wrapping output update. -/
theorem header_complete_stream_counter_effects (z : ZStream) (ob oo : Nat) :
    (headerCompleteStream z ob oo).total_in = z.total_in ∧
      (headerCompleteStream z ob oo).total_out = z.total_out + UInt64.ofNat 2 := by
  exact pending_stream_counter_effects z _ 2

/-- Either ordinary first call can split the header after one byte.
The real resulting stream has exact counters before any strategy runs. -/
theorem first_ordinary_one_run_counter_effects {h after : Heap} {r : ZStreamRef}
    {ds ob oo used produced : Nat} {z returned : ZStream} {d : DeflateState} {flush rc : Int32}
    (flag : flush = Z_NO_FLUSH ∨ flush = Z_FINISH)
    (initial : EngineStart h r ds z d) (level : d.level = 6) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo) (one : z.avail_out = 1)
    (valid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (run : deflate (some r) flush h = .ok (rc, after)) (live : r.get after = some returned)
    (account : StreamAccounting z returned used produced) :
    returned.total_in = z.total_in + UInt64.ofNat used ∧
      returned.total_out = z.total_out + UInt64.ofNat produced := by
  obtain ⟨output, outGet, outRw, outBound, outside⟩ := caller_raw_output initial.good buffers pointer
  obtain ⟨oldD, pb, buf, trees⟩ := initial.good.trees
  have sameD : oldD = d := Option.some.inj (trees.base.dstate.symm.trans initial.good.live.hs)
  subst oldD
  have separate : ob ≠ pb := by
    intro same
    subst ob
    exact outside (Or.inr (Or.inr (Or.inr (Or.inr trees.base.pbuf))))
  have room : 2 ≤ buf.size := by have size := trees.base.size; have lo := trees.base.lit_lo; omega
  have actual : deflate (some r) flush h = .ok (Z_OK, headerOneHeap h r ds pb ob oo z d buf output) := by
    rcases flag with rfl | rfl
    · exact first_no_flush_one_source initial level trees.base.pbuf trees.base.bytes room trees.base.rw
        pointer outGet outRw separate outBound one valid
    · exact first_finish_one_source initial level trees.base.pbuf trees.base.bytes room trees.base.rw
        pointer outGet outRw separate outBound one valid
  have get : r.get (headerOneHeap h r ds pb ob oo z d buf output) =
      some (pendingStream z (.ref (.blk ob) (oo + 1)) 1) := by
    unfold headerOneHeap
    rw [ZStreamRef.get_setD]
    apply ZStreamRef.get_put_same
    simpa only [headerOneBytes, stream_get_bytes] using initial.good.live.hz
  have same := actual_run_stream_unique actual run get live
  have expected := pending_stream_accounting (z := z) 1 pointer (by rw [one]; decide)
  have effects := pending_stream_counter_effects z (.ref (.blk ob) (oo + 1)) 1
  exact stream_counter_effects_identify same expected account (by simpa using effects.1) effects.2

end Zlib.Deflate.Engine.Proofs
