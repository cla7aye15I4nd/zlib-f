import ZlibF.Proof.«deflate.c.engine.caller-input-frame»
import ZlibF.Proof.«deflate.c.engine.public-pending-checksum»

/-! # Caller input snapshots through actual control and pending effects -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- A control store that retains the depth array retains every readable
byte view. No assumption on the caller pointer representation is added. -/
theorem caller_bytes_setD_depth {h : Heap} {ds n : Nat} {d result : DeflateState}
    {p : BPtr} {xs : List UInt8} (state : h.dstates ds = some d) (depth : result.depth = d.depth)
    (bytes : Bytes h p n xs) : Bytes (setD h ds result) p n xs := by
  rcases bytes with null | ⟨ref, off, a, pointer, get, fit, values⟩
  · exact Or.inl null
  · exact Or.inr ⟨ref, off, a, pointer, (byte_view_setD_depth state depth ref).trans get, fit, values⟩

/-- Actual low-bit pending publication consumes no input and retains its
entire original caller snapshot, even with shared disjoint raw ranges. -/
theorem flush_pending_low_input_snapshot {h after : Heap} {r : ZStreamRef} {ds pb ob oo produced : Nat}
    {z z' : ZStream} {d : DeflateState} {xs : List UInt8}
    (good : DGood h r ds z d) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo) (low : d.bi_valid.toInt < 8)
    (pending : d.pending_buf = .ref (.blk pb) 0)
    (snapshot : Bytes h z.next_in z.avail_in.toNat xs)
    (run : flush_pending (some r) h = .ok ((), after)) (live : r.get after = some z')
    (account : StreamAccounting z z' 0 produced) (storage : OutputStorage h after r ds pb ob) :
    Bytes after z'.next_in z'.avail_in.toNat xs := by
  have originalBuffers := buffers
  obtain ⟨old, get, range, _output, separated⟩ := originalBuffers
  have equal : old = z := Option.some.inj (get.symm.trans good.live.hz)
  subst old
  have separatedNow : Separate z.next_in z.avail_in.toNat z.next_out produced := by
    simpa only [advance_zero] using separate_advance_right (used := 0) separated
      (by have outputCount := account.2.2.2.1; omega)
  have interval : RawOutputInterval h after ob oo produced := by
    intro before getBefore
    exact flush_pending_low_run_output_interval good buffers pointer low run live account getBefore
  have kept := caller_input_bytes_preserved good buffers pointer range separatedNow (Nat.le_refl _)
    snapshot (storage.private_frame pending) interval
  have cursor : z'.next_in = z.next_in := by simpa only [advance_zero] using account.2.2.2.2.1
  have count : z'.avail_in.toNat = z.avail_in.toNat := by have inputCount := account.2.2.1; omega
  simpa only [cursor, count] using kept

end Zlib.Deflate.Engine.Proofs
