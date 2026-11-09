import ZlibF.Proof.«deflate.c.engine.common-header-boundary»
import ZlibF.Proof.«deflate.c.engine.header-caller»
import ZlibF.Proof.«deflate.c.engine.caller-sizes»

/-! # Completed header output retains caller ranges on the same heap -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

theorem common_header_complete_sizes {h : Heap} {r : ZStreamRef} {ds pb ob oo : Nat}
    {z : ZStream} {d : DeflateState} {buf output : Array UInt8}
    (state : h.dstates ds = some d) (get : h.bytes pb = some buf) (outGet : h.bytes ob = some output)
    (separate : ob ≠ pb) : ByteSizes h (levelHeaderCompleteHeap h r ds pb ob oo z d buf output) := by
  let staged := { h with bytes := upd h.bytes pb (some (levelHeaderBytes d.level buf)) }
  let copied := levelHeaderCompleteBytes d.level h pb ob oo buf output
  have copiedState : copied.dstates ds = some d := state
  have view : ∀ ref : BRef, Space.get (levelHeaderCompleteHeap h r ds pb ob oo z d buf output) ref = Space.get copied ref := by
    intro ref
    rw [levelHeaderCompleteHeap, byte_view_setD_depth (d := d) (result := headerCompleteState d) (by simpa using copiedState) rfl, byte_get_stream_put]
  refine ⟨?_, ?_⟩
  · intro ref a getA
    obtain ⟨middle, getM, sizeM⟩ := byte_view_write_size (new := levelHeaderBytes d.level buf) getA get (by simp [levelHeaderBytes])
    obtain ⟨result, getR, sizeR⟩ := byte_view_write_size getM
      (show staged.bytes ob = some output by simpa only [staged, upd_ne _ _ _ _ separate] using outGet)
      (size_copyRange output (levelHeaderBytes d.level buf) oo 0 2)
    exact ⟨result, (view ref).trans getR, sizeR.trans sizeM⟩
  · intro ref
    cases ref <;> simp [Space.ro, levelHeaderCompleteHeap, levelHeaderCompleteBytes]

/-- The raw level-dependent header's two output bytes preserve both public caller
ranges, including two disjoint intervals in one caller allocation. -/
theorem common_header_complete_buffers {h : Heap} {r : ZStreamRef} {ds pb ob oo : Nat}
    {z : ZStream} {d : DeflateState} {buf output : Array UInt8}
    (good : DGood h r ds z d) (buffers : StreamBuffers h r)
    (get : h.bytes pb = some buf) (outGet : h.bytes ob = some output) (separate : ob ≠ pb)
    (pointer : z.next_out = .ref (.blk ob) oo) (room : 2 ≤ z.avail_out.toNat) :
    StreamBuffers (levelHeaderCompleteHeap h r ds pb ob oo z d buf output) r := by
  have goodA := common_header_complete_good (oo := oo) good get outGet separate
  have owned : ∀ b, StreamOwned (levelHeaderCompleteHeap h r ds pb ob oo z d buf output) r b ↔ StreamOwned h r b := by
    intro b
    rw [stream_owned_deflate goodA, stream_owned_deflate good]
    rfl
  exact stream_buffers_sizes good.live.hz goodA.live.hz buffers
    (common_header_complete_sizes good.live.hs get outGet separate) owned (header_complete_accounting pointer room)

/-- `int ZEXPORT deflate(z_streamp strm, int flush)` (first header).
An accepted standard first Z_NO_FLUSH call with at least two raw output
bytes reaches actual data dispatch on the completed-header heap. This
internal theorem includes empty input; it does not cover output refusal
or a split header. -/
theorem public_common_header_complete {h : Heap} {r : ZStreamRef} {ds pb ob oo : Nat}
    {z : ZStream} {d : DeflateState} {buf output : Array UInt8}
    (initial : EngineStart h r ds z d)
    (pending : d.pending_buf = .ref (.blk pb) 0) (get : h.bytes pb = some buf)
    (pendingRoom : 2 ≤ buf.size) (rw : h.ro pb = false)
    (pointer : z.next_out = .ref (.blk ob) oo) (outGet : h.bytes ob = some output)
    (outRw : h.ro ob = false) (separate : ob ≠ pb)
    (outBound : oo + z.avail_out.toNat ≤ output.size) (room : 2 ≤ z.avail_out.toNat)
    (valid : z.avail_in ≠ 0 → z.next_in ≠ .null) :
    deflate (some r) Z_NO_FLUSH h =
      publicDataTail (some r) (some (.tab ds)) Z_NO_FLUSH
        (levelHeaderCompleteHeap h r ds pb ob oo z d buf output) := by
  have positive : z.avail_out ≠ 0 := by intro zero; rw [zero] at room; change 2 ≤ 0 at room; omega
  have selected : pendingLen 2 z.avail_out = 2 := by
    apply UInt32.toNat_inj.mp
    rw [pendingLen_value]
    change min 2 z.avail_out.toNat = 2
    omega
  let d0 := { d with last_flush := Z_NO_FLUSH }
  let h0 := setD h ds d0
  have getZ : r.get h0 = some z := by simpa [h0] using initial.good.live.hz
  have getD : h0.dstates ds = some d0 := by simp [h0]
  have header := public_common_header_run (h := h0) (d := d0) getZ initial.good.live.zst getD
    initial.status initial.wrap initial.bits initial.strategy initial.windowBits initial.start initial.pending
    pending initial.pendingOut (by simpa [h0] using get) pendingRoom (by simpa [h0] using rw)
    pointer (by simpa [h0] using outGet) (by simpa [h0] using outRw) separate outBound positive
    (publicDataTail (some r) (some (.tab ds)) Z_NO_FLUSH)
  rw [public_default_entry initial (by rw [pointer]; intro impossible; cases impossible) positive valid]
  rw [header]
  simp only [selected, show ((2 : UInt64) - (2 : UInt32).toUInt64 != 0) = false from rfl, Bool.false_eq_true, ite_false]
  congr 1
  have reset : pendingState (levelHeaderState d0) (.ref (.blk pb) 2) 2 = headerCompleteState d := by
    simp only [pendingState, levelHeaderState, d0, headerCompleteState,
      show ((2 : UInt64) - (2 : UInt32).toUInt64) = 0 from rfl, BEq.rfl, ite_true]
    rw [← initial.pending, ← initial.pendingOut]
  have adler : { z with adler := 1 } = z := by rw [← initial.adler]
  simp only [levelHeaderFlushed, selected, levelHeaderReady, reset, adler, h0, d0,
    setD_bytes, ZStreamRef.put_bytes, setD_bytes_commute, ← stream_put_bytes, ZStreamRef.put_setD, setD_setD,
    levelHeaderCompleteHeap, levelHeaderCompleteBytes, headerCompleteStream,
    show ((2 : UInt32).toNat) = 2 from rfl, ZStreamRef.put_put, reset]


end Zlib.Deflate.Engine.Proofs
