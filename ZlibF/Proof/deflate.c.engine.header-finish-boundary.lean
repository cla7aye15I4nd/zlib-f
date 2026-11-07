import ZlibF.Proof.«deflate.c.engine.header-caller»
import ZlibF.Proof.«deflate.c.engine.finish-entry»
import ZlibF.Proof.«deflate.c.engine.public-finish-ready»

/-! # Initial FINISH header and its initialized engine boundary -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

def headerFinishState (d : DeflateState) : DeflateState :=
  { headerCompleteState d with last_flush := Z_FINISH }

def headerFinishHeap (h : Heap) (r : ZStreamRef) (ds pb ob oo : Nat)
    (z : ZStream) (d : DeflateState) (buf output : Array UInt8) : Heap :=
  setD (headerCompleteHeap h r ds pb ob oo z d buf output) ds (headerFinishState d)

/-- The completed real header preserves the initialized strategy content
and both chain frontiers. Recording FINISH does not affect those fields. -/
theorem header_finish_strategy_boundary {h : Heap} {r : ZStreamRef}
    {ds pb ob oo origin base : Nat} {z : ZStream} {d : DeflateState}
    {buf output : Array UInt8} {input : Nat → UInt8} {config : EngineConfig}
    (boundary : StrategyBoundary h r ds z d input origin base [] config)
    (frontier : EndFrontier h d) (publish : PublishReady d)
    (pending : d.pending_buf = .ref (.blk pb) 0) (get : h.bytes pb = some buf)
    (outGet : h.bytes ob = some output) (outside : ¬ DeflateOwned ds d ob) :
    StrategyBoundary (headerFinishHeap h r ds pb ob oo z d buf output) r ds
      (headerCompleteStream z ob oo) (headerFinishState d) input origin base [] config ∧
    EndFrontier (headerFinishHeap h r ds pb ob oo z d buf output) (headerFinishState d) ∧
    PublishReady (headerFinishState d) := by
  have content := header_complete_content (oo := oo) boundary.toContentBoundary pending get outGet outside
  have state : StrategyBoundary (headerCompleteHeap h r ds pb ob oo z d buf output) r ds
      (headerCompleteStream z ob oo) (headerCompleteState d) input origin base [] config :=
    ⟨content, boundary.configuration, ⟨boundary.clear.bl, boundary.clear.opt, boundary.clear.fixed⟩,
      boundary.bits, boundary.strict, fun _ => publish⟩
  have endH : EndFrontier (headerCompleteHeap h r ds pb ob oo z d buf output) (headerCompleteState d) :=
    header_complete_chains boundary.good pending frontier outside
  exact ⟨last_flush_strategy_boundary state Z_FINISH, last_flush_end_frontier (ds := ds) endH Z_FINISH, publish⟩

/-- `int ZEXPORT deflate(z_streamp strm, int flush)` (entry prefix).
An actually initialized default stream with valid nonnull buffers reaches
the zlib-header statements after recording Z_FINISH. Empty input is
included. This is an accepted-entry path, not the refusal theorem. -/
theorem public_default_finish_initial_entry {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState} (start : EngineStart h r ds z d)
    (out : z.next_out ≠ .null) (positive : z.avail_out ≠ 0)
    (input : z.avail_in ≠ 0 → z.next_in ≠ .null) :
    deflate (some r) Z_FINISH h =
      publicZlibHeader (some r) (some (.tab ds))
        (publicDataTail (some r) (some (.tab ds)) Z_FINISH)
        (setD h ds { d with last_flush := Z_FINISH }) := by
  have checked := stateCheck_live start.good.live
  have inputs : (z.avail_in != 0 && z.next_in == .null) = false := by
    by_cases empty : z.avail_in = 0
    · simp [empty]
    · simp [input empty]
  have rank0 : RANK Z_FINISH = pure 8 := by rfl
  have rankOld : RANK (-2) = pure (-4) := by rfl
  rw [public_deflate_source]
  simp only [bind_app, pure_app, checked, show ((0 : Int32) != 0) = false from rfl,
    show (Z_FINISH > Z_BLOCK) = False from by decide,
    show (Z_FINISH < 0) = False from by decide, decide_false, Bool.false_or, Bool.false_eq_true, ite_false,
    zrd_eq, start.good.live.hz, start.good.live.zst, castDeflateState,
    ldZStream_ok start.good.live.hz, ldDeflateState_tab start.good.live.hs, inputs,
    show (z.next_out == .null) = false from beq_eq_false_iff_ne.mpr out,
    start.status, show (INIT_STATE == FINISH_STATE) = false from by decide,
    Bool.false_and, show (z.avail_out == 0) = false from beq_eq_false_iff_ne.mpr positive,
    wrD_eq, start.good.live.hs, start.pending, show ((0 : UInt64) != 0) = false from rfl,
    start.lastFlush, rank0, rankOld, show ((8 : Int32) ≤ -4) = False from by decide,
    show (Z_FINISH != Z_FINISH) = false from rfl, Bool.and_false, rdD_eq, setD_dstates_same, ZStreamRef.get_setD]

/-- `int ZEXPORT deflate(z_streamp strm, int flush)` (first header).
An accepted default first Z_FINISH call with at least two raw output
bytes reaches actual data dispatch on the completed-header heap. This
internal theorem includes empty input; it does not cover output refusal
or a split header. -/
theorem public_default_finish_header_complete {h : Heap} {r : ZStreamRef} {ds pb ob oo : Nat}
    {z : ZStream} {d : DeflateState} {buf output : Array UInt8}
    (initial : EngineStart h r ds z d) (level : d.level = 6)
    (pending : d.pending_buf = .ref (.blk pb) 0) (get : h.bytes pb = some buf)
    (pendingRoom : 2 ≤ buf.size) (rw : h.ro pb = false)
    (pointer : z.next_out = .ref (.blk ob) oo) (outGet : h.bytes ob = some output)
    (outRw : h.ro ob = false) (separate : ob ≠ pb)
    (outBound : oo + z.avail_out.toNat ≤ output.size) (room : 2 ≤ z.avail_out.toNat)
    (valid : z.avail_in ≠ 0 → z.next_in ≠ .null) :
    deflate (some r) Z_FINISH h =
      publicDataTail (some r) (some (.tab ds)) Z_FINISH
        (headerFinishHeap h r ds pb ob oo z d buf output) := by
  have positive : z.avail_out ≠ 0 := by intro zero; rw [zero] at room; change 2 ≤ 0 at room; omega
  have selected : pendingLen 2 z.avail_out = 2 := by
    apply UInt32.toNat_inj.mp
    rw [pendingLen_value]
    change min 2 z.avail_out.toNat = 2
    omega
  let d0 := { d with last_flush := Z_FINISH }
  let h0 := setD h ds d0
  have getZ : r.get h0 = some z := by simpa [h0] using initial.good.live.hz
  have getD : h0.dstates ds = some d0 := by simp [h0]
  have header := public_default_header_run (h := h0) (d := d0) getZ initial.good.live.zst getD
    initial.status initial.wrap initial.bits level initial.strategy initial.windowBits initial.start initial.pending
    pending initial.pendingOut (by simpa [h0] using get) pendingRoom (by simpa [h0] using rw)
    pointer (by simpa [h0] using outGet) (by simpa [h0] using outRw) separate outBound positive
    (publicDataTail (some r) (some (.tab ds)) Z_FINISH)
  rw [public_default_finish_initial_entry initial (by rw [pointer]; intro impossible; cases impossible) positive valid]
  rw [header]
  simp only [selected, show ((2 : UInt64) - (2 : UInt32).toUInt64 != 0) = false from rfl, Bool.false_eq_true, ite_false]
  congr 1
  have reset : pendingState (zlibHeaderState d0) (.ref (.blk pb) 2) 2 = headerFinishState d := by
    simp only [pendingState, zlibHeaderState, d0, headerFinishState, headerCompleteState,
      show ((2 : UInt64) - (2 : UInt32).toUInt64) = 0 from rfl, BEq.rfl, ite_true]
    rw [← initial.pending, ← initial.pendingOut]
  have adler : { z with adler := 1 } = z := by rw [← initial.adler]
  simp only [zlibHeaderFlushed, selected, zlibHeaderReady, reset, adler, h0, d0,
    setD_bytes, ZStreamRef.put_bytes, setD_bytes_commute, ← stream_put_bytes, ZStreamRef.put_setD, setD_setD,
    headerFinishHeap, headerCompleteHeap, headerCompleteBytes, headerCompleteStream,
    show ((2 : UInt32).toNat) = 2 from rfl, ZStreamRef.put_put, reset]


end Zlib.Deflate.Engine.Proofs
