import ZlibF.Proof.«deflate.c.borrow-stable-input-headers»
import ZlibF.Proof.«deflate.c.engine.public-nonfinal-data-interval»
import ZlibF.Proof.«deflate.c.engine.valid-first-header»
import ZlibF.Proof.«deflate.c.engine.initial-encoding-checksum»
import ZlibF.Proof.«deflate.c.engine.public-no-flush-input»
import ZlibF.Proof.«deflate.c.engine.input-snapshot-controls»
import ZlibF.Proof.«deflate.c.engine.header-full-storage»
import ZlibF.Proof.«deflate.c.engine.public-output-interval-prefix»
import ZlibF.Proof.«deflate.c.engine.header-encoding»
import ZlibF.Proof.«deflate.c.engine.public-first-no-flush-buffered»
import ZlibF.Proof.«deflate.c.engine.public-data-output-interval»

/-! # Every actual first complete-header nonfinal call encodes its original input -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- The real first public non-FINISH call writes the exact two-byte default
header and retains independently encoded raw output on the same final heap.
An output buffer of exactly two bytes is admitted: after the header the
actual data path can still accept input and produce pending raw blocks.
The accepted input equals the consumed prefix of the original caller snapshot. The one-byte split-header and refusal paths are separate obligations. -/
theorem public_first_nonfinal_complete_header_encoding_input {h : Heap} {r : ZStreamRef} {ds ob oo : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {config : EngineConfig}
    (initial : EngineStart h r ds z d) (level : d.level = 6)
    (boundary : BufferedBoundary h r ds z d input 0 0 [] config) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo) (room : 2 ≤ z.avail_out.toNat)
    (memory : config.memory.toNat = 16384) (valid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (flush : Int32) (flag : flush = Z_NO_FLUSH ∨ flush = Z_PARTIAL_FLUSH ∨ flush = Z_SYNC_FLUSH ∨
      flush = Z_FULL_FLUSH ∨ flush = Z_BLOCK)
    {actualInput : List UInt8} (snapshot : Bytes h z.next_in z.avail_in.toNat actualInput)
    (encoding : RawPrefix h d input 0 []) :
    ∃ used after z' result nextInput nextOrigin nextBase ys rawWritten,
      deflate (some r) flush h = .ok (Z_OK, after) ∧
      BufferedBoundary after r ds z' result nextInput nextOrigin nextBase ys config ∧ StreamBuffers after r ∧
      StreamAccounting z z' used (2 + rawWritten.length) ∧
      Bytes after z.next_out (2 + rawWritten.length) ([120, 156] ++ rawWritten) ∧
      (∀ i, i < 0 + fillEnd d → nextInput i = input i) ∧
      nextOrigin + fillEnd result = 0 + fillEnd d + used ∧ 0 ≤ nextBase ∧
      result.status = BUSY_STATE ∧ (result.last_flush = flush ∨ result.last_flush = -1) ∧
      RawPrefix after result nextInput nextBase rawWritten ∧
      z'.adler = (ZlibF.Spec.adler32 (inputPrefix nextInput (nextOrigin + fillEnd result))).toUInt64 ∧
      inputPrefix nextInput (nextOrigin + fillEnd result) = actualInput.take used := by
  have flagLo : 0 ≤ flush.toInt := by rcases flag with rfl | rfl | rfl | rfl | rfl <;> decide
  have flagHi : flush.toInt ≤ 5 := by rcases flag with rfl | rfl | rfl | rfl | rfl <;> decide
  obtain ⟨output, outGet, outRw, outBound, outside⟩ := caller_raw_output initial.good buffers pointer
  obtain ⟨oldD, pb, buf, trees⟩ := initial.good.trees
  have sameD : oldD = d := Option.some.inj (trees.base.dstate.symm.trans initial.good.live.hs)
  subst oldD
  have separate : ob ≠ pb := by
    intro same
    subst ob
    exact outside (Or.inr (Or.inr (Or.inr (Or.inr trees.base.pbuf))))
  have pendingRoom : 2 ≤ buf.size := by have size := trees.base.size; have lo := trees.base.lit_lo; omega
  have first := public_default_valid_header_complete initial level trees.base.pbuf trees.base.bytes pendingRoom trees.base.rw
    pointer outGet outRw separate outBound room valid flush flagLo flagHi
  have contentH := header_complete_content (oo := oo) boundary.toContentBoundary trees.base.pbuf trees.base.bytes outGet outside
  have stateH0 : BufferedBoundary (headerCompleteHeap h r ds pb ob oo z d buf output) r ds
      (headerCompleteStream z ob oo) (headerCompleteState d) input 0 0 [] config :=
    ⟨contentH, boundary.configuration, ⟨boundary.clear.bl, boundary.clear.opt, boundary.clear.fixed⟩,
      boundary.bits, boundary.strict,
      header_complete_chains boundary.good trees.base.pbuf boundary.end_frontier outside,
      fun _ => initial.pendingOut⟩
  have stateH := last_flush_buffered_boundary stateH0 flush
  have buffersH0 := header_complete_buffers initial.good buffers trees.base.bytes outGet separate pointer room
  have buffersH := last_flush_buffers stateH0.good buffersH0 flush
  have accountH := header_complete_accounting pointer room
  have wrapConfig : config.wrap = 1 := (congrArg EngineConfig.wrap boundary.configuration).symm.trans initial.wrap
  have readyH : PublishReady {headerCompleteState d with last_flush := flush} := ⟨initial.pending, initial.pendingOut, boundary.bits⟩
  have pointerH : (headerCompleteStream z ob oo).next_out = .ref (.blk ob) (oo + 2) := rfl
  have encodingH0 := header_complete_raw_prefix (oo := oo) initial boundary.toContentBoundary
    trees.base.pbuf trees.base.bytes outGet outside encoding
  have encodingH := encodingH0.last_flush stateH0.good flush
  have initialBuffers := buffers
  obtain ⟨oldZ, oldGet, inputRange, _outRange, separated⟩ := initialBuffers
  have oldEq : oldZ = z := Option.some.inj (oldGet.symm.trans initial.good.live.hz)
  subst oldZ
  have headerSeparate : Separate z.next_in z.avail_in.toNat z.next_out 2 := by
    simpa only [advance_zero] using separate_advance_right (used := 0) separated (by omega)
  have storageH := header_complete_full_storage (oo := oo) initial.good trees.base.bytes outGet separate
  have snapshotH0 := caller_input_bytes_preserved initial.good buffers pointer inputRange headerSeparate
    (Nat.le_refl _) snapshot (storageH.private_frame trees.base.pbuf)
    (header_complete_output_effect outGet (by omega))
      (header_complete_borrow_eq h r ds pb ob oo z d buf output)
  have snapshotH := caller_bytes_setD_depth (result := {headerCompleteState d with last_flush := flush}) stateH0.good.live.hs rfl snapshotH0
  obtain ⟨used, after, z', result, nextInput, nextOrigin, nextBase, ys, rawWritten,
      run, stateA, buffersA, accountA, bytesA, agreesA, endpointA, baseA, statusA, lastA, encodingA, checksumA, inputLedgerA, effect⟩ :=
    public_busy_nonfinal_data_raw_prefix_input_interval stateH buffersH rfl level initial.strategy pointerH memory wrapConfig readyH valid flush flag snapshotH (initial.logical_adler input) encodingH
  have headerBytes0 := header_complete_output_bytes h r ds pb ob oo z d buf output pendingRoom (by omega)
  have headerBytes := caller_bytes_setD_depth (result := {headerCompleteState d with last_flush := flush}) stateH0.good.live.hs rfl headerBytes0
  have oldBytes := effect.keep_published_bytes headerBytes
  have newBytes : Bytes after (.ref (.blk ob) (oo + 2)) rawWritten.length rawWritten := by
    rw [pointerH] at bytesA
    exact bytesA
  have combined := published_bytes_append oldBytes newBytes
  have account : StreamAccounting z z' used (2 + rawWritten.length) := by
    simpa only [Nat.zero_add] using stream_accounting_trans accountH accountA
  refine ⟨used, after, z', result, nextInput, nextOrigin, nextBase, ys, rawWritten,
    first.trans run, stateA, buffersA, account, ?_, agreesA, endpointA, baseA, statusA,
    lastA, ?_, checksumA, ?_⟩
  · rw [pointer]
    exact combined
  · simpa only [List.nil_append] using encodingA
  · have emptyPrefix : inputPrefix input (0 + fillEnd d) = [] := by
      simp only [fillEnd, initial.start, initial.lookahead, UInt32.toNat_zero, Nat.add_zero, inputPrefix, List.range_zero, List.map_nil]
    have endH : fillEnd {headerCompleteState d with last_flush := flush} = fillEnd d := rfl
    simpa only [endH, emptyPrefix, List.nil_append] using inputLedgerA

end Zlib.Deflate.Engine.Proofs
