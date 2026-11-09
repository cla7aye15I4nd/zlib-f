import ZlibF.Proof.«deflate.c.borrow-stable-input-headers»
import ZlibF.Proof.«deflate.c.engine.common-finish-data-representation»
import ZlibF.Proof.«deflate.c.engine.common-header-finish-boundary»
import ZlibF.Proof.«deflate.c.engine.public-first-finish-phase»
import ZlibF.Proof.«deflate.c.engine.initial-encoding-checksum»
import ZlibF.Proof.«deflate.c.engine.common-header-complete-encoding»
import ZlibF.Proof.«deflate.c.engine.header-full-storage»

/-! # The actual first complete-header FINISH call encodes its original input -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols ZlibF.Math.DeflateEncoding
set_option autoImplicit false

/-- The actual first FINISH call writes its level-specific header and executes
the entire strategy and trailer path, including exactly two output bytes.
Encoding and checksum are established from actual initialized fields.
The accepted input is exactly the consumed original caller snapshot.
Split headers and entry refusals have their separate source branches. -/
theorem public_common_first_finish_complete_encoding {h : Heap} {r : ZStreamRef} {ds ob oo : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {config : EngineConfig} {actualInput : List UInt8}
    (initial : EngineStart h r ds z d) (low : 4 ≤ d.level.toInt) (high : d.level.toInt ≤ 9)
    (boundary : BufferedBoundary h r ds z d input 0 0 [] config) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo) (room : 2 ≤ z.avail_out.toNat)
    (memory : config.memory.toNat = 16384) (valid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (snapshot : Bytes h z.next_in z.avail_in.toNat actualInput) :
    ∃ used rc after z' result rawWritten accepted,
      accepted = actualInput.take used ∧ deflate (some r) Z_FINISH h = .ok (rc, after) ∧
      DGood after r ds z' result ∧ StreamBuffers after r ∧ StreamAccounting z z' used (2 + rawWritten.length) ∧
      Bytes after z.next_out (2 + rawWritten.length) (levelHeaderPrefix config.level ++ rawWritten) ∧
      z'.adler = (ZlibF.Spec.adler32 accepted).toUInt64 ∧
      ((∃ nextInput nextOrigin nextBase ys,
          BufferedBoundary after r ds z' result nextInput nextOrigin nextBase ys config ∧ result.status = BUSY_STATE ∧
          RawPrefix after result nextInput nextBase rawWritten ∧
          inputPrefix nextInput (nextOrigin + fillEnd result) = accepted) ∨
       (FinishingPhase result config ∧ CommonFinishedEncoding after result config.level accepted rawWritten)) ∧
      (rc = Z_STREAM_END → ZlibF.Spec.Zlib.Valid accepted (levelHeaderPrefix config.level ++ rawWritten)) := by
  obtain ⟨output, outGet, outRw, outBound, outside⟩ := caller_raw_output initial.good buffers pointer
  obtain ⟨oldD, pb, buf, trees⟩ := initial.good.trees
  have sameD : oldD = d := Option.some.inj (trees.base.dstate.symm.trans initial.good.live.hs)
  subst oldD
  have separate : ob ≠ pb := by
    intro same
    subst ob
    exact outside (Or.inr (Or.inr (Or.inr (Or.inr trees.base.pbuf))))
  have pendingRoom : 2 ≤ buf.size := by have size := trees.base.size; have lo := trees.base.lit_lo; omega
  have first := public_common_valid_header_complete initial trees.base.pbuf trees.base.bytes pendingRoom trees.base.rw
    pointer outGet outRw separate outBound room valid Z_FINISH (by decide) (by decide)
  change deflate (some r) Z_FINISH h = publicDataTail (some r) (some (.tab ds)) Z_FINISH
    (levelHeaderFinishHeap h r ds pb ob oo z d buf output) at first
  have publish : PublishReady d := ⟨initial.pending, initial.pendingOut, boundary.bits⟩
  obtain ⟨stateH, endH, publishH⟩ := common_header_finish_strategy_boundary (boundary.strategy publish) boundary.end_frontier publish
    trees.base.pbuf trees.base.bytes outGet outside
  have goodH := common_header_complete_good (oo := oo) initial.good trees.base.bytes outGet separate
  have buffersH := last_flush_buffers goodH
    (common_header_complete_buffers initial.good buffers trees.base.bytes outGet separate pointer room) Z_FINISH
  have bufferedH := stateH.buffered endH (fun _ => publishH.2.1)
  have accountH := header_complete_accounting pointer room
  have wrapConfig : config.wrap = 1 := (congrArg EngineConfig.wrap boundary.configuration).symm.trans initial.wrap
  have pointerH : (headerCompleteStream z ob oo).next_out = .ref (.blk ob) (oo + 2) := rfl
  obtain ⟨before, pending⟩ := good_pending_bits initial.good
  have pendingNil := pending_bits_empty pending (by rw [initial.pending]; rfl) (by rw [initial.bits]; rfl)
  have encoding : RawPrefix h d input 0 [] := by
    rw [pendingNil] at pending
    refine ⟨[], [], pending, rfl, ?_⟩
    simpa only [inputPrefix, List.range_zero, List.map_nil] using block_prefix_empty ([] : List UInt8) [] 0
  have encodingH0 := common_header_complete_raw_prefix (oo := oo) initial boundary.toContentBoundary
    trees.base.pbuf trees.base.bytes outGet outside encoding
  have encodingH := encodingH0.last_flush goodH Z_FINISH
  have originalBuffers := buffers
  obtain ⟨oldZ, oldGet, inputRange, _outRange, separated⟩ := originalBuffers
  have oldEq : oldZ = z := Option.some.inj (oldGet.symm.trans initial.good.live.hz)
  subst oldZ
  have headerSeparate : Separate z.next_in z.avail_in.toNat z.next_out 2 := by
    simpa only [advance_zero] using separate_advance_right (used := 0) separated (by omega)
  have storageH := common_header_complete_full_storage (oo := oo) initial.good trees.base.bytes outGet separate
  have snapshotH0 := caller_input_bytes_preserved initial.good buffers pointer inputRange headerSeparate
    (Nat.le_refl _) snapshot (storageH.private_frame trees.base.pbuf) (common_header_complete_output_effect outGet (by omega))
      (level_header_complete_borrow_eq h r ds pb ob oo z d buf output)
  have snapshotH := caller_bytes_setD_depth (result := headerFinishState d) goodH.live.hs rfl snapshotH0
  obtain ⟨used, rc, after, z', result, rawWritten, accepted, acceptedA, run, goodA, buffersA,
      accountA, bytesA, checksumA, phasesA, endedA⟩ :=
    public_common_slow_finish_data_completed_encoding bufferedH buffersH rfl low high initial.strategy pointerH memory
      wrapConfig publishH valid snapshotH (initial.logical_adler input) encodingH
  have prefixEmpty : inputPrefix input (0 + fillEnd (headerFinishState d)) = [] := by
    simp only [fillEnd, headerFinishState, headerCompleteState, initial.start, initial.lookahead,
      UInt32.toNat_zero, Nat.add_zero, inputPrefix, List.range_zero, List.map_nil]
  have acceptedEq : accepted = actualInput.take used := by simpa only [prefixEmpty, List.nil_append] using acceptedA
  obtain ⟨_effectUsed, _effectProduced, _effectRc, _other, _otherZ, _otherD, effectRun, effectGood,
      effectAccount, _effectInput, _effectOutput, outputEffect⟩ :=
    public_common_slow_finish_output_execution stateH endH buffersH rfl low high initial.strategy pointerH memory wrapConfig publishH valid
  have effect : RawOutputInterval (levelHeaderFinishHeap h r ds pb ob oo z d buf output) after ob (oo + 2) rawWritten.length :=
    RawOutputInterval.identify effectRun run effectGood.live.hz goodA.live.hz effectAccount accountA outputEffect
  have headerBytes0 := common_header_complete_output_bytes h r ds pb ob oo z d buf output pendingRoom (by omega)
  have levelEq : d.level = config.level := congrArg EngineConfig.level boundary.configuration
  rw [levelEq] at headerBytes0
  have headerBytes := caller_bytes_setD_depth (result := headerFinishState d) goodH.live.hs rfl headerBytes0
  have earlier := effect.keep_published_bytes headerBytes
  have current : Bytes after (.ref (.blk ob) (oo + 2)) rawWritten.length rawWritten := by
    rw [pointerH] at bytesA
    exact bytesA
  have combinedBytes := published_bytes_append earlier current
  have account : StreamAccounting z z' used (2 + rawWritten.length) := by
    simpa only [Nat.zero_add] using stream_accounting_trans accountH accountA
  refine ⟨used, rc, after, z', result, rawWritten, accepted, acceptedEq, first.trans run,
    goodA, buffersA, account, ?_, checksumA, ?_, ?_⟩
  · rw [pointer]
    exact combinedBytes
  · simpa only [List.nil_append] using phasesA
  · intro ended
    simpa only [List.append_nil] using endedA ended

end Zlib.Deflate.Engine.Proofs
