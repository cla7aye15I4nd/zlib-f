import ZlibF.Proof.«deflate.c.borrow-stable-publish»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-partial-data-input»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-header-pending-one»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-caller-input-frame»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-pending-scalars»
import ZlibF.Proof.«deflate.c.engine.public-header-nonfinal-input»

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols ZlibF.Math.DeflateEncoding
set_option autoImplicit false

/-- With room beyond the remaining header byte, the actual public
PARTIAL call completes that byte and enters real raw compression. The
header byte remains readable after the later strategy output. The actual input snapshot survives that header output and identifies precisely the consumed logical prefix. -/
theorem public_foreign_header_pending_partial_continue_encoding_input {h : Heap} {r : ZStreamRef} {ds owner oo origin : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {config : EngineConfig}
    (boundary : BufferedBoundary h r ds z d input origin 0 [] config) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.dstate_depth owner) oo) (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (status : d.status = BUSY_STATE) (level : d.level = 6) (strategy : d.strategy = 0)
    (memory : config.memory.toNat = 16384) (wrap : config.wrap = 1)
    (room : 1 < z.avail_out.toNat)
    {actualInput : List UInt8} (snapshot : Bytes h z.next_in z.avail_in.toNat actualInput)
    (checksum : z.adler = (ZlibF.Spec.adler32 (inputPrefix input (origin + fillEnd d))).toUInt64)
    (encoding : HeaderPending h d [120]) :
    ∃ used after z' result nextInput nextOrigin nextBase ys rawWritten,
      deflate (some r) Z_PARTIAL_FLUSH h = .ok (Z_OK, after) ∧
      BufferedBoundary after r ds z' result nextInput nextOrigin nextBase ys config ∧ StreamBuffers after r ∧
      StreamAccounting z z' used (1 + rawWritten.length) ∧
      Bytes after z.next_out (1 + rawWritten.length) ([156] ++ rawWritten) ∧
      (∀ i, i < origin + fillEnd d → nextInput i = input i) ∧
      nextOrigin + fillEnd result = origin + fillEnd d + used ∧
      result.status = BUSY_STATE ∧ (result.last_flush = Z_PARTIAL_FLUSH ∨ result.last_flush = -1) ∧
      RawPrefix after result nextInput nextBase rawWritten ∧
      z'.adler = (ZlibF.Spec.adler32 (inputPrefix nextInput (nextOrigin + fillEnd result))).toUInt64 ∧
      inputPrefix nextInput (nextOrigin + fillEnd result) =
        inputPrefix input (origin + fillEnd d) ++ actualInput.take used := by
  have flagLo : 0 ≤ Z_PARTIAL_FLUSH.toInt := by decide
  have flagHi : Z_PARTIAL_FLUSH.toInt ≤ 5 := by decide
  have shape := encoding.one_remaining
  have boundary0 := last_flush_buffered_boundary boundary Z_PARTIAL_FLUSH
  have buffers0 := last_flush_buffers boundary.good buffers Z_PARTIAL_FLUSH
  have pending0 := last_flush_pending_bits boundary.good shape.2 Z_PARTIAL_FLUSH
  obtain ⟨_pb, producedP, middle, zm, dm, writtenP, remainingP, _baseP,
      flushRun, stateM, buffersM, accountM, _sizes, storageM, amountP, leftP, fieldsM,
      readyM, bytesM, pendingM, wireM,frameM⟩ :=
    flush_pending_buffered_foreign_boundary boundary0 buffers0 pointer pending0
  have countP : producedP = 1 := by
    change producedP = min d.pending.toNat z.avail_out.toNat at amountP
    rw [shape.1, Nat.min_eq_left (by omega)] at amountP
    exact amountP
  have emptyM : dm.pending.toNat = 0 := by
    change dm.pending.toNat + producedP = d.pending.toNat at leftP
    rw [shape.1, countP] at leftP
    omega
  have bitsM : dm.bi_valid.toInt.toNat = 0 := by
    rw [fieldsM]
    obtain ⟨_, _, _, bits, _, _⟩ := encoding
    exact bits
  obtain ⟨writtenEq, encodingM⟩ := header_byte_drain_encoding (input := input) pendingM emptyM bitsM wireM
  have outputM : 0 < zm.avail_out.toNat := by
    have count := accountM.2.2.2.1
    rw [countP] at count
    omega
  have statusM : dm.status = BUSY_STATE := by rw [fieldsM]; exact status
  have levelM : dm.level = 6 := by rw [fieldsM]; exact level
  have strategyM : dm.strategy = 0 := by rw [fieldsM]; exact strategy
  have lastM : dm.last_flush = Z_PARTIAL_FLUSH := by rw [fieldsM]
  have pointerM : zm.next_out = .ref (.dstate_depth owner) (oo + producedP) := by
    rw [accountM.2.2.2.2.2.1, pointer]
    rfl
  have validM := input_valid_accounting_output inputValid accountM
  have adlerM := (flush_pending_low_foreign_run_scalar_effects boundary0.good buffers0 pointer boundary0.bits
    flushRun stateM.good.live.hz accountM).1
  have checksumM : zm.adler = (ZlibF.Spec.adler32 (inputPrefix input (origin + fillEnd dm))).toUInt64 := by
    have endM : fillEnd dm = fillEnd d := by rw [fieldsM]; rfl
    rw [endM, adlerM]
    exact checksum
  have snapshot0 := caller_bytes_setD_depth (result := { d with last_flush := Z_PARTIAL_FLUSH }) boundary.good.live.hs rfl snapshot
  have snapshotM : Bytes middle zm.next_in zm.avail_in.toNat actualInput := by
    have originalBuffers:=buffers0
    obtain ⟨oldZ,oldGet,range,_outRange,separated⟩ := originalBuffers
    have oldEq : oldZ=z := Option.some.inj (oldGet.symm.trans boundary0.good.live.hz)
    subst oldZ
    have precise : BufferFrame (setD h ds {d with last_flush:=Z_PARTIAL_FLUSH}) middle
        (fun b=>StreamRoot r b ∨ DeflateOwned ds d b) [⟨z.next_out,producedP⟩] :=
      ⟨full_frame_weaken frameM.1 (by intro b changed;rcases changed with root|own;exact Or.inl root;exact Or.inr (Or.inl own)),frameM.2⟩
    have separatedNow : Separate z.next_in z.avail_in.toNat z.next_out producedP := by
      simpa only [advance_zero] using separate_advance_right (used:=0) separated
        (by have count:=accountM.2.2.2.1;omega)
    have kept:=foreign_caller_input_bytes_preserved boundary0.good buffers0 pointer range separatedNow
      (Nat.le_refl _) snapshot0 precise (Zlib.Deflate.BorrowProofs.stable_flush_pending _ _ _ _ flushRun)
    have inputPointer : zm.next_in=z.next_in := by simpa only [advance_zero] using accountM.2.2.2.2.1
    have inputCount : zm.avail_in=z.avail_in := UInt32.toNat_inj.mp (by have count:=accountM.2.2.1;omega)
    rw [inputPointer,inputCount]
    exact kept
  obtain ⟨used, after, z', result, nextInput, nextOrigin, nextBase, ys, written,
      dataRun, stateA, buffersA, accountA, bytesA, agreesA, endpointA, _baseA, statusA,
      lastA, encodingA, checksumA, inputLedgerA, effect⟩ :=
    public_foreign_busy_partial_data_raw_prefix_input_interval (stateM.strategy (readyM outputM)) stateM.end_frontier buffersM statusM levelM strategyM pointerM
      memory wrap (readyM outputM) validM snapshotM checksumM encodingM
  have queued : d.pending ≠ 0 := by intro zero; rw [zero] at shape; simp at shape
  have entry := public_pending_valid_continue boundary.good stateM.good status
    (by rw [pointer]; intro impossible; cases impossible)
    (by intro zero; rw [zero] at room; contradiction) inputValid queued Z_PARTIAL_FLUSH flagLo flagHi flushRun
    (by intro zero; rw [zero] at outputM; contradiction)
    (by intro impossible; rw [statusM] at impossible; cases impossible)
  have actual := entry.trans ((public_busy_header_skip_next stateM.good statusM (publicDataTail (some r) (some (.tab ds)) Z_PARTIAL_FLUSH)).trans dataRun)
  have earlier : Bytes after (.ref (.dstate_depth owner) oo) 1 [156] := by
    have oldBytes : Bytes middle (.ref (.dstate_depth owner) oo) [156].length [156] := by
      simpa only [pointer, countP, writtenEq, List.length_cons, List.length_nil] using bytesM
    have kept : ByteOutputInterval middle after (.dstate_depth owner) (oo + [156].length) written.length := by
      simpa only [List.length_cons, List.length_nil, countP] using effect
    exact kept.keep_published_bytes oldBytes
  have newBytes : Bytes after (.ref (.dstate_depth owner) (oo + 1)) written.length written := by
    simpa only [pointerM, countP] using bytesA
  have combinedBytes := generic_published_bytes_append earlier newBytes
  have account : StreamAccounting z z' used (1 + written.length) := by
    simpa only [countP, Nat.zero_add] using stream_accounting_trans accountM accountA
  have endM : fillEnd dm = fillEnd d := by rw [fieldsM]; rfl
  rw [lastM] at lastA
  refine ⟨used, after, z', result, nextInput, nextOrigin, nextBase, ys, written,
    actual, stateA, buffersA, account, ?_, ?_, ?_, statusA, lastA, ?_, checksumA, by simpa only [endM] using inputLedgerA⟩
  · simpa only [List.length_cons, List.length_nil, pointer] using combinedBytes
  · simpa only [endM] using agreesA
  · simpa only [endM] using endpointA
  · simpa only [List.nil_append] using encodingA



end Zlib.Deflate.Engine.Proofs
