import ZlibF.Proof.«deflate.c.engine.common-history-completes»
import ZlibF.Proof.«deflate.c.engine.public-witness»

/-! # A nondefault common-level history completes with nonempty input -/
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Spec.Public.Proofs.DeflateInit
set_option autoImplicit false

/-- A concrete actual level-four initializer and 300 readable input bytes
start the common-level history. Its first real NO_FLUSH output capacity
is one; no engine invariant is assumed. -/
theorem common_level_four_trace_witness :
    ∃ initialized after log z,
      C.run (deflateInit_ (some (.tab 0)) (4 : Int32) (.ref (.blk 1) 0) 112)
        publicWitnessHeap = .ok (Z_OK, initialized) ∧
      CommonDataTrace (.tab 0) after log ∧ log.input = [] ∧ log.output = [120] ∧
      (.tab 0 : ZStreamRef).get after = some z ∧ z.avail_in = 300 ∧
      StreamBuffers after (.tab 0) ∧
      Bytes after z.next_in z.avail_in.toNat (((ZlibF.Spec.Public.Proofs.DeflateInit.witnessHeap.static.dist_code).toList.drop 0).take 300) := by
  let enlarged := { ZlibF.Spec.Public.Proofs.DeflateInit.witnessHeap with bytes := upd ZlibF.Spec.Public.Proofs.DeflateInit.witnessHeap.bytes 1 (some #[49, 0, 0, 0]) }
  have oneGet : ZlibF.Spec.Public.Proofs.DeflateInit.witnessHeap.bytes 1 = some #[49, 0] := by simp [ZlibF.Spec.Public.Proofs.DeflateInit.witnessHeap, Heap.empty]
  have shapeB := shape_setB oneGet #[49, 0, 0, 0]
  have oldGet : (ZStreamRef.tab 0).get enlarged = some (default : ZStream) := by
    simp [ZStreamRef.get, enlarged, ZlibF.Spec.Public.Proofs.DeflateInit.witnessHeap]
  have shape := shapeB.trans (shape_put oldGet publicWitnessStream)
  have fresh : Fresh publicWitnessHeap := shape.fresh (by simp [publicWitnessHeap, enlarged]) witness_fresh
  have uniq : Uniq publicWitnessHeap := shape.uniq witness_uniq
  have get : (ZStreamRef.tab 0).get publicWitnessHeap = some publicWitnessStream :=
    ZStreamRef.get_put_same oldGet _
  have version : VersionValue publicWitnessHeap (.ref (.blk 1) 0) (some 49) := by
    right
    refine ⟨49, rfl, Or.inr ⟨.blk 1, 0, #[49, 0, 0, 0], rfl, ?_, by decide, rfl⟩⟩
    simp [Space.get, publicWitnessHeap, ZlibF.Spec.Public.Proofs.DeflateInit.witnessHeap, Heap.empty]
  obtain ⟨initialized, zi, sf, initRun, start, boundary, initial, _, nextIn, availIn, nextOut, availOut⟩ :=
    default_content_bindings (h := publicWitnessHeap) (r := .tab 0) (z := publicWitnessStream)
      (version := .ref (.blk 1) 0) (level := (4 : Int32)) (p := settings 4)
      fresh uniq (by rfl) get ⟨Or.inl rfl, Or.inl rfl⟩ version (by decide +kernel) (by intro _ _; rfl) (fun _ => 0)
  have count : zi.avail_in = 300 := availIn
  have initialCopy := initial
  obtain ⟨otherZ, otherD, good, _alloc, _free, level, _strategy, _bits, _hash, _wrap, _start,
    _look, _pending, _bitvalid, _header, _totalIn, _totalOut, _msg, oldFrame, _live, owned⟩ := initial
  have sameD : otherD = sf := Option.some.inj (good.live.hs.symm.trans start.good.live.hs)
  subst otherD
  have liveOne : publicWitnessHeap.live 1 := by simp [Heap.live, publicWitnessHeap, ZlibF.Spec.Public.Proofs.DeflateInit.witnessHeap, Heap.empty]
  have one := oldFrame.2.2.2.2.2 1 liveOne (by change ¬ (1 : Nat) = 0; decide)
  have bytesOne : initialized.bytes 1 = some #[49, 0, 0, 0] := by
    rw [one.1]
    simp [publicWitnessHeap, ZlibF.Spec.Public.Proofs.DeflateInit.witnessHeap, Heap.empty]
  have roOne : initialized.ro 1 = false := by rw [one.2.2.2.2.2.2.2]; rfl
  obtain ⟨_, _, _, trees⟩ := start.good.trees
  have distSize : initialized.static.dist_code.size = 512 := by
    rw [trees.base.static.dist_code, Zlib.Trees.Proofs.Out.dist_code_tab_size]
  have buffer : StreamBuffers initialized (.tab 0) := by
    refine ⟨zi, start.good.live.hz, ?_, ?_, ?_⟩
    · rw [nextIn, availIn]
      change CallerRange initialized (.tab 0) (.ref .st_dist_code 0) 300 false
      right
      refine ⟨⟨(initialized.static.dist_code.toList.drop 0).take 300,
        Or.inr ⟨.st_dist_code, 0, initialized.static.dist_code, rfl, rfl, by omega, rfl⟩⟩,
        ?_, fun _ root => False.elim root⟩
      intro impossible
      cases impossible
    · rw [nextOut, availOut]
      change CallerRange initialized (.tab 0) (.ref (.blk 1) 0) 4 true
      right
      refine ⟨⟨[49, 0, 0, 0], Or.inr ⟨.blk 1, 0, #[49, 0, 0, 0], rfl, bytesOne, by decide, rfl⟩⟩,
        fun _ => Or.inr ⟨.blk 1, 0, #[49, 0, 0, 0], rfl, bytesOne, roOne, by decide⟩, ?_⟩
      intro b root mine
      have equal : b = 1 := root
      subst b
      have mineOwned := (stream_owned_deflate start.good 1).mp mine
      have bound := (owned 1).mp mineOwned
      change 2 ≤ 1 ∧ 1 < 7 at bound
      omega
    · rw [nextIn, availIn, nextOut, availOut]
      change Separate (.ref .st_dist_code 0) 300 (.ref (.blk 1) 0) 4
      exact Or.inr (Or.inr (Or.inl (by decide)))

  have globals : LibraryGlobals initialized := oldFrame.1.symm.trans (show LibraryGlobals publicWitnessHeap from rfl)
  have allocators : DefAlloc zi := by
    have sameZ : otherZ = zi := Option.some.inj (good.live.hz.symm.trans start.good.live.hz)
    subst otherZ
    exact ⟨_alloc, _free⟩
  have fixedSize : ZlibF.Spec.Public.Proofs.DeflateInit.witnessHeap.static.dist_code.size = 512 := by
    have eq := congrArg (fun s : Statics => s.dist_code.size) globals
    exact eq.symm.trans distSize
  have snapshot : Bytes initialized zi.next_in zi.avail_in.toNat
      (((ZlibF.Spec.Public.Proofs.DeflateInit.witnessHeap.static.dist_code).toList.drop 0).take 300) := by
    rw [nextIn, availIn]
    exact Or.inr ⟨.st_dist_code, 0, (ZlibF.Spec.Public.Proofs.DeflateInit.witnessHeap.static.dist_code), rfl,
      by exact congrArg (fun s : Statics => some s.dist_code) globals, by rw [fixedSize]; decide, rfl⟩
  obtain ⟨g, zg, edit, getG, fieldsG, snapshotG, buffersG, _goodG, _allocG, _nextG, _attemptsG, _ownedG⟩ :=
    ZlibF.Spec.Public.Proofs.DeflateCore.rebuffer_one_byte_of_good start.good globals allocators
      (initial_no_header start initialCopy) buffer snapshot
  have domain : InitDomain publicWitnessHeap (.tab 0) (.ref (.blk 1) 0) :=
    ⟨fresh, uniq, rfl, version, publicWitnessStream, get, ⟨Or.inl rfl, Or.inl rfl⟩, rfl⟩
  obtain ⟨zf, sf0, _start0, _initial0, first⟩ :=
    common_observed_initialization_encoding domain (p := settings 4) (by decide +kernel)
      (by decide) (by decide) initRun
  obtain ⟨other, getOther, firstG⟩ := first g edit
  have same : other = zg := Option.some.inj (getOther.symm.trans getG)
  subst other
  have pointer : zg.next_out = .ref (.blk initialized.nextBlk) 0 := by rw [fieldsG]
  have one : zg.avail_out = 1 := by rw [fieldsG]
  have valid := ZlibF.Spec.Public.Proofs.DeflateCore.snapshot_input_valid snapshotG
  obtain ⟨after, z', result, actual, encodingA, buffersA, accountA, bytesA⟩ :=
    firstG initialized.nextBlk 0 pointer one buffersG valid Z_NO_FLUSH (by decide) (by decide)
  have observed : DataStep .deflate g after (.tab 0) Z_NO_FLUSH Z_OK
      (((ZlibF.Spec.Public.Proofs.DeflateInit.witnessHeap.static.dist_code).toList.drop 0).take 300) [120] 0 := by
    refine ⟨zg, z', getG, encodingA.protocol.good.live.hz, buffersG,
      default_finish_active_header _goodG (initial_no_header start initialCopy), snapshotG, ?_, ?_, actual⟩
    · have effect := accountA.2.2.1
      omega
    · have effect := accountA.2.2.2.1
      have difference : zg.avail_out.toNat - z'.avail_out.toNat = 1 := by omega
      rw [difference]
      exact bytesA
  let log := DeflateCore.advanceLog {} Z_NO_FLUSH Z_OK
    (((ZlibF.Spec.Public.Proofs.DeflateInit.witnessHeap.static.dist_code).toList.drop 0).take 300) [120] 0
  have trace : CommonDataTrace (.tab 0) after log := .first domain (p := settings 4)
    (by decide +kernel) (by decide) (by decide) initRun edit getG pointer one (by decide) (by decide) observed
  have world := trace.environment.1
  have inputCount : z'.avail_in = 300 := by
    apply UInt32.toNat_inj.mp
    have effect := accountA.2.2.1
    rw [fieldsG, count] at effect
    exact effect
  have inputPointer : z'.next_in = .ref .st_dist_code 0 := by
    have effect := accountA.2.2.2.2.1
    rw [fieldsG, nextIn] at effect
    exact effect
  have snapshotA : Bytes after z'.next_in z'.avail_in.toNat
      (((ZlibF.Spec.Public.Proofs.DeflateInit.witnessHeap.static.dist_code).toList.drop 0).take 300) := by
    rw [inputPointer, inputCount]
    exact Or.inr ⟨.st_dist_code, 0, (ZlibF.Spec.Public.Proofs.DeflateInit.witnessHeap.static.dist_code), rfl,
      by exact congrArg (fun s : Statics => some s.dist_code) world, by rw [fixedSize]; decide, rfl⟩
  exact ⟨initialized, after, log, z', initRun, trace, rfl, rfl,
    encodingA.protocol.good.live.hz, inputCount, buffersA, snapshotA⟩


/-- The concrete nondefault level-four history consumes all 300 input
bytes, finishes in finitely many real calls and has independently valid
cumulative output. The initialized history is therefore inhabited by a
nonempty, nondefault complete compression execution. -/
theorem common_level_four_complete_witness :
    ∃ initialized after log,
      C.run (deflateInit_ (some (.tab 0)) (4 : Int32) (.ref (.blk 1) 0) 112)
        publicWitnessHeap = .ok (Z_OK, initialized) ∧
      CommonDataTrace (.tab 0) after log ∧ log.input.length = 300 ∧
      log.result = Z_STREAM_END ∧ ZlibF.Spec.Zlib.Valid log.input log.output := by
  obtain ⟨initialized, h, log, z, initRun, history, empty, header, get, count, buffers, snapshot⟩ :=
    common_level_four_trace_witness
  obtain ⟨ds, current, d, config, state, _valid⟩ := history.encoding
  have same : current = z := Option.some.inj (state.protocol.good.live.hz.symm.trans get)
  subst current
  have busy : d.status = BUSY_STATE := by
    rcases state.phase with ⟨_, _, _, _, status, _⟩ | ⟨_, _, _, _, _, _, _, status, _, _⟩ |
      ⟨published, outputEq, _phase, _encoding⟩
    · exact status
    · exact status
    · rw [header] at outputEq
      have sizes := congrArg List.length outputEq
      simp only [levelHeaderPrefix, List.length_append, List.length_cons, List.length_nil] at sizes
      omega
  have protocol : ∀ ds' d', z.state = some (.deflate ds') → h.dstates ds' = some d' →
      d'.status = FINISH_STATE → ((ZlibF.Spec.Public.Proofs.DeflateInit.witnessHeap.static.dist_code).toList.drop 0).take 300 = [] := by
    intro ds' d' getState getD finished
    have keys : ds = ds' := by
      simpa only [state.protocol.good.live.zst, Option.some.injEq, StateRef.deflate.injEq] using getState
    subst ds'
    have sameD : d' = d := Option.some.inj (getD.symm.trans state.protocol.good.live.hs)
    subst d'
    exact False.elim ((by decide : BUSY_STATE ≠ FINISH_STATE) (busy.symm.trans finished))
  obtain ⟨after, finalLog, _continuation, content, ended, historyA, validA⟩ :=
    history.completes get buffers snapshot protocol
  have inputLength := caller_bytes_length snapshot
  rw [count] at inputLength
  refine ⟨initialized, after, finalLog, initRun, historyA, ?_, ended, ?_⟩
  · rw [content, empty, List.nil_append]
    exact inputLength
  · rw [content]
    exact validA

end Zlib.Deflate.Engine.Proofs
