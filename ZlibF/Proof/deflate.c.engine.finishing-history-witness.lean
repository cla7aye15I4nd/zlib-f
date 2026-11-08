import ZlibF.Proof.«deflate.c.engine.public-empty-finish»
import ZlibF.Proof.«deflate.c.engine.encoding-all-scalar-history»
import ZlibF.Proof.«deflate.c.engine.finishing-budget»

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Spec.Public.Proofs.DeflateInit
set_option autoImplicit false

/-- A concrete actual default init followed by empty-input FINISH with two
output bytes reaches FINISH_STATE. All data-trace and representation facts
are conclusions of real translated calls. This is a reachability witness,
not a whole-stream completion proof. -/
theorem actual_finishing_history_witness :
    ∃ h log z d, DefaultDataTrace (.tab 0) h log ∧ DGood h (.tab 0) 2 z d ∧
      log.input = [] ∧ log.output.length = 2 ∧ log.result = Z_OK ∧
      log.boundEligible = true ∧ log.finished = false ∧
      d.status = FINISH_STATE ∧ z.avail_in = 0 ∧ z.avail_out = 0 := by
  let caller : ZStream := { (default : ZStream) with next_out := .ref (.blk 1) 0, avail_out := 2 }
  let before := (ZStreamRef.tab 0).put ZlibF.Spec.Public.Proofs.DeflateInit.witnessHeap caller
  have oldGet : (ZStreamRef.tab 0).get ZlibF.Spec.Public.Proofs.DeflateInit.witnessHeap = some (default : ZStream) := by
    simp [ZStreamRef.get, ZlibF.Spec.Public.Proofs.DeflateInit.witnessHeap]
  have shape := shape_put oldGet caller
  have fresh : Fresh before := shape.fresh rfl witness_fresh
  have uniq : Uniq before := shape.uniq witness_uniq
  have get : (ZStreamRef.tab 0).get before = some caller := ZStreamRef.get_put_same oldGet caller
  have globals : LibraryGlobals before := rfl
  have allocators : DefaultOrNull caller := ⟨Or.inl rfl, Or.inl rfl⟩
  have version : VersionValue before (.ref (.blk 1) 0) (some 49) := by
    right
    refine ⟨49, rfl, Or.inr ⟨.blk 1, 0, #[49, 0], rfl, ?_, by decide, rfl⟩⟩
    simp [Space.get, before, ZlibF.Spec.Public.Proofs.DeflateInit.witnessHeap, Heap.empty]
  have domain : InitDomain before (.tab 0) (.ref (.blk 1) 0) :=
    ⟨fresh, uniq, globals, version, caller, get, allocators, rfl⟩
  have alloc : ∀ j, j < 5 → before.allocOk (before.nalloc + j) = true := by intro _ _; rfl
  obtain ⟨initialized, zi, sf, initRun, start, strategy, frontier, initial, _reachable⟩ :=
    default_initialization_end_frontier (h := before) (r := .tab 0) (z := caller)
      (version := .ref (.blk 1) 0) (level := Z_DEFAULT_COMPRESSION) (p := settings 6)
      fresh uniq globals get allocators version (by decide +kernel) alloc (fun _ => 0)
  obtain ⟨other, otherZ, otherD, otherRun, otherStart, _boundary, _initial, _history,
      nextIn, availIn, nextOut, availOut⟩ :=
    default_content_bindings (h := before) (r := .tab 0) (z := caller)
      (version := .ref (.blk 1) 0) (level := Z_DEFAULT_COMPRESSION) (p := settings 6)
      fresh uniq globals get allocators version (by decide +kernel) alloc (fun _ => 0)
  have heaps : other = initialized := (Prod.mk.inj (Except.ok.inj (otherRun.symm.trans initRun))).2
  subst other
  have streams : otherZ = zi := Option.some.inj (otherStart.good.live.hz.symm.trans start.good.live.hz)
  subst otherZ
  obtain ⟨oldZ, oldD, good, _alloc, _free, level, _strategy, _bits, _hash, _wrap, _start,
    _look, _pending, _bitvalid, _header, _totalIn, _totalOut, _msg, frame, _live, owned⟩ := initial
  have states : oldD = sf := Option.some.inj (good.live.hs.symm.trans start.good.live.hs)
  subst oldD
  have levelSix : sf.level = 6 := Int32.toInt_inj.mp level
  have liveOne : before.live 1 := by simp [Heap.live, before, ZlibF.Spec.Public.Proofs.DeflateInit.witnessHeap, Heap.empty]
  have one := frame.2.2.2.2.2 1 liveOne (by change ¬ (1 : Nat) = 0; decide)
  have bytesOne : initialized.bytes 1 = some #[49, 0] := by
    rw [one.1]
    simp [before, ZlibF.Spec.Public.Proofs.DeflateInit.witnessHeap, Heap.empty]
  have roOne : initialized.ro 1 = false := by rw [one.2.2.2.2.2.2.2]; rfl
  have buffers : StreamBuffers initialized (.tab 0) := by
    refine ⟨zi, start.good.live.hz, ?_, ?_, ?_⟩
    · exact Or.inl nextIn
    · rw [nextOut, availOut]
      change CallerRange initialized (.tab 0) (.ref (.blk 1) 0) 2 true
      right
      refine ⟨⟨[49, 0], Or.inr ⟨.blk 1, 0, #[49, 0], rfl, bytesOne, by decide, rfl⟩⟩,
        fun _ => Or.inr ⟨.blk 1, 0, #[49, 0], rfl, bytesOne, roOne, by decide⟩, ?_⟩
      intro b root mine
      have same : b = 1 := root
      subst b
      have bound := (owned 1).mp ((stream_owned_deflate start.good 1).mp mine)
      change 2 ≤ 1 ∧ 1 < 7 at bound
      omega
    · left
      rw [availIn]
      rfl
  have hash : sf.hash_size.toNat = 32768 := by rw [start.good.inv.hsize, start.hashBits]; rfl
  have memory : sf.lit_bufsize.toNat = 16384 := by have size := start.good.inv.lit; omega
  have pointer : zi.next_out = .ref (.blk 1) 0 := nextOut
  have empty : zi.avail_in = 0 := availIn
  have output : zi.avail_out = 2 := availOut
  obtain ⟨after, zf, result, run, goodA, buffersA, accountA, statusA, outputA⟩ :=
    first_empty_finish_two start levelSix strategy frontier buffers pointer output memory empty
  have history : DefaultDataTrace (.tab 0) initialized {} := .init domain initRun
  obtain ⟨dsE, ziE, dE, configE, encoding, _done⟩ := history.encoding
  have sameZi : ziE = zi := Option.some.inj (encoding.protocol.good.live.hz.symm.trans start.good.live.hz)
  subst ziE
  have snapshot : Bytes initialized zi.next_in zi.avail_in.toNat [] := Or.inl ⟨nextIn, by rw [empty]; rfl, rfl⟩
  obtain ⟨usedE, rcE, afterE, zE, resultE, written, runE, stateE, _buffersE, accountE, bytesE, _endedE⟩ :=
    encoding.scalar_encoding_request buffers (Or.inr ⟨1, 0, pointer⟩) Z_FINISH snapshot
  obtain ⟨code, afters⟩ := Prod.mk.inj (Except.ok.inj (runE.symm.trans run))
  subst rcE afterE
  have sameZF : zE = zf := Option.some.inj (stateE.protocol.good.live.hz.symm.trans goodA.live.hz)
  subst zE
  obtain ⟨usedZero, writtenTwo⟩ := stream_accounting_counts_unique accountE accountA
  subst usedE
  have active : ActiveHeader initialized (.tab 0) :=
    default_finish_active_header encoding.protocol.good encoding.protocol.no_header
  have observed : DataStep .deflate initialized after (.tab 0) Z_FINISH Z_OK [] written 0 := by
    refine ⟨zi, zf, start.good.live.hz, goodA.live.hz, buffers, active, snapshot, ?_, ?_, run⟩
    · simp only [empty, UInt32.toNat_zero, Nat.zero_sub]
    · simpa only [output, outputA, UInt32.toNat_ofNat, Nat.sub_zero, writtenTwo] using bytesE
  let log : DataLog := { output := written }
  have actualHistory : DefaultDataTrace (.tab 0) after log := by
    simpa [log, show (Z_OK == Z_STREAM_END) = false from rfl] using
      (DefaultDataTrace.step history start.good.live.hz (Or.inr ⟨1, 0, pointer⟩) observed)
  have inputA : zf.avail_in = 0 := UInt32.toNat_inj.mp (by
    have count := accountA.2.2.1
    simpa only [empty, UInt32.toNat_zero, Nat.add_zero] using count)
  exact ⟨after, log, zf, result, actualHistory, goodA, rfl, writtenTwo, rfl, rfl, rfl, statusA, inputA, outputA⟩


/-- The finishing case of actual default histories completes under its
direct pending/trailer publication budget. The whole-stream deflateBound
inequality is a separate producer obligation. -/
theorem DefaultDataTrace.complete_finishing_budget
    {h : Heap} {r : ZStreamRef} {log : DataLog} {ds ob oo : Nat}
    {z : ZStream} {d : DeflateState}
    (history : DefaultDataTrace r h log) (good : DGood h r ds z d)
    (status : d.status = FINISH_STATE) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo) (empty : z.avail_in = 0)
    (room : d.pending.toNat + 4 ≤ z.avail_out.toNat) :
    ∃ after, C.run (deflate (some r) Z_FINISH) h = .ok (Z_STREAM_END, after) := by
  obtain ⟨ds0, z0, d0, config, protocol⟩ := history.protocol
  have sameZ : z0 = z := Option.some.inj (protocol.good.live.hz.symm.trans good.live.hz)
  subst z0
  have sameDS : ds0 = ds := by
    simpa only [protocol.good.live.zst, Option.some.injEq, StateRef.deflate.injEq] using good.live.zst
  subst ds0
  have sameD : d0 = d := Option.some.inj (protocol.good.live.hs.symm.trans good.live.hs)
  subst d0
  have phase : FinishingPhase d config := by
    rcases protocol.phase with ⟨_, _, _, start, _⟩ | ⟨_, _, _, _, _, busy⟩ | phase
    · exact False.elim ((by decide : INIT_STATE ≠ FINISH_STATE) (start.status.symm.trans status))
    · exact False.elim ((by decide : BUSY_STATE ≠ FINISH_STATE) (busy.symm.trans status))
    · exact phase
  obtain ⟨_produced, after, _z', _result, run, _goodA, _buffersA, _account⟩ :=
    public_finishing_pending_budget good buffers phase pointer empty room protocol.lower protocol.upper
  exact ⟨after, run⟩

end Zlib.Deflate.Engine.Proofs
