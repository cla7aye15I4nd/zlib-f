import ZlibF.Proof.«deflate.c.engine.all-scalar-request-contract»
import ZlibF.Proof.«deflate.c.engine.public-witness»

/-! # A real nonempty execution inhabits the complete default public contract -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
open ZlibF.Spec.Public.Proofs.DeflateInit
set_option autoImplicit false

/-- A concrete nonempty caller inhabits the complete default request
contract. Actual initialization is followed by a public NO_FLUSH call
accepting 300 bytes and writing the two real zlib header bytes. -/
theorem default_public_full_contract_witness :
    ∃ initialized zi sf config after zf result used written,
      C.run (deflateInit_ (some (.tab 0)) Z_DEFAULT_COMPRESSION (.ref (.blk 1) 0) 112)
        publicWitnessHeap = .ok (Z_OK, initialized) ∧
      DefaultFinishBoundary initialized (.tab 0) 2 zi sf config ∧ StreamBuffers initialized (.tab 0) ∧
      zi.avail_in = 300 ∧ C.run (deflate (some (.tab 0)) Z_NO_FLUSH) initialized = .ok (Z_OK, after) ∧
      DefaultFinishBoundary after (.tab 0) 2 zf result config ∧ StreamBuffers after (.tab 0) ∧
      StreamAccounting zi zf used written.length ∧ used = 300 ∧ written.length = 2 ∧
      Bytes after zi.next_out written.length written ∧
      zf.total_in = zi.total_in + UInt64.ofNat used ∧ zf.total_out = zi.total_out + UInt64.ofNat written.length ∧
      Shape initialized after ∧ BufferFrame initialized after
        (fun b => StreamRoot (.tab 0) b ∨ DeflateOwned 2 sf b) [⟨zi.next_out, written.length⟩] ∧
      LiveChange initialized after (fun _ => False) (fun _ => False) ∧
      after.nalloc = initialized.nalloc ∧ after.nextBlk = initialized.nextBlk := by
  let enlarged := { witnessHeap with bytes := upd witnessHeap.bytes 1 (some #[49, 0, 0, 0]) }
  have oneGet : witnessHeap.bytes 1 = some #[49, 0] := by simp [witnessHeap, Heap.empty]
  have shapeB := shape_setB oneGet #[49, 0, 0, 0]
  have oldGet : (ZStreamRef.tab 0).get enlarged = some (default : ZStream) := by
    simp [ZStreamRef.get, enlarged, witnessHeap]
  have shape := shapeB.trans (shape_put oldGet publicWitnessStream)
  have fresh : Fresh publicWitnessHeap := shape.fresh (by simp [publicWitnessHeap, enlarged]) witness_fresh
  have uniq : Uniq publicWitnessHeap := shape.uniq witness_uniq
  have get : (ZStreamRef.tab 0).get publicWitnessHeap = some publicWitnessStream :=
    ZStreamRef.get_put_same oldGet _
  have version : VersionValue publicWitnessHeap (.ref (.blk 1) 0) (some 49) := by
    right
    refine ⟨49, rfl, Or.inr ⟨.blk 1, 0, #[49, 0, 0, 0], rfl, ?_, by decide, rfl⟩⟩
    simp [Space.get, publicWitnessHeap, witnessHeap, Heap.empty]
  obtain ⟨initialized, zi, sf, initRun, start, boundary, initial, _, nextIn, availIn, nextOut, availOut⟩ :=
    default_content_bindings (h := publicWitnessHeap) (r := .tab 0) (z := publicWitnessStream)
      (version := .ref (.blk 1) 0) (level := Z_DEFAULT_COMPRESSION) (p := settings 6)
      fresh uniq (by rfl) get ⟨Or.inl rfl, Or.inl rfl⟩ version (by decide +kernel) (by intro _ _; rfl) (fun _ => 0)
  have count : zi.avail_in = 300 := availIn
  obtain ⟨otherZ, otherD, good, _alloc, _free, level, _strategy, _bits, _hash, _wrap, _start,
    _look, _pending, _bitvalid, _header, _totalIn, _totalOut, _msg, oldFrame, _live, owned⟩ := initial
  have sameD : otherD = sf := Option.some.inj (good.live.hs.symm.trans start.good.live.hs)
  subst otherD
  have levelSix : sf.level = 6 := Int32.toInt_inj.mp level
  have liveOne : publicWitnessHeap.live 1 := by simp [Heap.live, publicWitnessHeap, witnessHeap, Heap.empty]
  have one := oldFrame.2.2.2.2.2 1 liveOne (by change ¬ (1 : Nat) = 0; decide)
  have bytesOne : initialized.bytes 1 = some #[49, 0, 0, 0] := by
    rw [one.1]
    simp [publicWitnessHeap, witnessHeap, Heap.empty]
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
  obtain ⟨sameInit, sameZ, sameD, sameRun, protocol⟩ := default_initialization_finish_protocol
    (h := publicWitnessHeap) (r := .tab 0) (z := publicWitnessStream) (version := .ref (.blk 1) 0)
    fresh uniq rfl get ⟨Or.inl rfl, Or.inl rfl⟩ version (by intro _ _; rfl)
  have heapEq : sameInit = initialized := (Prod.mk.inj (Except.ok.inj (sameRun.symm.trans initRun))).2
  rw [heapEq] at protocol
  have streamEq : sameZ = zi := Option.some.inj (protocol.good.live.hz.symm.trans start.good.live.hz)
  have stateEq : sameD = sf := Option.some.inj (protocol.good.live.hs.symm.trans start.good.live.hs)
  subst sameZ sameD
  have raw : zi.next_out = .null ∨ ∃ ob oo, zi.next_out = .ref (.blk ob) oo := Or.inr ⟨1, 0, nextOut⟩
  obtain ⟨used, written, rc, after, zf, result, run, stateA, buffersA, _goodA, accountA, bytesA,
      inputA, outputA, _allowed, _controls, _invalid, _terminal, shape, frame, live, alloc, next⟩ :=
    protocol.all_scalar_request_contract Z_NO_FLUSH buffer raw
  obtain ⟨oldInit, oldZ, oldD, oldUsed, oldAfter, oldZF, oldResult, _ys, _extended, _origin,
      oldInitRun, _oldInput, oldStart, oldRun, oldContent, _oldBuffers, oldAccount, accepted,
      _nonempty, _header⟩ := default_public_first_witness_header
  have oldHeaps : oldInit = initialized := (Prod.mk.inj (Except.ok.inj (oldInitRun.symm.trans initRun))).2
  rw [oldHeaps] at oldStart oldRun
  have oldStream : oldZ = zi := Option.some.inj (oldStart.good.live.hz.symm.trans start.good.live.hz)
  subst oldZ
  have sameReturned := actual_run_stream_unique oldRun run oldContent.good.live.hz stateA.good.live.hz
  rw [sameReturned] at oldAccount
  have counts := stream_accounting_counts_unique accountA oldAccount
  have rcOK : Z_OK = rc := (Prod.mk.inj (Except.ok.inj (oldRun.symm.trans run))).1
  subst rc
  exact ⟨initialized, zi, sf, engineConfig sf, after, zf, result, used, written,
    initRun, protocol, buffer, count, run, stateA, buffersA, accountA,
    counts.1.trans accepted, counts.2, bytesA, inputA, outputA, shape, frame, live, alloc, next⟩

end Zlib.Deflate.Engine.Proofs
