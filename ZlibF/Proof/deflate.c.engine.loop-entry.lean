import ZlibF.Proof.«deflate.c.engine.slow-loop»

/-! # The outer-loop path starts from actual default initialization -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
open ZlibF.Spec.Public.Proofs.DeflateInit
set_option autoImplicit false

theorem EngineStart.symbol_capacity {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (start : EngineStart h r ds z d) : d.sym_end.toNat = 49149 := by
  have hash : d.hash_size.toNat = 32768 := by rw [start.good.inv.hsize, start.hashBits]; rfl
  have lit : d.lit_bufsize.toNat = 16384 := by have size := start.good.inv.lit; omega
  rw [start.good.inv.sym.2.1, lit]

/-- Actual default entry retains caller bindings while establishing the
content boundary. Both conclusions concern its one returned heap. -/
theorem default_content_bindings {h : Heap} {r : ZStreamRef} {z : ZStream}
    {version : BPtr} {level : Int32} {p : ZlibF.Spec.Api.DeflParams}
    (hf : Fresh h) (hu : Uniq h) (hg : LibraryGlobals h) (hz : r.get h = some z)
    (ha : DefaultOrNull z) (hv : VersionValue h version (some 49))
    (params : ZlibF.Spec.Api.deflInit? level.toInt 8 15 8 0 = some p)
    (alloc : ∀ j, j < 5 → h.allocOk (h.nalloc + j) = true) (input : Nat → UInt8) :
    ∃ after zf sf,
      C.run (deflateInit_ (some r) level version 112) h = .ok (Z_OK, after) ∧
      EngineStart after r h.nextBlk zf sf ∧ ContentBoundary after r h.nextBlk zf sf input 0 0 [] ∧
      DeflateInitial h after r p ∧ StreamReachable .deflate after r ∧
      zf.next_in = z.next_in ∧ zf.avail_in = z.avail_in ∧ zf.next_out = z.next_out ∧ zf.avail_out = z.avail_out := by
  obtain ⟨after, zf, sf, run, start, boundary, initial, reachable⟩ :=
    default_initialization_content_boundary hf hu hg hz ha hv params alloc input
  obtain ⟨other, otherZ, otherD, otherRun, otherStart, _, _, nextIn, availIn, nextOut, availOut⟩ :=
    default_initialization_engine_bindings hf hu hg hz ha hv params alloc
  have same : other = after := congrArg Prod.snd (Except.ok.inj (otherRun.symm.trans run))
  subst other
  have sameZ : otherZ = zf := Option.some.inj (otherStart.good.live.hz.symm.trans start.good.live.hz)
  subst otherZ
  exact ⟨after, zf, sf, run, start, boundary, initial, reachable, nextIn, availIn, nextOut, availOut⟩

def loopWitnessStream : ZStream :=
  { (default : ZStream) with
    next_in := .ref .st_dist_code 0, avail_in := 300,
    next_out := .ref (.blk 1) 0, avail_out := 2 }

def loopWitnessHeap : Heap := (ZStreamRef.tab 0).put witnessHeap loopWitnessStream

/-- Non-vacuity for the complete loop path. A concrete default entry has
300 readable static-table bytes and a two-byte caller output range. The
actual strategy call terminates with decoded content and valid buffers.
This is an internal strategy witness, not public deflate dispatch. -/
theorem default_slow_loop_witness :
    ∃ initialized zi sf used after zf result ys extended nextOrigin,
      C.run (deflateInit_ (some (.tab 0)) Z_DEFAULT_COMPRESSION (.ref (.blk 1) 0) 112)
        loopWitnessHeap = .ok (Z_OK, initialized) ∧ zi.avail_in = 300 ∧ StreamBuffers initialized (.tab 0) ∧
      EngineStart initialized (.tab 0) 2 zi sf ∧
      deflate_slow (some (.tab 2)) Z_NO_FLUSH initialized = .ok (need_more, after) ∧
      ContentBoundary after (.tab 0) 2 zf result extended nextOrigin 0 ys ∧
      StreamBuffers after (.tab 0) ∧ StreamAccounting zi zf used 0 ∧ used = 300 ∧ ys ≠ [] := by
  have oldGet : (ZStreamRef.tab 0).get witnessHeap = some (default : ZStream) := by
    simp [ZStreamRef.get, witnessHeap]
  have shape := shape_put oldGet loopWitnessStream
  have fresh : Fresh loopWitnessHeap := shape.fresh (by simp [loopWitnessHeap]) witness_fresh
  have uniq : Uniq loopWitnessHeap := shape.uniq witness_uniq
  have get : (ZStreamRef.tab 0).get loopWitnessHeap = some loopWitnessStream := ZStreamRef.get_put_same oldGet _
  have version : VersionValue loopWitnessHeap (.ref (.blk 1) 0) (some 49) := by
    right
    refine ⟨49, rfl, Or.inr ⟨.blk 1, 0, #[49, 0], rfl, ?_, by decide, rfl⟩⟩
    simp [Space.get, loopWitnessHeap, witnessHeap, Heap.empty]
  obtain ⟨initialized, zi, sf, initRun, start, boundary, initial, _, nextIn, availIn, nextOut, availOut⟩ :=
    default_content_bindings (h := loopWitnessHeap) (r := .tab 0) (z := loopWitnessStream)
      (version := .ref (.blk 1) 0) (level := Z_DEFAULT_COMPRESSION) (p := settings 6)
      fresh uniq (by rfl) get ⟨Or.inl rfl, Or.inl rfl⟩ version (by decide +kernel) (by intro _ _; rfl) (fun _ => 0)
  have count : zi.avail_in = 300 := availIn
  obtain ⟨otherZ, otherD, good, _alloc, _free, _level, _strategy, _bits, _hash, _wrap, _start,
    _look, _pending, _bitvalid, _header, _totalIn, _totalOut, _msg, oldFrame, _live, owned⟩ := initial
  have sameD : otherD = sf := Option.some.inj (good.live.hs.symm.trans start.good.live.hs)
  subst otherD
  have liveOne : loopWitnessHeap.live 1 := by simp [Heap.live, loopWitnessHeap, witnessHeap, Heap.empty]
  have one := oldFrame.2.2.2.2.2 1 liveOne (by change ¬ (1 : Nat) = 0; decide)
  have bytesOne : initialized.bytes 1 = some #[49, 0] := by
    rw [one.1]
    simp [loopWitnessHeap, witnessHeap, Heap.empty]
  have roOne : initialized.ro 1 = false := by rw [one.2.2.2.2.2.2.2]; rfl
  obtain ⟨_, _, _, trees⟩ := start.good.trees
  have distSize : initialized.static.dist_code.size = 512 := by rw [trees.base.static.dist_code, Zlib.Trees.Proofs.Out.dist_code_tab_size]
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
      change CallerRange initialized (.tab 0) (.ref (.blk 1) 0) 2 true
      right
      refine ⟨⟨[49, 0], Or.inr ⟨.blk 1, 0, #[49, 0], rfl, bytesOne, by decide, rfl⟩⟩,
        fun _ => Or.inr ⟨.blk 1, 0, #[49, 0], rfl, bytesOne, roOne, by decide⟩, ?_⟩
      intro b root mine
      have equal : b = 1 := root
      subst b
      have mineOwned := (stream_owned_deflate start.good 1).mp mine
      have bound := (owned 1).mp mineOwned
      change 2 ≤ 1 ∧ 1 < 7 at bound
      omega
    · rw [nextIn, availIn, nextOut, availOut]
      change Separate (.ref .st_dist_code 0) 300 (.ref (.blk 1) 0) 2
      exact Or.inr (Or.inr (Or.inl (by decide)))
  have budget : 3 * (0 + fillEnd sf + zi.avail_in.toNat - 0 + 1) < sf.sym_end.toNat := by
    rw [start.symbol_capacity, count]
    simp only [fillEnd, start.start, start.lookahead]
    decide +kernel
  obtain ⟨used, after, zf, result, ys, extended, nextOrigin, run, content, buffersA, account,
      _storage, _fields, _agrees, _symbols, endpoint, _expands, stopped, acceptedAll⟩ :=
    deflate_slow_no_flush_before_block boundary start.wrap buffer (by rw [nextIn]; intro _; decide) budget
  have outputPositive : zi.avail_out ≠ 0 := by rw [availOut]; change (2 : UInt32) ≠ 0; decide
  have accepted : used = 300 := by
    have value := acceptedAll outputPositive
    rw [count] at value
    exact value
  have outputFinal : zf.avail_out = zi.avail_out := UInt32.toNat_inj.mp (by
    have value := account.2.2.2.1
    omega)
  have short : result.lookahead.toNat < 262 := by
    rcases stopped with ⟨_, short⟩ | empty
    · exact short
    · exact False.elim (outputPositive (outputFinal.symm.trans empty))
  have initialEnd : fillEnd sf = 0 := by simp [fillEnd, start.start, start.lookahead]
  rw [initialEnd, accepted] at endpoint
  have credit : pendingCredit result ≤ 1 := by unfold pendingCredit; split <;> omega
  have positive : 0 < represented ys := by
    have accounted := content.accounted
    dsimp only [fillEnd] at endpoint
    omega
  have nonempty : ys ≠ [] := by
    intro empty
    rw [empty] at positive
    change 0 < 0 at positive
    omega
  exact ⟨initialized, zi, sf, used, after, zf, result, ys, extended, nextOrigin,
    initRun, count, buffer, start, run, content, buffersA, account, accepted, nonempty⟩

end Zlib.Deflate.Engine.Proofs
