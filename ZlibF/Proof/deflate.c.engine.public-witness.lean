import ZlibF.Proof.«deflate.c.engine.public-first»

/-! # A real default initialization followed by public deflate

The nonempty call goes through entry checks, the wrapper header and the
selected strategy. It is not a direct internal-strategy invocation.
-/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
open ZlibF.Spec.Public.Proofs.DeflateInit
set_option autoImplicit false

def publicWitnessStream : ZStream :=
  { (default : ZStream) with
    next_in := .ref .st_dist_code 0, avail_in := 300,
    next_out := .ref (.blk 1) 0, avail_out := 4 }

def publicWitnessHeap : Heap :=
  (ZStreamRef.tab 0).put { witnessHeap with bytes := upd witnessHeap.bytes 1 (some #[49, 0, 0, 0]) }
    publicWitnessStream

/-- The default public entry has a concrete nonempty execution. Actual
initialization precedes the public Z_NO_FLUSH call. It accepts 300 input
bytes, produces two wrapper bytes and retains a nonempty decoded symbol
trace with valid caller buffers. Block bits are still buffered. -/
theorem default_public_first_witness_header :
    ∃ initialized zi sf used after zf result ys extended nextOrigin,
      C.run (deflateInit_ (some (.tab 0)) Z_DEFAULT_COMPRESSION (.ref (.blk 1) 0) 112)
        publicWitnessHeap = .ok (Z_OK, initialized) ∧ zi.avail_in = 300 ∧
      EngineStart initialized (.tab 0) 2 zi sf ∧
      deflate (some (.tab 0)) Z_NO_FLUSH initialized = .ok (Z_OK, after) ∧
      ContentBoundary after (.tab 0) 2 zf result extended nextOrigin 0 ys ∧
      StreamBuffers after (.tab 0) ∧ StreamAccounting zi zf used 2 ∧ used = 300 ∧ ys ≠ [] ∧
      ∃ written, after.bytes 1 = some written ∧ written[0]? = some 120 ∧ written[1]? = some 156 := by
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
  have budget : 3 * (fillEnd sf + zi.avail_in.toNat + 1) < sf.sym_end.toNat := by
    rw [start.symbol_capacity, count]
    simp only [fillEnd, start.start, start.lookahead]
    decide +kernel
  obtain ⟨used, after, zf, result, ys, extended, nextOrigin, run, content, buffersA, account,
      usedAll, empty, short, endpoint, _expands, written⟩ :=
    public_default_first_before_block_output start levelSix boundary buffer (by exact nextOut)
      (by rw [availOut]; change 3 ≤ 4; decide) (by rw [nextIn]; intro _; decide) budget
  have accepted : used = 300 := by rw [usedAll, count]; rfl
  have initialEnd : fillEnd sf = 0 := by simp [fillEnd, start.start, start.lookahead]
  rw [initialEnd, accepted] at endpoint
  have credit : pendingCredit result ≤ 1 := by unfold pendingCredit; split <;> omega
  have positive : 0 < represented ys := by
    have accounted := content.accounted
    dsimp only [fillEnd] at endpoint
    omega
  have nonempty : ys ≠ [] := by
    intro emptySymbols
    rw [emptySymbols] at positive
    change 0 < 0 at positive
    omega
  exact ⟨initialized, zi, sf, used, after, zf, result, ys, extended, nextOrigin,
    initRun, count, start, run, content, buffersA, account, accepted, nonempty, written⟩

/-- The original public-call witness retains its exact statement. -/
theorem default_public_first_witness :
    ∃ initialized zi sf used after zf result ys extended nextOrigin,
      C.run (deflateInit_ (some (.tab 0)) Z_DEFAULT_COMPRESSION (.ref (.blk 1) 0) 112)
        publicWitnessHeap = .ok (Z_OK, initialized) ∧ zi.avail_in = 300 ∧
      EngineStart initialized (.tab 0) 2 zi sf ∧
      deflate (some (.tab 0)) Z_NO_FLUSH initialized = .ok (Z_OK, after) ∧
      ContentBoundary after (.tab 0) 2 zf result extended nextOrigin 0 ys ∧
      StreamBuffers after (.tab 0) ∧ StreamAccounting zi zf used 2 ∧ used = 300 ∧ ys ≠ [] := by
  obtain ⟨initialized, zi, sf, used, after, zf, result, ys, extended, nextOrigin, initRun, count,
    start, run, content, buffers, account, accepted, nonempty, _written⟩ := default_public_first_witness_header
  exact ⟨initialized, zi, sf, used, after, zf, result, ys, extended, nextOrigin,
    initRun, count, start, run, content, buffers, account, accepted, nonempty⟩

end Zlib.Deflate.Engine.Proofs
