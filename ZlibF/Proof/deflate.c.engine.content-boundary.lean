import ZlibF.Proof.«deflate.c.engine.symbol-content»

/-! # Initialization, refill and the real slow body preserve symbol content -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Successful default entry establishes the empty content trace on its
actual allocated heap. No universal Init2 contract is assumed. -/
theorem default_initialization_content_boundary {h : Heap} {r : ZStreamRef} {z : ZStream}
    {version : BPtr} {level : Int32} {p : ZlibF.Spec.Api.DeflParams}
    (hf : Fresh h) (hu : Uniq h) (hg : LibraryGlobals h) (hz : r.get h = some z)
    (ha : DefaultOrNull z) (hv : VersionValue h version (some 49))
    (params : ZlibF.Spec.Api.deflInit? level.toInt 8 15 8 0 = some p)
    (alloc : ∀ j, j < 5 → h.allocOk (h.nalloc + j) = true) (input : Nat → UInt8) :
    ∃ after zf sf,
      C.run (deflateInit_ (some r) level version 112) h = .ok (Z_OK, after) ∧
      EngineStart after r h.nextBlk zf sf ∧ ContentBoundary after r h.nextBlk zf sf input 0 0 [] ∧
      DeflateInitial h after r p ∧ StreamReachable .deflate after r := by
  obtain ⟨after, zf, sf, run, start, boundary, initial, reachable⟩ :=
    default_initialization_pending_boundary hf hu hg hz ha hv params alloc input
  refine ⟨after, zf, sf, run, start, ⟨boundary, .empty, ?_⟩, initial, reachable⟩
  simp [pendingCredit, represented, start.start, start.matchAvailable]

/-- Caller edits preserve the private symbols and their logical meaning. -/
theorem rebuffer_content_boundary {h g : Heap} {r : ZStreamRef} {ds origin base : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {xs : List Symbol}
    (boundary : ContentBoundary h r ds z d input origin base xs)
    (edit : Rebuffer h g r) (header : d.gzhead = none) :
    ∃ z', r.get g = some z' ∧ ContentBoundary g r ds z' d input origin base xs := by
  obtain ⟨z', getZ, next⟩ := rebuffer_pending_boundary boundary.toPendingBoundary edit header
  exact ⟨z', getZ, next, boundary.trace, boundary.accounted⟩

/-- Default initialization and every legal caller buffer replacement
establish the content boundary on actual reachable states. -/
theorem default_content_rebuffered {h : Heap} {r : ZStreamRef} {z : ZStream}
    {version : BPtr} {level : Int32} {p : ZlibF.Spec.Api.DeflParams}
    (hf : Fresh h) (hu : Uniq h) (hg : LibraryGlobals h) (hz : r.get h = some z)
    (ha : DefaultOrNull z) (hv : VersionValue h version (some 49))
    (params : ZlibF.Spec.Api.deflInit? level.toInt 8 15 8 0 = some p)
    (alloc : ∀ j, j < 5 → h.allocOk (h.nalloc + j) = true) (input : Nat → UInt8) :
    ∃ after zf sf, C.run (deflateInit_ (some r) level version 112) h = .ok (Z_OK, after) ∧
      ContentBoundary after r h.nextBlk zf sf input 0 0 [] ∧ StreamReachable .deflate after r ∧
      ∀ g, Rebuffer after g r → ∃ zg,
        ContentBoundary g r h.nextBlk zg sf input 0 0 [] ∧ StreamReachable .deflate g r := by
  obtain ⟨after, zf, sf, run, start, boundary, initial, reachable⟩ :=
    default_initialization_content_boundary hf hu hg hz ha hv params alloc input
  refine ⟨after, zf, sf, run, boundary, reachable, ?_⟩
  intro g edit
  obtain ⟨zg, _, boundaryG⟩ := rebuffer_content_boundary boundary edit (initial_no_header start initial)
  exact ⟨zg, boundaryG, StreamReachable.rebuffer reachable edit⟩

/-- The actual fill extends input only beyond the previously accepted
prefix. The stored symbols and their cumulative positions retain their
meaning through sliding, pending insertions and every padding branch. -/
theorem fill_window_content_boundary {h : Heap} {r : ZStreamRef} {ds origin base : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {xs : List Symbol}
    (boundary : ContentBoundary h r ds z d input origin base xs)
    (short : d.lookahead.toNat < 262) (wrap : d.wrap = 1) (buffers : StreamBuffers h r)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null) :
    ∃ used after z' result extended nextOrigin,
      fill_window (some (.tab ds)) h = .ok ((), after) ∧
      ContentBoundary after r ds z' result extended nextOrigin base xs ∧ StreamAccounting z z' used 0 ∧
      nextOrigin + result.strstart.toNat = origin + d.strstart.toNat ∧
      result.lookahead.toNat = d.lookahead.toNat + used ∧ result.wrap = 1 ∧
      (nextOrigin = origin ∨ nextOrigin = origin + d.w_size.toNat) ∧
      (∀ i, i < origin + fillEnd d → extended i = input i) ∧
      (262 ≤ result.lookahead.toNat ∨ z'.avail_in = 0) ∧ FillRecordFrame d result := by
  obtain ⟨used, after, z', result, extended, nextOrigin, run, pending, account,
      start, look, wrapA, originA, agrees, stopped, frame⟩ :=
    fill_window_pending_boundary_all_frame boundary.toPendingBoundary short wrap buffers inputValid
  have accounted := boundary.accounted
  have credit : pendingCredit result = pendingCredit d := by
    have available : result.match_available = d.match_available := congrArg (·.match_available) frame
    unfold pendingCredit
    rw [available]
  have traceA : Trace extended base xs := boundary.trace.extend (by dsimp only [fillEnd]; omega) agrees
  exact ⟨used, after, z', result, extended, nextOrigin, run, ⟨pending, traceA, by omega⟩,
    account, start, look, wrapA, originA, agrees, stopped, frame⟩

/-- All three real decisions preserve the decoded meaning of the exact
stored symbols as well as the actual heap boundary. Search and tally
are executed; their specifications are not caller assumptions. -/
theorem slow_body_content_boundary {h : Heap} {r : ZStreamRef} {ds origin base : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {xs : List Symbol}
    (boundary : ContentBoundary h r ds z d input origin base xs)
    (lookahead : 262 ≤ d.lookahead.toNat) (space : d.sym_next.toNat + 3 < d.sym_end.toNat)
    (flush : Int32) (st : LoopS) :
    ∃ next after result ys,
      deflate_slow_body (some (.tab ds)) flush st h = .ok (next, after) ∧
      ContentBoundary after r ds z result input origin base ys ∧
      SlowRecordFrame d result ∧ d.strstart.toNat < result.strstart.toNat ∧
      result.lookahead.toNat < d.lookahead.toNat ∧ fillEnd result = fillEnd d ∧
      (ys = xs ∨ ∃ symbol, ys = xs ++ [symbol]) ∧
      result.sym_next.toNat < result.sym_end.toNat ∧ next.brk = st.brk ∧
      (next.ret = st.ret ∨ next.ret = some need_more) := by
  obtain ⟨w, p, q, wa, pa, qa, env, chains⟩ := heap_chains_environment boundary.good boundary.chains
  obtain ⟨w0, wa0, win, get, view, form⟩ := boundary.data
  have sameWindow : w0 = w := by
    simpa only [env.win, Ptr.ref.injEq, BRef.blk.injEq, and_true] using win.symm
  subst w0
  have sameArray : wa0 = wa := Option.some.inj (get.symm.trans env.wbytes)
  subst wa0
  obtain ⟨next, after, result, ys, run, goodA, chainsA, winA, bytesA, rangeA, endpoint,
      advance, less, formA, historyA, deferredA, countA, brkA, retA, symbolsA, step, frameA, values⟩ :=
    slow_body_with_symbol_values boundary.good boundary.symbols env chains (Nat.le_refl _)
      boundary.range lookahead boundary.history boundary.deferred view (form (by omega)) space flush st
  change fillEnd result = fillEnd d at endpoint
  have core : SlowBoundary after r ds z result input origin ys :=
    ⟨goodA, chainsA, rangeA, historyA, deferredA, symbolsA, w, wa, winA, bytesA,
      (fun i bound => view i (by rw [← endpoint]; exact bound)), fun _ => formA⟩
  have insert : result.insert = 0 :=
    (congrArg (·.insert) frameA).trans (boundary.ready (by omega))
  have pending : PendingBoundary after r ds z result input origin ys :=
    ⟨core, by simp [insert], by simpa only [insert, show (0 : UInt32).toNat = 0 from rfl, Nat.sub_zero] using chainsA,
      fun _ => insert⟩
  obtain ⟨_, _, _, _, balance⟩ := boundary.symbols
  obtain ⟨_, _, _, _, balanceA⟩ := symbolsA
  refine ⟨next, after, result, ys, run,
    ⟨pending, slow_value_trace boundary view values,
      content_accounted_body balance balanceA frameA boundary.accounted⟩,
    frameA, advance, less, endpoint, ?_, countA, brkA, retA⟩
  rcases step with same | literal | matched
  · exact Or.inl same
  · exact Or.inr ⟨_, literal⟩
  · exact Or.inr ⟨_, matched⟩

/-- The buffered symbols expand under the format's copyBack to the real
input prefix, ending immediately before any deferred byte. -/
theorem ContentBoundary.expands {h : Heap} {r : ZStreamRef} {ds origin base : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {xs : List Symbol}
    (boundary : ContentBoundary h r ds z d input origin base xs) :
    expandSymbols xs (inputPrefix input base) =
      inputPrefix input (origin + d.strstart.toNat - pendingCredit d) := by
  have position := boundary.accounted
  have endpoint : base + represented xs = origin + d.strstart.toNat - pendingCredit d := by omega
  rw [← endpoint]
  exact boundary.trace.expands

open ZlibF.Spec.Public.Proofs.DeflateInit in
/-- An actual default entry inhabits the content boundary. -/
theorem default_content_boundary_witness :
    ∃ after zf sf,
      C.run (deflateInit_ (some (.tab 0)) Z_DEFAULT_COMPRESSION (.ref (.blk 1) 0) 112)
        witnessHeap = .ok (Z_OK, after) ∧
      ContentBoundary after (.tab 0) 2 zf sf (fun _ => 0) 0 0 [] := by
  obtain ⟨after, zf, sf, run, _, boundary, _, _⟩ :=
    default_initialization_content_boundary (h := witnessHeap) (r := .tab 0) (z := default)
      (version := .ref (.blk 1) 0) (level := Z_DEFAULT_COMPRESSION) (p := settings 6)
      witness_fresh witness_uniq rfl (by simp [ZStreamRef.get, witnessHeap])
      ⟨Or.inl rfl, Or.inl rfl⟩ witness_version (by decide +kernel) (by intro _ _; rfl) (fun _ => 0)
  exact ⟨after, zf, sf, run, boundary⟩

end Zlib.Deflate.Engine.Proofs
