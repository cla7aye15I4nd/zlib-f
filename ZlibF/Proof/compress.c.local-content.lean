import ZlibF.Proof.«compress.c.local-body-history»
import ZlibF.Proof.«compress.c.local-first-input-history»
import ZlibF.Proof.«deflate.c.engine.content-boundary»

/-! # Internal content trace built and preserved by actual local execution -/
namespace ZlibF.Spec.Public.Proofs.CompressLocalContent
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open Zlib.Deflate.Engine.Proofs ZlibF.Spec.Public
open ZlibF.Spec.Public.Proofs.CompressLocalInit ZlibF.Spec.Public.Proofs.CompressLocalHash
open ZlibF.Spec.Public.Proofs.CompressLocalBodyHistory ZlibF.Spec.Public.Proofs.CompressLocalFirstInputHistory
open ZlibF.Spec.Public.Proofs.CompressLocalFill ZlibF.Spec.Public.Proofs.CompressLocalData ZlibF.Spec.Public.Proofs.CompressLocalLiteralLoop
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

/-- An internal execution invariant. The actual first-refill constructor
below establishes it, and the actual complete body preserves it. This
neither changes the old ContentBoundary nor adds a public caller premise. -/
structure LocalContent (h : Heap) (cutoff : Nat) (r : ZStreamRef) (ds : Nat) (z : ZStream) (d : DeflateState)
    (input : Nat → UInt8) (origin base : Nat) (xs : List Symbol) : Prop where
  state : LocalState h cutoff r ds z d
  chains : HeapChains h d d.strstart.toNat
  range : fillEnd d ≤ d.window_size.toNat
  history : LazyHistory input origin d
  deferred : DeferredByte d
  symbols : SymbolBoundary h ds d xs
  data : ∃ w wa, d.window = .ref (.blk w) 0 ∧ h.bytes w = some wa ∧
    (∀ i, i < fillEnd d → bfn wa i = input (origin+i)) ∧
    (3 ≤ d.lookahead.toNat → InsHForm d.hash_shift d.hash_mask (bfn wa) d.strstart.toNat d.ins_h)
  insert_le : d.insert.toNat ≤ d.strstart.toNat
  frontier : HeapChains h d (d.strstart.toNat-d.insert.toNat)
  ready : 3 ≤ d.lookahead.toNat → d.insert = 0
  trace : Trace input base xs
  accounted : base + represented xs + pendingCredit d = origin + d.strstart.toNat

theorem local_value_trace {h : Heap} {r : ZStreamRef} {cutoff ds origin base : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {wa : Array UInt8} {xs ys : List Symbol}
    (boundary : LocalContent h cutoff r ds z d input origin base xs)
    (view : ∀ i, i < fillEnd d → bfn wa i = input (origin + i))
    (values : SlowSymbolValueStep d wa xs ys) : Trace input base ys := by
  have accounted := boundary.accounted
  rcases values with same | ⟨available, literal⟩ | ⟨large, matched⟩
  · rw [same]
    exact boundary.trace
  · have credit : pendingCredit d = 1 := by simp [pendingCredit, available]
    have position : base + represented xs = origin + d.strstart.toNat - 1 := by omega
    rw [literal]
    apply Trace.snoc boundary.trace
    rw [position]
    exact literal_input_meaning boundary.deferred available view
  · have available : d.match_available ≠ 0 := (boundary.history.2 large).2.1
    have credit : pendingCredit d = 1 := by simp [pendingCredit, available]
    have position : base + represented xs = origin + d.strstart.toNat - 1 := by omega
    have window : d.w_size.toNat ≤ 32768 := by
      rw [boundary.state.inv.wsize]
      exact Nat.pow_le_pow_right (by decide) boundary.state.inv.wbits_hi
    rw [matched]
    apply Trace.snoc boundary.trace
    rw [position]
    exact retained_match_input_meaning boundary.history window large

theorem local_content_body {h : Heap} {r : ZStreamRef} {cutoff ds origin base : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {xs : List Symbol}
    (boundary : LocalContent h cutoff r ds z d input origin base xs)
    (lookahead : 262 ≤ d.lookahead.toNat) (space : d.sym_next.toNat + 3 < d.sym_end.toNat)
    (flush : Int32) (st : LoopS) :
    ∃ next after result ys,
      deflate_slow_body (some (.tab ds)) flush st h = .ok (next, after) ∧
      LocalContent after cutoff r ds z result input origin base ys ∧
      SlowRecordFrame d result ∧ d.strstart.toNat < result.strstart.toNat ∧
      result.lookahead.toNat < d.lookahead.toNat ∧ fillEnd result = fillEnd d ∧
      (ys = xs ∨ ∃ symbol, ys = xs ++ [symbol]) ∧
      result.sym_next.toNat < result.sym_end.toNat ∧ next.brk = st.brk ∧
      (next.ret = st.ret ∨ next.ret = some need_more) := by
  obtain ⟨w, p, q, wa, pa, qa, env, chains⟩ := local_heap_chains_environment boundary.state boundary.chains
  obtain ⟨w0, wa0, win, get, view, form⟩ := boundary.data
  have sameWindow : w0 = w := by
    simpa only [env.win, Ptr.ref.injEq, BRef.blk.injEq, and_true] using win.symm
  subst w0
  have sameArray : wa0 = wa := Option.some.inj (get.symm.trans env.wbytes)
  subst wa0
  obtain ⟨next, after, result, ys, run, goodA, chainsA, winA, bytesA, rangeA, endpoint,
      advance, less, formA, historyA, deferredA, countA, brkA, retA, symbolsA, step, frameA, values,_storageA,_returned⟩ :=
    local_body_history_symbols boundary.state boundary.symbols env chains (Nat.le_refl _)
      boundary.range lookahead boundary.history boundary.deferred view (form (by omega)) space flush st
  change fillEnd result = fillEnd d at endpoint
  have insert : result.insert = 0 :=
    (congrArg (·.insert) frameA).trans (boundary.ready (by omega))
  obtain ⟨_, _, _, _, balance⟩ := boundary.symbols
  have symbolCopy := symbolsA
  obtain ⟨_, _, _, _, balanceA⟩ := symbolCopy
  refine ⟨next, after, result, ys, run,
    ⟨goodA,chainsA,rangeA,historyA,deferredA,symbolsA,
      ⟨w,wa,winA,bytesA,(fun i bound => view i (by rw [←endpoint];exact bound)),fun _ => formA⟩,
      (by rw [insert];simp),
      (by simpa only [insert,show (0 : UInt32).toNat = 0 from rfl,Nat.sub_zero] using chainsA),
      (fun _ => insert),local_value_trace boundary view values,
      content_accounted_body balance balanceA frameA boundary.accounted⟩,
    frameA, advance, less, endpoint, ?_, countA, brkA, retA⟩
  rcases step with same | literal | matched
  · exact Or.inl same
  · exact Or.inr ⟨_, literal⟩
  · exact Or.inr ⟨_, matched⟩

theorem LocalContent.expands {h : Heap} {r : ZStreamRef} {cutoff ds origin base : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {xs : List Symbol}
    (boundary : LocalContent h cutoff r ds z d input origin base xs) :
    expandSymbols xs (inputPrefix input base) =
      inputPrefix input (origin + d.strstart.toNat - pendingCredit d) := by
  have position := boundary.accounted
  have endpoint : base + represented xs = origin + d.strstart.toNat - pendingCredit d := by omega
  rw [← endpoint]
  exact boundary.trace.expands

/-- Actual first refill establishes the content invariant for every
nonempty offered uInt input length. It refers to the original source
bytes, preserves the empty stored-symbol trace, and needs no global Uniq. -/
theorem first_fill_local_content {h : Heap} {r : ZStreamRef} {cutoff ds w io : Nat}
    {z : ZStream} {d : DeflateState} {ref : BRef} {ia wa : Array UInt8}
    (state : LocalState h cutoff r ds z d) (fields : InitialReadFields d)
    (chains : HeapChains h d 0) (symbol : SymbolBoundary h ds d [])
    (length : d.match_length = 2) (available : d.match_available = 0)
    (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa)
    (writable : h.ro w = false) (size : wa.size = 65536)
    (pointer : z.next_in = .ref ref io) (input : Space.get h ref = some ia)
    (inputBound : io+z.avail_in.toNat ≤ ia.size) (nonzero : z.avail_in ≠ 0)
    (separate : BRef.blk w ≠ ref ∨ (rbLen z.avail_in 65536).toNat ≤ io ∨
      io+(rbLen z.avail_in 65536).toNat ≤ 0) :
    let n := rbLen z.avail_in 65536
    let next := readStream z n ref io (adlerValue z.adler ((ia.toList.drop io).take n.toNat))
    let result := firstFillState d n (copyRange wa ia 0 io n.toNat)
    let after := firstFillHeap h r ds w z d ref io ia wa
    fill_window (some (.tab ds)) h = .ok ((),after) ∧
      LocalContent after cutoff r ds next result (fun i => bfn ia (io+i)) 0 0 [] ∧
      StreamAccounting z next n.toNat 0 := by
  let n := rbLen z.avail_in 65536
  let copied := copyRange wa ia 0 io n.toNat
  let result := firstFillState d n copied
  let after := firstFillHeap h r ds w z d ref io ia wa
  let packed := fillRange copied n.toNat (firstPadding n).toNat 0
  have count := rbLen_nat z.avail_in 65536
  change n.toNat = min z.avail_in.toNat 65536 at count
  have bound : n.toNat ≤ 65536 := by omega
  obtain ⟨fill,stateF,account,_,_,lookF,startF,_statusF,_levelF,_strategyF,_lastF,getF⟩ :=
    local_fill_window_first state win get writable size fields.1 fields.2.1 fields.2.2.1 fields.2.2.2.1
      fields.2.2.2.2.1 fields.2.2.2.2.2.1 fields.2.2.2.2.2.2.1 pointer input inputBound nonzero separate
  have chainsF := first_fill_chains (r := r) (ds := ds) (z := z) (ref := ref) (io := io) (ia := ia) chains win get fields.1 fields.2.1
  have symbolsF := local_first_fill_symbols state symbol win stateF
  have keep : result.match_length = d.match_length ∧ result.match_available = d.match_available ∧
      result.hash_shift = d.hash_shift ∧ result.hash_mask = d.hash_mask ∧
      result.window_size = d.window_size ∧ result.window = d.window ∧ result.insert = 0 := by
    unfold result firstFillState primeState
    split <;> exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,fields.2.2.1⟩
  have start : result.strstart = 0 := startF
  have looked : result.lookahead = n := lookF
  have mainChains : HeapChains after result result.strstart.toNat := by
    rw [start]
    exact chainsF
  have rangeF : fillEnd result ≤ result.window_size.toNat := by
    change result.strstart.toNat+result.lookahead.toNat ≤ result.window_size.toNat
    rw [startF,lookF,keep.2.2.2.2.1,fields.2.2.2.2.2.1]
    simpa only [show (0 : UInt32).toNat = 0 from rfl,show (65536 : UInt64).toNat = 65536 from rfl,Nat.zero_add] using bound
  have history := logical_history_initial (keep.1.trans length) (fun i => bfn ia (io+i)) 0
  have deferred : DeferredByte result := by intro bad;exact False.elim (bad (keep.2.1.trans available))
  have view : ∀ i, i < fillEnd result → bfn packed i = (fun j => bfn ia (io+j)) (0+i) := by
    change ∀ i, i < result.strstart.toNat+result.lookahead.toNat → bfn packed i = bfn ia (io+(0+i))
    rw [startF,lookF]
    simpa only [show (0 : UInt32).toNat = 0 from rfl,Nat.zero_add] using
      (first_fill_prefix_view (ia := ia) (io := io) size bound)
  have form : 3 ≤ result.lookahead.toNat → InsHForm result.hash_shift result.hash_mask (bfn packed) result.strstart.toNat result.ins_h := by
    intro enough
    rw [startF,keep.2.2.1,keep.2.2.2.1]
    have enoughN : 3 ≤ n.toNat := by rw [looked] at enough;exact enough
    exact first_fill_form (hash_parameters state.inv) bound (by rw [size_copyRange];exact size)
      (by change (3 : UInt32) ≤ n;rw [UInt32.le_iff_toNat_le];exact enoughN)
  have content : LocalContent after cutoff r ds (readStream z n ref io (adlerValue z.adler ((ia.toList.drop io).take n.toNat))) result (fun i => bfn ia (io+i)) 0 0 [] := by
    refine ⟨stateF,mainChains,rangeF,history,deferred,symbolsF,⟨w,packed,keep.2.2.2.2.2.1.trans win,getF,view,form⟩,
      ?_,?_,(fun _ => keep.2.2.2.2.2.2),.empty,?_⟩
    · rw [keep.2.2.2.2.2.2]
      simp
    · rw [keep.2.2.2.2.2.2,show (0 : UInt32).toNat = 0 from rfl,Nat.sub_zero]
      exact mainChains
    · have availableZero : result.match_available = 0 := keep.2.1.trans available
      simp [pendingCredit,availableZero,start,represented]
  exact ⟨fill,content,account⟩

end ZlibF.Spec.Public.Proofs.CompressLocalContent
