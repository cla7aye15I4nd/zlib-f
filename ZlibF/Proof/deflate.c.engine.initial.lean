import ZlibF.Proof.«public-deflate-init»
import ZlibF.Proof.«deflate.c.engine.macros»
import ZlibF.Proof.«deflate.c.engine.chains»
import ZlibF.Spec.Public.History

/-! # Default initialization reaches the actual engine boundary

Connect the existing mathematical hash-chain invariant to the arrays
written by initialization. The arbitrary fresh prev array stays arbitrary.
These are initial-entry facts, not preservation across every public call.
-/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open Zlib.Deflate.Proofs.DefaultInit ZlibF.Spec.Public
open ZlibF.Spec
open ZlibF.Spec.Public.Proofs.DeflateInit
set_option autoImplicit false

/-- The chain invariant refers to the actual window and word arrays. -/
def HeapChains (h : Heap) (d : DeflateState) (top : Nat) : Prop :=
  ∃ w p q wa pa qa,
    d.window = .ref (.blk w) 0 ∧ d.prev = .ref (.blk p) 0 ∧ d.head = .ref (.blk q) 0 ∧
    h.bytes w = some wa ∧ h.words p = some pa ∧ h.words q = some qa ∧
    HashChains (wfn qa) (wfn pa) (bfn wa) d.hash_size d.hash_shift d.hash_mask
      d.w_size.toNat top (d.strstart.toNat + d.lookahead.toNat)

theorem hash_parameters {h : Heap} {ds : Nat} {d : DeflateState} (inv : DStInv h ds d) :
    HashParams d.hash_size d.hash_shift d.hash_mask := by
  refine ⟨⟨d.hash_bits.toNat, inv.hbits_lo, inv.hbits_hi, inv.hsize, ?_, ?_⟩, ?_⟩
  · rw [inv.hmask, inv.hsize]
  · rw [inv.hshift]; omega
  · have bits := inv.hbits_hi
    rw [inv.hshift]; omega

/-- The memory premises for insertion follow from the same actual arrays
as DGood and H. They are not an assumed INSERT_STRING contract. -/
theorem heap_chains_environment {h : Heap} {r : ZStreamRef} {ds top : Nat}
    {z : ZStream} {d : DeflateState} (good : DGood h r ds z d) (chains : HeapChains h d top) :
    ∃ w p q wa pa qa, HashEnv h d w q p wa qa pa ∧
      HashChains (wfn qa) (wfn pa) (bfn wa) d.hash_size d.hash_shift d.hash_mask
        d.w_size.toNat top (d.strstart.toNat + d.lookahead.toNat) := by
  obtain ⟨w, p, q, wa, pa, qa, win, prev, head, hw, hp, hq, H⟩ := chains
  obtain ⟨w0, p0, q0, b, blocks⟩ := good.inv.blocks
  have we : w0 = w := by
    simpa only [win, Ptr.ref.injEq, BRef.blk.injEq, and_true] using blocks.win.symm
  have pe : p0 = p := by
    simpa only [prev, Ptr.ref.injEq, WRef.blk.injEq, and_true] using blocks.prev.symm
  have qe : q0 = q := by
    simpa only [head, Ptr.ref.injEq, WRef.blk.injEq, and_true] using blocks.head.symm
  subst w0 p0 q0
  have hsize : d.hash_size.toNat ≤ qa.size := by
    obtain ⟨qa0, get, size⟩ := blocks.qa
    have eq : qa0 = qa := Option.some.inj (get.symm.trans hq)
    subst qa0
    omega
  have psize : d.w_size.toNat ≤ pa.size := by
    obtain ⟨pa0, get, size⟩ := blocks.pa
    have eq : pa0 = pa := Option.some.inj (get.symm.trans hp)
    subst pa0
    omega
  have mask : d.w_mask.toNat < d.w_size.toNat := by
    have pos : 0 < d.w_size.toNat := by rw [good.inv.wsize]; exact Nat.two_pow_pos _
    rw [good.inv.wmask]
    omega
  exact ⟨w, p, q, wa, pa, qa, ⟨win, hw, blocks.wro, head, hq, prev, hp,
    blocks.pq.symm, hsize, psize, mask, hash_parameters good.inv⟩, H⟩

theorem window_extent {h : Heap} {r : ZStreamRef} {ds w : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8}
    (good : DGood h r ds z d) (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa) :
    wa.size = d.window_size.toNat ∧ d.window_size.toNat ≤ 65536 := by
  obtain ⟨w0, p, q, b, blocks⟩ := good.inv.blocks
  have wid : w0 = w := by simpa only [win, Ptr.ref.injEq, BRef.blk.injEq, and_true] using blocks.win.symm
  subst w0
  obtain ⟨wa0, get0, size⟩ := blocks.wa
  have array : wa0 = wa := Option.some.inj (get0.symm.trans get)
  subst wa0
  have ws : d.w_size.toNat ≤ 32768 := by
    rw [good.inv.wsize]
    calc 2 ^ d.w_bits.toNat ≤ 2 ^ 15 := Nat.pow_le_pow_right (by decide) good.inv.wbits_hi
         _ = 32768 := by decide
  rw [good.inv.wsz]
  exact ⟨size, by omega⟩

theorem window_writable {h : Heap} {r : ZStreamRef} {ds w : Nat}
    {z : ZStream} {d : DeflateState} (good : DGood h r ds z d)
    (win : d.window = .ref (.blk w) 0) : h.ro w = false := by
  obtain ⟨w0, p, q, b, blocks⟩ := good.inv.blocks
  have same : w0 = w := by
    simpa only [win, Ptr.ref.injEq, BRef.blk.injEq, and_true] using blocks.win.symm
  subst w0
  exact blocks.wro

/-- Appending input or padding beyond valid data preserves the hash keys
of all previously represented strings. -/
theorem heap_chains_window_write {h : Heap} {d : DeflateState} {top w : Nat}
    {wa wa' : Array UInt8} (chains : HeapChains h d top)
    (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa)
    (keepBytes : ∀ i, i < d.strstart.toNat + d.lookahead.toNat → bfn wa' i = bfn wa i) :
    HeapChains { h with bytes := upd h.bytes w (some wa') } d top := by
  obtain ⟨w0, p, q, a, pa, qa, win0, prev, head, get0, hp, hq, H⟩ := chains
  have id : w0 = w := by
    simpa only [win, Ptr.ref.injEq, BRef.blk.injEq, and_true] using win0.symm
  subst w0
  have eq : a = wa := Option.some.inj (get0.symm.trans get)
  subst a
  exact ⟨w, p, q, wa', pa, qa, win, prev, head, by simp, hp, hq,
    chains_congr H (fun _ => rfl) (fun _ => rfl) keepBytes⟩

/-- Empty heads establish H for arbitrary predecessor and window contents. -/
theorem chains_empty {head prev : Nat → UInt16} {w : Nat → UInt8}
    {n hsh hm : UInt32} {ws top lim : Nat}
    (heads : ∀ k, k < n.toNat → head k = 0) :
    HashChains head prev w n hsh hm ws top lim := by
  have zero : ∀ k p, k < n.toNat → Reach head prev ws top k p → p = 0 := by
    intro k p hk hr
    induction hr with
    | head => simp [heads k hk]
    | step _ hp _ ih => exact False.elim (hp ih)
  exact ⟨fun k p hk hr hp _ => False.elim (hp (zero k p hk hr))⟩

theorem clear_head_zero (qa : Array UInt16) (n : Nat) (hn : 0 < n) (hs : n ≤ qa.size)
    (j : Nat) (hj : j < n) : (clearHead qa n)[j]? = some 0 := by
  unfold clearHead
  rw [getElem?_fillRange _ 0 (n - 1) 0 j (by simp; omega)]
  by_cases hp : j < n - 1
  · simp [hp]
  · have hx : j = n - 1 := by omega
    subst j
    simp [Array.set!_eq_setIfInBounds, show n - 1 < qa.size by omega]

/-- The actual initialized heap establishes H. No fact about the values
of the uninitialized prev entries is needed. -/
theorem initialized_chains {h : Heap} {r : ZStreamRef} {z : ZStream} {level : Int32}
    {a1 a2 a3 : Array CtData} {qa : Array UInt16}
    (good : DGood (successHeap h r z level a1 a2 a3 qa) r h.nextBlk
      (resultStream h r z level) (resultState h r level a1 a2 a3)) :
    HeapChains (successHeap h r z level a1 a2 a3 qa) (resultState h r level a1 a2 a3) 0 := by
  obtain ⟨w, p, q, b, blocks⟩ := good.inv.blocks
  obtain ⟨wa, hw, _⟩ := blocks.wa
  obtain ⟨pa, hp, _⟩ := blocks.pa
  obtain ⟨heads, hq, size⟩ := blocks.qa
  have qid : q = h.nextBlk + 3 := by
    simpa only [resultState, finalState, lmD, resetState, rkPost, rkPost3, rkMid,
      Zlib.Trees.Proofs.Out.ibRec, Zlib.Trees.Proofs.Out.trInitRec,
      readyState, allocatedState, Ptr.ref.injEq, WRef.blk.injEq, and_true] using blocks.head.symm
  have eq : heads = clearHead qa 32768 := by
    rw [qid] at hq
    simpa [successHeap, readyHeap, successfulBuffers, publishedHeap, stateHeap, setW,
      Nat.add_assoc] using hq.symm
  have qs : 32768 ≤ qa.size := by
    rw [eq, size_clearHead] at size
    change qa.size = 32768 at size
    omega
  refine ⟨w, p, q, wa, pa, heads, blocks.win, blocks.prev, blocks.head, hw, hp, hq, ?_⟩
  apply chains_empty
  intro k hk
  change k < 32768 at hk
  rw [eq]
  have zero := clear_head_zero qa 32768 (by decide) qs k hk
  simp only [wfn, Array.getD_eq_getD_getElem?, zero, Option.getD_some]

/-- Source-established facts for the first engine entry. Later calls need
preservation, and may have nonempty chains and nonzero counters. -/
structure EngineStart (h : Heap) (r : ZStreamRef) (ds : Nat) (z : ZStream) (d : DeflateState) : Prop where
  good : DGood h r ds z d
  chains : HeapChains h d 0
  status : d.status = INIT_STATE
  wrap : d.wrap = 1
  strategy : d.strategy = 0
  windowBits : d.w_bits = 15
  hashBits : d.hash_bits = 15
  adler : z.adler = 1
  start : d.strstart = 0
  lookahead : d.lookahead = 0
  blockStart : d.block_start = 0
  insert : d.insert = 0
  highWater : d.high_water = 0
  pending : d.pending = 0
  pendingOut : d.pending_out = d.pending_buf
  symbols : d.sym_next = 0
  bits : d.bi_valid = 0
  lastFlush : d.last_flush = -2
  previousLength : d.prev_length = 2
  matchLength : d.match_length = 2
  matchAvailable : d.match_available = 0

theorem initialized_engine {h : Heap} {r : ZStreamRef} {z : ZStream} {level : Int32}
    {a1 a2 a3 : Array CtData} {qa : Array UInt16}
    (good : DGood (successHeap h r z level a1 a2 a3 qa) r h.nextBlk
      (resultStream h r z level) (resultState h r level a1 a2 a3)) :
    EngineStart (successHeap h r z level a1 a2 a3 qa) r h.nextBlk
      (resultStream h r z level) (resultState h r level a1 a2 a3) := by
  exact ⟨good, initialized_chains good, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A successful default initialization is an actual reachable state.
The universal Init2 theorem is not required by the history constructor. -/
theorem default_initialization_reachable {h : Heap} {r : ZStreamRef} {z : ZStream}
    {version : BPtr} {level : Int32} {p : Api.DeflParams}
    (hf : Fresh h) (hu : Uniq h) (hg : LibraryGlobals h) (hz : r.get h = some z)
    (ha : DefaultOrNull z) (hv : VersionValue h version (some 49))
    (params : Api.deflInit? level.toInt 8 15 8 0 = some p)
    (alloc : ∀ j, j < 5 → h.allocOk (h.nalloc + j) = true) :
    ∃ after, C.run (deflateInit_ (some r) level version 112) h = .ok (Z_OK, after) ∧
      DeflateInitial h after r p ∧ StreamReachable .deflate after r := by
  obtain ⟨rc, after, hr, post⟩ := (deflateInit_proof level).2.2 h r z version hf hu hg hz ha hv
  change (match Api.deflInit? level.toInt 8 15 8 0 with
    | none => _
    | some _ => _) at post
  rw [params] at post
  have first : h.allocOk h.nalloc = true := by simpa using alloc 0 (by decide)
  have all : (List.range 5).all (fun j => h.allocOk (h.nalloc + j)) = true := by
    simpa only [List.all_eq_true, List.mem_range] using alloc
  simp only [first, Bool.true_eq_false, if_false, all, if_true] at post
  rw [post.2.1] at hr
  refine ⟨after, hr, post.2.2, ?_⟩
  exact StreamReachable.deflateInit hf hu hg hz ha hv hr

/-- Actual default initialization supplies the first engine boundary on a
reachable heap. Only caller storage, legal parameters and allocator
success are premises; neither DGood nor H is supplied by the caller. -/
theorem default_initialization_engine_bindings {h : Heap} {r : ZStreamRef} {z : ZStream}
    {version : BPtr} {level : Int32} {p : Api.DeflParams}
    (hf : Fresh h) (hu : Uniq h) (hg : LibraryGlobals h) (hz : r.get h = some z)
    (ha : DefaultOrNull z) (hv : VersionValue h version (some 49))
    (params : Api.deflInit? level.toInt 8 15 8 0 = some p)
    (alloc : ∀ j, j < 5 → h.allocOk (h.nalloc + j) = true) :
    ∃ after zf sf, C.run (deflateInit_ (some r) level version 112) h = .ok (Z_OK, after) ∧
      EngineStart after r h.nextBlk zf sf ∧ DeflateInitial h after r p ∧
      StreamReachable .deflate after r ∧
      zf.next_in = z.next_in ∧ zf.avail_in = z.avail_in ∧
      zf.next_out = z.next_out ∧ zf.avail_out = z.avail_out := by
  obtain ⟨after, hr, hi, reachable⟩ := default_initialization_reachable hf hu hg hz ha hv params alloc
  let zp := preparedStream z
  let hp := r.put h zp
  let lev := levelValue level
  have shape := shape_put hz zp
  have hfP : Fresh hp := shape.fresh (by simp [hp]) hf
  have huP : Uniq hp := shape.uniq hu
  have hzP : r.get hp = some zp := ZStreamRef.get_put_same hz _
  have haP : DefAlloc zp := prepared_allocators ha
  have bad : ¬ (levelValue level < 0 || levelValue level > 9) = true := by
    intro hb
    have parsed := parameters_equiv level
    rw [params] at parsed
    simp only [if_pos hb] at parsed
    cases parsed
  have bounds : 0 ≤ lev.toInt ∧ lev.toInt ≤ 9 := by
    have bn := bad
    simp only [Bool.or_eq_true, decide_eq_true_eq, Int32.lt_iff_toInt_lt] at bn
    change ¬ (lev.toInt < 0 ∨ 9 < lev.toInt) at bn
    omega
  obtain ⟨a1, a2, a3, qa, run, good, _⟩ := allocate_success hfP huP hzP haP
    (by simpa [hp] using globals_trees hg) (by simpa [hp] using alloc) lev bounds.1 bounds.2
  have actual : C.run (deflateInit_ (some r) level version 112) h =
      .ok (Z_OK, successHeap hp r zp lev a1 a2 a3 qa) := by
    rw [C.run, entry_run hz hv level, if_neg bad]
    exact run
  rw [actual] at hr
  cases hr
  refine ⟨_, resultStream hp r zp lev, resultState hp r lev a1 a2 a3, actual, ?_, hi, reachable, rfl, rfl, rfl, rfl⟩
  have engine := initialized_engine good
  simpa only [hp, ZStreamRef.put_nextBlk] using engine

/-- The earlier initialized engine theorem retains its exact statement. -/
theorem default_initialization_engine {h : Heap} {r : ZStreamRef} {z : ZStream}
    {version : BPtr} {level : Int32} {p : Api.DeflParams}
    (hf : Fresh h) (hu : Uniq h) (hg : LibraryGlobals h) (hz : r.get h = some z)
    (ha : DefaultOrNull z) (hv : VersionValue h version (some 49))
    (params : Api.deflInit? level.toInt 8 15 8 0 = some p)
    (alloc : ∀ j, j < 5 → h.allocOk (h.nalloc + j) = true) :
    ∃ after zf sf, C.run (deflateInit_ (some r) level version 112) h = .ok (Z_OK, after) ∧
      EngineStart after r h.nextBlk zf sf ∧ DeflateInitial h after r p ∧
      StreamReachable .deflate after r := by
  obtain ⟨after, zf, sf, run, start, initial, reachable, _, _, _, _⟩ :=
    default_initialization_engine_bindings hf hu hg hz ha hv params alloc
  exact ⟨after, zf, sf, run, start, initial, reachable⟩

theorem EngineStart.window_range {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (start : EngineStart h r ds z d) :
    d.strstart.toNat + d.lookahead.toNat ≤ d.window_size.toNat := by
  simp [start.start, start.lookahead]

end Zlib.Deflate.Engine.Proofs
