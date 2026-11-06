import ZlibF.Zlib.«trees.c»

/-!
# trees.c: the invariant `TreesInv` and the calculus the proofs of `trees.c` use

* `Wp`, a weakest-precondition calculus for `M` (loops with a measure, `if`, `bind`).
* `setD`, the heap after replacing a deflate record; run lemmas for the helpers of `trees.c.lean`
  (`rd`, `md`, `getFc`, `setFc`, ...) in terms of it.
* `TreesInv h id`: the deflate state of block `id` is well formed for the code of `trees.c` (array sizes,
  descriptors, bit buffer, the byte block that holds `pending_buf` and `sym_buf`, the static tables).
  `TreesBase` is the part `deflateInit2_` establishes before `_tr_init` runs; `_tr_init_safe` extends it to
  `TreesInv`.
* The bit stream of the output (`outBits`): the bits of the pending bytes followed by the bits of `bi_buf`.
-/

namespace Zlib.Trees.Proofs.Out
open C Zlib.Trees

/-! ## A weakest-precondition calculus for `M` -/

/-- `m` runs on `h` without a fault and its result satisfies `Q`. -/
def Wp {α : Type} (m : M α) (h : Heap) (Q : α → Heap → Prop) : Prop :=
  ∃ a h', m h = .ok (a, h') ∧ Q a h'

theorem Wp.pure' {α : Type} {a : α} {h : Heap} {Q : α → Heap → Prop} (hq : Q a h) :
    Wp (Pure.pure a : M α) h Q := ⟨a, h, rfl, hq⟩

theorem Wp.bind' {α β : Type} {m : M α} {f : α → M β} {h : Heap} {Q : α → Heap → Prop} {R : β → Heap → Prop}
    (hm : Wp m h Q) (hf : ∀ a h', Q a h' → Wp (f a) h' R) : Wp (m >>= f) h R := by
  obtain ⟨a, h1, e, hq⟩ := hm
  obtain ⟨b, h2, e2, hr⟩ := hf a h1 hq
  exact ⟨b, h2, by rw [bind_app, e]; exact e2, hr⟩

theorem Wp.mono {α : Type} {m : M α} {h : Heap} {Q R : α → Heap → Prop} (hm : Wp m h Q)
    (hr : ∀ a h', Q a h' → R a h') : Wp m h R := by
  obtain ⟨a, h1, e, hq⟩ := hm
  exact ⟨a, h1, e, hr a h1 hq⟩

theorem Wp.ite {α : Type} {c : Prop} [Decidable c] {m1 m2 : M α} {h : Heap} {Q : α → Heap → Prop}
    (h1 : c → Wp m1 h Q) (h2 : ¬ c → Wp m2 h Q) : Wp (if c then m1 else m2) h Q := by
  by_cases hc : c
  · simp only [hc, ite_true]; exact h1 hc
  · simp only [hc, ite_false]; exact h2 hc

theorem Wp.of_eq {α : Type} {m : M α} {h h' : Heap} {a : α} (e : m h = .ok (a, h')) {Q : α → Heap → Prop}
    (hq : Q a h') : Wp m h Q := ⟨a, h', e, hq⟩

theorem Wp.bind_eq {α β : Type} {m : M α} {f : α → M β} {h h1 : Heap} {a : α} {R : β → Heap → Prop}
    (e : m h = .ok (a, h1)) (hf : Wp (f a) h1 R) : Wp (m >>= f) h R := by
  obtain ⟨b, h2, e2, hr⟩ := hf
  exact ⟨b, h2, by rw [bind_app, e]; exact e2, hr⟩

/-- Loop with a measure: `Inv` is kept, the measure decreases at each iteration, and `Q` holds when the
condition fails. -/
theorem Wp.cwhile {σ : Type} {cond : σ → M (Bool × σ)} {body : σ → M σ} (Inv : σ → Heap → Prop) (μ : σ → Nat)
    (Q : σ → Heap → Prop)
    (hstep : ∀ s h, Inv s h →
      (∃ s1 h1, cond s h = .ok ((false, s1), h1) ∧ Q s1 h1) ∨
      (∃ s1 h1 s2 h2, cond s h = .ok ((true, s1), h1) ∧ body s1 h1 = .ok (s2, h2) ∧ Inv s2 h2 ∧ μ s2 < μ s))
    {s : σ} {h : Heap} (hI : Inv s h) (hfuel : μ s < fuel) :
    Wp (cwhile cond body s) h Q := by
  have key : ∀ k n s h, Inv s h → μ s ≤ k → k < n → ∃ s' h', cwhile.go cond body n s h = .ok (s', h') ∧ Q s' h' := by
    intro k
    induction k using Nat.strongRecOn with
    | _ k ih =>
      intro n s h hI hμ hn
      obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      rcases hstep s h hI with ⟨s1, h1, hc, hq⟩ | ⟨s1, h1, s2, h2, hc, hb, hI2, hlt⟩
      · exact ⟨s1, h1, by simp [cwhile.go, hc], hq⟩
      · obtain ⟨s', h', hgo, hq⟩ := ih (μ s2) (by omega) n s2 h2 hI2 (Nat.le_refl _) (by omega)
        exact ⟨s', h', by simp [cwhile.go, hc, hb, hgo], hq⟩
  obtain ⟨s', h', e, hq⟩ := key (μ s) fuel s h hI (Nat.le_refl _) hfuel
  exact ⟨s', h', e, hq⟩

/-- `do ... while` with a measure: `Inv` holds before each body; the measure decreases. -/
theorem Wp.cdoWhile {σ : Type} {cond : σ → M (Bool × σ)} {body : σ → M σ} (Inv : σ → Heap → Prop) (μ : σ → Nat)
    (Q : σ → Heap → Prop)
    (hstep : ∀ s h, Inv s h → ∃ s1 h1, body s h = .ok (s1, h1) ∧
      ((∃ s2 h2, cond s1 h1 = .ok ((false, s2), h2) ∧ Q s2 h2) ∨
       (∃ s2 h2, cond s1 h1 = .ok ((true, s2), h2) ∧ Inv s2 h2 ∧ μ s2 < μ s)))
    {s : σ} {h : Heap} (hI : Inv s h) (hfuel : μ s < fuel) :
    Wp (cdoWhile body cond s) h Q := by
  have key : ∀ k n s h, Inv s h → μ s ≤ k → k < n → ∃ s' h', cdoWhile.go body cond n s h = .ok (s', h') ∧ Q s' h' := by
    intro k
    induction k using Nat.strongRecOn with
    | _ k ih =>
      intro n s h hI hμ hn
      obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      obtain ⟨s1, h1, hb, hc⟩ := hstep s h hI
      rcases hc with ⟨s2, h2, hc, hq⟩ | ⟨s2, h2, hc, hI2, hlt⟩
      · exact ⟨s2, h2, by simp [cdoWhile.go, hb, hc], hq⟩
      · obtain ⟨s', h', hgo, hq⟩ := ih (μ s2) (by omega) n s2 h2 hI2 (Nat.le_refl _) (by omega)
        exact ⟨s', h', by simp [cdoWhile.go, hb, hc, hgo], hq⟩
  obtain ⟨s', h', e, hq⟩ := key (μ s) fuel s h hI (Nat.le_refl _) hfuel
  exact ⟨s', h', e, hq⟩

/-! ## Machine integers -/

theorem i32_ofInt_toInt {v : Int} (h1 : -2147483648 ≤ v) (h2 : v ≤ 2147483647) : (Int32.ofInt v).toInt = v := by
  rw [Int32.toInt_ofInt]
  simp only [Int32.size, Int.bmod]
  omega

theorem ck_eq {x : Int} (h1 : -2147483648 ≤ x) (h2 : x ≤ 2147483647) : ck x = pure (Int32.ofInt x) := by
  funext h; simp [ck, h1, h2]

theorem iadd_eq {a b : Int32} (h1 : -2147483648 ≤ a.toInt + b.toInt) (h2 : a.toInt + b.toInt ≤ 2147483647) :
    iadd a b = pure (Int32.ofInt (a.toInt + b.toInt)) := ck_eq h1 h2

theorem isub_eq {a b : Int32} (h1 : -2147483648 ≤ a.toInt - b.toInt) (h2 : a.toInt - b.toInt ≤ 2147483647) :
    isub a b = pure (Int32.ofInt (a.toInt - b.toInt)) := ck_eq h1 h2

/-! ## The deflate record and its helpers -/

/-- The heap after replacing the deflate record `id`. -/
def setD (h : Heap) (id : Nat) (d : DeflateState) : Heap := { h with dstates := upd h.dstates id (some d) }

@[simp] theorem setD_dstates_same (h : Heap) (id : Nat) (d : DeflateState) : (setD h id d).dstates id = some d := by
  simp [setD]
theorem setD_dstates_ne (h : Heap) (id k : Nat) (d : DeflateState) (hne : k ≠ id) :
    (setD h id d).dstates k = h.dstates k := by simp [setD, hne]
@[simp] theorem setD_bytes (h : Heap) (id : Nat) (d : DeflateState) : (setD h id d).bytes = h.bytes := rfl
@[simp] theorem setD_words (h : Heap) (id : Nat) (d : DeflateState) : (setD h id d).words = h.words := rfl
@[simp] theorem setD_ro (h : Heap) (id : Nat) (d : DeflateState) : (setD h id d).ro = h.ro := rfl
@[simp] theorem setD_static (h : Heap) (id : Nat) (d : DeflateState) : (setD h id d).static = h.static := rfl
@[simp] theorem setD_streams (h : Heap) (id : Nat) (d : DeflateState) : (setD h id d).streams = h.streams := rfl
@[simp] theorem setD_setD (h : Heap) (id : Nat) (d d' : DeflateState) : setD (setD h id d) id d' = setD h id d' := by
  simp [setD, upd_upd]

/-- The heap after replacing the byte block `b`. -/
def setB (h : Heap) (b : Nat) (a : Array UInt8) : Heap := { h with bytes := upd h.bytes b (some a) }

@[simp] theorem setB_bytes_same (h : Heap) (b : Nat) (a : Array UInt8) : (setB h b a).bytes b = some a := by
  simp [setB]
theorem setB_bytes_ne (h : Heap) (b k : Nat) (a : Array UInt8) (hne : k ≠ b) : (setB h b a).bytes k = h.bytes k := by
  simp [setB, hne]
@[simp] theorem setB_dstates (h : Heap) (b : Nat) (a : Array UInt8) : (setB h b a).dstates = h.dstates := rfl
@[simp] theorem setB_ro (h : Heap) (b : Nat) (a : Array UInt8) : (setB h b a).ro = h.ro := rfl
@[simp] theorem setB_static (h : Heap) (b : Nat) (a : Array UInt8) : (setB h b a).static = h.static := rfl
@[simp] theorem setB_words (h : Heap) (b : Nat) (a : Array UInt8) : (setB h b a).words = h.words := rfl
@[simp] theorem setD_setB (h : Heap) (id b : Nat) (a : Array UInt8) (d : DeflateState) :
    setD (setB h b a) id d = setB (setD h id d) b a := rfl

theorem rd_run {h : Heap} {id : Nat} {d : DeflateState} (e : h.dstates id = some d) :
    rd (some (.tab id)) h = .ok (d, h) := ldDeflateState_tab e

theorem md_run {h : Heap} {id : Nat} {d : DeflateState} (e : h.dstates id = some d) (f : DeflateState → DeflateState) :
    md (some (.tab id)) f h = .ok ((), setD h id (f d)) := by
  simp [md, ldDeflateState_tab e, stDeflateState_tab e, setD]
  try rfl

theorem sid_run {h : Heap} {id : Nat} {d : DeflateState} (e : h.dstates id = some d) :
    sid (some (.tab id)) h = .ok (id, h) := by
  simp [sid, ldDeflateState_tab e]; try rfl

/-- The deflate record `id` of `h` (the default record if it is not live). -/
def rdD (h : Heap) (id : Nat) : DeflateState := (h.dstates id).getD default

theorem rd_run' {h : Heap} {id : Nat} (e : h.dstates id ≠ none) :
    rd (some (.tab id)) h = .ok (rdD h id, h) := by
  cases hd : h.dstates id with
  | none => exact absurd hd e
  | some d => simp [rdD, hd, rd_run hd]

theorem md_run' {h : Heap} {id : Nat} (e : h.dstates id ≠ none) (f : DeflateState → DeflateState) :
    md (some (.tab id)) f h = .ok ((), setD h id (f (rdD h id))) := by
  cases hd : h.dstates id with
  | none => exact absurd hd e
  | some d => simp [rdD, hd, md_run hd]

@[simp] theorem rdD_setD_same (h : Heap) (id : Nat) (d : DeflateState) : rdD (setD h id d) id = d := by
  simp [rdD]
@[simp] theorem rdD_setB (h : Heap) (id b : Nat) (a : Array UInt8) : rdD (setB h b a) id = rdD h id := rfl
theorem setD_ne_none (h : Heap) (id : Nat) (d : DeflateState) : (setD h id d).dstates id ≠ none := by simp

theorem pLtree_run {h : Heap} {id : Nat} {d : DeflateState} (e : h.dstates id = some d) :
    pLtree (some (.tab id)) h = .ok (.ref (.dstate_dyn_ltree id) 0, h) := by
  simp [pLtree, sid_run e]; try rfl
theorem pDtree_run {h : Heap} {id : Nat} {d : DeflateState} (e : h.dstates id = some d) :
    pDtree (some (.tab id)) h = .ok (.ref (.dstate_dyn_dtree id) 0, h) := by
  simp [pDtree, sid_run e]; try rfl
theorem pBltree_run {h : Heap} {id : Nat} {d : DeflateState} (e : h.dstates id = some d) :
    pBltree (some (.tab id)) h = .ok (.ref (.dstate_bl_tree id) 0, h) := by
  simp [pBltree, sid_run e]; try rfl
theorem pHeap_run {h : Heap} {id : Nat} {d : DeflateState} (e : h.dstates id = some d) :
    pHeap (some (.tab id)) h = .ok (.ref (.dstate_heap id) 0, h) := by
  simp [pHeap, sid_run e]; try rfl
theorem pDepth_run {h : Heap} {id : Nat} {d : DeflateState} (e : h.dstates id = some d) :
    pDepth (some (.tab id)) h = .ok (.ref (.dstate_depth id) 0, h) := by
  simp [pDepth, sid_run e]; try rfl
theorem pBlCount_run {h : Heap} {id : Nat} {d : DeflateState} (e : h.dstates id = some d) :
    pBlCount (some (.tab id)) h = .ok (.ref (.dstate_bl_count id) 0, h) := by
  simp [pBlCount, sid_run e]; try rfl


/-! ## The static data of `trees.c` -/

/-- The static tables and descriptors of `trees.c` are installed: `install_trees` (`trees.c.lean`) provides this on
any heap, and no function of `trees.c` changes `h.static`. -/
def TreesStatic (st : Statics) : Prop := trees_statics st = st

theorem install_trees_static (h : Heap) : TreesStatic (install_trees h).static := by
  simp [TreesStatic, install_trees, trees_statics]

theorem TreesStatic.dist_code {st : Statics} (hs : TreesStatic st) : st.dist_code = dist_code_tab := by
  have := congrArg Statics.dist_code hs; simpa [trees_statics] using this.symm
theorem TreesStatic.length_code {st : Statics} (hs : TreesStatic st) : st.length_code = length_code_tab := by
  have := congrArg Statics.length_code hs; simpa [trees_statics] using this.symm
theorem TreesStatic.base_dist {st : Statics} (hs : TreesStatic st) : st.base_dist = base_dist_tab := by
  have := congrArg Statics.base_dist hs; simpa [trees_statics] using this.symm
theorem TreesStatic.base_length {st : Statics} (hs : TreesStatic st) : st.base_length = base_length_tab := by
  have := congrArg Statics.base_length hs; simpa [trees_statics] using this.symm
theorem TreesStatic.static_ltree {st : Statics} (hs : TreesStatic st) : st.static_ltree = static_ltree_tab := by
  have := congrArg Statics.static_ltree hs; simpa [trees_statics] using this.symm
theorem TreesStatic.static_dtree {st : Statics} (hs : TreesStatic st) : st.static_dtree = static_dtree_tab := by
  have := congrArg Statics.static_dtree hs; simpa [trees_statics] using this.symm
theorem TreesStatic.extra_lbits {st : Statics} (hs : TreesStatic st) : st.extra_lbits = extra_lbits_tab := by
  have := congrArg Statics.extra_lbits hs; simpa [trees_statics] using this.symm
theorem TreesStatic.extra_dbits {st : Statics} (hs : TreesStatic st) : st.extra_dbits = extra_dbits_tab := by
  have := congrArg Statics.extra_dbits hs; simpa [trees_statics] using this.symm
theorem TreesStatic.extra_blbits {st : Statics} (hs : TreesStatic st) : st.extra_blbits = extra_blbits_tab := by
  have := congrArg Statics.extra_blbits hs; simpa [trees_statics] using this.symm

theorem dist_code_tab_size : dist_code_tab.size = 512 := by decide +kernel
theorem length_code_tab_size : length_code_tab.size = 256 := by decide +kernel
theorem static_ltree_tab_size : static_ltree_tab.size = 288 := by decide +kernel
theorem static_dtree_tab_size : static_dtree_tab.size = 30 := by decide +kernel

/-! ## The invariant -/

/-- **What `deflateInit2_` establishes before `_tr_init` runs.** The deflate record `d` of block `id` is live and
well formed (`dyn_ltree`, `heap`, `depth` have `HEAP_SIZE` = 573 entries, `dyn_dtree` 61, `bl_tree` 39, `bl_count`
16); the static tables of `trees.c` are installed; `pending_buf` is the start of the writable byte block `b`, whose
content is `buf` and whose size is `4 * lit_bufsize` (`ZALLOC(strm, lit_bufsize, LIT_BUFS)`, with
`pending_buf_size = 4 * lit_bufsize`); `sym_buf = pending_buf + lit_bufsize` is in the same block
(`deflate.c` L519: the overlay of the symbols on the output); `sym_end = (lit_bufsize - 1) * 3`;
`lit_bufsize = 1 << (memLevel + 6)` lies in `128 .. 32768`; and `pending <= pending_buf_size` (zero after
`deflateResetKeep`). -/
structure TreesBase (h : Heap) (id : Nat) (d : DeflateState) (b : Nat) (buf : Array UInt8) : Prop where
  dstate : h.dstates id = some d
  wf : d.WellFormed
  static : TreesStatic h.static
  pbuf : d.pending_buf = .ref (.blk b) 0
  bytes : h.bytes b = some buf
  rw : h.ro b = false
  size : buf.size = 4 * d.lit_bufsize.toNat
  psize : d.pending_buf_size.toNat = buf.size
  sym : d.sym_buf = .ref (.blk b) d.lit_bufsize.toNat
  lit_lo : 128 ≤ d.lit_bufsize.toNat
  lit_hi : d.lit_bufsize.toNat ≤ 32768
  sym_end : d.sym_end.toNat = 3 * (d.lit_bufsize.toNat - 1)
  pending_le : d.pending.toNat ≤ d.pending_buf_size.toNat

/-- **What `_tr_init` adds.** The three tree descriptors point at the arrays of the record and at the static
descriptors; the bit buffer holds `bi_valid <= 16 = Buf_size` bits (fact F9 of `docs/proof/trees.md`: `send_bits`
shifts by at most 16) and no bit above them; the symbol count is a multiple of 3 and at most `sym_end`
(`_tr_tally` is always followed by a flush when `sym_next == sym_end`). -/
structure TreesRun (id : Nat) (d : DeflateState) : Prop where
  ldyn : d.l_desc.dyn_tree = .ref (.dstate_dyn_ltree id) 0
  lstat : d.l_desc.stat_desc = some .st_static_l_desc
  ddyn : d.d_desc.dyn_tree = .ref (.dstate_dyn_dtree id) 0
  dstat : d.d_desc.stat_desc = some .st_static_d_desc
  bldyn : d.bl_desc.dyn_tree = .ref (.dstate_bl_tree id) 0
  blstat : d.bl_desc.stat_desc = some .st_static_bl_desc
  bi_lo : 0 ≤ d.bi_valid.toInt
  bi_hi : d.bi_valid.toInt ≤ 16
  bi_buf : d.bi_buf.toNat < 2 ^ d.bi_valid.toInt.toNat
  sym_next_le : d.sym_next.toNat ≤ d.sym_end.toNat
  sym_next_mod : d.sym_next.toNat % 3 = 0

/-- The part of `TreesRun` that does not mention the symbol buffer: descriptors and bit buffer. -/
structure TreesRun0 (id : Nat) (d : DeflateState) : Prop where
  ldyn : d.l_desc.dyn_tree = .ref (.dstate_dyn_ltree id) 0
  lstat : d.l_desc.stat_desc = some .st_static_l_desc
  ddyn : d.d_desc.dyn_tree = .ref (.dstate_dyn_dtree id) 0
  dstat : d.d_desc.stat_desc = some .st_static_d_desc
  bldyn : d.bl_desc.dyn_tree = .ref (.dstate_bl_tree id) 0
  blstat : d.bl_desc.stat_desc = some .st_static_bl_desc
  bi_lo : 0 ≤ d.bi_valid.toInt
  bi_hi : d.bi_valid.toInt ≤ 16
  bi_buf : d.bi_buf.toNat < 2 ^ d.bi_valid.toInt.toNat

theorem TreesRun.to0 {id : Nat} {d : DeflateState} (hr : TreesRun id d) : TreesRun0 id d :=
  ⟨hr.ldyn, hr.lstat, hr.ddyn, hr.dstat, hr.bldyn, hr.blstat, hr.bi_lo, hr.bi_hi, hr.bi_buf⟩

theorem TreesRun0.withSym {id : Nat} {d : DeflateState} (hr : TreesRun0 id d) (h1 : d.sym_next.toNat ≤ d.sym_end.toNat)
    (h2 : d.sym_next.toNat % 3 = 0) : TreesRun id d :=
  ⟨hr.ldyn, hr.lstat, hr.ddyn, hr.dstat, hr.bldyn, hr.blstat, hr.bi_lo, hr.bi_hi, hr.bi_buf, h1, h2⟩

/-- **The deflate state is well formed for the code of `trees.c`**, with the byte block `b` (content `buf`) that
holds `pending_buf` and `sym_buf`. -/
structure TreesInvAt (h : Heap) (id : Nat) (d : DeflateState) (b : Nat) (buf : Array UInt8) : Prop where
  base : TreesBase h id d b buf
  run : TreesRun id d

/-- `TreesInv h id`: the deflate state of block `id` is well formed for the code of `trees.c` (see `TreesInvAt`). -/
def TreesInv (h : Heap) (id : Nat) : Prop := ∃ d b buf, TreesInvAt h id d b buf

/-- Everything of the heap except the byte block `b` and the deflate record `id` is the same. -/
structure HFrame (h h' : Heap) (b id : Nat) : Prop where
  bytes : ∀ k, k ≠ b → h'.bytes k = h.bytes k
  dstates : ∀ k, k ≠ id → h'.dstates k = h.dstates k
  words : ∀ k, h'.words k = h.words k
  ro : ∀ k, h'.ro k = h.ro k
  streams : ∀ k, h'.streams k = h.streams k
  gzheaders : ∀ k, h'.gzheaders k = h.gzheaders k
  istates : ∀ k, h'.istates k = h.istates k
  gzstates : ∀ k, h'.gzstates k = h.gzstates k
  static : h'.static = h.static
  nextBlk : h'.nextBlk = h.nextBlk
  nalloc : h'.nalloc = h.nalloc
  allocOk : h'.allocOk = h.allocOk
  garbage : h'.garbage = h.garbage

theorem HFrame.refl (h : Heap) (b id : Nat) : HFrame h h b id :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl,
   fun _ => rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem HFrame.trans {h1 h2 h3 : Heap} {b id : Nat} (a : HFrame h1 h2 b id) (c : HFrame h2 h3 b id) :
    HFrame h1 h3 b id :=
  ⟨fun k hk => (c.bytes k hk).trans (a.bytes k hk), fun k hk => (c.dstates k hk).trans (a.dstates k hk),
   fun k => (c.words k).trans (a.words k), fun k => (c.ro k).trans (a.ro k),
   fun k => (c.streams k).trans (a.streams k), fun k => (c.gzheaders k).trans (a.gzheaders k),
   fun k => (c.istates k).trans (a.istates k), fun k => (c.gzstates k).trans (a.gzstates k),
   c.static.trans a.static, c.nextBlk.trans a.nextBlk, c.nalloc.trans a.nalloc, c.allocOk.trans a.allocOk,
   c.garbage.trans a.garbage⟩

theorem HFrame.setD (h : Heap) (b id : Nat) (d : DeflateState) : HFrame h (setD h id d) b id :=
  ⟨fun _ _ => rfl, fun k hk => setD_dstates_ne h id k d hk, fun _ => rfl, fun _ => rfl, fun _ => rfl,
   fun _ => rfl, fun _ => rfl, fun _ => rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem HFrame.setB (h : Heap) (b id : Nat) (a : Array UInt8) : HFrame h (setB h b a) b id :=
  ⟨fun k hk => setB_bytes_ne h b k a hk, fun _ _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl,
   fun _ => rfl, fun _ => rfl, fun _ => rfl, rfl, rfl, rfl, rfl, rfl⟩


/-! ## The bit stream of the output -/

/-- The low `n` bits of `v`, least significant first. -/
def natBits (v n : Nat) : List Bool := (List.range n).map (fun i => v.testBit i)

/-- The bits of the first `n` bytes of `a`, each byte least significant bit first. -/
def bytesBits (a : Array UInt8) (n : Nat) : List Bool := (List.range n).flatMap (fun i => natBits (a.getD i 0).toNat 8)

/-- **The output so far**, as a bit stream: the bits of the pending bytes `pending_buf[0 .. pending)` (each byte least
significant bit first, as DEFLATE packs them), followed by the `bi_valid` low bits of `bi_buf` (least significant
first). `buf` is the content of the byte block of `pending_buf`. Every bit writer of `trees.c` appends to this
stream, and `flush_pending` moves complete bytes out of it. -/
def outBits (buf : Array UInt8) (d : DeflateState) : List Bool :=
  bytesBits buf d.pending.toNat ++ natBits d.bi_buf.toNat d.bi_valid.toInt.toNat

@[simp] theorem natBits_length (v n : Nat) : (natBits v n).length = n := by simp [natBits]

theorem natBits_add (v m n : Nat) : natBits v (m + n) = natBits v m ++ natBits (v >>> m) n := by
  unfold natBits
  rw [List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp [Nat.testBit_shiftRight]

theorem natBits_congr {v w : Nat} (n : Nat) (h : v % 2 ^ n = w % 2 ^ n) : natBits v n = natBits w n := by
  unfold natBits
  apply List.map_congr_left
  intro i hi
  have hi : i < n := List.mem_range.mp hi
  have h1 := Nat.testBit_mod_two_pow v n i
  rw [h] at h1
  simp [hi] at h1
  exact h1.symm

theorem natBits_zero (n : Nat) : natBits 0 n = List.replicate n false := by
  unfold natBits
  apply List.ext_getElem <;> simp

@[simp] theorem bytesBits_zero (a : Array UInt8) : bytesBits a 0 = [] := by simp [bytesBits]

theorem bytesBits_succ (a : Array UInt8) (n : Nat) :
    bytesBits a (n + 1) = bytesBits a n ++ natBits (a.getD n 0).toNat 8 := by
  simp [bytesBits, List.range_succ]

@[simp] theorem bytesBits_length (a : Array UInt8) (n : Nat) : (bytesBits a n).length = 8 * n := by
  induction n with
  | zero => simp
  | succ n ih => rw [bytesBits_succ]; simp [ih]; omega

theorem bytesBits_congr {a a' : Array UInt8} (n : Nat) (h : ∀ i, i < n → a.getD i 0 = a'.getD i 0) :
    bytesBits a n = bytesBits a' n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [bytesBits_succ, bytesBits_succ, ih (fun i hi => h i (by omega)), h n (by omega)]

theorem bytesBits_set {a : Array UInt8} {j n : Nat} (v : UInt8) (hj : n ≤ j) :
    bytesBits (a.set! j v) n = bytesBits a n := by
  apply bytesBits_congr
  intro i hi
  rw [Array.set!_eq_setIfInBounds, Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?,
    Array.getElem?_setIfInBounds]
  have : j ≠ i := by omega
  simp [this]

end Zlib.Trees.Proofs.Out
