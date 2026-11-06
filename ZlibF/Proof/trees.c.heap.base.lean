import ZlibF.Zlib.«trees.c»

/-!
# trees.c: the calculus for `pqdownheap`, `pqremove`, `gen_bitlen`, `build_tree`

All four functions touch one record of the heap, the `deflate_state` with block number `id`, and nothing else
(the static tables are read, never written). So the heap is always `setD h0 id d`: a base heap `h0` with the record
`id` replaced by `d`. `WS h0 id m d Q` says that the computation `m` run on `setD h0 id d` ends without a fault on
`setD h0 id d'` with a result `a` such that `Q a d'`. Then every proof is about the record `d`, and `h0` only matters
through the static tables.
-/

namespace Zlib.Trees.Proofs
open C Zlib.Trees

/-- The heap `h` with the deflate state `id` replaced by `d`. -/
def setD (h : Heap) (id : Nat) (d : DeflateState) : Heap := { h with dstates := upd h.dstates id (some d) }

@[simp] theorem setD_dstates_same (h : Heap) (id : Nat) (d : DeflateState) : (setD h id d).dstates id = some d := by
  simp [setD]
@[simp] theorem setD_setD (h : Heap) (id : Nat) (d d' : DeflateState) : setD (setD h id d) id d' = setD h id d' := by
  simp [setD, upd_upd]
@[simp] theorem setD_static (h : Heap) (id : Nat) (d : DeflateState) : (setD h id d).static = h.static := rfl
theorem setD_self {h : Heap} {id : Nat} {d : DeflateState} (hd : h.dstates id = some d) : setD h id d = h := by
  simp [setD, upd_self _ _ _ hd]

/-- `m` run on `setD h0 id d` ends in `setD h0 id d'` with a result `a`, and `Q a d'`. -/
def WS {α : Type} (h0 : Heap) (id : Nat) (m : M α) (d : DeflateState) (Q : α → DeflateState → Prop) : Prop :=
  ∃ a d', m (setD h0 id d) = .ok (a, setD h0 id d') ∧ Q a d'

section ws
variable {α β : Type} {h0 : Heap} {id : Nat}

theorem WS.pure' {a : α} {d : DeflateState} {Q : α → DeflateState → Prop} (hq : Q a d) :
    WS h0 id (Pure.pure a : M α) d Q := ⟨a, d, rfl, hq⟩

theorem WS.bind' {m : M α} {f : α → M β} {d : DeflateState} {Q : α → DeflateState → Prop}
    {R : β → DeflateState → Prop} (hm : WS h0 id m d Q) (hf : ∀ a d', Q a d' → WS h0 id (f a) d' R) :
    WS h0 id (m >>= f) d R := by
  obtain ⟨a, d1, e, hq⟩ := hm
  obtain ⟨b, d2, e2, hr⟩ := hf a d1 hq
  exact ⟨b, d2, by rw [bind_app, e]; exact e2, hr⟩

theorem WS.mono {m : M α} {d : DeflateState} {Q R : α → DeflateState → Prop} (hm : WS h0 id m d Q)
    (hr : ∀ a d', Q a d' → R a d') : WS h0 id m d R := by
  obtain ⟨a, d1, e, hq⟩ := hm
  exact ⟨a, d1, e, hr a d1 hq⟩

theorem WS.ite' {c : Prop} [Decidable c] {m1 m2 : M α} {d : DeflateState} {Q : α → DeflateState → Prop}
    (h1 : c → WS h0 id m1 d Q) (h2 : ¬ c → WS h0 id m2 d Q) : WS h0 id (if c then m1 else m2) d Q := by
  by_cases hc : c
  · simp only [hc, ite_true]; exact h1 hc
  · simp only [hc, ite_false]; exact h2 hc

theorem WS.of_eq {m : M α} {d d' : DeflateState} {a : α} (e : m (setD h0 id d) = .ok (a, setD h0 id d'))
    {Q : α → DeflateState → Prop} (hq : Q a d') : WS h0 id m d Q := ⟨a, d', e, hq⟩

/-- `while` with a measure: `Inv` is kept, the measure decreases, and `Q` holds when the condition fails. -/
theorem WS.cwhile' {σ : Type} {cond : σ → M (Bool × σ)} {body : σ → M σ}
    (Inv : σ → DeflateState → Prop) (μ : σ → DeflateState → Nat) (Q : σ → DeflateState → Prop)
    (hstep : ∀ s d, Inv s d →
      (∃ s1 d1, cond s (setD h0 id d) = .ok ((false, s1), setD h0 id d1) ∧ Q s1 d1) ∨
      (∃ s1 d1 s2 d2, cond s (setD h0 id d) = .ok ((true, s1), setD h0 id d1) ∧
        body s1 (setD h0 id d1) = .ok (s2, setD h0 id d2) ∧ Inv s2 d2 ∧ μ s2 d2 < μ s d))
    {s : σ} {d : DeflateState} (hI : Inv s d) (hfuel : μ s d < fuel) :
    WS h0 id (cwhile cond body s) d (fun s' d' => Q s' d') := by
  have key : ∀ k n s d, Inv s d → μ s d ≤ k → k < n →
      ∃ s' d', cwhile.go cond body n s (setD h0 id d) = .ok (s', setD h0 id d') ∧ Q s' d' := by
    intro k
    induction k using Nat.strongRecOn with
    | _ k ih =>
      intro n s d hI hμ hn
      obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      rcases hstep s d hI with ⟨s1, d1, hc, hq⟩ | ⟨s1, d1, s2, d2, hc, hb, hI2, hlt⟩
      · exact ⟨s1, d1, by simp [cwhile.go, hc], hq⟩
      · obtain ⟨s', d', hgo, hq⟩ := ih (μ s2 d2) (by omega) n s2 d2 hI2 (Nat.le_refl _) (by omega)
        exact ⟨s', d', by simp [cwhile.go, hc, hb, hgo], hq⟩
  obtain ⟨s', d', e, hq⟩ := key (μ s d) fuel s d hI (Nat.le_refl _) hfuel
  exact ⟨s', d', e, hq⟩

/-- `do ... while` with a measure. -/
theorem WS.cdoWhile' {σ : Type} {cond : σ → M (Bool × σ)} {body : σ → M σ}
    (Inv : σ → DeflateState → Prop) (μ : σ → DeflateState → Nat) (Q : σ → DeflateState → Prop)
    (hstep : ∀ s d, Inv s d → ∃ s1 d1, body s (setD h0 id d) = .ok (s1, setD h0 id d1) ∧
      ((∃ s2 d2, cond s1 (setD h0 id d1) = .ok ((false, s2), setD h0 id d2) ∧ Q s2 d2) ∨
       (∃ s2 d2, cond s1 (setD h0 id d1) = .ok ((true, s2), setD h0 id d2) ∧ Inv s2 d2 ∧ μ s2 d2 < μ s d)))
    {s : σ} {d : DeflateState} (hI : Inv s d) (hfuel : μ s d < fuel) :
    WS h0 id (cdoWhile body cond s) d (fun s' d' => Q s' d') := by
  have key : ∀ k n s d, Inv s d → μ s d ≤ k → k < n →
      ∃ s' d', cdoWhile.go body cond n s (setD h0 id d) = .ok (s', setD h0 id d') ∧ Q s' d' := by
    intro k
    induction k using Nat.strongRecOn with
    | _ k ih =>
      intro n s d hI hμ hn
      obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      obtain ⟨s1, d1, hb, hc⟩ := hstep s d hI
      rcases hc with ⟨s2, d2, hc, hq⟩ | ⟨s2, d2, hc, hI2, hlt⟩
      · exact ⟨s2, d2, by simp [cdoWhile.go, hb, hc], hq⟩
      · obtain ⟨s', d', hgo, hq⟩ := ih (μ s2 d2) (by omega) n s2 d2 hI2 (Nat.le_refl _) (by omega)
        exact ⟨s', d', by simp [cdoWhile.go, hb, hc, hgo], hq⟩
  obtain ⟨s', d', e, hq⟩ := key (μ s d) fuel s d hI (Nat.le_refl _) hfuel
  exact ⟨s', d', e, hq⟩

/-- `while`, with the steps written as `WS` facts: the condition, and on `true` the body. -/
theorem WS.cwhile2 {σ : Type} {cond : σ → M (Bool × σ)} {body : σ → M σ}
    (Inv : σ → DeflateState → Prop) (μ : σ → DeflateState → Nat) (Q : σ → DeflateState → Prop)
    (hstep : ∀ s d, Inv s d → WS h0 id (cond s) d (fun r d1 =>
      (r.1 = false ∧ Q r.2 d1) ∨
      (r.1 = true ∧ WS h0 id (body r.2) d1 (fun s2 d2 => Inv s2 d2 ∧ μ s2 d2 < μ s d))))
    {s : σ} {d : DeflateState} (hI : Inv s d) (hfuel : μ s d < fuel) :
    WS h0 id (cwhile cond body s) d (fun s' d' => Q s' d') := by
  refine WS.cwhile' Inv μ Q ?_ hI hfuel
  intro s d hI
  obtain ⟨⟨b, s1⟩, d1, hc, hq⟩ := hstep s d hI
  rcases hq with ⟨hb, hq⟩ | ⟨hb, s2, d2, hbody, hI2, hlt⟩
  · simp only at hb hq
    subst hb
    exact Or.inl ⟨s1, d1, hc, hq⟩
  · simp only at hb
    subst hb
    exact Or.inr ⟨s1, d1, s2, d2, hc, hbody, hI2, hlt⟩

/-- `do ... while`, with the steps written as `WS` facts. -/
theorem WS.cdoWhile2 {σ : Type} {cond : σ → M (Bool × σ)} {body : σ → M σ}
    (Inv : σ → DeflateState → Prop) (μ : σ → DeflateState → Nat) (Q : σ → DeflateState → Prop)
    (hstep : ∀ s d, Inv s d → WS h0 id (body s) d (fun s1 d1 => WS h0 id (cond s1) d1 (fun r d2 =>
      (r.1 = false ∧ Q r.2 d2) ∨ (r.1 = true ∧ Inv r.2 d2 ∧ μ r.2 d2 < μ s d))))
    {s : σ} {d : DeflateState} (hI : Inv s d) (hfuel : μ s d < fuel) :
    WS h0 id (cdoWhile body cond s) d (fun s' d' => Q s' d') := by
  refine WS.cdoWhile' Inv μ Q ?_ hI hfuel
  intro s d hI
  obtain ⟨s1, d1, hb, ⟨⟨b, s2⟩, d2, hc, hq⟩⟩ := hstep s d hI
  refine ⟨s1, d1, hb, ?_⟩
  rcases hq with ⟨hb', hq⟩ | ⟨hb', hI2, hlt⟩
  · simp only at hb' hq
    subst hb'
    exact Or.inl ⟨s2, d2, hc, hq⟩
  · simp only at hb' hI2 hlt
    subst hb'
    exact Or.inr ⟨s2, d2, hc, hI2, hlt⟩

theorem getD_set {α : Type} [Inhabited α] (a : Array α) (k i : Nat) (x : α) (hk : k < a.size) :
    (a.set! k x)[i]! = if i = k then x else a[i]! := by
  by_cases h : i = k
  · subst h; simp [Array.set!_eq_setIfInBounds, getElem!_pos, hk]
  · simp only [h, ite_false]
    simp only [Array.set!_eq_setIfInBounds]
    rcases Nat.lt_or_ge i a.size with hi | hi
    · rw [getElem!_pos (a.setIfInBounds k x) i (by simpa using hi), getElem!_pos a i hi]
      rw [Array.getElem_setIfInBounds]; simp [Ne.symm h]; exact hi
    · have h1 : ¬ i < (a.setIfInBounds k x).size := by simp; omega
      rw [getElem!_neg (a.setIfInBounds k x) i h1, getElem!_neg a i (by omega)]

theorem size_set! {α : Type} (a : Array α) (k : Nat) (x : α) : (a.set! k x).size = a.size := by simp

end ws

/-! ### Generic array access at offset 0 -/

section arr
variable {R T : Type} [Space Heap R T] [Inhabited T]

theorem index0_ok {h : Heap} {r : R} {a : Array T} (hg : Space.get h r = some a) {i : Int} (h0 : 0 ≤ i)
    (h1 : i < a.size) : Ptr.index (Ptr.ref r 0) i h = .ok (a[i.toNat]!, h) := by
  have := Ptr.index_ok (h := h) (r := r) (a := a) (off := 0) (i := i.toNat) hg (by omega)
  have e : ((i.toNat : Nat) : Int) = i := by omega
  rw [e] at this
  have hlt : i.toNat < a.size := by omega
  simp only [Nat.zero_add] at this
  rw [getElem!_pos a i.toNat hlt]
  exact this

omit [Inhabited T] in
theorem setAt0_ok {h : Heap} {r : R} {a : Array T} (hg : Space.get h r = some a) (hro : Space.ro h r = false)
    {i : Int} (h0 : 0 ≤ i) (h1 : i < a.size) (v : T) :
    setAt (Ptr.ref r 0) i v h = .ok ((), Space.put h r (a.set! i.toNat v)) := by
  have hadd : OkOn h (Ptr.add (Ptr.ref r 0) i) (Ptr.ref r i.toNat) := by
    have := Ptr.add_ok (h := h) (r := r) (a := a) (off := 0) (k := i) hg (by omega) (by omega)
    simpa using this
  unfold setAt
  rw [bind_app, hadd]
  exact Ptr.store_ok hg hro (by omega)

end arr

/-! ### The three dynamic trees -/

/-- Which tree array of the deflate state: `dyn_ltree`, `dyn_dtree` or `bl_tree`. -/
inductive TK where
  | lit | dist | bl
  deriving DecidableEq, Inhabited

def TK.ref : TK → Nat → CtDataRef
  | .lit, id => .dstate_dyn_ltree id
  | .dist, id => .dstate_dyn_dtree id
  | .bl, id => .dstate_bl_tree id

def TK.arr : TK → DeflateState → Array CtData
  | .lit, d => d.dyn_ltree
  | .dist, d => d.dyn_dtree
  | .bl, d => d.bl_tree

def TK.setArr : TK → DeflateState → Array CtData → DeflateState
  | .lit, d, a => { d with dyn_ltree := a }
  | .dist, d, a => { d with dyn_dtree := a }
  | .bl, d, a => { d with bl_tree := a }

/-- The size of the tree array: 573, 61, 39. -/
def TK.size : TK → Nat
  | .lit => 573
  | .dist => 61
  | .bl => 39

section prim
variable {h0 : Heap} {id : Nat} {d : DeflateState}

theorem tk_get (k : TK) : Space.get (setD h0 id d) (k.ref id) = some (k.arr d) := by
  cases k <;> simp [TK.ref, TK.arr, Space.get, setD]
theorem tk_put (k : TK) (a : Array CtData) : Space.put (setD h0 id d) (k.ref id) a = setD h0 id (k.setArr d a) := by
  cases k <;> simp [TK.ref, TK.setArr, Space.put, setD, upd_upd]
theorem tk_ro (k : TK) : Space.ro (setD h0 id d) (k.ref id) = false := by cases k <;> rfl

@[simp] theorem tk_setArr_heap (k : TK) (a) : (k.setArr d a).heap = d.heap := by cases k <;> rfl
@[simp] theorem tk_setArr_depth (k : TK) (a) : (k.setArr d a).depth = d.depth := by cases k <;> rfl
@[simp] theorem tk_setArr_bl_count (k : TK) (a) : (k.setArr d a).bl_count = d.bl_count := by cases k <;> rfl
@[simp] theorem tk_setArr_heap_len (k : TK) (a) : (k.setArr d a).heap_len = d.heap_len := by cases k <;> rfl
@[simp] theorem tk_setArr_heap_max (k : TK) (a) : (k.setArr d a).heap_max = d.heap_max := by cases k <;> rfl
@[simp] theorem tk_setArr_opt_len (k : TK) (a) : (k.setArr d a).opt_len = d.opt_len := by cases k <;> rfl
@[simp] theorem tk_setArr_static_len (k : TK) (a) : (k.setArr d a).static_len = d.static_len := by cases k <;> rfl
@[simp] theorem tk_setArr_l_desc (k : TK) (a) : (k.setArr d a).l_desc = d.l_desc := by cases k <;> rfl
@[simp] theorem tk_setArr_d_desc (k : TK) (a) : (k.setArr d a).d_desc = d.d_desc := by cases k <;> rfl
@[simp] theorem tk_setArr_bl_desc (k : TK) (a) : (k.setArr d a).bl_desc = d.bl_desc := by cases k <;> rfl
@[simp] theorem tk_arr_setArr (k : TK) (a) : k.arr (k.setArr d a) = a := by cases k <;> rfl

/-- `S id`: the pointer `s`. -/
abbrev Sp (id : Nat) : DeflateStatePtr := some (DeflateStateRef.tab id)

theorem ws_sid : WS h0 id (sid (Sp id)) d (fun v d' => v = id ∧ d' = d) :=
  WS.of_eq (by simp [sid, ldDeflateState, DeflateStateRef.get]) ⟨rfl, rfl⟩

theorem ws_rd : WS h0 id (rd (Sp id)) d (fun v d' => v = d ∧ d' = d) :=
  WS.of_eq (by simp [rd, ldDeflateState, DeflateStateRef.get]) ⟨rfl, rfl⟩

theorem ws_md (f : DeflateState → DeflateState) : WS h0 id (md (Sp id) f) d (fun _ d' => d' = f d) := by
  refine WS.of_eq (a := ()) (d' := f d) ?_ rfl
  simp only [md, bind_app, ldDeflateState, DeflateStateRef.get, setD_dstates_same, stDeflateState,
    DeflateStateRef.isRo, DeflateStateRef.put]
  simp [setD, upd_upd]

theorem ws_pHeap : WS h0 id (pHeap (Sp id)) d (fun v d' => v = Ptr.ref (IRef.dstate_heap id) 0 ∧ d' = d) :=
  WS.bind' ws_sid fun a d' ⟨ha, hd'⟩ => by subst ha; subst hd'; exact WS.pure' ⟨rfl, rfl⟩
theorem ws_pDepth : WS h0 id (pDepth (Sp id)) d (fun v d' => v = Ptr.ref (BRef.dstate_depth id) 0 ∧ d' = d) :=
  WS.bind' ws_sid fun a d' ⟨ha, hd'⟩ => by subst ha; subst hd'; exact WS.pure' ⟨rfl, rfl⟩
theorem ws_pBlCount : WS h0 id (pBlCount (Sp id)) d (fun v d' => v = Ptr.ref (WRef.dstate_bl_count id) 0 ∧ d' = d) :=
  WS.bind' ws_sid fun a d' ⟨ha, hd'⟩ => by subst ha; subst hd'; exact WS.pure' ⟨rfl, rfl⟩

/-! Reads and writes of the arrays of the record. `i` is a C index (an `Int`). -/

theorem ws_index_heap (i : Int) (h0' : 0 ≤ i) (h1 : i < d.heap.size) :
    WS h0 id (Ptr.index (Ptr.ref (IRef.dstate_heap id) 0) i) d (fun v d' => v = d.heap[i.toNat]! ∧ d' = d) :=
  WS.of_eq (index0_ok (IRef.get_dstate_heap (setD_dstates_same h0 id d)) h0' h1) ⟨rfl, rfl⟩

theorem ws_setAt_heap (i : Int) (v : Int32) (h0' : 0 ≤ i) (h1 : i < d.heap.size) :
    WS h0 id (setAt (Ptr.ref (IRef.dstate_heap id) 0) i v) d (fun _ d' => d' = { d with heap := d.heap.set! i.toNat v }) := by
  refine WS.of_eq (a := ()) (d' := { d with heap := d.heap.set! i.toNat v }) ?_ rfl
  rw [setAt0_ok (IRef.get_dstate_heap (setD_dstates_same h0 id d)) (IRef.ro_dstate_heap _ _) h0' h1,
    IRef.put_dstate_heap (setD_dstates_same h0 id d)]
  simp [setD, upd_upd]

theorem ws_index_depth (i : Int) (h0' : 0 ≤ i) (h1 : i < d.depth.size) :
    WS h0 id (Ptr.index (Ptr.ref (BRef.dstate_depth id) 0) i) d (fun v d' => v = d.depth[i.toNat]! ∧ d' = d) :=
  WS.of_eq (index0_ok (BRef.get_dstate_depth (setD_dstates_same h0 id d)) h0' h1) ⟨rfl, rfl⟩

theorem ws_setAt_depth (i : Int) (v : UInt8) (h0' : 0 ≤ i) (h1 : i < d.depth.size) :
    WS h0 id (setAt (Ptr.ref (BRef.dstate_depth id) 0) i v) d (fun _ d' => d' = { d with depth := d.depth.set! i.toNat v }) := by
  refine WS.of_eq (a := ()) (d' := { d with depth := d.depth.set! i.toNat v }) ?_ rfl
  rw [setAt0_ok (BRef.get_dstate_depth (setD_dstates_same h0 id d)) (BRef.ro_dstate_depth _ _) h0' h1,
    BRef.put_dstate_depth (setD_dstates_same h0 id d)]
  simp [setD, upd_upd]

theorem ws_index_blc (i : Int) (h0' : 0 ≤ i) (h1 : i < d.bl_count.size) :
    WS h0 id (Ptr.index (Ptr.ref (WRef.dstate_bl_count id) 0) i) d (fun v d' => v = d.bl_count[i.toNat]! ∧ d' = d) :=
  WS.of_eq (index0_ok (WRef.get_dstate_bl_count (setD_dstates_same h0 id d)) h0' h1) ⟨rfl, rfl⟩

theorem ws_setAt_blc (i : Int) (v : UInt16) (h0' : 0 ≤ i) (h1 : i < d.bl_count.size) :
    WS h0 id (setAt (Ptr.ref (WRef.dstate_bl_count id) 0) i v) d (fun _ d' => d' = { d with bl_count := d.bl_count.set! i.toNat v }) := by
  refine WS.of_eq (a := ()) (d' := { d with bl_count := d.bl_count.set! i.toNat v }) ?_ rfl
  rw [setAt0_ok (WRef.get_dstate_bl_count (setD_dstates_same h0 id d)) (WRef.ro_dstate_bl_count _ _) h0' h1,
    WRef.put_dstate_bl_count (setD_dstates_same h0 id d)]
  simp [setD, upd_upd]

/-! The tree arrays. -/

theorem ws_getFc (k : TK) (i : Int) (h0' : 0 ≤ i) (h1 : i < (k.arr d).size) :
    WS h0 id (getFc (Ptr.ref (k.ref id) 0) i) d (fun v d' => v = ((k.arr d)[i.toNat]!).fc ∧ d' = d) := by
  unfold getFc
  have := index0_ok (tk_get (h0 := h0) (id := id) (d := d) k) h0' h1
  exact WS.of_eq (by simp only [bind_app, this]; rfl) ⟨rfl, rfl⟩

theorem ws_getDl (k : TK) (i : Int) (h0' : 0 ≤ i) (h1 : i < (k.arr d).size) :
    WS h0 id (getDl (Ptr.ref (k.ref id) 0) i) d (fun v d' => v = ((k.arr d)[i.toNat]!).dl ∧ d' = d) := by
  unfold getDl
  have := index0_ok (tk_get (h0 := h0) (id := id) (d := d) k) h0' h1
  exact WS.of_eq (by simp only [bind_app, this]; rfl) ⟨rfl, rfl⟩

/-- `tree[i]` with the fields `fc`, `dl` replaced. -/
def CtData.withFc (e : CtData) (v : UInt16) : CtData := { e with fc := v }

theorem ws_setFc (k : TK) (i : Int) (v : UInt16) (h0' : 0 ≤ i) (h1 : i < (k.arr d).size) :
    WS h0 id (setFc (Ptr.ref (k.ref id) 0) i v) d
      (fun _ d' => d' = k.setArr d ((k.arr d).set! i.toNat { (k.arr d)[i.toNat]! with fc := v })) := by
  refine WS.of_eq (a := ()) (d' := k.setArr d ((k.arr d).set! i.toNat { (k.arr d)[i.toNat]! with fc := v })) ?_ rfl
  have hg := tk_get (h0 := h0) (id := id) (d := d) k
  have hpt : OkOn (setD h0 id d) (Ptr.add (Ptr.ref (k.ref id) 0) i) (Ptr.ref (k.ref id) i.toNat) := by
    have := Ptr.add_ok (h := setD h0 id d) (r := k.ref id) (a := k.arr d) (off := 0) (k := i) hg (by omega) (by omega)
    simpa using this
  have hld : OkOn (setD h0 id d) (Ptr.load (Ptr.ref (k.ref id) i.toNat)) ((k.arr d)[i.toNat]!) := by
    have := Ptr.load_ok (h := setD h0 id d) (r := k.ref id) (a := k.arr d) (off := i.toNat) hg (by omega)
    rwa [← getElem!_pos (k.arr d) i.toNat (by omega)] at this
  unfold setFc
  simp only [bind_app]
  unfold OkOn at hpt hld
  rw [hpt]; simp only []
  rw [hld]; simp only []
  rw [Ptr.store_ok hg (tk_ro k) (by omega), tk_put]

theorem ws_setDl (k : TK) (i : Int) (v : UInt16) (h0' : 0 ≤ i) (h1 : i < (k.arr d).size) :
    WS h0 id (setDl (Ptr.ref (k.ref id) 0) i v) d
      (fun _ d' => d' = k.setArr d ((k.arr d).set! i.toNat { (k.arr d)[i.toNat]! with dl := v })) := by
  refine WS.of_eq (a := ()) (d' := k.setArr d ((k.arr d).set! i.toNat { (k.arr d)[i.toNat]! with dl := v })) ?_ rfl
  have hg := tk_get (h0 := h0) (id := id) (d := d) k
  have hpt : OkOn (setD h0 id d) (Ptr.add (Ptr.ref (k.ref id) 0) i) (Ptr.ref (k.ref id) i.toNat) := by
    have := Ptr.add_ok (h := setD h0 id d) (r := k.ref id) (a := k.arr d) (off := 0) (k := i) hg (by omega) (by omega)
    simpa using this
  have hld : OkOn (setD h0 id d) (Ptr.load (Ptr.ref (k.ref id) i.toNat)) ((k.arr d)[i.toNat]!) := by
    have := Ptr.load_ok (h := setD h0 id d) (r := k.ref id) (a := k.arr d) (off := i.toNat) hg (by omega)
    rwa [← getElem!_pos (k.arr d) i.toNat (by omega)] at this
  unfold setDl
  simp only [bind_app]
  unfold OkOn at hpt hld
  rw [hpt]; simp only []
  rw [hld]; simp only []
  rw [Ptr.store_ok hg (tk_ro k) (by omega), tk_put]

end prim

end Zlib.Trees.Proofs
