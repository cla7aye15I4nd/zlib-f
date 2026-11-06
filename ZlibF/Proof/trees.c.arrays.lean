import ZlibF.Proof.«trees.c.inv»

/-!
# trees.c: reading and writing the tree arrays of the deflate record

Run lemmas for `getFc`, `setFc`, `getDl`, `setDl` on `s->dyn_ltree`, `s->dyn_dtree`, `s->bl_tree`, and the facts
that such a write keeps the record well formed (array sizes) and `TreesBase`.
-/

namespace Zlib.Trees.Proofs.Out
open C Zlib.Trees

section generic
variable {h : Heap} {r : CtDataRef} {a : Array CtData} {i : Nat}

theorem getFc_gen (hg : Space.get h r = some a) (hi : i < a.size) :
    getFc (.ref r 0) (i : Int) h = .ok ((a[i]).fc, h) := by
  have e := Ptr.index_ok (off := 0) (i := i) hg (by omega)
  unfold OkOn at e
  unfold getFc
  rw [bind_app, e]
  simp

theorem getDl_gen (hg : Space.get h r = some a) (hi : i < a.size) :
    getDl (.ref r 0) (i : Int) h = .ok ((a[i]).dl, h) := by
  have e := Ptr.index_ok (off := 0) (i := i) hg (by omega)
  unfold OkOn at e
  unfold getDl
  rw [bind_app, e]
  simp

theorem setFc_gen (hg : Space.get h r = some a) (hro : Space.ro h r = false) (hi : i < a.size) (v : UInt16) :
    setFc (.ref r 0) (i : Int) v h = .ok ((), Space.put h r (a.set! i { a[i] with fc := v })) := by
  have e1 := Ptr.add_nat_ok (off := 0) (n := i) hg (by omega)
  have e2 := Ptr.load_ok (off := 0 + i) hg (by omega)
  have e3 := Ptr.store_ok (v := ({ a[0 + i] with fc := v } : CtData)) (off := 0 + i) hg hro (by omega)
  unfold OkOn at e1 e2
  unfold setFc
  rw [bind_app, e1]
  simp only []
  rw [bind_app, e2]
  simp only []
  rw [e3]
  simp

theorem setDl_gen (hg : Space.get h r = some a) (hro : Space.ro h r = false) (hi : i < a.size) (v : UInt16) :
    setDl (.ref r 0) (i : Int) v h = .ok ((), Space.put h r (a.set! i { a[i] with dl := v })) := by
  have e1 := Ptr.add_nat_ok (off := 0) (n := i) hg (by omega)
  have e2 := Ptr.load_ok (off := 0 + i) hg (by omega)
  have e3 := Ptr.store_ok (v := ({ a[0 + i] with dl := v } : CtData)) (off := 0 + i) hg hro (by omega)
  unfold OkOn at e1 e2
  unfold setDl
  rw [bind_app, e1]
  simp only []
  rw [bind_app, e2]
  simp only []
  rw [e3]
  simp

end generic


theorem getElem!_set! {α : Type} [Inhabited α] (a : Array α) (i j : Nat) (v : α) :
    (a.set! i v)[j]! = if i = j ∧ i < a.size then v else a[j]! := by
  rw [Array.getElem!_eq_getD, Array.getElem!_eq_getD, Array.set!_eq_setIfInBounds, Array.getD_eq_getD_getElem?,
    Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds]
  by_cases h1 : i = j
  · subst h1; by_cases h2 : i < a.size <;> simp [h2]
  · simp [h1]

theorem getElem!_ge {α : Type} [Inhabited α] (a : Array α) (n : Nat) (h : a.size ≤ n) : a[n]! = default := by
  rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_eq_none h]; rfl

/-- The three code arrays of the deflate record. -/
inductive Sel where
  | l | d | bl
  deriving DecidableEq

/-- The reference to the array. -/
def Sel.ref (s : Sel) (id : Nat) : CtDataRef :=
  match s with
  | .l => .dstate_dyn_ltree id
  | .d => .dstate_dyn_dtree id
  | .bl => .dstate_bl_tree id

/-- The array in the record. -/
def Sel.arr (s : Sel) (d : DeflateState) : Array CtData :=
  match s with
  | .l => d.dyn_ltree
  | .d => d.dyn_dtree
  | .bl => d.bl_tree

/-- The record with the array replaced. -/
def Sel.upd (s : Sel) (d : DeflateState) (a : Array CtData) : DeflateState :=
  match s with
  | .l => { d with dyn_ltree := a }
  | .d => { d with dyn_dtree := a }
  | .bl => { d with bl_tree := a }

/-- The size of the array in the C declaration. -/
def Sel.size (s : Sel) : Nat :=
  match s with
  | .l => 573
  | .d => 61
  | .bl => 39

theorem Sel.get_ref {h : Heap} {id : Nat} {d : DeflateState} (e : h.dstates id = some d) (s : Sel) :
    Space.get h (s.ref id) = some (s.arr d) := by
  cases s <;> simp [Sel.ref, Sel.arr, Space.get, e]

theorem Sel.ro_ref (h : Heap) (id : Nat) (s : Sel) : Space.ro h (s.ref id) = false := by
  cases s <;> rfl

theorem Sel.put_ref {h : Heap} {id : Nat} {d : DeflateState} (e : h.dstates id = some d) (s : Sel) (a : Array CtData) :
    Space.put h (s.ref id) a = setD h id (s.upd d a) := by
  cases s <;> simp [Sel.ref, Sel.upd, Space.put, e, setD]

theorem Sel.size_arr {d : DeflateState} (hw : d.WellFormed) (s : Sel) : (s.arr d).size = s.size := by
  obtain ⟨h1, h2, h3, -⟩ := hw
  cases s <;> simp [Sel.arr, Sel.size, h1, h2, h3]

theorem Sel.wf_upd {d : DeflateState} (hw : d.WellFormed) (s : Sel) (a : Array CtData) (ha : a.size = s.size) :
    (s.upd d a).WellFormed := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hw
  cases s <;> simp_all [Sel.upd, Sel.size, DeflateState.WellFormed]

theorem Sel.arr_upd (s : Sel) (d : DeflateState) (a : Array CtData) : s.arr (s.upd d a) = a := by
  cases s <;> rfl

theorem Sel.upd_arr (s : Sel) (d : DeflateState) : s.upd d (s.arr d) = d := by
  cases s <;> rfl

theorem Sel.upd_upd (s : Sel) (d : DeflateState) (a a' : Array CtData) : s.upd (s.upd d a) a' = s.upd d a' := by
  cases s <;> rfl

theorem getFc_sel {h : Heap} {id : Nat} {d : DeflateState} (e : h.dstates id = some d) (s : Sel) {i : Nat}
    (hi : i < (s.arr d).size) :
    getFc (.ref (s.ref id) 0) (i : Int) h = .ok (((s.arr d)[i]!).fc, h) := by
  rw [getElem!_pos (s.arr d) i hi]; exact getFc_gen (Sel.get_ref e s) hi

theorem getDl_sel {h : Heap} {id : Nat} {d : DeflateState} (e : h.dstates id = some d) (s : Sel) {i : Nat}
    (hi : i < (s.arr d).size) :
    getDl (.ref (s.ref id) 0) (i : Int) h = .ok (((s.arr d)[i]!).dl, h) := by
  rw [getElem!_pos (s.arr d) i hi]; exact getDl_gen (Sel.get_ref e s) hi

theorem setFc_sel {h : Heap} {id : Nat} {d : DeflateState} (e : h.dstates id = some d) (s : Sel) {i : Nat}
    (hi : i < (s.arr d).size) (v : UInt16) :
    setFc (.ref (s.ref id) 0) (i : Int) v h =
      .ok ((), setD h id (s.upd d ((s.arr d).set! i { (s.arr d)[i]! with fc := v }))) := by
  rw [getElem!_pos (s.arr d) i hi, setFc_gen (Sel.get_ref e s) (Sel.ro_ref h id s) hi, Sel.put_ref e]

theorem setDl_sel {h : Heap} {id : Nat} {d : DeflateState} (e : h.dstates id = some d) (s : Sel) {i : Nat}
    (hi : i < (s.arr d).size) (v : UInt16) :
    setDl (.ref (s.ref id) 0) (i : Int) v h =
      .ok ((), setD h id (s.upd d ((s.arr d).set! i { (s.arr d)[i]! with dl := v }))) := by
  rw [getElem!_pos (s.arr d) i hi, setDl_gen (Sel.get_ref e s) (Sel.ro_ref h id s) hi, Sel.put_ref e]

theorem TreesBase.treeUpd {h : Heap} {id : Nat} {d : DeflateState} {b : Nat} {buf : Array UInt8}
    (hb : TreesBase h id d b buf) (s : Sel) (a : Array CtData) (ha : a.size = s.size) :
    TreesBase (setD h id (s.upd d a)) id (s.upd d a) b buf := by
  refine ⟨setD_dstates_same _ _ _, Sel.wf_upd hb.wf s a ha, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (cases s <;> simpa [Sel.upd] using hb.static)
    | (cases s <;> simpa [Sel.upd] using hb.pbuf)
    | (cases s <;> simpa [Sel.upd] using hb.bytes)
    | (cases s <;> simpa [Sel.upd] using hb.rw)
    | (cases s <;> simpa [Sel.upd] using hb.size)
    | (cases s <;> simpa [Sel.upd] using hb.psize)
    | (cases s <;> simpa [Sel.upd] using hb.sym)
    | (cases s <;> simpa [Sel.upd] using hb.lit_lo)
    | (cases s <;> simpa [Sel.upd] using hb.lit_hi)
    | (cases s <;> simpa [Sel.upd] using hb.sym_end)
    | (cases s <;> simpa [Sel.upd] using hb.pending_le)

theorem TreesRun.treeUpd {id : Nat} {d : DeflateState} (hr : TreesRun id d) (s : Sel) (a : Array CtData) :
    TreesRun id (s.upd d a) := by
  cases s <;> exact ⟨hr.ldyn, hr.lstat, hr.ddyn, hr.dstat, hr.bldyn, hr.blstat, hr.bi_lo, hr.bi_hi, hr.bi_buf,
    hr.sym_next_le, hr.sym_next_mod⟩

theorem TreesInvAt.treeUpd {h : Heap} {id : Nat} {d : DeflateState} {b : Nat} {buf : Array UInt8}
    (hI : TreesInvAt h id d b buf) (s : Sel) (a : Array CtData) (ha : a.size = s.size) :
    TreesInvAt (setD h id (s.upd d a)) id (s.upd d a) b buf :=
  ⟨hI.base.treeUpd s a ha, hI.run.treeUpd s a⟩

end Zlib.Trees.Proofs.Out
