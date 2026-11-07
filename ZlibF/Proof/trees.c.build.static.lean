import ZlibF.Proof.«trees.c.build.complete»
import ZlibF.Proof.«trees.c.inv»

/-! # trees.c: the three installed static tree descriptors -/

namespace Zlib.Trees.Proofs
open C Zlib.Trees

/-- The actual installed descriptor selected by a dynamic tree. -/
def TK.buildDesc : TK → StaticTreeDesc
  | .lit => (trees_statics default).static_l_desc
  | .dist => (trees_statics default).static_d_desc
  | .bl => (trees_statics default).static_bl_desc

def TK.buildStaticRef : TK → StaticTreeDescRef
  | .lit => .st_static_l_desc
  | .dist => .st_static_d_desc
  | .bl => .st_static_bl_desc

/-- Extra-bit counts of the actual installed tables, including the literal
prefix with no extra bits. -/
def TK.buildExtra : TK → Nat → Nat
  | .lit, n => if n < 257 then 0 else extra_lbits_tab[n - 257]!.toInt.toNat
  | .dist, n => extra_dbits_tab[n]!.toInt.toNat
  | .bl, n => extra_blbits_tab[n]!.toInt.toNat

def TK.buildStaticLen : TK → Option (Nat → Nat)
  | .lit => some (fun n => static_ltree_tab[n]!.dl.toNat)
  | .dist => some (fun n => static_dtree_tab[n]!.dl.toNat)
  | .bl => none

/-- Installed descriptors are exactly the ones read by build_tree. -/
theorem trees_build_desc_get {h : Heap} (hs : Out.TreesStatic h.static) (tk : TK) :
    StaticTreeDescRef.get h tk.buildStaticRef = some tk.buildDesc := by
  cases tk
  · have he := congrArg Statics.static_l_desc hs
    change some h.static.static_l_desc = _
    rw [← he]
    rfl
  · have he := congrArg Statics.static_d_desc hs
    change some h.static.static_d_desc = _
    rw [← he]
    rfl
  · have he := congrArg Statics.static_bl_desc hs
    change some h.static.static_bl_desc = _
    rw [← he]
    rfl

set_option maxRecDepth 4096 in
/-- Every static-data premise of the construction theorem holds for the
actual installed tables. The finite value bounds are checked by the kernel. -/
theorem trees_build_static {h0 : Heap} {id : Nat} (hs : Out.TreesStatic h0.static) (tk : TK) :
    BTBuildStatic h0 id tk.buildDesc tk.buildExtra tk.buildStaticLen := by
  have hL : ∀ i : Fin 29, 0 ≤ extra_lbits_tab[i.val]!.toInt ∧ extra_lbits_tab[i.val]!.toInt ≤ 1000 := by decide +kernel
  have hD : ∀ i : Fin 30, 0 ≤ extra_dbits_tab[i.val]!.toInt ∧ extra_dbits_tab[i.val]!.toInt ≤ 1000 := by decide +kernel
  have hB : ∀ i : Fin 19, 0 ≤ extra_blbits_tab[i.val]!.toInt ∧ extra_blbits_tab[i.val]!.toInt ≤ 1000 := by decide +kernel
  have hSL : ∀ i : Fin 288, static_ltree_tab[i.val]!.dl.toNat ≤ 15 := by decide +kernel
  have hSD : ∀ i : Fin 30, static_dtree_tab[i.val]!.dl.toNat ≤ 15 := by decide +kernel
  cases tk
  · refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_⟩
    · intro n hn
      change n < 286 at hn
      constructor
      · intro hbase
        change 257 ≤ n at hbase
        refine ⟨.st_extra_lbits, extra_lbits_tab, rfl, ?_, by change n - 257 < 29; omega, ?_, ?_, ?_⟩
        · intro e
          simp [Space.get, setD, hs.extra_lbits]
        · exact (hL ⟨n - 257, by omega⟩).1
        · exact (hL ⟨n - 257, by omega⟩).2
        · simp only [TK.buildExtra, ite_eq_right (show ¬ n < 257 by omega)]
          rfl
      · intro hbase
        change n < 257 at hbase
        simp only [TK.buildExtra, hbase, ite_true]
    · refine Or.inr ⟨.st_static_ltree, static_ltree_tab, (fun n => static_ltree_tab[n]!.dl.toNat), rfl, rfl, ?_, ?_⟩
      · intro e
        simp [Space.get, setD, hs.static_ltree]
      · intro n hn
        change n < 286 at hn
        exact ⟨by change n < 288; omega, hSL ⟨n, by omega⟩, rfl⟩
  · refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_⟩
    · intro n hn
      change n < 30 at hn
      constructor
      · intro hbase
        refine ⟨.st_extra_dbits, extra_dbits_tab, rfl, ?_, ?_, ?_, ?_, ?_⟩
        · intro e
          simp [Space.get, setD, hs.extra_dbits]
        · change n - 0 < 30; omega
        · exact (hD ⟨n, hn⟩).1
        · exact (hD ⟨n, hn⟩).2
        · rfl
      · intro hbase
        change n < 0 at hbase
        omega
    · refine Or.inr ⟨.st_static_dtree, static_dtree_tab, (fun n => static_dtree_tab[n]!.dl.toNat), rfl, rfl, ?_, ?_⟩
      · intro e
        simp [Space.get, setD, hs.static_dtree]
      · intro n hn
        change n < 30 at hn
        exact ⟨by change n < 30; exact hn, hSD ⟨n, hn⟩, rfl⟩
  · refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, Or.inl ⟨rfl, rfl⟩⟩
    intro n hn
    change n < 19 at hn
    constructor
    · intro hbase
      refine ⟨.st_extra_blbits, extra_blbits_tab, rfl, ?_, ?_, ?_, ?_, ?_⟩
      · intro e
        simp [Space.get, setD, hs.extra_blbits]
      · change n - 0 < 19; omega
      · exact (hB ⟨n, hn⟩).1
      · exact (hB ⟨n, hn⟩).2
      · rfl
    · intro hbase
      change n < 0 at hbase
      omega


/-- Local construction result, retaining the built layout, actual bit-length
result and exact canonical-code stores. Caller-to-input-frequency refinement
and compressed-bit emission are separate obligations. -/
def BTBuildResult (tk : TK) (N L : Nat) (xb : Nat → Nat) (slOpt : Option (Nat → Nat))
    (e : DeflateState) : Prop :=
  ∃ (prepared built mid : DeflateState) (mc : Int32) (K : Nat),
    BTBuilt tk N K mc prepared built ∧
    GBDone tk built (574 - 2 * K) (K - 1) mc.toInt.toNat L xb slOpt mid ∧
    ∃ a : Array CtData, e = tk.setArr mid a ∧ a.size = (tk.arr mid).size ∧
      ∀ i < a.size, a[i]! =
        if i < (mc.toInt + 1).toNat ∧ (tk.arr mid)[i]!.dl ≠ 0 then
          { (tk.arr mid)[i]! with fc := UInt16.ofNat (Math.storedCode
            (fun b => mid.bl_count[b]!.toNat) (fun v => (tk.arr mid)[v]!.dl.toNat) i) }
        else (tk.arr mid)[i]!

/-- The state representation actually established by initialization supplies
all tree-construction storage, descriptor and static-table premises for any
of the three dynamic trees. Old frequencies, depths, lengths and heap
contents are unrestricted. This is the local construction contract, not
complete deflate correctness or a registered public goal. -/
theorem ws_build_tree_initialized {h0 : Heap} {id : Nat} {d : DeflateState}
    (tk : TK) (hwf : d.WellFormed) (hs : Out.TreesStatic h0.static) (hr : Out.TreesRun0 id d) :
    WS h0 id (build_tree (Sp id) (some (tk.descRef id))) d (fun _ e =>
      BTBuildResult tk tk.buildDesc.elems.toInt.toNat tk.buildDesc.max_length.toInt.toNat
        tk.buildExtra tk.buildStaticLen e) := by
  obtain ⟨hLT, hDT, hBT, hBC, hH, hD⟩ := hwf
  have he3 : 3 ≤ tk.buildDesc.elems.toInt := by cases tk <;> decide +kernel
  have he286 : tk.buildDesc.elems.toInt ≤ 286 := by cases tk <;> decide +kernel
  have hT : 2 * tk.buildDesc.elems.toInt.toNat - 1 ≤ (tk.arr d).size := by
    cases tk
    · change 571 ≤ d.dyn_ltree.size; omega
    · change 59 ≤ d.dyn_dtree.size; omega
    · change 37 ≤ d.bl_tree.size; omega
  have hTbig : (tk.arr d).size ≤ 600 := by
    cases tk
    · change d.dyn_ltree.size ≤ 600; omega
    · change d.dyn_dtree.size ≤ 600; omega
    · change d.bl_tree.size ≤ 600; omega
  have hDepth : 2 * tk.buildDesc.elems.toInt.toNat - 1 ≤ d.depth.size := by
    cases tk
    · change 571 ≤ d.depth.size; omega
    · change 59 ≤ d.depth.size; omega
    · change 37 ≤ d.depth.size; omega
  have hstat : (tk.getDesc d).stat_desc = some tk.buildStaticRef := by
    cases tk
    · exact hr.lstat
    · exact hr.dstat
    · exact hr.blstat
  have htree : (tk.getDesc d).dyn_tree = .ref (tk.ref id) 0 := by
    cases tk
    · exact hr.ldyn
    · exact hr.ddyn
    · exact hr.bldyn
  exact ws_build_tree_complete (bt_desc_get tk h0 id d) (trees_build_desc_get hs tk) hstat htree
    he3 he286 hT hTbig hDepth hH hBC (trees_build_static hs tk)

/-- The installed initialized-state theorem runs on the caller's actual
heap, rather than a hypothetical replacement heap. The state and table
representation is supplied by the existing actual initialization results. -/
theorem build_tree_initialized {h : Heap} {id : Nat} {d : DeflateState}
    (tk : TK) (hd : h.dstates id = some d) (hwf : d.WellFormed)
    (hs : Out.TreesStatic h.static) (hr : Out.TreesRun0 id d) :
    ∃ e : DeflateState, build_tree (Sp id) (some (tk.descRef id)) h = .ok ((), setD h id e) ∧
      BTBuildResult tk tk.buildDesc.elems.toInt.toNat tk.buildDesc.max_length.toInt.toNat
        tk.buildExtra tk.buildStaticLen e := by
  obtain ⟨a, e, he, hresult⟩ := ws_build_tree_initialized tk hwf hs hr
  have ha : a = () := Subsingleton.elim _ _
  subst a
  rw [setD_self hd] at he
  exact ⟨e, he, hresult⟩

end Zlib.Trees.Proofs
