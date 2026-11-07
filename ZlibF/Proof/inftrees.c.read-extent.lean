import ZlibF.Proof.«inftrees.c.decoder-safe»
import ZlibF.Spec.InflateTableExtent

namespace Zlib.Inftrees.Proofs
open C Zlib.Inftrees Zlib.Inftrees.Spec Zlib.Inftrees.Canon Zlib.Inffast.Spec
set_option autoImplicit false

private theorem prefix_cell (ca : Array Code) {stop i : Nat} (bound : i < stop) :
    (ca.extract 0 stop)[i]? = ca[i]? := by
  rw [Array.getElem?_extract]
  simp only [Nat.sub_zero, Nat.zero_add]
  by_cases inside : i < ca.size
  · rw [ite_eq_left (by omega)]
  · rw [ite_eq_right (by omega), Array.getElem?_eq_none (by omega)]

private theorem prefix_getD (ca : Array Code) {stop i : Nat} (bound : i < stop) :
    (ca.extract 0 stop).getD i default = ca.getD i default := by
  simp only [Array.getD_eq_getD_getElem?]
  rw [prefix_cell ca bound]

private theorem prefix_link_bound {P : Nat → Code → Prop} {L : Code → Prop}
    [DecidablePred L] {ca : Array Code} {offset root used : Nat}
    (safe : TableSafe P L (ca.extract 0 (offset + used)) offset root)
    (rootEnd : 2 ^ root ≤ used) {i : Nat} (index : i < 2 ^ root)
    (link : L (ca.getD (offset + i) default)) :
    offset + (ca.getD (offset + i) default).val.toNat +
      2 ^ (ca.getD (offset + i) default).op.toNat ≤ offset + used := by
  have entry := safe.2.2 i index
  rw [prefix_getD ca (by omega), ite_eq_left link] at entry
  have bound := Array.size_extract_le (as := ca) (i := 0) (j := offset + used)
  simp only [Nat.sub_zero] at bound
  exact Nat.le_trans entry.2.2.2.1 bound

/-- Every retained write and root link remains present after discarding
the array suffix past the actual final descriptor. -/
theorem complete_content_prefix {e : Env} {ca : Array Code}
    (code : CompleteCode e.ls e.R e.mx)
    (written : Written e e.m ca) (links : Links e e.m ca) :
    Written e e.m (ca.extract 0 (e.oc + (e.D (e.m - 1)).used)) ∧
      Links e e.m (ca.extract 0 (e.oc + (e.D (e.m - 1)).used)) := by
  have lastIndex : e.m - 1 < Canon.nz e.ls := by rw [e.nz_eq]; have := e.h_pos; change 0 < e.m at this; omega
  have rootBound : 2 ^ e.R ≤ (e.D (e.m - 1)).used := by
    exact desc_used_mono e.ls e.R e.mx (Nat.zero_le (e.m - 1))
  constructor
  · intro j index replica bound
    have listIndex : j < Canon.nz e.ls := by rw [e.nz_eq]; exact index
    have region := (gAddr_in_region code listIndex bound).2
    have order := desc_used_mono e.ls e.R e.mx (by omega : j ≤ e.m - 1)
    have total : gAddr e.ls e.R e.mx j replica < (e.D (e.m - 1)).used :=
      Nat.lt_of_lt_of_le region order
    rw [prefix_cell ca (by omega)]
    exact written j index replica bound
  · intro a positive le index start
    have slot : gSlot e.ls e.R a < 2 ^ e.R := Canon.rev_lt _ _
    rw [prefix_cell ca (by omega)]
    exact links a positive le index start

theorem complete_table_read_extent {e : Env} {ca : Array Code}
    (complete : Kc e.f e.n 15 = 2 ^ 15)
    (written : Written e e.m ca) (links : Links e e.m ca) :
    TableReadExtent e.c.type ca e.oc e.R (e.D (e.m - 1)).used := by
  have code := e.completeCode complete
  obtain ⟨writtenPrefix, linksPrefix⟩ := complete_content_prefix code written links
  have rootBound : 2 ^ e.R ≤ (e.D (e.m - 1)).used :=
    desc_used_mono e.ls e.R e.mx (Nat.zero_le (e.m - 1))
  refine ⟨e.h_R1, Nat.le_trans code.root_le code.mx_le, by omega, ?_⟩
  intro i index
  dsimp only
  intro link
  rcases link with ⟨type, link⟩ | ⟨type, link⟩
  · exact prefix_link_bound (complete_len_table_of_content type complete writtenPrefix linksPrefix)
      rootBound index link
  · exact prefix_link_bound (complete_dist_table_of_content type complete writtenPrefix linksPrefix)
      rootBound index link

private theorem two_cells_read_extent {type : UInt32} {ca : Array Code} {offset : Nat}
    {first second : Code} (one : ca[offset]? = some first) (two : ca[offset + 1]? = some second)
    (firstLen : type = LENS → ¬ LenLink first) (firstDist : type = DISTS → ¬ DistLink first)
    (secondLen : ¬ LenLink second) (secondDist : ¬ DistLink second) :
    TableReadExtent type ca offset 1 2 := by
  refine ⟨by decide, by decide, by omega, ?_⟩
  intro i index
  dsimp only
  intro link
  have cases : i = 0 ∨ i = 1 := by change i < 2 at index; omega
  rcases cases with rfl | rfl
  · simp only [Nat.add_zero, Array.getD_eq_getD_getElem?, one, Option.getD_some] at link
    rcases link with ⟨kind, link⟩ | ⟨kind, link⟩
    · exact False.elim (firstLen kind link)
    · exact False.elim (firstDist kind link)
  · simp only [Array.getD_eq_getD_getElem?, two, Option.getD_some] at link
    rcases link with ⟨kind, link⟩ | ⟨kind, link⟩
    · exact False.elim (secondLen link)
    · exact False.elim (secondDist link)

theorem singleton_table_read_extent {e : Env} {ca : Array Code}
    (single : e.m = 1) (one : e.mx = 1) (written : Written e e.m ca)
    (invalid : ca[e.oc + 1]? = some ⟨64, 1, 0⟩) :
    TableReadExtent e.c.type ca e.oc e.R (e.D (e.m - 1)).used := by
  have root : e.R = 1 := by
    have := e.h_R1
    have := e.h_Rmx
    have one' : mxl e.f e.n = 1 := one
    omega
  have len : Canon.L e.ls 0 = 1 := by
    rw [show Canon.L e.ls 0 = lenAt e.f e.n 0 from L_eq e.f e.n e.h_pos]
    have last : e.mx = lenAt e.f e.n 0 := by
      change lenAt e.f e.n (e.m - 1) = lenAt e.f e.n 0
      rw [single]
    exact last.symm.trans one
  have replicas : 0 < gReps e.ls e.R e.mx 0 := Nat.two_pow_pos _
  have first := written 0 (by omega) 0 replicas
  rw [gaddr0 e single root replicas, Nat.add_zero] at first
  have drop : (e.D 0).drop = 0 := rfl
  have leaf := here_data_leaf_of_drop (e := e) (j := 0) (by omega)
    (by rw [drop]; omega) (by omega)
  have invalidLeaf := Cover.invalid_leaf 0 1 (by decide)
  have firstLen : e.c.type = LENS → ¬ LenLink (e.here 0) := by
    intro type
    have firstLeaf : LenLeaf 0 (e.here 0) := by simpa only [drop] using leaf.1 type
    exact lenLeaf_not_link firstLeaf
  have firstDist : e.c.type = DISTS → ¬ DistLink (e.here 0) := by
    intro type
    have firstLeaf : DistLeaf 0 (e.here 0) := by simpa only [drop] using leaf.2 type
    exact distLeaf_not_link firstLeaf
  have extent : (e.D (e.m - 1)).used = 2 := by
    rw [single]
    change 2 ^ e.R = 2
    rw [root]
  rw [extent, root]
  exact two_cells_read_extent first invalid firstLen firstDist
    (lenLeaf_not_link invalidLeaf.1) (distLeaf_not_link invalidLeaf.2)

/-- `int inflate_table(codetype type, unsigned short *lens, unsigned codes,
code **table, unsigned *bits, unsigned short *work)`.
The existing returned-extent goal. Decoder safety and every read bound
are established on the same actual returned heap, including empty and
accepted single-symbol tables and every constructor error return. -/
theorem inflate_table_read_extent : Goal.inflate_table_read_extent := by
  intro h type rl ol codes rc oc bits rw ow pre
  obtain ⟨result, after, run, frame, _, construction⟩ :=
    inflate_table_construction h type rl ol codes rc oc bits rw ow pre
  obtain ⟨safeResult, safeAfter, safeRun, _, decoder⟩ :=
    inflate_table_decoder_safe h type rl ol codes rc oc bits rw ow pre
  have same := run.symm.trans safeRun
  cases same
  refine ⟨result, after, run, frame, ?_⟩
  intro success
  have returned : ∃ used, used ≤ capOf type ∧ result.2.1 = .ref rc (oc + used) := by
    obtain ⟨_, _, _, _, _, _, _, classify⟩ := frame
    rcases classify with ⟨_, used, bound, pointer⟩ | ⟨bad, _⟩
    · exact ⟨used, bound, pointer⟩
    · rcases bad with bad | bad <;> rw [success] at bad <;> cases bad
  obtain ⟨safeArray, safeGet, _, _, codeSafe, lenSafe, distSafe⟩ := decoder success
  rcases construction success with ⟨_, root, endPointer, ca, get, first, second⟩ |
    ⟨_, e, ca, function, count, width, reference, offset, kind, get, written, links, details⟩
  · have sameArray := Option.some.inj (safeGet.symm.trans get)
    subst safeArray
    obtain ⟨used, bound, pointer⟩ := returned
    have two : used = 2 := by
      have equality := Ptr.ref.inj (pointer.symm.trans endPointer)
      omega
    have invalidLeaf := Cover.invalid_leaf 0 1 (by decide)
    have extent : TableReadExtent type ca oc 1 2 :=
      two_cells_read_extent first second
        (fun _ => lenLeaf_not_link invalidLeaf.1) (fun _ => distLeaf_not_link invalidLeaf.2)
        (lenLeaf_not_link invalidLeaf.1) (distLeaf_not_link invalidLeaf.2)
    exact ⟨ca, 2, get, endPointer, by omega, by rw [root]; exact extent,
      codeSafe, lenSafe, distSafe⟩
  · have sameArray := Option.some.inj (safeGet.symm.trans get)
    subst safeArray
    obtain ⟨used, pointer, usedValue, invalid⟩ := details success
    rw [reference, offset] at pointer
    obtain ⟨otherUsed, bound, otherPointer⟩ := returned
    have usedEq : used = otherUsed := by
      have equality := Ptr.ref.inj (pointer.symm.trans otherPointer)
      omega
    have extent : TableReadExtent e.c.type ca e.oc e.R (e.D (e.m - 1)).used := by
      rcases e.h_end with complete | ⟨one, single, _⟩
      · exact complete_table_read_extent complete written links
      · exact singleton_table_read_extent single one written (invalid single one)
    rw [kind, offset, width, ← usedValue] at extent
    exact ⟨ca, used, get, pointer, by omega, extent, codeSafe, lenSafe, distSafe⟩

/-- Constructor refusals retain the input pointer and root width. Thus
the successful-extent facts also bound every returned pointer and width
at a mode call whose requested root width is already bounded. -/
theorem result_pointer_width_bounds {h after : Heap} {rw : WRef} {rc : CodeRef}
    {ow oc cap count : Nat} {work : Array UInt16} {codes : Array Code} {bits : UInt32}
    {result : Int32 × CodePtr × UInt32}
    (frame : Result h rw rc ow oc cap count work codes (.ref rc oc) bits result after)
    (root : bits.toNat ≤ 15) (successRoot : result.1 = 0 → result.2.2.toNat ≤ 15) :
    (∃ used, used ≤ cap ∧ result.2.1 = .ref rc (oc + used)) ∧ result.2.2.toNat ≤ 15 := by
  obtain ⟨_, _, _, _, _, _, _, classify⟩ := frame
  rcases classify with ⟨success, used, bound, pointer⟩ | ⟨_, pointer, width⟩
  · exact ⟨⟨used, bound, pointer⟩, successRoot success⟩
  · exact ⟨⟨0, Nat.zero_le _, by simpa only [Nat.add_zero] using pointer⟩, by rw [width]; exact root⟩

end Zlib.Inftrees.Proofs
