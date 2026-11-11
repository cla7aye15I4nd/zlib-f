import ZlibF.Proof.«public-uncompress-refusal»

/-!
# uncompr.c: the caller heap during decompression

`Agree keep E H` says that `H` holds the objects of the expected heap `E` at every
block in `keep`, typically the blocks live in the caller heap. The expected heap is
the caller heap with the output written so far (`writeOut`). Local objects and the
decoder's own blocks lie outside the caller blocks and are not compared.
-/

namespace ZlibF.Spec.Public.Proofs.Uncompress
open C ZlibF.Spec ZlibF.Spec.Public Zlib.Gzguts Zlib.Inflate.Proofs
set_option autoImplicit false

/-- The heap `h` with `xs` written at `p` (unchanged for an empty write or an
invalid pointer). -/
def writeOut (h : Heap) (p : BPtr) (xs : List UInt8) : Heap :=
  match p with
  | .ref r i =>
    match Space.get h r with
    | some a => if xs = [] then h else Space.put h r (a.extract 0 i ++ xs.toArray ++ a.extract (i + xs.length) a.size)
    | none => h
  | .null => h

theorem writeOut_nil (h : Heap) (p : BPtr) : writeOut h p [] = h := by
  unfold writeOut
  split
  · split <;> simp
  · rfl

/-- `writeOut` is the `Store` of the contracts on a writable range. -/
theorem store_writeOut {h : Heap} {p : BPtr} {xs : List UInt8} (w : Writable h p xs.length) :
    Store h p xs (writeOut h p xs) := by
  by_cases e : xs = []
  · subst e; exact Or.inl ⟨rfl, writeOut_nil h p⟩
  rcases w with ⟨-, h0⟩ | ⟨r, i, a, rfl, g, ro, hi⟩
  · exact absurd (List.eq_nil_of_length_eq_zero h0) e
  · refine Or.inr ⟨r, i, a, rfl, g, ro, hi, ?_⟩
    simp [writeOut, g, e]

/-- The objects at block `b` of two heaps are the same. -/
def SameAt (X Y : Heap) (b : Nat) : Prop :=
  Y.bytes b = X.bytes b ∧ Y.words b = X.words b ∧ Y.streams b = X.streams b ∧
  Y.gzheaders b = X.gzheaders b ∧ Y.dstates b = X.dstates b ∧ Y.istates b = X.istates b ∧
  Y.gzstates b = X.gzstates b ∧ Y.ro b = X.ro b

theorem SameAt.refl (X : Heap) (b : Nat) : SameAt X X b := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem SameAt.trans {X Y Z : Heap} {b : Nat} (a : SameAt X Y b) (c : SameAt Y Z b) : SameAt X Z b := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := a
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8⟩ := c
  exact ⟨c1.trans a1, c2.trans a2, c3.trans a3, c4.trans a4, c5.trans a5, c6.trans a6, c7.trans a7,
    c8.trans a8⟩

theorem SameAt.symm {X Y : Heap} {b : Nat} (a : SameAt X Y b) : SameAt Y X b := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := a
  exact ⟨a1.symm, a2.symm, a3.symm, a4.symm, a5.symm, a6.symm, a7.symm, a8.symm⟩

/-- `H` holds the objects of `E` at every block in `keep`, and the global parts of
the heap that the contracts compare. -/
structure Agree (keep : Nat → Prop) (E H : Heap) : Prop where
  blocks : ∀ b, keep b → SameAt E H b
  static : H.static = E.static
  allocOk : H.allocOk = E.allocOk
  garbage : H.garbage = E.garbage
  borrow : H.libcErrorBorrow = E.libcErrorBorrow

/-- The block of a byte view, if it has one. -/
def BRef.block : BRef → Option Nat
  | .blk b => some b
  | .dstate_depth b => some b
  | _ => none

/-- A byte view whose block agrees reads the same array. -/
theorem get_of_same {X Y : Heap} {r : BRef} (same : ∀ b, BRef.block r = some b → SameAt X Y b)
    (static : Y.static = X.static) (borrow : Y.libcErrorBorrow = X.libcErrorBorrow) :
    Space.get Y r = Space.get X r ∧ Space.ro Y r = Space.ro X r := by
  cases r with
  | blk b =>
    obtain ⟨s1, -, -, -, -, -, -, s8⟩ := same b rfl
    exact ⟨s1, s8⟩
  | str i => simp [Space.get, Space.ro, staticStringBytes, borrow]
  | dstate_depth b =>
    obtain ⟨-, -, -, -, s5, -, -, -⟩ := same b rfl
    simp [Space.get, Space.ro, s5]
  | st_dist_code => simp [Space.get, Space.ro, static]
  | st_length_code => simp [Space.get, Space.ro, static]

/-- Writing the same array through the same view keeps blocks that agreed. -/
theorem SameAt.put {X Y : Heap} {r : BRef} {b : Nat} (a : Array UInt8)
    (same : SameAt X Y b) (sameR : ∀ c, BRef.block r = some c → SameAt X Y c) :
    SameAt (Space.put X r a) (Space.put Y r a) b := by
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8⟩ := same
  cases r with
  | blk c =>
    simp only [Space.put]
    refine ⟨?_, s2, s3, s4, s5, s6, s7, s8⟩
    simp only [upd_apply]
    split <;> simp_all
  | str i => exact ⟨s1, s2, s3, s4, s5, s6, s7, s8⟩
  | dstate_depth c =>
    obtain ⟨-, -, -, -, t5, -, -, -⟩ := sameR c rfl
    simp only [Space.put]
    rw [t5]
    cases X.dstates c with
    | none => exact ⟨s1, s2, s3, s4, s5, s6, s7, s8⟩
    | some st =>
      refine ⟨s1, s2, s3, s4, ?_, s6, s7, s8⟩
      simp only [upd_apply]
      split <;> simp_all
  | st_dist_code => exact ⟨s1, s2, s3, s4, s5, s6, s7, s8⟩
  | st_length_code => exact ⟨s1, s2, s3, s4, s5, s6, s7, s8⟩

theorem put_put_any (X : Heap) (r : BRef) (a a' : Array UInt8) :
    Space.put (Space.put X r a) r a' = Space.put X r a' := by
  cases r with
  | blk b => simp [Space.put, upd_upd]
  | str i => simp [Space.put]
  | dstate_depth b =>
    cases e : X.dstates b with
    | none => simp [Space.put, e]
    | some st => simp [Space.put, e, upd_upd]
  | st_dist_code => simp [Space.put]
  | st_length_code => simp [Space.put]

theorem put_self_any {X : Heap} {r : BRef} {a : Array UInt8} (g : Space.get X r = some a) :
    Space.put X r a = X := by
  cases r with
  | blk b => simp only [Space.get] at g; simp [Space.put, upd_self _ _ _ g]
  | str i => simp [Space.put]
  | dstate_depth b =>
    cases e : X.dstates b with
    | none => simp [Space.get, e] at g
    | some st =>
      have same : st.depth = a := by simpa [Space.get, e] using g
      rw [← same]
      simp [Space.put, e, upd_self _ _ _ e]
  | st_dist_code => simp [Space.put]
  | st_length_code => simp [Space.put]

/-- A write through one view leaves the objects of other blocks. -/
theorem SameAt.put_other (X : Heap) {r : BRef} {b : Nat} (a : Array UInt8)
    (other : BRef.block r ≠ some b) : SameAt X (Space.put X r a) b := by
  cases r with
  | blk c =>
    have ne : b ≠ c := fun e => other (by rw [e]; rfl)
    simp only [Space.put]
    exact ⟨by simp [upd_ne _ _ _ _ ne], rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | str i => exact SameAt.refl X b
  | dstate_depth c =>
    have ne : b ≠ c := fun e => other (by rw [e]; rfl)
    simp only [Space.put]
    cases X.dstates c with
    | none => exact SameAt.refl X b
    | some st => exact ⟨rfl, rfl, rfl, rfl, by simp [upd_ne _ _ _ _ ne], rfl, rfl, rfl⟩
  | st_dist_code => exact SameAt.refl X b
  | st_length_code => exact SameAt.refl X b

theorem put_globals (X : Heap) (r : BRef) (a : Array UInt8) :
    (Space.put X r a).static = X.static ∧ (Space.put X r a).allocOk = X.allocOk ∧
      (Space.put X r a).garbage = X.garbage ∧
      (Space.put X r a).libcErrorBorrow = X.libcErrorBorrow := by
  cases r with
  | dstate_depth b =>
    simp only [Space.put]
    split <;> simp
  | _ => simp [Space.put]

/-- An array that holds `xs` at `i` and the old bytes elsewhere is the written array. -/
theorem written_array {a a' : Array UInt8} {i : Nat} {xs : List UInt8}
    (size : a'.size = a.size) (fits : i + xs.length ≤ a'.size)
    (inside : xs = (a'.toList.drop i).take xs.length)
    (outside : ∀ j, j < a.size → ¬ (i ≤ j ∧ j < i + xs.length) → a'[j]? = a[j]?) :
    a' = a.extract 0 i ++ xs.toArray ++ a.extract (i + xs.length) a.size := by
  apply Array.ext'
  simp only [Array.toList_append, Array.toList_extract, List.toList_toArray]
  apply List.ext_getElem?
  intro j
  simp only [List.getElem?_append, List.getElem?_take, List.getElem?_drop, List.length_append,
    List.length_take, List.length_drop, Array.length_toList, List.drop_zero, Nat.sub_zero, Nat.zero_add,
    Nat.min_eq_left (show i ≤ a.size by omega)]
  by_cases lo : j < i
  · have := outside j (by omega) (by omega)
    simp only [Array.getElem?_toList] at this ⊢
    simp [lo, show j < i + xs.length by omega, this]
  by_cases hi : i + xs.length ≤ j
  · simp only [lo, show ¬ j < i + xs.length by omega, ite_false]
    by_cases inb : j < a.size
    · have := outside j inb (by omega)
      rw [if_pos (by omega), show i + xs.length + (j - (i + xs.length)) = j by omega]
      simpa only [Array.getElem?_toList] using this
    · rw [if_neg (by omega)]
      simp only [Array.getElem?_toList]
      rw [Array.getElem?_eq_none (by omega)]
  · rw [if_pos (by omega), if_neg lo]
    have e := congrArg (fun l => l[j - i]?) inside
    simp only [List.getElem?_take, List.getElem?_drop, show j - i < xs.length by omega, ite_true,
      show i + (j - i) = j by omega] at e
    simpa only [Array.getElem?_toList] using e.symm

/-- `restoreRegions` for a single region. -/
theorem restore_one (H H' : Heap) (p : BPtr) (n : Nat) :
    restoreRegions H H' [⟨p, n⟩] =
      match p with
      | .null => H'
      | .ref r _ => match Space.get H r with
        | none => H'
        | some a => Space.put H' r a := by
  simp only [restoreRegions, List.foldl]
  cases p <;> rfl

/-- One decoder call that writes `out` at `p`, changes only blocks outside the caller
blocks, and keeps the libc borrow, keeps `H` in agreement with the caller heap
updated by `out`. -/
theorem agree_after_call {keep : Nat → Prop} {E H H' : Heap} {changed : Nat → Prop} {p : BPtr}
    {out : List UInt8}
    (agree : Agree keep E H) (elive : ∀ b, keep b → E.live b) (eback : ∀ b, E.live b → keep b)
    (outside : ∀ b, keep b → ¬ changed b)
    (frame : BufferFrame H H' changed [⟨p, out.length⟩])
    (written : Bytes H' p out.length out)
    (wE : out ≠ [] → Writable E p out.length)
    (borrow : H'.libcErrorBorrow = H.libcErrorBorrow) :
    Agree keep (writeOut E p out) H' := by
  obtain ⟨⟨fs, fa, fg, -, -, fb⟩, part⟩ := frame
  rw [restore_one] at fs fa fg fb
  -- the restored heap keeps every caller block of `H`
  have kept : ∀ b, keep b → SameAt H (restoreRegions H H' [⟨p, out.length⟩]) b := by
    intro b live
    have hl : H.live b := by
      obtain ⟨s1, s2, s3, s4, s5, s6, s7, -⟩ := agree.blocks b live
      have el := elive b live
      simp only [Heap.live] at el ⊢
      rw [s1, s2, s3, s4, s5, s6, s7]; exact el
    obtain ⟨x1, x2, x3, x4, x5, x6, x7, x8⟩ := fb b hl (outside b live)
    rw [restore_one]
    exact ⟨x1, x2, x3, x4, x5, x6, x7, x8⟩
  have putG := fun (X : Heap) (rr : BRef) (a : Array UInt8) => put_globals X rr a
  -- global parts
  have globals : ∀ X : Heap, X.static = E.static → X.allocOk = E.allocOk → X.garbage = E.garbage →
      X.libcErrorBorrow = E.libcErrorBorrow → H'.static = H.static → H'.allocOk = H.allocOk →
      H'.garbage = H.garbage → Agree keep X H' → Agree keep X H' := fun _ _ _ _ _ _ _ _ a => a
  clear globals
  -- the write leaves E's globals
  have wG : (writeOut E p out).static = E.static ∧ (writeOut E p out).allocOk = E.allocOk ∧
      (writeOut E p out).garbage = E.garbage ∧
      (writeOut E p out).libcErrorBorrow = E.libcErrorBorrow := by
    unfold writeOut
    split
    · split
      · split
        · exact ⟨rfl, rfl, rfl, rfl⟩
        · exact putG _ _ _
      · exact ⟨rfl, rfl, rfl, rfl⟩
    · exact ⟨rfl, rfl, rfl, rfl⟩
  -- H' and H share their globals
  have hG : H'.static = H.static ∧ H'.allocOk = H.allocOk ∧ H'.garbage = H.garbage := by
    cases p with
    | null => exact ⟨fs.symm, fa.symm, fg.symm⟩
    | ref rr off =>
      simp only [] at fs fa fg
      cases g : Space.get H rr with
      | none => simp only [g] at fs fa fg; exact ⟨fs.symm, fa.symm, fg.symm⟩
      | some aH =>
        simp only [g] at fs fa fg
        obtain ⟨p1, p2, p3, -⟩ := putG H' rr aH
        exact ⟨(fs.trans p1).symm, (fa.trans p2).symm, (fg.trans p3).symm⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  rotate_left
  · rw [wG.1, hG.1, agree.static]
  · rw [wG.2.1, hG.2.1, agree.allocOk]
  · rw [wG.2.2.1, hG.2.2, agree.garbage]
  · rw [wG.2.2.2, borrow, agree.borrow]
  intro b live
  have eh := agree.blocks b live
  have hr := kept b live
  -- views of E and H agree on every block that E holds
  have views : ∀ rr : BRef, (∀ c, BRef.block rr = some c → keep c) →
      Space.get H rr = Space.get E rr := by
    intro rr blocks
    exact (get_of_same (fun c hc => agree.blocks c (blocks c hc)) agree.static agree.borrow).1
  have eview : ∀ rr : BRef, ∀ a, Space.get E rr = some a → ∀ c, BRef.block rr = some c → keep c := by
    intro rr a g c hc
    apply eback
    cases rr with
    | blk d =>
      simp only [BRef.block, Option.some.injEq] at hc
      subst hc
      exact Or.inl (by simp only [Space.get] at g; rw [g]; simp)
    | dstate_depth d =>
      simp only [BRef.block, Option.some.injEq] at hc
      subst hc
      simp only [Space.get] at g
      cases e : E.dstates d with
      | none => rw [e] at g; cases g
      | some st => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by rw [e]; simp)))))
    | _ => cases hc
  cases p with
  | null =>
    rw [restore_one] at hr
    exact (eh.trans hr).symm.symm |> fun x => by simpa [writeOut] using x
  | ref rr off =>
    rw [restore_one] at hr
    simp only [] at hr
    cases g : Space.get H rr with
    | none =>
      rw [g] at hr
      by_cases e : out = []
      · subst e; rw [writeOut_nil]; exact eh.trans hr
      · exfalso
        rcases wE e with ⟨h0, -⟩ | ⟨r', i', a, hp, gE, -, -⟩
        · cases h0
        · cases hp
          rw [views rr (eview rr a gE), gE] at g
          cases g
    | some aH =>
      rw [g] at hr
      obtain ⟨a', g', size, same⟩ := part ⟨Ptr.ref rr off, out.length⟩ (List.mem_singleton_self _) rr off aH rfl g
      have H'eq : Space.put (Space.put H' rr aH) rr a' = H' := by
        rw [put_put_any, put_self_any g']
      by_cases e : out = []
      · subst e
        rw [writeOut_nil]
        have arr : a' = aH := by
          apply Array.ext size
          intro j h1 h2
          have := same j h2 (by
            rintro ⟨reg, mem, ⟨o, -, lo, hi⟩⟩
            simp only [List.mem_singleton] at mem
            subst mem
            simp only [List.length_nil] at hi
            omega)
          rw [Array.getElem?_eq_getElem h1, Array.getElem?_eq_getElem h2] at this
          exact Option.some.inj this
        rw [arr] at H'eq
        rw [← H'eq, put_put_any]
        exact eh.trans hr
      · rcases wE e with ⟨h0, -⟩ | ⟨r', i', aE, hp, gE, -, -⟩
        · cases h0
        · cases hp
          have gH : Space.get H rr = some aE := by rw [views rr (eview rr aE gE)]; exact gE
          rw [g] at gH
          cases gH
          rcases written with ⟨h0, h1, -⟩ | ⟨r2, i2, a2, hp2, g2, fit2, inside⟩
          · cases h0
          · cases hp2
            rw [g'] at g2
            cases g2
            have arr := written_array (i := off) (xs := out) size fit2 inside (fun j hj notIn => same j hj (by
              rintro ⟨reg, mem, ⟨o, hpo, lo, hi⟩⟩
              simp only [List.mem_singleton] at mem
              subst mem
              simp only [Ptr.ref.injEq] at hpo
              obtain ⟨-, rfl⟩ := hpo
              exact notIn ⟨lo, hi⟩))
            have wEq : writeOut E (Ptr.ref rr off) out =
                Space.put E rr (aH.extract 0 off ++ out.toArray ++ aH.extract (off + out.length) aH.size) := by
              simp [writeOut, gE, e]
            rw [wEq, ← H'eq, ← arr]
            refine SameAt.put a' (eh.trans hr) ?_
            intro c hc
            have lc := eview rr aH gE c hc
            exact (agree.blocks c lc).trans (by
              have := kept c lc
              rw [restore_one] at this
              simpa only [g] using this)

end ZlibF.Spec.Public.Proofs.Uncompress
