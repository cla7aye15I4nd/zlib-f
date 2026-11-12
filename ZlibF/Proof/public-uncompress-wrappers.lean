import ZlibF.Proof.«public-uncompress-cells»

/-!
# uncompr.c: the wrappers `uncompress_z`, `uncompress2` and `uncompress`

`uncompress_z` and `uncompress` keep the source length in an automatic cell and call
the counted entry. `uncompress2` copies both lengths into automatic cells, calls
`uncompress2_z`, and copies the results back.
-/

namespace ZlibF.Spec.Public.Proofs.Uncompress
open C ZlibF.Spec ZlibF.Spec.Public Zlib.Gzguts Zlib.Inflate.Proofs Zlib.Inflate.Spec Zlib.Uncompr
set_option autoImplicit false

/-- A single-length wrapper over a counted entry. -/
def singleWrap (P : BPtr → BPtr → BPtr → BPtr → M Int32) (dest destLen source : BPtr) (n : UInt64) :
    M Int32 := do
  let used ← allocLocal 8
  store64 used n
  let r ← P dest destLen source used
  freeB used
  return r

/-- `UncompressCounted` with the data relation `Rel src capacity rc out used` as a
parameter: `Uncompressed` gives the functional goal, a bound relation the safety goal. -/
def CountedWith (program : BPtr → BPtr → BPtr → BPtr → M Int32) (nullableLengths : Bool)
    (Rel : List UInt8 → Nat → Int32 → List UInt8 → Nat → Prop) : Prop :=
  ∀ h dest destLen source sourceLen capacity n src,
    Fresh h → Zlib.Inflate.Spec.Uniq h → LibraryGlobals h → ZlibF.PlatformMemory.ByteObjectsFit h →
    (destLen ≠ .null → LengthCell h destLen capacity) →
    (sourceLen ≠ .null → LengthCell h sourceLen n) →
    (nullableLengths = false → destLen ≠ .null ∧ sourceLen ≠ .null) →
    (source ≠ .null → Bytes h source n.toNat src) →
    (dest ≠ .null → Writable h dest capacity.toNat) →
    UtilitySeparation dest capacity.toNat source n.toNat destLen sourceLen →
    ∃ rc after, C.run (program dest destLen source sourceLen) h = .ok (rc, after) ∧
      (sourceLen = .null ∨ destLen = .null ∨ (source = .null ∧ n ≠ 0) ∨
        (dest = .null ∧ capacity ≠ 0) → rc = Z_STREAM_ERROR ∧ SameObjectsUpToTableShape h after) ∧
      (sourceLen ≠ .null → destLen ≠ .null →
        (source = .null → n = 0) → (dest = .null → capacity = 0) →
        ∃ out used got consumed h₁ h₂ expected,
          Store h dest out h₁ ∧ Store h₁ sourceLen (lengthBytes consumed) h₂ ∧
          Store h₂ destLen (lengthBytes got) expected ∧ SameObjectsUpToTableShape expected after ∧
          Rel (if source = .null then [] else src) capacity.toNat rc out used ∧
          ((got.toNat = out.length ∧ consumed.toNat = used) ∨
            (rc = Z_MEM_ERROR ∧ out = [] ∧ got = capacity ∧ consumed = n)) ∧
          (rc = Z_MEM_ERROR → AllocationFailed h after))

/-- `UncompressSingle` with the data relation as a parameter. -/
def SingleWith (program : BPtr → BPtr → BPtr → UInt64 → M Int32) (nullableLength : Bool)
    (Rel : List UInt8 → Nat → Int32 → List UInt8 → Nat → Prop) : Prop :=
  ∀ h dest destLen source capacity n src,
    Fresh h → Zlib.Inflate.Spec.Uniq h → LibraryGlobals h → ZlibF.PlatformMemory.ByteObjectsFit h →
    (destLen ≠ .null → LengthCell h destLen capacity) →
    (nullableLength = false → destLen ≠ .null) →
    (source ≠ .null → Bytes h source n.toNat src) →
    (dest ≠ .null → Writable h dest capacity.toNat) →
    Separate source n.toNat dest capacity.toNat →
    Separate destLen 8 dest capacity.toNat → Separate destLen 8 source n.toNat →
    ∃ rc after, C.run (program dest destLen source n) h = .ok (rc, after) ∧
      (destLen = .null ∨ (source = .null ∧ n ≠ 0) ∨ (dest = .null ∧ capacity ≠ 0) →
        rc = Z_STREAM_ERROR ∧ SameObjectsUpToTableShape h after) ∧
      (destLen ≠ .null → (source = .null → n = 0) → (dest = .null → capacity = 0) →
        ∃ out used got h₁ expected,
          Store h dest out h₁ ∧ Store h₁ destLen (lengthBytes got) expected ∧
          SameObjectsUpToTableShape expected after ∧
          Rel (if source = .null then [] else src) capacity.toNat rc out used ∧
          (got.toNat = out.length ∨ (rc = Z_MEM_ERROR ∧ out = [] ∧ got = capacity)) ∧
          (rc = Z_MEM_ERROR → AllocationFailed h after))

theorem counted_with_uncompressed (P : BPtr → BPtr → BPtr → BPtr → M Int32) (nl : Bool) :
    CountedWith P nl Uncompressed = UncompressCounted P nl := rfl

theorem single_with_uncompressed (P : BPtr → BPtr → BPtr → UInt64 → M Int32) (nl : Bool) :
    SingleWith P nl Uncompressed = UncompressSingle P nl := rfl

theorem single_of_counted {P : BPtr → BPtr → BPtr → BPtr → M Int32} {nl : Bool}
    {Rel : List UInt8 → Nat → Int32 → List UInt8 → Nat → Prop}
    (inner : CountedWith P nl Rel) : SingleWith (singleWrap P) nl Rel := by
  intro h dest destLen source capacity n src fresh uniq globals fit dcell dnull srcB destW sep1 sep2 sep3
  have kept := cellHeap_kept fresh n
  have agree := cellHeap_agree fresh n
  have k0 : ¬ h.live h.nextBlk := fresh h.nextBlk (Nat.le_refl _)
  -- caller pointers are not into the cell's block
  have viaWritable : ∀ (q : BPtr) (m : Nat), (q ≠ .null → Writable h q m) →
      ∀ r i, q = .ref r i → ∀ c, BRef.block r = some c → c ≠ h.nextBlk := by
    intro q m w r i hq
    exact not_cell_block fresh (fun r' i' hq' => by
      rcases w (by rw [hq]; simp) with ⟨h0, -⟩ | ⟨r'', i'', a, hq'', g, -, -⟩
      · rw [hq] at h0; cases h0
      · rw [hq'] at hq''; cases hq''; exact ⟨a, g⟩) r i hq
  have viaBytes : ∀ (q : BPtr) (m : Nat) (xs : List UInt8), (q ≠ .null → Bytes h q m xs) →
      ∀ r i, q = .ref r i → ∀ c, BRef.block r = some c → c ≠ h.nextBlk := by
    intro q m xs b r i hq
    exact not_cell_block fresh (fun r' i' hq' => by
      rcases b (by rw [hq]; simp) with ⟨h0, -, -⟩ | ⟨r'', i'', a, hq'', g, -, -⟩
      · rw [hq] at h0; cases h0
      · rw [hq'] at hq''; cases hq''; exact ⟨a, g⟩) r i hq
  have destK := viaWritable dest _ destW
  have srcK := viaBytes source _ _ srcB
  have lenK : ∀ r i, destLen = .ref r i → ∀ c, BRef.block r = some c → c ≠ h.nextBlk :=
    viaWritable destLen 8 (fun dl => (dcell dl).2)
  have sepCell : ∀ (q : BPtr) (m : Nat), (∀ r i, q = .ref r i → ∀ c, BRef.block r = some c → c ≠ h.nextBlk) →
      Separate (cellPtr h) 8 q m := by
    intro q m qk
    exact separate_cell (fun i e => qk (.blk h.nextBlk) i e h.nextBlk rfl rfl)
  have sepU : UtilitySeparation dest capacity.toNat source n.toNat destLen (cellPtr h) :=
    ⟨separate_symm sep1, sep2, sep3, sepCell dest _ destK, sepCell source _ srcK,
      separate_symm (sepCell destLen 8 lenK)⟩
  obtain ⟨rc, after', run', bad', good'⟩ := inner (cellHeap h n) dest destLen source (cellPtr h) capacity n src
    (cellHeap_fresh fresh n) (cellHeap_uniq fresh uniq n) (cellHeap_globals globals n) (cellHeap_fit fresh fit n)
    (fun dl => kept.cell_of (dcell dl)) (fun _ => cellHeap_cell h n)
    (fun e => ⟨dnull e, by simp [cellPtr]⟩) (fun sn => kept.bytes_of (srcB sn))
    (fun dn => kept.writable_of (destW dn)) sepU
  -- the cell is still there after the inner call
  have cellAfter : ∀ X', SameObjectsUpToTableShape X' after' → X'.bytes h.nextBlk ≠ none →
      X'.ro h.nextBlk = false → ∃ a, after'.bytes h.nextBlk = some a ∧ after'.ro h.nextBlk = false := by
    intro X' sm nb ro
    obtain ⟨s1, -, s3, -⟩ := sm
    cases e : X'.bytes h.nextBlk with
    | none => exact absurd e nb
    | some a =>
      refine ⟨a, by rw [s1, e], ?_⟩
      rw [s3 h.nextBlk (Or.inl (by rw [e]; simp)), ro]
  have cellRun : ∀ X', SameObjectsUpToTableShape X' after' → X'.bytes h.nextBlk ≠ none →
      X'.ro h.nextBlk = false →
      C.run (singleWrap P dest destLen source n) h =
        .ok (rc, { after' with bytes := upd after'.bytes h.nextBlk none }) := by
    intro X' sm nb ro
    obtain ⟨a, hb, hro⟩ := cellAfter X' sm nb ro
    unfold singleWrap
    simp only [C.run, bind_app, alloc_cell_run fresh, store_cell_run]
    rw [show P dest destLen source (cellPtr h) (cellHeap h n) = .ok (rc, after') from run']
    simp only [cellPtr]
    rw [freeB_blk_run hb hro]
    rfl
  have x'k : (cellHeap h n).words h.nextBlk = none ∧ (cellHeap h n).streams h.nextBlk = none ∧
      (cellHeap h n).gzheaders h.nextBlk = none ∧ (cellHeap h n).dstates h.nextBlk = none ∧
      (cellHeap h n).istates h.nextBlk = none ∧ (cellHeap h n).gzstates h.nextBlk = none := by
    simp only [Heap.live, not_or, ne_eq, Decidable.not_not] at k0
    exact ⟨k0.2.1, k0.2.2.1, k0.2.2.2.1, k0.2.2.2.2.1, k0.2.2.2.2.2.1, k0.2.2.2.2.2.2⟩
  by_cases badW : destLen = .null ∨ (source = .null ∧ n ≠ 0) ∨ (dest = .null ∧ capacity ≠ 0)
  · obtain ⟨rcE, sm⟩ := bad' (Or.inr badW)
    refine ⟨rc, _, cellRun _ sm (by simp [cellHeap]) (by simp [cellHeap]), fun _ => ⟨rcE, ?_⟩, ?_⟩
    · exact same_without_cell sm agree k0 x'k (by simp [cellHeap]) (by simp [cellHeap])
    · intro dl sN dN
      exfalso
      rcases badW with b | b | b
      · exact dl b
      · exact b.2 (sN b.1)
      · exact b.2 (dN b.1)
  · have dl : destLen ≠ .null := fun e => badW (Or.inl e)
    have sN : source = .null → n = 0 := fun e => Classical.byContradiction fun ne =>
      badW (Or.inr (Or.inl ⟨e, ne⟩))
    have dN : dest = .null → capacity = 0 := fun e => Classical.byContradiction fun ne =>
      badW (Or.inr (Or.inr ⟨e, ne⟩))
    obtain ⟨out, used, got, consumed, h₁', h₂', exp', S1, S2, S3, sm, unc, counts, mem'⟩ :=
      good' (by simp [cellPtr]) dl sN dN
    -- the heaps of the inner stores
    have e1 := store_fun S1
    have e2 := store_fun S2
    have e3 := store_fun S3
    subst e1 e2 e3
    have a1 := agree.writeOut_both (xs := out) destK
    have a2 := a1.write_right (xs := lengthBytes consumed) (p := cellPtr h)
      (fun r i hp => by simp only [cellPtr, Ptr.ref.injEq] at hp; obtain ⟨rfl, -⟩ := hp; rfl)
    have a3 := a2.writeOut_both (xs := lengthBytes got) lenK
    have storeD := agree.store_left S1 destK
    have storeL := a2.store_left S3 lenK
    -- the cell before the free
    have cellB : (writeOut (writeOut (writeOut (cellHeap h n) dest out) (cellPtr h) (lengthBytes consumed)) destLen
        (lengthBytes got)).bytes h.nextBlk ≠ none ∧
        (writeOut (writeOut (writeOut (cellHeap h n) dest out) (cellPtr h) (lengthBytes consumed)) destLen
        (lengthBytes got)).ro h.nextBlk = false := by
      have l0 := writeOut_same_other (H := cellHeap h n) (p := dest) (xs := out) h.nextBlk
        (fun r i hp hb => destK r i hp _ hb rfl)
      have l2 := writeOut_same_other (H := writeOut (writeOut (cellHeap h n) dest out) (cellPtr h)
        (lengthBytes consumed)) (p := destLen) (xs := lengthBytes got) h.nextBlk
        (fun r i hp hb => lenK r i hp _ hb rfl)
      have g1 : Space.get (writeOut (cellHeap h n) dest out) (BRef.blk h.nextBlk) =
          some (lengthBytes n).toArray := by
        show (writeOut (cellHeap h n) dest out).bytes h.nextBlk = _
        rw [l0.1]; simp [cellHeap]
      have r1 : Space.ro (writeOut (cellHeap h n) dest out) (BRef.blk h.nextBlk) = false := by
        show (writeOut (cellHeap h n) dest out).ro h.nextBlk = false
        rw [l0.2.2.2.2.2.2.2]; simp [cellHeap]
      have mid := writeOut_same (xs := lengthBytes consumed) (i := 0) g1 r1
      refine ⟨?_, ?_⟩
      · rw [l2.1]
        show Space.get (writeOut (writeOut (cellHeap h n) dest out) (cellPtr h) (lengthBytes consumed))
          (BRef.blk h.nextBlk) ≠ none
        rcases mid with x | ⟨-, x⟩
        · rw [cellPtr, x]; simp
        · rw [cellPtr, x]; simp
      · rw [l2.2.2.2.2.2.2.2]
        have := writeOut_ro (h := writeOut (cellHeap h n) dest out) (q := cellPtr h) (xs := lengthBytes consumed)
          (BRef.blk h.nextBlk)
        exact this.trans r1
    have others : ∀ (X : Heap), (X.words h.nextBlk = none ∧ X.streams h.nextBlk = none ∧
        X.gzheaders h.nextBlk = none ∧ X.dstates h.nextBlk = none ∧ X.istates h.nextBlk = none ∧
        X.gzstates h.nextBlk = none) → ∀ (q : BPtr) (xs : List UInt8),
        (∀ r i, q = .ref r i → (BRef.block r ≠ some h.nextBlk ∨ ∃ j, r = .blk j)) →
        ((writeOut X q xs).words h.nextBlk = none ∧ (writeOut X q xs).streams h.nextBlk = none ∧
        (writeOut X q xs).gzheaders h.nextBlk = none ∧ (writeOut X q xs).dstates h.nextBlk = none ∧
        (writeOut X q xs).istates h.nextBlk = none ∧ (writeOut X q xs).gzstates h.nextBlk = none) := by
      intro X hx q xs hq
      cases q with
      | null => simpa [writeOut] using hx
      | ref r i =>
        rcases hq r i rfl with ne | ⟨j, rfl⟩
        · obtain ⟨-, t2, t3, t4, t5, t6, t7, -⟩ := writeOut_same_other (H := X) (p := .ref r i) (xs := xs)
            h.nextBlk (fun r' i' hp hb => by simp only [Ptr.ref.injEq] at hp; obtain ⟨rfl, -⟩ := hp; exact ne hb)
          rw [t2, t3, t4, t5, t6, t7]; exact hx
        · obtain ⟨o1, o2, o3, o4, o5, o6⟩ := writeOut_blk_others X j i xs
          rw [o1, o2, o3, o4, o5, o6]; exact hx
    have notKq : ∀ (q : BPtr), (∀ r i, q = .ref r i → ∀ c, BRef.block r = some c → c ≠ h.nextBlk) →
        ∀ r i, q = .ref r i → (BRef.block r ≠ some h.nextBlk ∨ ∃ j, r = .blk j) :=
      fun q qk r i hq => Or.inl (fun hb => qk r i hq _ hb rfl)
    have x'k3 := others _ (others _ (others _ x'k dest out (notKq dest destK)) (cellPtr h) (lengthBytes consumed)
      (fun r i hp => by simp only [cellPtr, Ptr.ref.injEq] at hp; obtain ⟨rfl, -⟩ := hp; exact Or.inr ⟨_, rfl⟩))
      destLen (lengthBytes got) (notKq destLen lenK)
    have gl : ∀ (X : Heap) (q : BPtr) (xs : List UInt8), (writeOut X q xs).nextBlk = X.nextBlk ∧
        (writeOut X q xs).nalloc = X.nalloc := fun X q xs =>
      ⟨(writeOut_globals X q xs).2.2.2.1, (writeOut_globals X q xs).2.2.2.2.1⟩
    have xkE : ¬ (writeOut (writeOut h dest out) destLen (lengthBytes got)).live h.nextBlk := by
      rw [writeOut_live, writeOut_live]; exact k0
    refine ⟨rc, _, cellRun _ sm cellB.1 cellB.2, fun b => absurd b badW, fun _ _ _ => ?_⟩
    refine ⟨out, used, got, writeOut h dest out, _, storeD, storeL,
      same_without_cell sm a3 xkE x'k3 ?_ ?_, unc, ?_, ?_⟩
    · rw [(gl _ _ _).1, (gl _ _ _).1, (gl _ _ _).1, (gl _ _ _).1, (gl _ _ _).1]; simp [cellHeap]
    · rw [(gl _ _ _).2, (gl _ _ _).2, (gl _ _ _).2, (gl _ _ _).2, (gl _ _ _).2]; simp [cellHeap]
    · rcases counts with ⟨g1, -⟩ | ⟨m, o, g, -⟩
      · exact Or.inl g1
      · exact Or.inr ⟨m, o, g⟩
    · intro hm
      obtain ⟨j, lo, hi, bad⟩ := mem' hm
      exact ⟨j, lo, hi, bad⟩

theorem singleWrap_uncompress_z : uncompress_z = singleWrap uncompress2_z := rfl

/-- `int uncompress_z(Bytef *dest, z_size_t *destLen, const Bytef *source, z_size_t sourceLen)`,
from the decoder facts of batch 3 (`DecoderFacts`), which are explicit hypotheses. -/
theorem uncompress_z_of_facts (facts : DecoderFacts) : Goal.uncompress_z := by
  unfold Goal.uncompress_z
  rw [singleWrap_uncompress_z]
  rw [← single_with_uncompressed]
  exact single_of_counted (uncompress2_z_of_facts facts)

end ZlibF.Spec.Public.Proofs.Uncompress
