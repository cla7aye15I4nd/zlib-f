import ZlibF.Proof.«inflate.c.meaning-format»
import ZlibF.Proof.«inflate.c.history-invariant»

/-!
# inflate.c: the format meaning is kept when the heap keeps what the state points to

`StageMatches` and `WrapMatches` read the heap only through the decoding
tables the state points to and its window (`SameRefs`). A caller rebuffer
keeps both, so it keeps `ParseMeaning` (`meaning_rebuffer`).
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The heap `after` agrees with `h` on the tables and the window of `s`. -/
structure SameRefs (h after : Heap) (s : InflateState) : Prop where
  codes : ∀ (ref : CodeRef) (offset : Nat), (s.lencode = .ref ref offset ∨ s.distcode = .ref ref offset) →
    (Space.get after ref : Option (Array Code)) = Space.get h ref
  window : ∀ (ref : BRef) (offset : Nat), s.window = .ref ref offset →
    (Space.get after ref : Option (Array UInt8)) = Space.get h ref

theorem TableMeaning.frameRefs {h after : Heap} {s : InflateState} (same : SameRefs h after s)
    {pointer : CodePtr} (which : pointer = s.lencode ∨ pointer = s.distcode) {root type : UInt32}
    {lens : List Nat} (meaning : TableMeaning h pointer root type lens) :
    TableMeaning after pointer root type lens := by
  obtain ⟨ref, offset, codes, used, rfl, get, rest⟩ := meaning
  refine ⟨ref, offset, codes, used, rfl, ?_, rest⟩
  rw [same.codes ref offset (by rcases which with eq | eq <;> simp [eq])]
  exact get

theorem DynamicMatches.frameRefs {h after : Heap} {s : InflateState} (same : SameRefs h after s)
    {header : List Bool} (meaning : DynamicMatches h s header) : DynamicMatches after s header := by
  rcases meaning with table | ⟨hlit, hdist, hclen, r1, r2, r3, e1, e2, e3, counts, nlen, ndist,
    ncode, lenlens | ⟨mode, cl, r4, ref, offset, codes, read, pointer, get, rest⟩⟩
  · exact Or.inl table
  · exact Or.inr ⟨hlit, hdist, hclen, r1, r2, r3, e1, e2, e3, counts, nlen, ndist, ncode,
      Or.inl lenlens⟩
  · refine Or.inr ⟨hlit, hdist, hclen, r1, r2, r3, e1, e2, e3, counts, nlen, ndist, ncode,
      Or.inr ⟨mode, cl, r4, ref, offset, codes, read, pointer, ?_, rest⟩⟩
    rw [same.codes ref offset (Or.inl pointer)]
    exact get

theorem InflateDictionary.frameRefs {h after : Heap} {s : InflateState} (same : SameRefs h after s)
    {xs : List UInt8} (meaning : InflateDictionary h s xs) : InflateDictionary after s xs := by
  rcases meaning with empty | ⟨ref, off, a, pointer, get, rest⟩
  · exact Or.inl empty
  · refine Or.inr ⟨ref, off, a, pointer, ?_, rest⟩
    rw [same.window ref off pointer]
    exact get

theorem WindowMeaning.frameRefs {h after : Heap} {s : InflateState} (same : SameRefs h after s)
    {dict out : List UInt8} (meaning : WindowMeaning h s dict out) : WindowMeaning after s dict out := by
  rcases meaning with ⟨size, dictionary⟩ | none
  · exact Or.inl ⟨size, InflateDictionary.frameRefs same dictionary⟩
  · exact Or.inr none

theorem BodyMatches.frameRefs {h after : Heap} {s : InflateState} (same : SameRefs h after s)
    {pos : DeflatePos} (meaning : BodyMatches h s pos) : BodyMatches after s pos := by
  obtain ⟨out, final, stage⟩ := pos
  cases stage with
  | boundary => exact meaning
  | storedHeader => exact meaning
  | stored remaining => exact meaning
  | dynamicHeader header =>
    obtain ⟨dynamic, last⟩ := meaning
    exact ⟨dynamic.frameRefs same, last⟩
  | codes L D pending =>
    obtain ⟨last, lengths, distances, modes⟩ := meaning
    exact ⟨last, lengths.frameRefs same (Or.inl rfl), distances.frameRefs same (Or.inr rfl), modes⟩
  | finished => exact meaning

theorem StageMatches.frameRefs {h after : Heap} {s : InflateState} (same : SameRefs h after s)
    {wrap : Api.Wrap} {dict : List UInt8} {stage : WrapStage}
    (meaning : StageMatches h s wrap dict stage) : StageMatches after s wrap dict stage := by
  cases stage with
  | body header pos =>
    obtain ⟨body, window, check⟩ := meaning
    exact ⟨body.frameRefs same, window.frameRefs same, check⟩
  | _ => exact meaning

theorem WrapMatches.frameRefs {h after : Heap} {s : InflateState} (same : SameRefs h after s)
    {wrap : Api.Wrap} {configured : Nat} {dict : List UInt8} {stage : WrapStage}
    (meaning : WrapMatches h s wrap configured dict stage) :
    WrapMatches after s wrap configured dict stage := by
  cases stage with
  | header bytes =>
    obtain ⟨headerMatches, window, used⟩ := meaning
    exact ⟨headerMatches, window.frameRefs same, used⟩
  | needDict header =>
    obtain ⟨check, flags, bits, width, empty, installed⟩ := meaning
    exact ⟨check, flags, bits, width, empty, fun have_ => ⟨(installed have_).1,
      (installed have_).2.frameRefs same⟩⟩
  | _ => exact meaning

/-- A caller rebuffer keeps the tables and the window of the state. -/
theorem rebuffer_sameRefs {h after : Heap} {r : ZStreamRef} {i : Nat} {z : ZStream}
    {s : InflateState} (inv : InflateInv h r i z s) (edit : Rebuffer h after r) :
    SameRefs h after s := by
  have editCopy := edit
  obtain ⟨_, _, _, frame, _⟩ := editCopy
  obtain ⟨statics, _, _, _, _, objects⟩ := frame
  have owned : StreamOwned h r i :=
    ⟨z, inv.good.live.hz, Or.inl ⟨i, s, inv.good.live.zst, inv.good.live.hs, Or.inl rfl⟩⟩
  have live : h.live i := by simp [Heap.live, inv.good.live.hs]
  have state : after.istates i = h.istates i :=
    (objects i live (fun unowned => unowned owned)).2.2.2.2.2.1
  have codeRef : ∀ ref : CodeRef, (ref = .istate_codes i ∨ ref = .st_lenfix ∨ ref = .st_distfix) →
      (Space.get after ref : Option (Array Code)) = Space.get h ref := by
    rintro ref (rfl | rfl | rfl)
    · simp [Space.get, state]
    · simp [Space.get, statics]
    · simp [Space.get, statics]
  constructor
  · intro ref offset pointer
    apply codeRef
    rcases inv.good.inv.ptr.2 with ⟨a, b, len, dist, _, _⟩ | ⟨len, dist⟩
    · rcases pointer with eq | eq
      · rw [len] at eq; cases eq; exact Or.inl rfl
      · rw [dist] at eq; cases eq; exact Or.inl rfl
    · rcases pointer with eq | eq
      · rw [len] at eq; cases eq; exact Or.inr (Or.inl rfl)
      · rw [dist] at eq; cases eq; exact Or.inr (Or.inr rfl)
  · intro ref offset pointer
    rcases inv.good.inv.win.block with null | ⟨b, array, windowEq, _, _, _⟩
    · rw [null] at pointer; cases pointer
    · rw [windowEq] at pointer
      cases pointer
      have kept := rebuffer_inflate_owned inv.good edit (Or.inr windowEq)
      simp [Space.get, kept.1]

/-- A caller rebuffer keeps the format meaning (statement as on
`skeleton/inflate`). -/
theorem meaning_rebuffer {h after : Heap} {r : ZStreamRef} {wb : Int32} {log : DataLog}
    {pending : Bool} (current : ParseMeaning wb r h log pending) (edit : Rebuffer h after r) :
    ParseMeaning wb r after log pending := by
  obtain ⟨wrap, configured, i, z, s, params, inv, config, dataError, ended, bad, memory,
    stageClause⟩ :=
    current
  obtain ⟨z', inv'⟩ := rebuffer_invariant inv edit
  have same := rebuffer_sameRefs inv edit
  refine ⟨wrap, configured, i, z', s, params, inv', config, dataError, ended, bad, memory, ?_⟩
  intro single notBad notMem notSync
  obtain ⟨consumed, held, stage, inputBits, heldBits, parsed, stageMatches, wrapMatches, outputEq,
    request⟩ := stageClause single notBad notMem notSync
  exact ⟨consumed, held, stage, inputBits, heldBits, parsed, stageMatches.frameRefs same,
    wrapMatches.frameRefs same, outputEq, request⟩

#print axioms rebuffer_sameRefs
#print axioms meaning_rebuffer

end Zlib.Inflate.Proofs
