import ZlibF.Proof.«inflate.c.meaning-prefix-order»
import ZlibF.Proof.«inflate.c.meaning-wrap-steps»

/-!
# inflate.c: the wrapper stages against the format specification

Heap-free. A stage that `WrapParsed` reaches on the consumed bits of a
beginning of a valid stream has an output that begins the stream's decoding,
and the end stage consumed exactly the stream (`wrapParsed_prefix`). The end
stage reached on any input is a stream that zlib accepts
(`wrapParsed_accepted`). These give `meaning_prefix` and `meaning_accepted`.
-/

namespace Zlib.Inflate.Proofs
open C ZlibF.Spec ZlibF.Spec.Proofs
set_option autoImplicit false

/-! ## Bytes and their bits -/

theorem byteBits_length (b : UInt8) : (byteBits b).length = 8 := by simp [byteBits]

theorem byteBits_injective {a b : UInt8} (eq : byteBits a = byteBits b) : a = b := by
  have read := readBits_byteBits a []
  rw [eq, readBits_byteBits] at read
  exact UInt8.toNat.inj (by simpa using read.symm)

theorem bytesToBits_take (l : List UInt8) :
    ∀ k, (bytesToBits l).take (8 * k) = bytesToBits (l.take k) := by
  induction l with
  | nil => intro k; simp [bytesToBits]
  | cons x rest ih =>
    intro k
    cases k with
    | zero => simp [bytesToBits]
    | succ k =>
      have split : bytesToBits (x :: rest) = byteBits x ++ bytesToBits rest := by
        simp [bytesToBits]
      rw [split, show 8 * (k + 1) = (byteBits x).length + 8 * k by simp [byteBits_length]; omega,
        List.take_length_add_append, ih k]
      simp [bytesToBits]

theorem bytesToBits_drop (l : List UInt8) :
    ∀ k, (bytesToBits l).drop (8 * k) = bytesToBits (l.drop k) := by
  induction l with
  | nil => intro k; simp [bytesToBits]
  | cons x rest ih =>
    intro k
    cases k with
    | zero => simp
    | succ k =>
      have split : bytesToBits (x :: rest) = byteBits x ++ bytesToBits rest := by
        simp [bytesToBits]
      rw [split, show 8 * (k + 1) = (byteBits x).length + 8 * k by simp [byteBits_length]; omega,
        List.drop_length_add_append, ih k]
      simp

theorem bytesToBits_injective : ∀ {a b : List UInt8}, bytesToBits a = bytesToBits b → a = b
  | [], [], _ => rfl
  | [], y :: _, eq => by simp [bytesToBits, byteBits] at eq
  | x :: _, [], eq => by simp [bytesToBits, byteBits] at eq
  | x :: a, y :: b, eq => by
    have split : ∀ (z : UInt8) (l : List UInt8), bytesToBits (z :: l) = byteBits z ++ bytesToBits l :=
      fun _ _ => by simp [bytesToBits]
    rw [split, split] at eq
    obtain ⟨first, rest⟩ := List.append_inj eq (by simp [byteBits_length])
    rw [byteBits_injective first, bytesToBits_injective rest]

theorem bytesToBits_prefix_iff {a b : List UInt8} : bytesToBits a <+: bytesToBits b ↔ a <+: b := by
  constructor
  · intro pre
    rw [List.prefix_iff_eq_take] at pre ⊢
    rw [bytesToBits_length', bytesToBits_take] at pre
    exact bytesToBits_injective pre
  · rintro ⟨t, rfl⟩
    exact ⟨bytesToBits t, (bytesToBits_append' a t).symm⟩

/-- Bits between two byte strings that end on a byte boundary are the bits of
the bytes between them. -/
theorem bytesToBits_middle {input a c : List UInt8} {X : List Bool}
    (eq : bytesToBits input = bytesToBits a ++ X ++ bytesToBits c) (aligned : X.length % 8 = 0) :
    ∃ m, input = a ++ m ++ c ∧ X = bytesToBits m := by
  have lengths := congrArg List.length eq
  simp only [List.length_append, bytesToBits_length'] at lengths
  obtain ⟨k, hk⟩ : ∃ k, X.length = 8 * k := ⟨X.length / 8, by omega⟩
  have dropA := congrArg (fun l => l.drop (8 * a.length)) eq
  simp only [bytesToBits_drop, List.append_assoc] at dropA
  rw [List.drop_left' (by rw [bytesToBits_length'])] at dropA
  have takeK := congrArg (fun l => l.take (8 * k)) dropA
  simp only [bytesToBits_take] at takeK
  rw [List.take_left' hk] at takeK
  have dropK := congrArg (fun l => l.drop (8 * k)) dropA
  simp only [bytesToBits_drop] at dropK
  rw [List.drop_left' hk] at dropK
  have takeA := congrArg (fun l => l.take (8 * a.length)) eq
  simp only [bytesToBits_take, List.append_assoc] at takeA
  rw [List.take_left' (by rw [bytesToBits_length'])] at takeA
  refine ⟨(input.drop a.length).take k, ?_, takeK.symm⟩
  have first := bytesToBits_injective takeA
  have last := bytesToBits_injective dropK
  calc input = input.take a.length ++
        ((input.drop a.length).take k ++ (input.drop a.length).drop k) := by
          rw [List.take_append_drop, List.take_append_drop]
    _ = a ++ (input.drop a.length).take k ++ c := by rw [first, last]; simp

/-! ## The end stage is an accepted stream -/

/-- The deflate part of an end stage is `Deflate.Prefix` with the trailer. -/
theorem done_deflate_prefix {bodyDict : List UInt8} {dbits pad : List Bool} {out m T : List UInt8}
    (parsed : DeflateParsed bodyDict dbits ⟨out, true, .finished⟩)
    (padLength : pad.length = (8 - dbits.length % 8) % 8) (middle : bytesToBits m = dbits ++ pad) :
    Deflate.Prefix bodyDict (m ++ T) T out := by
  have aligned : (dbits ++ (pad ++ bytesToBits T)).length % 8 = 0 := by
    simp only [List.length_append, bytesToBits_length']
    omega
  refine ⟨pad ++ bytesToBits T, ?_, ?_⟩
  · rw [bytesToBits_append', middle, List.append_assoc]
    exact deflateParsed_blocks parsed aligned
  · exact stored_drop_pad (by omega) (by rw [bytesToBits_length']; omega)

theorem zlibHeader_not_gzip {configured : Nat} {dict header : List UInt8} {window : Nat}
    (zlib : ZlibHeader configured dict header window) : ¬ IsGzipHeader header := by
  obtain ⟨cmf, flg, ⟨method, _⟩, _, _, shape⟩ := zlib
  intro magic
  have first : header.take 2 = [cmf, flg] := by
    rcases shape with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp
  unfold IsGzipHeader at magic
  rw [first] at magic
  simp at magic
  rw [magic.1] at method
  simp at method

theorem gzipHeader_is_gzip {header : List UInt8} (gzip : GzipHeader header) : IsGzipHeader header := by
  obtain ⟨flg, mt, xfl, os, ex, nm, cm, _, _, _, _, _, rfl⟩ := gzip
  simp [IsGzipHeader, Gzip.header]

/-- The end stage reached on all of `input` (nothing held): `input` is a
stream that inflate accepts in the configuration. -/
theorem wrapParsed_accepted {wrap : Api.Wrap} {configured : Nat} {dict input out : List UInt8}
    {consumed : List Bool} (parsed : WrapParsed wrap configured dict consumed (.done out))
    (bits : bytesToBits input = consumed) :
    Api.Layer.InflateAccepted wrap configured dict input out := by
  obtain ⟨header, bodyDict, dbits, pad, wrapHeader, dparsed, padLength, rfl⟩ := parsed
  obtain ⟨m, inputEq, middle⟩ := bytesToBits_middle (X := dbits ++ pad)
    (by simpa [List.append_assoc] using bits)
    (by simp only [List.length_append]; omega)
  have deflate := done_deflate_prefix (T := WrapTrailer wrap header out) dparsed padLength middle.symm
  subst inputEq
  have zlibCase : ∀ window, ZlibHeader configured dict header window →
      bodyDict = (if header.length = 2 then [] else bodyDictionary window dict) →
      WrapTrailer wrap header out = be32 (adler32 out).toNat →
      Zlib.DecodesWithWindow configured dict (header ++ m ++ WrapTrailer wrap header out) out ∧
        Api.ZlibFits configured (header ++ m ++ WrapTrailer wrap header out) := by
    intro window zlib dictEq trailer
    obtain ⟨cmf, flg, ok, fits, windowEq, shape⟩ := zlib
    rw [trailer] at deflate ⊢
    have fitsAll : Api.ZlibFits configured
        (header ++ m ++ be32 (adler32 out).toNat) := by
      rcases fits with zero | ⟨c, head, small⟩
      · exact Or.inl zero
      · refine Or.inr ⟨c, ?_, small⟩
        rcases shape with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simpa using head
    refine ⟨?_, fitsAll⟩
    rcases shape with ⟨plain, rfl⟩ | ⟨fdict, rfl⟩
    · simp only [List.length_cons, List.length_nil, ↓reduceIte] at dictEq
      subst dictEq
      refine ⟨cmf, flg, [], m ++ be32 (adler32 out).toNat, by simp, ok, fun _ => ⟨rfl, deflate⟩,
        fun bad => by omega⟩
    · have long : ([cmf, flg] ++ be32 (adler32 dict).toNat).length ≠ 2 := by simp [be32]
      simp only [long, ↓reduceIte] at dictEq
      subst dictEq windowEq
      refine ⟨cmf, flg, be32 (adler32 dict).toNat, m ++ be32 (adler32 out).toNat, by simp, ok,
        fun bad => by omega, fun _ => ⟨rfl, deflate⟩⟩
  have gzipCase : GzipHeader header → bodyDict = [] →
      WrapTrailer wrap header out = le32 (crc32 out).toNat ++ le32 (out.length % 2 ^ 32) →
      Gzip.Decodes (header ++ m ++ WrapTrailer wrap header out) out := by
    intro gzip dictEq trailer
    subst dictEq
    rw [trailer] at deflate ⊢
    obtain ⟨flg, mt, xfl, os, ex, nm, cm, small, mtLength, exLimit, nmOk, cmOk, rfl⟩ := gzip
    exact ⟨flg, mt, xfl, os, ex, nm, cm, m ++ (le32 (crc32 out).toNat ++ le32 (out.length % 2 ^ 32)),
      small, mtLength, exLimit, nmOk, cmOk, by simp [List.append_assoc], deflate⟩
  cases wrap with
  | raw =>
    obtain ⟨rfl, rfl⟩ := wrapHeader
    simpa [WrapTrailer, Api.Layer.InflateAccepted, Api.Layer.Decodes, Deflate.Decodes,
      bodyDictionary] using deflate
  | zlib =>
    obtain ⟨window, zlib, dictEq⟩ := wrapHeader
    exact zlibCase window zlib dictEq rfl
  | gzip =>
    obtain ⟨gzip, dictEq⟩ := wrapHeader
    exact gzipCase gzip dictEq rfl
  | auto =>
    rcases wrapHeader with ⟨window, zlib, dictEq⟩ | ⟨gzip, dictEq⟩
    · have notGzip := zlibHeader_not_gzip zlib
      exact Or.inl (zlibCase window zlib dictEq (by simp [WrapTrailer, IsGzipHeader] at notGzip ⊢; simp [notGzip]))
    · have isGzip := gzipHeader_is_gzip gzip
      exact Or.inr (gzipCase gzip dictEq (by simp [WrapTrailer, IsGzipHeader] at isGzip ⊢; simp [isGzip]))

#print axioms wrapParsed_accepted

/-! ## A larger dictionary decodes a valid stream the same way -/

theorem copyBack_dict_suffix {big small p : List UInt8} (eq : big = p ++ small) (dist : Nat) :
    ∀ (n : Nat) (h : List UInt8), dist ≤ (small ++ h).length →
      copyBack big dist n h = copyBack small dist n h
  | 0, _, _ => rfl
  | n + 1, h, bound => by
    have same : (big ++ h).getD ((big ++ h).length - dist) 0 =
        (small ++ h).getD ((small ++ h).length - dist) 0 := by
      subst eq
      rw [List.append_assoc, List.length_append,
        show p.length + (small ++ h).length - dist = p.length + ((small ++ h).length - dist) by omega]
      simp only [List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
    simp only [copyBack]
    rw [same]
    exact copyBack_dict_suffix eq dist n _ (Nat.le_trans bound (by simp))

theorem _root_.ZlibF.Spec.Symbols.dict_suffix {L D : List Nat} {big small p : List UInt8} (eq : big = p ++ small)
    {h : List UInt8} {inp rest : List Bool} {out : List UInt8}
    (parse : Symbols L D small h inp rest out) : Symbols L D big h inp rest out := by
  induction parse with
  | eob d => exact .eob d
  | lit d lt _ ih => exact .lit d lt ih
  | @copy h inp r1 r2 r3 r4 rest s dsym xl xd out d lo hi x e ds y bound _ ih =>
    have bound' : xd + distBases.getD dsym 0 ≤ (big ++ h).length := by
      subst eq
      simp only [List.length_append] at bound ⊢
      omega
    refine .copy d lo hi x e ds y bound' ?_
    rw [copyBack_dict_suffix eq _ _ _ (by omega)]
    exact ih

theorem _root_.ZlibF.Spec.Body.dict_suffix {big small p : List UInt8} (eq : big = p ++ small) {bt : Nat}
    {h : List UInt8} {inp rest : List Bool} {out : List UInt8}
    (parse : Body small bt h inp rest out) : Body big bt h inp rest out := by
  cases parse with
  | stored one two comp bytes => exact .stored one two comp bytes
  | fixed symbols => exact .fixed (symbols.dict_suffix eq)
  | dynamic f1 f2 f3 counts f4 acc codeLens eob accL accD symbols =>
    exact .dynamic f1 f2 f3 counts f4 acc codeLens eob accL accD (symbols.dict_suffix eq)

theorem _root_.ZlibF.Spec.Blocks.dict_suffix {big small p : List UInt8} (eq : big = p ++ small)
    {h : List UInt8} {inp rest : List Bool} {out : List UInt8}
    (parse : Blocks small h inp rest out) : Blocks big h inp rest out := by
  induction parse with
  | last one two body => exact .last one two (body.dict_suffix eq)
  | more one two body _ ih => exact .more one two (body.dict_suffix eq) ih

/-- The last `small` bytes of a dictionary are a suffix of its last `big` bytes. -/
theorem drop_suffix (dict : List UInt8) {small big : Nat} (le : small ≤ big) :
    ∃ p, dict.drop (dict.length - big) = p ++ dict.drop (dict.length - small) := by
  refine ⟨(dict.drop (dict.length - big)).take ((dict.length - small) - (dict.length - big)), ?_⟩
  have tailEq : dict.drop (dict.length - small) =
      (dict.drop (dict.length - big)).drop ((dict.length - small) - (dict.length - big)) := by
    rw [List.drop_drop]
    congr 1
    omega
  rw [tailEq, List.take_append_drop]

#print axioms ZlibF.Spec.Blocks.dict_suffix

/-! ## The header of a stage is the header of a valid stream it begins -/

theorem zlib_source_split {configured : Nat} {dict header source decoded : List UInt8}
    {window : Nat} (zlib : ZlibHeader configured dict header window)
    (valid : Zlib.Decodes dict source decoded) (pre : header <+: source) :
    ∃ s small p, source = header ++ s ∧
      (if header.length = 2 then [] else bodyDictionary window dict) = p ++ small ∧
      Deflate.Prefix small s (be32 (adler32 decoded).toNat) decoded := by
  obtain ⟨cmf, flg, ok, fits, windowEq, shape⟩ := zlib
  obtain ⟨cmf', flg', pre', s, rfl, _, plainCase, fdictCase⟩ := valid
  have same : cmf = cmf' ∧ flg = flg' := by
    obtain ⟨t, eq⟩ := pre
    rcases shape with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp at eq <;> exact ⟨eq.1, eq.2.1⟩
  obtain ⟨rfl, rfl⟩ := same
  rcases shape with ⟨plain, rfl⟩ | ⟨fdict, rfl⟩
  · obtain ⟨rfl, deflatePrefix⟩ := plainCase plain
    exact ⟨s, [], [], by simp, by simp, deflatePrefix⟩
  · obtain ⟨rfl, deflatePrefix⟩ := fdictCase fdict
    have le : Zlib.windowSize cmf ≤ window := by
      rw [windowEq]
      split
      · exact Nat.le_refl _
      · rcases fits with zero | ⟨c, head, small⟩
        · contradiction
        · simp at head
          subst head
          unfold Zlib.windowSize
          exact Nat.pow_le_pow_right (by decide) small
    obtain ⟨p, eq⟩ := drop_suffix dict le
    refine ⟨s, _, p, by simp, ?_, deflatePrefix⟩
    have long : ([cmf, flg] ++ be32 (adler32 dict).toNat).length ≠ 2 := by simp [be32]
    simp only [long, ↓reduceIte, bodyDictionary]
    exact eq

theorem gzip_source_split {header source decoded : List UInt8} (gzip : GzipHeader header)
    (valid : Gzip.Decodes source decoded) (pre : header <+: source) :
    ∃ s, source = header ++ s ∧
      Deflate.Prefix [] s (le32 (crc32 decoded).toNat ++ le32 (decoded.length % 2 ^ 32)) decoded := by
  obtain ⟨flg, mt, xfl, os, ex, nm, cm, small, mtLength, exLimit, nmOk, cmOk, rfl⟩ := gzip
  obtain ⟨flg', mt', xfl', os', ex', nm', cm', s, small', mtLength', exLimit', nmOk', cmOk',
    rfl, deflatePrefix⟩ := valid
  obtain ⟨t, eq⟩ := pre
  have sameFlags : flg' = flg := by
    have := congrArg (fun l => l.getD 3 0) eq
    simpa [Gzip.header] using this.symm
  subst sameFlags
  have core := PU_HdrSet flg' _ _ _ _
    (header_mem flg' mt xfl os ex nm cm mtLength exLimit nmOk cmOk)
    (header_mem flg' mt' xfl' os' ex' nm' cm' mtLength' exLimit' nmOk' cmOk')
    (by simpa [List.append_assoc] using eq)
  refine ⟨s, ?_, deflatePrefix⟩
  rw [core]

theorem source_split {wrap : Api.Wrap} {configured : Nat} {dict header bodyDict source decoded :
    List UInt8} (wrapHeader : WrapHeader wrap configured dict header bodyDict)
    (valid : Api.Layer.Decodes wrap configured dict source decoded) (pre : header <+: source) :
    ∃ s small p, source = header ++ s ∧ bodyDict = p ++ small ∧
      Deflate.Prefix small s (WrapTrailer wrap header decoded) decoded := by
  cases wrap with
  | raw =>
    obtain ⟨rfl, rfl⟩ := wrapHeader
    exact ⟨source, bodyDictionary (2 ^ configured) dict, [], by simp, by simp,
      by simpa [WrapTrailer, Api.Layer.Decodes, Deflate.Decodes, bodyDictionary] using valid⟩
  | zlib =>
    obtain ⟨window, zlib, rfl⟩ := wrapHeader
    exact zlib_source_split zlib valid.1 pre
  | gzip =>
    obtain ⟨gzip, rfl⟩ := wrapHeader
    obtain ⟨s, eq, deflatePrefix⟩ := gzip_source_split gzip valid pre
    exact ⟨s, [], [], eq, rfl, deflatePrefix⟩
  | auto =>
    have zlibFirst : ∀ (c : UInt8) (rest : List UInt8), Zlib.Decodes dict (c :: rest) decoded →
        c ≠ 31 := by
      rintro c rest ⟨cmf, flg, _, _, eq, ⟨method, _⟩, _⟩ rfl
      simp at eq
      rw [← eq.1] at method
      simp at method
    rcases wrapHeader with ⟨window, zlib, rfl⟩ | ⟨gzip, rfl⟩
    · have notGzip := zlibHeader_not_gzip zlib
      rcases valid with ⟨member, _⟩ | member
      · obtain ⟨s, small, p, eq, dictEq, deflatePrefix⟩ := zlib_source_split zlib member pre
        exact ⟨s, small, p, eq, dictEq, by simpa [WrapTrailer, notGzip] using deflatePrefix⟩
      · exfalso
        obtain ⟨H, tail, full, rfl⟩ := gzipDecodes_header member
        obtain ⟨cmf, flg, ⟨method, _⟩, _, _, shape⟩ := zlib
        have first : header.headD 0 = cmf := by rcases shape with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> rfl
        obtain ⟨t, eq⟩ := pre
        obtain ⟨flg', mt, xfl, os, ex, nm, cm, _, rfl⟩ := full
        have := congrArg (fun l => l.headD 0) eq
        rcases shape with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp [Gzip.header] at this <;> rw [this] at method <;>
          simp at method
    · have isGzip := gzipHeader_is_gzip gzip
      rcases valid with ⟨member, _⟩ | member
      · exfalso
        obtain ⟨t, eq⟩ := pre
        obtain ⟨flg, mt, xfl, os, ex, nm, cm, _, _, _, _, _, rfl⟩ := gzip
        rw [← eq] at member
        exact zlibFirst 31 _ (by simpa [Gzip.header] using member) rfl
      · obtain ⟨s, eq, deflatePrefix⟩ := gzip_source_split gzip member pre
        exact ⟨s, [], [], eq, rfl, by simpa [WrapTrailer, isGzip] using deflatePrefix⟩

#print axioms source_split

/-! ## On a beginning of a valid stream -/

/-- The deflate bits of a stage that a valid stream begins continue to the
stream's deflate data, on the larger dictionary. -/
theorem body_on_source {wrap : Api.Wrap} {configured : Nat}
    {dict header bodyDict input source decoded : List UInt8} {dbits rest : List Bool}
    (wrapHeader : WrapHeader wrap configured dict header bodyDict)
    (valid : Api.Layer.Decodes wrap configured dict source decoded) (started : input <+: source)
    (bits : bytesToBits input = bytesToBits header ++ dbits ++ rest) :
    ∃ more tail, (dbits ++ more).length % 8 = 0 ∧
      bytesToBits source = bytesToBits header ++ (dbits ++ more) ∧
      Blocks bodyDict [] (dbits ++ more) tail decoded ∧
      tail.drop (tail.length % 8) = bytesToBits (WrapTrailer wrap header decoded) := by
  have headerPre : header <+: source := by
    rw [← bytesToBits_prefix_iff]
    exact List.IsPrefix.trans (⟨dbits ++ rest, by rw [bits]; simp [List.append_assoc]⟩ :
      bytesToBits header <+: bytesToBits input) (bytesToBits_prefix_iff.mpr started)
  obtain ⟨s, small, p, rfl, dictEq, ⟨tail, blocks, trailer⟩⟩ := source_split wrapHeader valid headerPre
  have inner : dbits <+: bytesToBits s := by
    have whole : bytesToBits header ++ dbits <+: bytesToBits header ++ bytesToBits s := by
      rw [← bytesToBits_append']
      exact List.IsPrefix.trans (⟨rest, by rw [bits]⟩ : bytesToBits header ++ dbits <+:
        bytesToBits input) (bytesToBits_prefix_iff.mpr started)
    exact (List.prefix_append_right_inj _).mp whole
  obtain ⟨more, moreEq⟩ := inner
  refine ⟨more, tail, by rw [moreEq, bytesToBits_length']; omega,
    by rw [bytesToBits_append', moreEq], ?_, trailer⟩
  rw [moreEq]
  exact blocks.dict_suffix dictEq

/-- A stage reached on a beginning of a valid stream: its output begins the
decoding, and the end stage with nothing held consumed exactly the stream. -/
theorem wrapParsed_prefix {wrap : Api.Wrap} {configured : Nat} {dict input source decoded :
    List UInt8} {consumed held : List Bool} {stage : WrapStage}
    (parsed : WrapParsed wrap configured dict consumed stage)
    (bits : bytesToBits input = consumed ++ held)
    (valid : Api.Layer.Decodes wrap configured dict source decoded) (started : input <+: source) :
    stage.output <+: decoded ∧
      (∀ out, stage = .done out → held = [] → input = source ∧ out = decoded) := by
  cases stage with
  | header bytes => exact ⟨List.nil_prefix, fun _ eq => by cases eq⟩
  | needDict header => exact ⟨List.nil_prefix, fun _ eq => by cases eq⟩
  | body header pos =>
    obtain ⟨bodyDict, dbits, wrapHeader, rfl, dparsed⟩ := parsed
    obtain ⟨more, tail, aligned, _, blocks, _⟩ :=
      body_on_source wrapHeader valid started (rest := held) (by rw [bits])
    exact ⟨deflateParsed_output dparsed aligned blocks, fun _ eq => by cases eq⟩
  | trailer header out bytes =>
    obtain ⟨bodyDict, dbits, pad, wrapHeader, dparsed, _, _, _, _, rfl⟩ := parsed
    obtain ⟨more, tail, aligned, _, blocks, _⟩ :=
      body_on_source (dbits := dbits) wrapHeader valid started (rest := pad ++ bytesToBits bytes ++ held)
        (by rw [bits]; simp [List.append_assoc])
    obtain ⟨_, outEq⟩ := deflateParsed_finished dparsed aligned blocks
    exact ⟨by rw [outEq]; exact List.prefix_refl _, fun _ eq => by cases eq⟩
  | done out =>
    obtain ⟨header, bodyDict, dbits, pad, wrapHeader, dparsed, padLength, rfl⟩ := parsed
    obtain ⟨more, tail, aligned, sourceBits, blocks, trailer⟩ :=
      body_on_source (dbits := dbits) wrapHeader valid started
        (rest := pad ++ bytesToBits (WrapTrailer wrap header out) ++ held)
        (by rw [bits]; simp [List.append_assoc])
    obtain ⟨moreTail, outEq⟩ := deflateParsed_finished dparsed aligned blocks
    subst moreTail outEq
    refine ⟨List.prefix_refl _, fun _ eq empty => ⟨?_, by cases eq; rfl⟩⟩
    subst empty
    have tailLength : more.length % 8 = pad.length := by
      simp only [List.length_append] at aligned
      omega
    have moreSplit : more = more.take pad.length ++ bytesToBits (WrapTrailer wrap header out) := by
      rw [← trailer, tailLength, List.take_append_drop]
    apply List.IsPrefix.eq_of_length started
    have lengths := congrArg List.length bits
    have sourceLengths := congrArg List.length sourceBits
    have moreLength := congrArg List.length moreSplit
    simp only [List.length_append, bytesToBits_length', List.length_take, List.append_nil]
      at lengths sourceLengths moreLength
    have : more.length ≥ pad.length := by omega
    rw [Nat.min_eq_left this] at moreLength
    omega

#print axioms wrapParsed_prefix

end Zlib.Inflate.Proofs
