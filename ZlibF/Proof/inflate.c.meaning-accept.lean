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

end Zlib.Inflate.Proofs
