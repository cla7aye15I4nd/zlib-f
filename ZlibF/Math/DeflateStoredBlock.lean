import ZlibF.Math.DeflateRunDecode
import Init.Data.UInt.Bitwise

/-! # Stored-byte output satisfies the independent block grammar -/

namespace Zlib.Trees.Proofs.Out
open C ZlibF.Spec
set_option autoImplicit false

/-- Whole-byte encoding has the exact length used by stored alignment. -/
theorem stored_bytes_length (bytes : List UInt8) : (bytesToBits bytes).length = 8 * bytes.length := by
  induction bytes with
  | nil => rfl
  | cons byte bytes ih =>
    simp only [bytesToBits, List.flatMap_cons, List.length_append, byteBits, List.length_map,
      List.length_range, List.length_cons] at ih ⊢
    omega

/-- Independent byte reading recovers every emitted source byte and the
unchanged trailing suffix. -/
theorem readBytes_encoded (bytes : List UInt8) (suffix : List Bool) :
    readBytes bytes.length (bytesToBits bytes ++ suffix) = some (bytes, suffix) := by
  induction bytes with
  | nil => rfl
  | cons byte bytes ih =>
    change readBytes (bytes.length + 1) ((natBits byte.toNat 8 ++ bytesToBits bytes) ++ suffix) = _
    rw [List.append_assoc]
    simp only [readBytes, readBits_natBits 8 byte.toNat _ byte.toNat_lt, ih, UInt8.ofNat_toNat]

def storedBodyBits (padding : Nat) (bytes : List UInt8) : List Bool :=
  List.replicate padding false ++ natBits bytes.length 16 ++
    natBits (65535 - bytes.length) 16 ++ bytesToBits bytes

/-- Stored bodies end at a byte boundary. The remaining complete stream
therefore has byte-multiple length; this explicit condition makes the
independent grammar's alignment skip agree with the emitted padding. -/
theorem stored_body_grammar (history bytes : List UInt8) (padding : Nat) (suffix : List Bool)
    (small : bytes.length < 65536) (pad : padding < 8) (aligned : suffix.length % 8 = 0) :
    Body [] 0 history (storedBodyBits padding bytes ++ suffix) suffix (history ++ bytes) := by
  have skip : (storedBodyBits padding bytes ++ suffix).length % 8 = padding := by
    simp only [storedBodyBits, List.length_append, List.length_replicate, natBits_length, stored_bytes_length]
    omega
  have drop : (storedBodyBits padding bytes ++ suffix).drop
        ((storedBodyBits padding bytes ++ suffix).length % 8) =
      natBits bytes.length 16 ++ natBits (65535 - bytes.length) 16 ++ bytesToBits bytes ++ suffix := by
    rw [skip]
    simp only [storedBodyBits, List.append_assoc, List.drop_append_of_le_length
      (show padding ≤ (List.replicate padding false).length by simp),
      List.length_replicate, List.drop_replicate, Nat.sub_self, List.replicate_zero, List.nil_append]
  refine Body.stored (len := bytes.length) (nlen := 65535 - bytes.length)
    (r1 := natBits (65535 - bytes.length) 16 ++ (bytesToBits bytes ++ suffix))
    (r2 := bytesToBits bytes ++ suffix) ?_ ?_ rfl ?_
  · rw [drop, List.append_assoc, List.append_assoc]
    exact readBits_natBits 16 bytes.length _ small
  · exact readBits_natBits 16 (65535 - bytes.length) _ (by omega)
  · exact readBytes_encoded bytes suffix

theorem stored_length_words (length : UInt64) (small : length.toNat < 65536) :
    length.toUInt16.toNat = length.toNat ∧ (~~~length).toUInt16.toNat = 65535 - length.toNat := by
  have low : length.toUInt16.toNat = length.toNat := by
    rw [UInt64.toNat_toUInt16, Nat.mod_eq_of_lt small]
  refine ⟨low, ?_⟩
  rw [UInt64.toUInt16_not, UInt16.toNat_not, low]
  rfl

/-- BFINAL and BTYPE = 0 in the stored writer's low-bit order. -/
def storedTag (last : Bool) : List Bool := natBits (if last then 1 else 0) 3

theorem storedTag_wire (last : Bool) :
    storedTag last = natBits (if last then 1 else 0) 1 ++ natBits 0 2 := by
  cases last <;> decide +kernel

/-- A final stored block accepts the exact source bytes and retains an
aligned trailer suffix. No symbol-decoder premise is involved. -/
theorem stored_last_grammar (history bytes : List UInt8) (padding : Nat) (suffix : List Bool)
    (small : bytes.length < 65536) (pad : padding < 8) (aligned : suffix.length % 8 = 0) :
    Blocks [] history ((storedTag true ++ storedBodyBits padding bytes) ++ suffix) suffix (history ++ bytes) := by
  rw [storedTag_wire, List.append_assoc, List.append_assoc]
  exact Blocks.last (readBits_natBits 1 1 _ (by decide +kernel))
    (readBits_natBits 2 0 _ (by decide +kernel)) (stored_body_grammar history bytes padding suffix small pad aligned)

/-- A non-final stored block composes with its actual aligned continuation. -/
theorem stored_more_grammar {history out : List UInt8} (bytes : List UInt8) (padding : Nat)
    {suffix rest : List Bool} (small : bytes.length < 65536) (pad : padding < 8)
    (aligned : suffix.length % 8 = 0) (next : Blocks [] (history ++ bytes) suffix rest out) :
    Blocks [] history ((storedTag false ++ storedBodyBits padding bytes) ++ suffix) rest out := by
  rw [storedTag_wire, List.append_assoc, List.append_assoc]
  exact Blocks.more (readBits_natBits 1 0 _ (by decide +kernel))
    (readBits_natBits 2 0 _ (by decide +kernel)) (stored_body_grammar history bytes padding suffix small pad aligned) next

end Zlib.Trees.Proofs.Out
