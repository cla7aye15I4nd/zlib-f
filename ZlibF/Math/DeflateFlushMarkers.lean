import ZlibF.Math.DeflateFixedBlock
import ZlibF.Math.DeflateStoredBlock
import ZlibF.Proof.«trees.c.stored-header»

/-! # Real empty flush marker bits retain the independent block continuation -/

namespace Zlib.Trees.Proofs.Out
open C ZlibF.Spec
set_option autoImplicit false

/-- The real PARTIAL_FLUSH end marker is an empty fixed block. -/
theorem partial_marker_body (history : List UInt8) (suffix : List Bool) :
    Body [] 1 history (natBits 0 7 ++ suffix) suffix history := by
  have word : codeBits fixedLiteralWords 256 = natBits 0 7 := by decide +kernel
  have decoded := fixed_literal_decode 256 (by decide +kernel) suffix
  rw [word] at decoded
  exact Body.fixed (Symbols.eob decoded)

/-- The actual nonfinal fixed marker adds no decoded bytes and retains
all later blocks, independently of the current bit alignment. -/
theorem partial_marker_continuation {history decoded : List UInt8} {suffix rest : List Bool}
    (next : Blocks [] history suffix rest decoded) :
    Blocks [] history ((natBits 2 3 ++ natBits 0 7) ++ suffix) rest decoded := by
  change Blocks [] history ((fixedTag false ++ natBits 0 7) ++ suffix) rest decoded
  exact fixed_more_grammar (partial_marker_body history) next

/-- An empty stored marker has LEN=0 and NLEN=65535; only its alignment
padding depends on the previous buffered bit count. -/
theorem empty_stored_marker_continuation (padding : Nat) (pad : padding < 8)
    {history decoded : List UInt8} {suffix rest : List Bool}
    (aligned : suffix.length % 8 = 0) (next : Blocks [] history suffix rest decoded) :
    Blocks [] history
      ((natBits 0 3 ++ List.replicate padding false ++ natBits 0 16 ++ natBits 65535 16) ++ suffix)
      rest decoded := by
  have grammar := stored_more_grammar (history := history) [] padding
    (by decide +kernel) pad aligned (by simpa only [List.append_nil] using next)
  simpa only [storedTag, storedBodyBits, Bool.false_eq_true, ite_false, List.length_nil, Nat.sub_zero,
    bytesToBits, List.flatMap_nil, List.append_nil, List.append_assoc] using grammar

/-- The exact real SYNC/FULL marker bit list preserves all subsequent
independently parsed blocks when their bits start at its byte boundary. -/
theorem stored_header_zero_continuation (d : DeflateState)
    {history decoded : List UInt8} {suffix rest : List Bool}
    (aligned : suffix.length % 8 = 0) (next : Blocks [] history suffix rest decoded) :
    Blocks [] history (storedHeaderBits d 0 false ++ suffix) rest decoded := by
  apply empty_stored_marker_continuation ((8 - (d.bi_valid.toInt.toNat + 3) % 8) % 8)
    (Nat.mod_lt _ (by decide +kernel)) aligned next

end Zlib.Trees.Proofs.Out

