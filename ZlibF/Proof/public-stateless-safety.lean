import ZlibF.Proof.«public-adler-update»
import ZlibF.Proof.«public-adler-combine»
import ZlibF.Proof.«public-crc-updates»
import ZlibF.Proof.«public-crc-combine»
import ZlibF.Proof.«public-zlib-version»
import ZlibF.Proof.«public-zlib-compile-flags»
import ZlibF.Spec.Safety.Checksums
import ZlibF.Spec.Safety.Queries

/-!
# Safety of the checksum and query functions

Each goal of `ZlibF/Spec/Safety/Checksums.lean` and `ZlibF/Spec/Safety/Queries.lean` is the
full contract of the same function with the value forgotten.
-/

namespace ZlibF.Spec.Public.StatelessSafetyProof
open C ZlibF.Spec ZlibF.Spec.Public

theorem adler32_safety : Goal.adler32_safety := fun h seed p n bytes d =>
  ⟨_, AdlerUpdateProof.adler_public h seed p n bytes d⟩

theorem adler32_z_safety : Goal.adler32_z_safety := fun h seed p n bytes d =>
  ⟨_, AdlerUpdateProof.adler_z_public h seed p n bytes d⟩

theorem adler32_combine_safety : Goal.adler32_combine_safety := fun h a b n => by
  obtain ⟨v, hv, -⟩ := AdlerCombineProof.combine_public h a b n
  exact ⟨v, hv⟩

theorem adler32_combine64_safety : Goal.adler32_combine64_safety := fun h a b n => by
  obtain ⟨v, hv, -⟩ := AdlerCombineProof.combine64_public h a b n
  exact ⟨v, hv⟩

theorem crc32_safety : Goal.crc32_safety := fun h seed p n bytes g d =>
  ⟨_, Proofs.crc32 h seed p n bytes g d⟩

theorem crc32_z_safety : Goal.crc32_z_safety := fun h seed p n bytes g d =>
  ⟨_, Proofs.crc32_z h seed p n bytes g d⟩

theorem crc32_combine_gen_safety : Goal.crc32_combine_gen_safety := fun h n g =>
  ⟨_, CrcCombineProof.gen h n g⟩

theorem crc32_combine_gen64_safety : Goal.crc32_combine_gen64_safety := fun h n g =>
  ⟨_, CrcCombineProof.gen64 h n g⟩

theorem crc32_combine_op_safety : Goal.crc32_combine_op_safety := by
  intro h a b n op g hop
  have hop' : op = crcOperator n := by
    rcases hop with hop | hop
    · rw [CrcCombineProof.gen h n g] at hop
      cases hop; rfl
    · rw [CrcCombineProof.gen64 h n g] at hop
      cases hop; rfl
  subst hop'
  exact ⟨_, CrcCombineProof.op h a b n g⟩

theorem crc32_combine_safety : Goal.crc32_combine_safety := fun h a b n g =>
  ⟨_, CrcCombineProof.combine h a b n g⟩

theorem crc32_combine64_safety : Goal.crc32_combine64_safety := fun h a b n g =>
  ⟨_, CrcCombineProof.combine64 h a b n g⟩

theorem zlibVersion_safety : Goal.zlibVersion_safety := fun h => by
  obtain ⟨p, hp, -⟩ := Proofs.zlibVersion h
  exact ⟨p, hp⟩

theorem zlibCompileFlags_safety : Goal.zlibCompileFlags_safety := fun h =>
  ⟨_, Proofs.zlibCompileFlags h⟩

end ZlibF.Spec.Public.StatelessSafetyProof
