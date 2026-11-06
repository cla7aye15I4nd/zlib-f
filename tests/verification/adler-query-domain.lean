import ZlibF.Spec.Public.Checksums
import ZlibF.Proof.«adler32.c»

/-!
Adler initialization queries require zero length. CRC keeps its separate NULL convention.
These checks exercise the public domain and the actual translated initialization calls.
-/

open C ZlibF.Spec.Public

example (h : Heap) (length : Nat) (bytes : List UInt8) :
    AdlerBufferBytes h .null length bytes ↔ length = 0 ∧ bytes = [] := by
  simp [AdlerBufferBytes, BufferBytes, and_comm]

example (h : Heap) : ¬ AdlerBufferBytes h .null 1 [] := by
  simp [AdlerBufferBytes]

example (h : Heap) (length : Nat) : BufferBytes h .null length [] :=
  Or.inl ⟨rfl, rfl⟩

example (h : Heap) (seed : UInt64) :
    C.run (Zlib.Adler32.adler32_z seed .null 0) h = .ok (1, h) := by
  rw [Zlib.Adler32.Proofs.adler32_z_null_init]
  rfl

example (h : Heap) (seed : UInt64) :
    C.run (Zlib.Adler32.adler32 seed .null 0) h = .ok (1, h) := by
  rw [Zlib.Adler32.Proofs.adler32_null_init]
  rfl
