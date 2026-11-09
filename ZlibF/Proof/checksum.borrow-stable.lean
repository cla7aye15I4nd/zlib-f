import ZlibF.Proof.LibcBorrowLoops
import Init.Data.Range.Lemmas
import ZlibF.Zlib.«adler32.c»
import ZlibF.Zlib.«crc32.c»

/-! Borrow metadata preservation by the actual checksum read loops. -/
set_option maxRecDepth 10000
namespace C.LibcBorrow

/-- Array indexing is a read, including every supported static reference. -/
theorem stable_ptr_index {R T : Type} [Space Heap R T] (p : Ptr R) (k : Int) :
    StableM (Ptr.index p k : M T) := by
  unfold Ptr.index
  exact StableM.bind (stable_ptr_add _ _) (fun _ => stable_ptr_load _)

macro "borrow_steps" : tactic => `(tactic|
  repeat' first
    | with_reducible exact StableM.pure _
    | exact StableM.ub _
    | with_reducible exact stable_load8 _
    | with_reducible exact stable_index8 _ _
    | with_reducible exact stable_ptr_add _ _
    | with_reducible exact stable_ptr_index _ _
    | with_reducible apply StableM.cwhile
    | with_reducible apply StableM.cdoWhile
    | with_reducible apply StableM.ite
    | with_reducible apply StableM.bind
    | intro x
    | dsimp only)

open Zlib.Adler32 in
theorem stable_adler_do1 (s : Locals) (i : Int) : StableM (do1 s i) := by
  unfold do1
  borrow_steps

open Zlib.Adler32 in
theorem stable_adler_do16 (s : Locals) : StableM (do16 s) := by
  unfold do16
  repeat' first | with_reducible exact stable_adler_do1 _ _ | with_reducible apply StableM.bind | intro x

open Zlib.Adler32 in
theorem stable_adler_stepByte (s : Locals) : StableM (stepByte s) := by
  unfold stepByte
  borrow_steps

open Zlib.Adler32 in
theorem stable_adler32_z (v : UInt64) (p : BPtr) (n : UInt64) : StableM (adler32_z v p n) := by
  unfold adler32_z
  repeat' first
    | with_reducible exact stable_adler_do16 _
    | with_reducible exact stable_adler_stepByte _
    | (unfold lenPostDec; exact StableM.pure _)
    | with_reducible exact StableM.pure _
    | with_reducible exact stable_index8 _ _
    | with_reducible exact stable_ptr_add _ _
    | with_reducible apply StableM.cwhile
    | with_reducible apply StableM.cdoWhile
    | with_reducible apply StableM.ite
    | with_reducible apply StableM.bind
    | intro x
    | dsimp only

open Zlib.Adler32 in
theorem stable_adler32 (v : UInt64) (p : BPtr) (n : UInt32) : StableM (adler32 v p n) :=
  stable_adler32_z _ _ _

open Zlib.Crc32 in
theorem stable_crc_idx1 {α : Type} (a : Array α) (i : Nat) : StableM (idx1 a i) := by
  unfold idx1
  split
  · exact StableM.pure _
  · exact StableM.ub _

open Zlib.Crc32 in
theorem stable_crc_idx2 {α : Type} (a : Array (Array α)) (i j : Nat) : StableM (idx2 a i j) := by
  unfold idx2
  split
  · split
    · exact StableM.pure _
    · exact StableM.ub _
  · exact StableM.ub _

open Zlib.Crc32 in
theorem stable_crcTab (i : UInt64) : StableM (crcTab i) := stable_ptr_index _ _

open Zlib.Crc32 in
theorem stable_crc_addrOf (p : BPtr) : StableM (addrOf p) := by
  intro h v after hr
  cases hr
  rfl

open Zlib.Crc32 in
theorem stable_crc_shr64 (x n : UInt64) : StableM (shr64 x n) := by
  unfold shr64
  borrow_steps

open Zlib.Crc32 in
theorem stable_crc_loadWord (p : BPtr) : StableM (loadWord p) := by
  unfold loadWord
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  apply StableM.bind
  · apply StableM.list_forIn
    intro value member state
    apply StableM.bind (stable_index8 _ _)
    intro b
    exact StableM.pure _
  · intro w
    exact StableM.pure _

open Zlib.Crc32 in
theorem stable_crc_wordAt (p : BPtr) (i : Nat) : StableM (wordAt p i) := by
  unfold wordAt
  exact StableM.bind (stable_ptr_add _ _) (fun _ => stable_crc_loadWord _)

open Zlib.Crc32 in
theorem stable_crc_word (v : UInt64) : StableM (crc_word v) := by
  unfold crc_word
  repeat' first
    | with_reducible exact stable_crcTab _
    | with_reducible exact StableM.pure _
    | with_reducible apply StableM.cwhile
    | with_reducible apply StableM.bind
    | rintro ⟨a, b⟩
    | intro x

open Zlib.Crc32 in
theorem stable_crc_word_big (v : UInt64) : StableM (crc_word_big v) := by
  unfold crc_word_big
  repeat' first
    | with_reducible exact stable_crc_idx1 _ _
    | with_reducible exact StableM.pure _
    | with_reducible apply StableM.cwhile
    | with_reducible apply StableM.bind
    | rintro ⟨a, b⟩
    | intro x

open Zlib.Crc32 in
theorem stable_crc_braidTab (k : Int32) (v : UInt64) : StableM (braidTab k v) := by
  unfold braidTab
  exact StableM.bind (stable_crc_shr64 _ _) (fun _ => stable_crc_idx2 _ _ _)

open Zlib.Crc32 in
theorem stable_crc_braidBigTab (k : Int32) (v : UInt64) : StableM (braidBigTab k v) := by
  unfold braidBigTab
  exact StableM.bind (stable_crc_shr64 _ _) (fun _ => stable_crc_idx2 _ _ _)

open Zlib.Crc32 in
theorem stable_crc_blockLittle (s : BL) : StableM (blockLittle s) := by
  unfold blockLittle
  apply StableM.bind (stable_crc_wordAt _ _)
  intro w0
  apply StableM.bind (stable_crc_wordAt _ _)
  intro w1
  apply StableM.bind (stable_crc_wordAt _ _)
  intro w2
  apply StableM.bind (stable_crc_wordAt _ _)
  intro w3
  apply StableM.bind (stable_crc_wordAt _ _)
  intro w4
  apply StableM.bind (stable_ptr_add _ _)
  intro words
  apply StableM.bind (stable_crc_braidTab _ _)
  intro c0
  apply StableM.bind (stable_crc_braidTab _ _)
  intro c1
  apply StableM.bind (stable_crc_braidTab _ _)
  intro c2
  apply StableM.bind (stable_crc_braidTab _ _)
  intro c3
  apply StableM.bind (stable_crc_braidTab _ _)
  intro c4
  apply StableM.bind
  · apply StableM.cwhile
    · intro q; exact StableM.pure _
    · rintro ⟨a, b, c, d, e, f⟩
      apply StableM.bind (stable_crc_braidTab _ _)
      intro t0
      apply StableM.bind (stable_crc_braidTab _ _)
      intro t1
      apply StableM.bind (stable_crc_braidTab _ _)
      intro t2
      apply StableM.bind (stable_crc_braidTab _ _)
      intro t3
      apply StableM.bind (stable_crc_braidTab _ _)
      intro t4
      exact StableM.pure _
  · rintro ⟨a, b, c, d, e, f⟩
    exact StableM.pure _

open Zlib.Crc32 in
theorem stable_crc_blockBig (s : BB) : StableM (blockBig s) := by
  unfold blockBig
  apply StableM.bind (stable_crc_wordAt _ _)
  intro w0
  apply StableM.bind (stable_crc_wordAt _ _)
  intro w1
  apply StableM.bind (stable_crc_wordAt _ _)
  intro w2
  apply StableM.bind (stable_crc_wordAt _ _)
  intro w3
  apply StableM.bind (stable_crc_wordAt _ _)
  intro w4
  apply StableM.bind (stable_ptr_add _ _)
  intro words
  apply StableM.bind (StableM.bind (stable_crc_shr64 _ _) (fun _ => stable_crc_idx2 _ _ _))
  intro c0
  apply StableM.bind (StableM.bind (stable_crc_shr64 _ _) (fun _ => stable_crc_idx2 _ _ _))
  intro c1
  apply StableM.bind (StableM.bind (stable_crc_shr64 _ _) (fun _ => stable_crc_idx2 _ _ _))
  intro c2
  apply StableM.bind (StableM.bind (stable_crc_shr64 _ _) (fun _ => stable_crc_idx2 _ _ _))
  intro c3
  apply StableM.bind (StableM.bind (stable_crc_shr64 _ _) (fun _ => stable_crc_idx2 _ _ _))
  intro c4
  apply StableM.bind
  · apply StableM.cwhile
    · intro q; exact StableM.pure _
    · rintro ⟨a, b, c, d, e, f⟩
      apply StableM.bind (stable_crc_braidBigTab _ _)
      intro t0
      apply StableM.bind (stable_crc_braidBigTab _ _)
      intro t1
      apply StableM.bind (stable_crc_braidBigTab _ _)
      intro t2
      apply StableM.bind (stable_crc_braidBigTab _ _)
      intro t3
      apply StableM.bind (stable_crc_braidBigTab _ _)
      intro t4
      exact StableM.pure _
  · rintro ⟨a, b, c, d, e, f⟩
    exact StableM.pure _

open Zlib.Crc32 in
theorem stable_crcByte (v : UInt64) (p : BPtr) : StableM (crcByte v p) := by
  unfold crcByte
  repeat' first
    | with_reducible exact stable_crcTab _
    | with_reducible exact stable_load8 _
    | with_reducible exact stable_ptr_add _ _
    | with_reducible exact StableM.pure _
    | with_reducible apply StableM.bind
    | intro x

open Zlib.Crc32 in
theorem stable_crc32_z (v : UInt64) (p : BPtr) (n : UInt64) : StableM (crc32_z v p n) := by
  unfold crc32_z
  repeat' first
    | with_reducible exact stable_crcByte _ _
    | with_reducible exact stable_crc_addrOf _
    | with_reducible exact stable_crc_blockLittle _
    | with_reducible exact stable_crc_blockBig _
    | with_reducible exact stable_crc_wordAt _ _
    | with_reducible exact stable_crc_word _
    | with_reducible exact stable_crc_word_big _
    | with_reducible exact stable_ptr_add _ _
    | with_reducible exact StableM.pure _
    | with_reducible apply StableM.cwhile
    | with_reducible apply StableM.ite
    | with_reducible apply StableM.bind
    | with_reducible intro x
    | split
    | dsimp only

open Zlib.Crc32 in
theorem stable_crc32 (v : UInt64) (p : BPtr) (n : UInt32) : StableM (crc32 v p n) :=
  stable_crc32_z _ _ _

#print axioms stable_adler32
#print axioms stable_crc32
end C.LibcBorrow
