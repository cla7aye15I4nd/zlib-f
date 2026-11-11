import ZlibF.Proof.«deflate.c.universal-params-prims»
import Init.Data.Range.Lemmas
import ZlibF.Zlib.«adler32.c»
import ZlibF.Zlib.«crc32.c»

/-! The checksum read loops keep every parameter (batch C, `bound_before_output`). -/
set_option maxRecDepth 10000
namespace Zlib.Deflate.Universal.Params
open C


theorem ExactM.list_forIn {α β : Type} (values : List α)
    (body : (value : α) → value ∈ values → β → M (ForInStep β))
    (stable : ∀ value member state, ExactM (body value member state))
    (initial : β) : ExactM (List.forIn' values initial body) := by
  induction values generalizing initial with
  | nil =>
    simp only [List.forIn'_eq_forIn', List.forIn'_nil]
    exact ExactM.pure _
  | cons head tail ih =>
    simp only [List.forIn'_eq_forIn', List.forIn'_cons]
    apply ExactM.bind (stable head (by simp) initial)
    intro decision
    cases decision with
    | done value => exact ExactM.pure _
    | yield next =>
      exact ih (fun value member state => body value (by simp [member]) state)
        (fun value member state => stable value (by simp [member]) state) next

macro "exact_steps" : tactic => `(tactic|
  repeat' first
    | with_reducible exact ExactM.pure _
    | exact ExactM.ub _
    | with_reducible exact exact_load8 _
    | with_reducible exact exact_index8 _ _
    | with_reducible exact exact_ptr_add _ _
    | with_reducible exact exact_ptr_index _ _
    | with_reducible apply ExactM.cwhile
    | with_reducible apply ExactM.cdoWhile
    | with_reducible apply ExactM.ite
    | with_reducible apply ExactM.bind
    | intro x
    | dsimp only)

open Zlib.Adler32 in
theorem exact_adler_do1 (s : Locals) (i : Int) : ExactM (do1 s i) := by
  unfold do1
  exact_steps

open Zlib.Adler32 in
theorem exact_adler_do16 (s : Locals) : ExactM (do16 s) := by
  unfold do16
  repeat' first | with_reducible exact exact_adler_do1 _ _ | with_reducible apply ExactM.bind | intro x

open Zlib.Adler32 in
theorem exact_adler_stepByte (s : Locals) : ExactM (stepByte s) := by
  unfold stepByte
  exact_steps

open Zlib.Adler32 in
theorem exact_adler32_z (v : UInt64) (p : BPtr) (n : UInt64) : ExactM (adler32_z v p n) := by
  unfold adler32_z
  repeat' first
    | with_reducible exact exact_adler_do16 _
    | with_reducible exact exact_adler_stepByte _
    | (unfold lenPostDec; exact ExactM.pure _)
    | with_reducible exact ExactM.pure _
    | with_reducible exact exact_index8 _ _
    | with_reducible exact exact_ptr_add _ _
    | with_reducible apply ExactM.cwhile
    | with_reducible apply ExactM.cdoWhile
    | with_reducible apply ExactM.ite
    | with_reducible apply ExactM.bind
    | intro x
    | dsimp only

open Zlib.Adler32 in
theorem exact_adler32 (v : UInt64) (p : BPtr) (n : UInt32) : ExactM (adler32 v p n) :=
  exact_adler32_z _ _ _

open Zlib.Crc32 in
theorem exact_crc_idx1 {α : Type} (a : Array α) (i : Nat) : ExactM (idx1 a i) := by
  unfold idx1
  split
  · exact ExactM.pure _
  · exact ExactM.ub _

open Zlib.Crc32 in
theorem exact_crc_idx2 {α : Type} (a : Array (Array α)) (i j : Nat) : ExactM (idx2 a i j) := by
  unfold idx2
  split
  · split
    · exact ExactM.pure _
    · exact ExactM.ub _
  · exact ExactM.ub _

open Zlib.Crc32 in
theorem exact_crcTab (i : UInt64) : ExactM (crcTab i) := exact_ptr_index _ _

open Zlib.Crc32 in
theorem exact_crc_addrOf (p : BPtr) : ExactM (addrOf p) := by
  intro h v after hr
  cases hr
  exact ExactRel.refl h

open Zlib.Crc32 in
theorem exact_crc_shr64 (x n : UInt64) : ExactM (shr64 x n) := by
  unfold shr64
  exact_steps

open Zlib.Crc32 in
theorem exact_crc_loadWord (p : BPtr) : ExactM (loadWord p) := by
  unfold loadWord
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  apply ExactM.bind
  · apply ExactM.list_forIn
    intro value member state
    apply ExactM.bind (exact_index8 _ _)
    intro b
    exact ExactM.pure _
  · intro w
    exact ExactM.pure _

open Zlib.Crc32 in
theorem exact_crc_wordAt (p : BPtr) (i : Nat) : ExactM (wordAt p i) := by
  unfold wordAt
  exact ExactM.bind (exact_ptr_add _ _) (fun _ => exact_crc_loadWord _)

open Zlib.Crc32 in
theorem exact_crc_word (v : UInt64) : ExactM (crc_word v) := by
  unfold crc_word
  repeat' first
    | with_reducible exact exact_crcTab _
    | with_reducible exact ExactM.pure _
    | with_reducible apply ExactM.cwhile
    | with_reducible apply ExactM.bind
    | rintro ⟨a, b⟩
    | intro x

open Zlib.Crc32 in
theorem exact_crc_word_big (v : UInt64) : ExactM (crc_word_big v) := by
  unfold crc_word_big
  repeat' first
    | with_reducible exact exact_crc_idx1 _ _
    | with_reducible exact ExactM.pure _
    | with_reducible apply ExactM.cwhile
    | with_reducible apply ExactM.bind
    | rintro ⟨a, b⟩
    | intro x

open Zlib.Crc32 in
theorem exact_crc_braidTab (k : Int32) (v : UInt64) : ExactM (braidTab k v) := by
  unfold braidTab
  exact ExactM.bind (exact_crc_shr64 _ _) (fun _ => exact_crc_idx2 _ _ _)

open Zlib.Crc32 in
theorem exact_crc_braidBigTab (k : Int32) (v : UInt64) : ExactM (braidBigTab k v) := by
  unfold braidBigTab
  exact ExactM.bind (exact_crc_shr64 _ _) (fun _ => exact_crc_idx2 _ _ _)

open Zlib.Crc32 in
theorem exact_crc_blockLittle (s : BL) : ExactM (blockLittle s) := by
  unfold blockLittle
  apply ExactM.bind (exact_crc_wordAt _ _)
  intro w0
  apply ExactM.bind (exact_crc_wordAt _ _)
  intro w1
  apply ExactM.bind (exact_crc_wordAt _ _)
  intro w2
  apply ExactM.bind (exact_crc_wordAt _ _)
  intro w3
  apply ExactM.bind (exact_crc_wordAt _ _)
  intro w4
  apply ExactM.bind (exact_ptr_add _ _)
  intro words
  apply ExactM.bind (exact_crc_braidTab _ _)
  intro c0
  apply ExactM.bind (exact_crc_braidTab _ _)
  intro c1
  apply ExactM.bind (exact_crc_braidTab _ _)
  intro c2
  apply ExactM.bind (exact_crc_braidTab _ _)
  intro c3
  apply ExactM.bind (exact_crc_braidTab _ _)
  intro c4
  apply ExactM.bind
  · apply ExactM.cwhile
    · intro q; exact ExactM.pure _
    · rintro ⟨a, b, c, d, e, f⟩
      apply ExactM.bind (exact_crc_braidTab _ _)
      intro t0
      apply ExactM.bind (exact_crc_braidTab _ _)
      intro t1
      apply ExactM.bind (exact_crc_braidTab _ _)
      intro t2
      apply ExactM.bind (exact_crc_braidTab _ _)
      intro t3
      apply ExactM.bind (exact_crc_braidTab _ _)
      intro t4
      exact ExactM.pure _
  · rintro ⟨a, b, c, d, e, f⟩
    exact ExactM.pure _

open Zlib.Crc32 in
theorem exact_crc_blockBig (s : BB) : ExactM (blockBig s) := by
  unfold blockBig
  apply ExactM.bind (exact_crc_wordAt _ _)
  intro w0
  apply ExactM.bind (exact_crc_wordAt _ _)
  intro w1
  apply ExactM.bind (exact_crc_wordAt _ _)
  intro w2
  apply ExactM.bind (exact_crc_wordAt _ _)
  intro w3
  apply ExactM.bind (exact_crc_wordAt _ _)
  intro w4
  apply ExactM.bind (exact_ptr_add _ _)
  intro words
  apply ExactM.bind (ExactM.bind (exact_crc_shr64 _ _) (fun _ => exact_crc_idx2 _ _ _))
  intro c0
  apply ExactM.bind (ExactM.bind (exact_crc_shr64 _ _) (fun _ => exact_crc_idx2 _ _ _))
  intro c1
  apply ExactM.bind (ExactM.bind (exact_crc_shr64 _ _) (fun _ => exact_crc_idx2 _ _ _))
  intro c2
  apply ExactM.bind (ExactM.bind (exact_crc_shr64 _ _) (fun _ => exact_crc_idx2 _ _ _))
  intro c3
  apply ExactM.bind (ExactM.bind (exact_crc_shr64 _ _) (fun _ => exact_crc_idx2 _ _ _))
  intro c4
  apply ExactM.bind
  · apply ExactM.cwhile
    · intro q; exact ExactM.pure _
    · rintro ⟨a, b, c, d, e, f⟩
      apply ExactM.bind (exact_crc_braidBigTab _ _)
      intro t0
      apply ExactM.bind (exact_crc_braidBigTab _ _)
      intro t1
      apply ExactM.bind (exact_crc_braidBigTab _ _)
      intro t2
      apply ExactM.bind (exact_crc_braidBigTab _ _)
      intro t3
      apply ExactM.bind (exact_crc_braidBigTab _ _)
      intro t4
      exact ExactM.pure _
  · rintro ⟨a, b, c, d, e, f⟩
    exact ExactM.pure _

open Zlib.Crc32 in
theorem exact_crcByte (v : UInt64) (p : BPtr) : ExactM (crcByte v p) := by
  unfold crcByte
  repeat' first
    | with_reducible exact exact_crcTab _
    | with_reducible exact exact_load8 _
    | with_reducible exact exact_ptr_add _ _
    | with_reducible exact ExactM.pure _
    | with_reducible apply ExactM.bind
    | intro x

open Zlib.Crc32 in
theorem exact_crc32_z (v : UInt64) (p : BPtr) (n : UInt64) : ExactM (crc32_z v p n) := by
  unfold crc32_z
  repeat' first
    | with_reducible exact exact_crcByte _ _
    | with_reducible exact exact_crc_addrOf _
    | with_reducible exact exact_crc_blockLittle _
    | with_reducible exact exact_crc_blockBig _
    | with_reducible exact exact_crc_wordAt _ _
    | with_reducible exact exact_crc_word _
    | with_reducible exact exact_crc_word_big _
    | with_reducible exact exact_ptr_add _ _
    | with_reducible exact ExactM.pure _
    | with_reducible apply ExactM.cwhile
    | with_reducible apply ExactM.ite
    | with_reducible apply ExactM.bind
    | with_reducible intro x
    | split
    | dsimp only

open Zlib.Crc32 in
theorem exact_crc32 (v : UInt64) (p : BPtr) (n : UInt32) : ExactM (crc32 v p n) :=
  exact_crc32_z _ _ _

end Zlib.Deflate.Universal.Params
