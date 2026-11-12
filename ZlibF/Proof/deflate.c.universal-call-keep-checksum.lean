import ZlibF.Proof.«deflate.c.universal-call-keep-base»
import Init.Data.Range.Lemmas
import ZlibF.Zlib.«adler32.c»
import ZlibF.Zlib.«crc32.c»

/-! The checksum read loops are in `KeepRel` (`deflate.c.universal-call-keep-base`). Port of
`deflate.c.universal-params-checksum`. -/
set_option maxRecDepth 10000
namespace Zlib.Deflate.Universal.Keep
open C


theorem KeepM.list_forIn {α β : Type} (values : List α)
    (body : (value : α) → value ∈ values → β → M (ForInStep β))
    (stable : ∀ value member state, KeepM (body value member state))
    (initial : β) : KeepM (List.forIn' values initial body) := by
  induction values generalizing initial with
  | nil =>
    simp only [List.forIn'_eq_forIn', List.forIn'_nil]
    exact KeepM.pure _
  | cons head tail ih =>
    simp only [List.forIn'_eq_forIn', List.forIn'_cons]
    apply KeepM.bind (stable head (by simp) initial)
    intro decision
    cases decision with
    | done value => exact KeepM.pure _
    | yield next =>
      exact ih (fun value member state => body value (by simp [member]) state)
        (fun value member state => stable value (by simp [member]) state) next

macro "keep_steps" : tactic => `(tactic|
  repeat' first
    | with_reducible exact KeepM.pure _
    | exact KeepM.ub _
    | with_reducible exact keep_load8 _
    | with_reducible exact keep_index8 _ _
    | with_reducible exact keep_ptr_add _ _
    | with_reducible exact keep_ptr_index _ _
    | with_reducible apply KeepM.cwhile
    | with_reducible apply KeepM.cdoWhile
    | with_reducible apply KeepM.ite
    | with_reducible apply KeepM.bind
    | intro x
    | dsimp only)

open Zlib.Adler32 in
theorem keep_adler_do1 (s : Locals) (i : Int) : KeepM (do1 s i) := by
  unfold do1
  keep_steps

open Zlib.Adler32 in
theorem keep_adler_do16 (s : Locals) : KeepM (do16 s) := by
  unfold do16
  repeat' first | with_reducible exact keep_adler_do1 _ _ | with_reducible apply KeepM.bind | intro x

open Zlib.Adler32 in
theorem keep_adler_stepByte (s : Locals) : KeepM (stepByte s) := by
  unfold stepByte
  keep_steps

open Zlib.Adler32 in
theorem keep_adler32_z (v : UInt64) (p : BPtr) (n : UInt64) : KeepM (adler32_z v p n) := by
  unfold adler32_z
  repeat' first
    | with_reducible exact keep_adler_do16 _
    | with_reducible exact keep_adler_stepByte _
    | (unfold lenPostDec; exact KeepM.pure _)
    | with_reducible exact KeepM.pure _
    | with_reducible exact keep_index8 _ _
    | with_reducible exact keep_ptr_add _ _
    | with_reducible apply KeepM.cwhile
    | with_reducible apply KeepM.cdoWhile
    | with_reducible apply KeepM.ite
    | with_reducible apply KeepM.bind
    | intro x
    | dsimp only

open Zlib.Adler32 in
theorem keep_adler32 (v : UInt64) (p : BPtr) (n : UInt32) : KeepM (adler32 v p n) :=
  keep_adler32_z _ _ _

open Zlib.Crc32 in
theorem keep_crc_idx1 {α : Type} (a : Array α) (i : Nat) : KeepM (idx1 a i) := by
  unfold idx1
  split
  · exact KeepM.pure _
  · exact KeepM.ub _

open Zlib.Crc32 in
theorem keep_crc_idx2 {α : Type} (a : Array (Array α)) (i j : Nat) : KeepM (idx2 a i j) := by
  unfold idx2
  split
  · split
    · exact KeepM.pure _
    · exact KeepM.ub _
  · exact KeepM.ub _

open Zlib.Crc32 in
theorem keep_crcTab (i : UInt64) : KeepM (crcTab i) := keep_ptr_index _ _

open Zlib.Crc32 in
theorem keep_crc_addrOf (p : BPtr) : KeepM (addrOf p) := by
  intro h v after hr
  cases hr
  exact KeepRel.refl h

open Zlib.Crc32 in
theorem keep_crc_shr64 (x n : UInt64) : KeepM (shr64 x n) := by
  unfold shr64
  keep_steps

open Zlib.Crc32 in
theorem keep_crc_loadWord (p : BPtr) : KeepM (loadWord p) := by
  unfold loadWord
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  apply KeepM.bind
  · apply KeepM.list_forIn
    intro value member state
    apply KeepM.bind (keep_index8 _ _)
    intro b
    exact KeepM.pure _
  · intro w
    exact KeepM.pure _

open Zlib.Crc32 in
theorem keep_crc_wordAt (p : BPtr) (i : Nat) : KeepM (wordAt p i) := by
  unfold wordAt
  exact KeepM.bind (keep_ptr_add _ _) (fun _ => keep_crc_loadWord _)

open Zlib.Crc32 in
theorem keep_crc_word (v : UInt64) : KeepM (crc_word v) := by
  unfold crc_word
  repeat' first
    | with_reducible exact keep_crcTab _
    | with_reducible exact KeepM.pure _
    | with_reducible apply KeepM.cwhile
    | with_reducible apply KeepM.bind
    | rintro ⟨a, b⟩
    | intro x

open Zlib.Crc32 in
theorem keep_crc_word_big (v : UInt64) : KeepM (crc_word_big v) := by
  unfold crc_word_big
  repeat' first
    | with_reducible exact keep_crc_idx1 _ _
    | with_reducible exact KeepM.pure _
    | with_reducible apply KeepM.cwhile
    | with_reducible apply KeepM.bind
    | rintro ⟨a, b⟩
    | intro x

open Zlib.Crc32 in
theorem keep_crc_braidTab (k : Int32) (v : UInt64) : KeepM (braidTab k v) := by
  unfold braidTab
  exact KeepM.bind (keep_crc_shr64 _ _) (fun _ => keep_crc_idx2 _ _ _)

open Zlib.Crc32 in
theorem keep_crc_braidBigTab (k : Int32) (v : UInt64) : KeepM (braidBigTab k v) := by
  unfold braidBigTab
  exact KeepM.bind (keep_crc_shr64 _ _) (fun _ => keep_crc_idx2 _ _ _)

open Zlib.Crc32 in
theorem keep_crc_blockLittle (s : BL) : KeepM (blockLittle s) := by
  unfold blockLittle
  apply KeepM.bind (keep_crc_wordAt _ _)
  intro w0
  apply KeepM.bind (keep_crc_wordAt _ _)
  intro w1
  apply KeepM.bind (keep_crc_wordAt _ _)
  intro w2
  apply KeepM.bind (keep_crc_wordAt _ _)
  intro w3
  apply KeepM.bind (keep_crc_wordAt _ _)
  intro w4
  apply KeepM.bind (keep_ptr_add _ _)
  intro words
  apply KeepM.bind (keep_crc_braidTab _ _)
  intro c0
  apply KeepM.bind (keep_crc_braidTab _ _)
  intro c1
  apply KeepM.bind (keep_crc_braidTab _ _)
  intro c2
  apply KeepM.bind (keep_crc_braidTab _ _)
  intro c3
  apply KeepM.bind (keep_crc_braidTab _ _)
  intro c4
  apply KeepM.bind
  · apply KeepM.cwhile
    · intro q; exact KeepM.pure _
    · rintro ⟨a, b, c, d, e, f⟩
      apply KeepM.bind (keep_crc_braidTab _ _)
      intro t0
      apply KeepM.bind (keep_crc_braidTab _ _)
      intro t1
      apply KeepM.bind (keep_crc_braidTab _ _)
      intro t2
      apply KeepM.bind (keep_crc_braidTab _ _)
      intro t3
      apply KeepM.bind (keep_crc_braidTab _ _)
      intro t4
      exact KeepM.pure _
  · rintro ⟨a, b, c, d, e, f⟩
    exact KeepM.pure _

open Zlib.Crc32 in
theorem keep_crc_blockBig (s : BB) : KeepM (blockBig s) := by
  unfold blockBig
  apply KeepM.bind (keep_crc_wordAt _ _)
  intro w0
  apply KeepM.bind (keep_crc_wordAt _ _)
  intro w1
  apply KeepM.bind (keep_crc_wordAt _ _)
  intro w2
  apply KeepM.bind (keep_crc_wordAt _ _)
  intro w3
  apply KeepM.bind (keep_crc_wordAt _ _)
  intro w4
  apply KeepM.bind (keep_ptr_add _ _)
  intro words
  apply KeepM.bind (KeepM.bind (keep_crc_shr64 _ _) (fun _ => keep_crc_idx2 _ _ _))
  intro c0
  apply KeepM.bind (KeepM.bind (keep_crc_shr64 _ _) (fun _ => keep_crc_idx2 _ _ _))
  intro c1
  apply KeepM.bind (KeepM.bind (keep_crc_shr64 _ _) (fun _ => keep_crc_idx2 _ _ _))
  intro c2
  apply KeepM.bind (KeepM.bind (keep_crc_shr64 _ _) (fun _ => keep_crc_idx2 _ _ _))
  intro c3
  apply KeepM.bind (KeepM.bind (keep_crc_shr64 _ _) (fun _ => keep_crc_idx2 _ _ _))
  intro c4
  apply KeepM.bind
  · apply KeepM.cwhile
    · intro q; exact KeepM.pure _
    · rintro ⟨a, b, c, d, e, f⟩
      apply KeepM.bind (keep_crc_braidBigTab _ _)
      intro t0
      apply KeepM.bind (keep_crc_braidBigTab _ _)
      intro t1
      apply KeepM.bind (keep_crc_braidBigTab _ _)
      intro t2
      apply KeepM.bind (keep_crc_braidBigTab _ _)
      intro t3
      apply KeepM.bind (keep_crc_braidBigTab _ _)
      intro t4
      exact KeepM.pure _
  · rintro ⟨a, b, c, d, e, f⟩
    exact KeepM.pure _

open Zlib.Crc32 in
theorem keep_crcByte (v : UInt64) (p : BPtr) : KeepM (crcByte v p) := by
  unfold crcByte
  repeat' first
    | with_reducible exact keep_crcTab _
    | with_reducible exact keep_load8 _
    | with_reducible exact keep_ptr_add _ _
    | with_reducible exact KeepM.pure _
    | with_reducible apply KeepM.bind
    | intro x

open Zlib.Crc32 in
theorem keep_crc32_z (v : UInt64) (p : BPtr) (n : UInt64) : KeepM (crc32_z v p n) := by
  unfold crc32_z
  repeat' first
    | with_reducible exact keep_crcByte _ _
    | with_reducible exact keep_crc_addrOf _
    | with_reducible exact keep_crc_blockLittle _
    | with_reducible exact keep_crc_blockBig _
    | with_reducible exact keep_crc_wordAt _ _
    | with_reducible exact keep_crc_word _
    | with_reducible exact keep_crc_word_big _
    | with_reducible exact keep_ptr_add _ _
    | with_reducible exact KeepM.pure _
    | with_reducible apply KeepM.cwhile
    | with_reducible apply KeepM.ite
    | with_reducible apply KeepM.bind
    | with_reducible intro x
    | split
    | dsimp only

open Zlib.Crc32 in
theorem keep_crc32 (v : UInt64) (p : BPtr) (n : UInt32) : KeepM (crc32 v p n) :=
  keep_crc32_z _ _ _

end Zlib.Deflate.Universal.Keep
