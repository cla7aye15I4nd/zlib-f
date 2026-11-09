import ZlibF.Zlib.«compress.c»

/-! # Non-wrapping buffer refills in compress.c

These lemmas concern the exact scalar expressions used by the outer chunk loop.
They do not assume or assert a successful deflate call or whole-loop termination.
-/

namespace ZlibF.Spec.Public.Proofs.CompressChunks
open C Zlib.Compress Zlib.Deflate
set_option autoImplicit false

/-- The exact `uInt` refill expression used for both input and output. -/
def chunk (remaining : UInt64) : UInt32 :=
  let max : UInt32 := 0xffffffff
  if remaining > max.toUInt64 then max else remaining.toUInt32

/-- `int compress2_z(Bytef *dest, z_size_t *destLen, const Bytef *source,
z_size_t sourceLen, int level)`.
Each outer-loop refill is the natural minimum, even when the remaining
length exceeds the range of `uInt`. The narrowing cast loses no bytes. -/
theorem chunk_value (remaining : UInt64) :
    (chunk remaining).toNat = min remaining.toNat (2 ^ 32 - 1) := by
  dsimp only [chunk]
  split
  · rename_i large
    have large' : 4294967295 < remaining.toNat := UInt64.lt_iff_toNat_lt.mp large
    change 4294967295 = min remaining.toNat (2 ^ 32 - 1)
    omega
  · rename_i small
    have small' : remaining.toNat ≤ 4294967295 := by
      have := UInt64.le_iff_toNat_le.mp (UInt64.not_lt.mp small)
      exact this
    rw [UInt64.toNat_toUInt32, Nat.mod_eq_of_lt (by omega)]
    omega

/-- `int compress2_z(Bytef *dest, z_size_t *destLen, const Bytef *source,
z_size_t sourceLen, int level)`.
The actual unsigned subtraction does not wrap. The assigned avail count
and still-unoffered count preserve the exact original length. -/
theorem chunk_accounting (remaining : UInt64) :
    (chunk remaining).toUInt64 ≤ remaining ∧
    (remaining - (chunk remaining).toUInt64).toNat + (chunk remaining).toNat =
      remaining.toNat := by
  have value := chunk_value remaining
  have bounded : (chunk remaining).toUInt64 ≤ remaining := by
    rw [UInt64.le_iff_toNat_le, UInt32.toNat_toUInt64]
    omega
  refine ⟨bounded, ?_⟩
  rw [UInt64.toNat_sub_of_le _ _ bounded, UInt32.toNat_toUInt64]
  omega

/-- `int compress2_z(Bytef *dest, z_size_t *destLen, const Bytef *source,
z_size_t sourceLen, int level)`.
A positive refill offers bytes and strictly reduces the still-unoffered
count. This is refill progress, not a claim that every engine call progresses. -/
theorem chunk_progress (remaining : UInt64) (positive : 0 < remaining) :
    0 < (chunk remaining).toNat ∧
    (remaining - (chunk remaining).toUInt64).toNat < remaining.toNat := by
  have pos := UInt64.lt_iff_toNat_lt.mp positive
  have value := chunk_value remaining
  have counts := (chunk_accounting remaining).2
  change 0 < remaining.toNat at pos
  constructor <;> omega

/-- `int compress2_z(Bytef *dest, z_size_t *destLen, const Bytef *source,
z_size_t sourceLen, int level)`.
After the last input chunk is offered, the actual loop selects FINISH.
Earlier chunks select NO_FLUSH. The flag depends on still-unoffered input;
it does not require the current avail_in to have been consumed. -/
theorem chunk_flush (remaining : UInt64) :
    (if remaining - (chunk remaining).toUInt64 != 0 then Z_NO_FLUSH else Z_FINISH) =
      (if remaining.toNat > 2 ^ 32 - 1 then Z_NO_FLUSH else Z_FINISH) := by
  have value := chunk_value remaining
  have count := (chunk_accounting remaining).2
  have zero : remaining - (chunk remaining).toUInt64 = 0 ↔ remaining.toNat ≤ 2 ^ 32 - 1 := by
    rw [← UInt64.toNat_inj]
    change (remaining - (chunk remaining).toUInt64).toNat = 0 ↔ _
    omega
  by_cases small : remaining.toNat ≤ 2 ^ 32 - 1
  · simp [zero.mpr small, Nat.not_lt.mpr small]
  · have nz : remaining - (chunk remaining).toUInt64 ≠ 0 := fun e => small (zero.mp e)
    simp [nz, Nat.lt_of_not_ge small]

/-- `int compress2_z(Bytef *dest, z_size_t *destLen, const Bytef *source,
z_size_t sourceLen, int level)`.
The actual output-refill fragment writes exactly the assigned chunk and
returns the exact still-unoffered count. This is a local cutpoint before
calling deflate, with no callee contract as a premise. -/
theorem output_refill_run (h : Heap) (r : ZStreamRef) (z : ZStream) (remaining : UInt64)
    (get : r.get h = some z) (empty : z.avail_out = 0) :
    C.run (do
      let max : UInt32 := 0xffffffff
      let mut left := remaining
      if (← zrd (some r) (·.avail_out)) == 0 then
        let ao : UInt32 := if left > max.toUInt64 then max else left.toUInt32
        zwr (some r) (fun z => { z with avail_out := ao })
        left := left - ao.toUInt64
      pure left) h =
      .ok (remaining - (chunk remaining).toUInt64,
        r.put h { z with avail_out := chunk remaining }) := by
  have writable : r.isRo = false := by cases r <;> rfl
  simp [C.run, zrd, zwr, ldZStream, stZStream, get, writable, empty, chunk]

/-- `int compress2_z(Bytef *dest, z_size_t *destLen, const Bytef *source,
z_size_t sourceLen, int level)`.
The actual input-refill fragment has the same exact count effect and
updates only avail_in. No input bytes are claimed to be consumed here. -/
theorem input_refill_run (h : Heap) (r : ZStreamRef) (z : ZStream) (remaining : UInt64)
    (get : r.get h = some z) (empty : z.avail_in = 0) :
    C.run (do
      let max : UInt32 := 0xffffffff
      let mut sourceLen := remaining
      if (← zrd (some r) (·.avail_in)) == 0 then
        let ai : UInt32 := if sourceLen > max.toUInt64 then max else sourceLen.toUInt32
        zwr (some r) (fun z => { z with avail_in := ai })
        sourceLen := sourceLen - ai.toUInt64
      pure sourceLen) h =
      .ok (remaining - (chunk remaining).toUInt64,
        r.put h { z with avail_in := chunk remaining }) := by
  have writable : r.isRo = false := by cases r <;> rfl
  simp [C.run, zrd, zwr, ldZStream, stZStream, get, writable, empty, chunk]

end ZlibF.Spec.Public.Proofs.CompressChunks
