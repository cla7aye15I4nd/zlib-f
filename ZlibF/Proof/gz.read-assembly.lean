import ZlibF.Proof.«gz.read-gzread»
import ZlibF.Proof.«gz.read-look»
import ZlibF.Proof.«gzread.c.skip-fetch»
import ZlibF.Proof.«gzread.c.fread»

/-!
# gz read side: the assembly of `gz_read` and `gzread`

The read helpers compose:
- `gz_look_safe : GzLookSpec`;
- `gz_decomp_safe_of : InflateStuckNoOutput → GzDecompSpec`;
- `gz_fetch_safe_of : GzLookSpec → GzDecompSpec → GzFetchSafe`;
- `gzSkipRead_holds : GzFetchSafe → GzSkipRead` (`gzread.c.skip-fetch`);
- `gz_read_safe_of : GzSkipRead → GzFetchSafe → GzDecompSpec → GzReadSafe`;
- `gzread_step_of_read : GzReadSafe → gzread_step`, and `gzfread_step_of_read : GzReadSafe → gzfread_step`
  (`gzread.c.fread`).

The one premise left is `InflateStuckNoOutput`, a fact of `inflate` that is **open**: a call from mode `BAD` or `MEM`
moves neither buffer.
-/

namespace ZlibF.Spec.Public.GzRead
open C Zlib.GzFs Zlib.Gzguts Zlib.Gzlib.Spec Zlib.Gzlib.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- `gz_fetch`, from the open fact on a stuck inflate stream. -/
theorem gz_fetch_safe_stuck (stuck : InflateStuckNoOutput) : GzFetchSafe :=
  gz_fetch_safe_of gz_look_safe (gz_decomp_safe_of stuck)

/-- `gz_read`, from the open fact on a stuck inflate stream. -/
theorem gz_read_safe_stuck (stuck : InflateStuckNoOutput) : GzReadSafe :=
  gz_read_safe_of (gzSkipRead_holds (gz_fetch_safe_stuck stuck)) (gz_fetch_safe_stuck stuck)
    (gz_decomp_safe_of stuck)

/-- **The leaf `gzread_step`**, from the open fact on a stuck inflate stream. -/
theorem gzread_step_stuck (stuck : InflateStuckNoOutput) :
    ∀ (i : Nat) (buf : BPtr) (len : UInt32), GzCallSafe i (.gzread (some (.in_gzstate_x i)) buf len) :=
  gzread_step_of_read (gz_read_safe_stuck stuck)

/-- **The leaf `gzfread_step`**, from the open fact on a stuck inflate stream. -/
theorem gzfread_step_stuck (stuck : InflateStuckNoOutput) :
    ∀ (i : Nat) (buf : BPtr) (size nitems : UInt64),
      GzCallSafe i (.gzfread buf size nitems (some (.in_gzstate_x i))) :=
  gzfread_step_of_read (gz_read_safe_stuck stuck)

end ZlibF.Spec.Public.GzRead
#print axioms ZlibF.Spec.Public.GzRead.gz_read_safe_stuck
#print axioms ZlibF.Spec.Public.GzRead.gzread_step_stuck
#print axioms ZlibF.Spec.Public.GzRead.gzfread_step_stuck
