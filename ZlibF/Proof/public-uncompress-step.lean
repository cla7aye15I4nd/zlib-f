import ZlibF.Proof.«public-uncompress-heap»
import ZlibF.Proof.«public-uncompress-format»
import ZlibF.Proof.«public-uncompress-loop-rule»

/-!
# uncompr.c: one iteration of the decompression loop

The loop body of `uncompress2_z` refills an empty output and an empty input
from the remaining lengths, then calls `inflate`. `loopBody` and `loopCond` are
the body and condition of the translation, with the local constant `max`
written out; they are definitionally the translation's.
-/

namespace ZlibF.Spec.Public.Proofs.Uncompress
open C ZlibF.Spec ZlibF.Spec.Public Zlib.Gzguts Zlib.Inflate.Proofs Zlib.Uncompr
open Zlib.Inflate (inflate)
set_option autoImplicit false

/-- The loop body of `uncompress2_z`. -/
def loopBody (stream : ZStreamPtr) : UncLoop → M UncLoop := fun (l : UncLoop) => do
  let mut l := l
  if (← ldZ stream).avail_out == 0 then
    let a : UInt32 := if l.left > (0xFFFFFFFF : UInt32).toUInt64 then 0xFFFFFFFF else l.left.toUInt32
    updZ stream fun z => { z with avail_out := a }
    l := { l with left := l.left - a.toUInt64 }
  if (← ldZ stream).avail_in == 0 then
    let a : UInt32 := if l.len > (0xFFFFFFFF : UInt32).toUInt64 then 0xFFFFFFFF else l.len.toUInt32
    updZ stream fun z => { z with avail_in := a }
    l := { l with len := l.len - a.toUInt64 }
  let err ← inflate stream Z_NO_FLUSH
  return { l with err }

/-- The loop condition of `uncompress2_z`. -/
def loopCond : UncLoop → M (Bool × UncLoop) := fun l => pure (l.err == Z_OK, l)

/-- A refill of at most `2^32 - 1` from a 64-bit remaining length. -/
def refill (x : UInt64) : UInt32 := if x > (0xFFFFFFFF : UInt32).toUInt64 then 0xFFFFFFFF else x.toUInt32

/-- The stream after the refills of one iteration. -/
def refilled (z : ZStream) (l : UncLoop) : ZStream :=
  { z with
    avail_out := if z.avail_out = 0 then refill l.left else z.avail_out
    avail_in := if z.avail_in = 0 then refill l.len else z.avail_in }

/-- The remaining lengths after the refills of one iteration. -/
def refilledLoop (z : ZStream) (l : UncLoop) : UncLoop :=
  { l with
    left := if z.avail_out = 0 then l.left - (refill l.left).toUInt64 else l.left
    len := if z.avail_in = 0 then l.len - (refill l.len).toUInt64 else l.len }

theorem loopBody_run {H : Heap} {r : ZStreamRef} {z : ZStream} (l : UncLoop)
    (hz : r.get H = some z) (ro : r.isRo = false) :
    loopBody (some r) l H =
      (do let e ← inflate (some r) Z_NO_FLUSH; pure { refilledLoop z l with err := e } : M UncLoop)
        (r.put H (refilled z l)) := by
  have self : r.put H z = H := by
    cases r with
    | tab i => simp only [ZStreamRef.get] at hz; simp [ZStreamRef.put, hz, upd_self _ _ _ hz]
    | in_gzstate_strm i =>
      simp only [ZStreamRef.get] at hz
      cases e : H.gzstates i with
      | none => simp [e] at hz
      | some g => simp [e] at hz; subst hz; simp [ZStreamRef.put, e, upd_self _ _ _ e]
  unfold loopBody
  by_cases ho : z.avail_out = 0 <;> by_cases hi : z.avail_in = 0 <;>
    simp [ldZ, updZ, ldZStream, stZStream, hz, ro, ho, hi, ZStreamRef.get_put_same hz,
      ZStreamRef.put_put, refilled, refilledLoop, refill, self] <;>
    rfl

end ZlibF.Spec.Public.Proofs.Uncompress
