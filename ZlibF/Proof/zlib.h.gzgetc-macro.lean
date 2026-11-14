import ZlibF.Proof.«gzread.c.getc-ungetc»
import ZlibF.Zlib.«zlib.h»

/-!
# zlib.h: the `gzgetc()` macro on a handle in `GzInv`

`gzgetc_macro_run`: with buffered output (`x.have ≠ 0`) the macro `Zlib.ZlibH.gzgetc` returns, with no fault and no
premise on the world, and keeps `GzInv` with the effect of a public call that writes no caller region (`Eff`).

The inline path is the same sequence of statements as the buffered path of the function `gzgetc`, without the
`again` reset before it. `GetcUngetc.getc_buffered` proves that sequence from any record in `GzInv` with
`x.have ≠ 0`: `GzCommon.next` puts `x.next` inside an owned buffer with `x.have` bytes after it, `posHave` keeps
`x.pos + 1` representable, and `haveSkip` gives `skip = 0`. A writer has `x.have = 0` (`GzWriteInv.have0`), so the
inline path runs only on a reader. With `x.have = 0` the macro is the call of the function `gzgetc`
(`gzgetc_macro_all`, from the read leaf `gzgetc_step` given as a hypothesis).
-/

namespace ZlibF.Spec.Public.GzMacro
open C Zlib.GzFs Zlib.Gzguts Zlib.Gzlib.Proofs ZlibF.Spec.Public
open ZlibF.Spec.Public.GetcUngetc
set_option autoImplicit false

theorem gzgetc_macro_eq (i : Nat) : Zlib.ZlibH.gzgetc (some (.in_gzstate_x i)) = (do
    let s ← ldS (some (.tab i))
    if s.x.«have» != 0 then
      updX (some (.tab i)) fun x => { x with «have» := x.«have» - 1 }
      let np ← i64add s.x.pos 1
      updX (some (.tab i)) fun x => { x with pos := np }
      let s ← ldS (some (.tab i))
      let b ← load8 s.x.next
      let nx ← s.x.next.add 1
      updX (some (.tab i)) fun x => { x with next := nx }
      return b.toUInt32.toInt32
    Zlib.Gzread.gzgetc (some (.in_gzstate_x i)) : G Int32) := rfl

/-- A handle with buffered output is a reader. -/
theorem mode_of_have {h : Heap} {i : Nat} {s : GzState} (inv : GzInv h i s) (hh : s.x.have ≠ 0) :
    s.mode = GZ_READ := by
  rcases inv.common.mode with hm | hw
  · exact hm
  · exact absurd (inv.writer hw).have0 hh

/-- **The inline path of the `gzgetc()` macro**: on a handle in `GzInv` with `x.have ≠ 0`, in every world, the
macro returns (no premise: no loop, no OS call) and its effect is `Eff`. -/
theorem gzgetc_macro_run {i : Nat} {h : Heap} {fs : Fs} {s : GzState} (inv : GzInv h i s) (hfs : FileSystem fs)
    (hh : s.x.have ≠ 0) :
    RunSafe (Zlib.ZlibH.gzgetc (some (.in_gzstate_x i))) fs h True
      (fun _ fs' after => Eff i h s fs fs' after) := by
  rw [gzgetc_macro_eq]
  refine RunSafe.bind_lift (ldS_run inv.common.record) ?_
  refine RunSafe.ite (fun _ => getc_buffered (GetcUngetc.Eff.refl inv hfs) inv (mode_of_have inv hh) hh)
    (fun hn => absurd (by simpa using hn) hh)

/-- **The `gzgetc()` macro in either branch**, given the safety of the function `gzgetc` (`gs`, the read leaf
`gzgetc_step`): with buffered output it is the inline path (`gzgetc_macro_run`), which returns with no premise; with
`x.have = 0` it is the call of the function, which returns under `ReadsFinite`. Every result keeps the descriptors and
has the post of the function. -/
theorem gzgetc_macro_all {i : Nat} {h : Heap} {fs : Fs} {s : GzState}
    (gs : GzCallSafe i (.gzgetc (some (.in_gzstate_x i)))) (inv : GzInv h i s) (hfs : FileSystem fs) :
    RunSafe (Zlib.ZlibH.gzgetc (some (.in_gzstate_x i))) fs h
      (s.x.have = 0 → NeedsReadBound (.gzgetc (some (.in_gzstate_x i))) → ReadsFinite fs s.fd)
      (fun _ fs' after => FdsKept fs fs' ∧ GzStepPost h i s (.gzgetc (some (.in_gzstate_x i))) fs' after) := by
  rw [gzgetc_macro_eq]
  refine RunSafe.bind_lift (ldS_run inv.common.record) ?_
  refine RunSafe.ite (fun hn => ?_) (fun hn => ?_)
  · -- `x.have ≠ 0`: the inline path.
    have hh : s.x.have ≠ 0 := by simpa using hn
    have R := getc_buffered (fin := True) (GetcUngetc.Eff.refl inv hfs) inv (mode_of_have inv hh) hh
    exact ⟨R.1, fun _ => R.2.1 trivial, fun v fs' after he => GetcUngetc.Eff.post rfl (R.2.2 v fs' after he)⟩
  · -- `x.have = 0`: the call `(gzgetc)(g)`.
    have hh : s.x.have = 0 := by simpa using hn
    obtain ⟨E, X, P⟩ := gs h fs s inv hfs trivial
    exact ⟨E, fun fin => X (fin hh), P⟩

/-- The macro step in the shape of the goal (conjunct 3 of `Goal.gz_sequence_safety`). -/
theorem gzgetc_macro_safe {i : Nat} {h : Heap} {fs : Fs} {s : GzState}
    (gs : GzCallSafe i (.gzgetc (some (.in_gzstate_x i)))) (inv : GzInv h i s) (hfs : FileSystem fs) :
    (∀ e, Zlib.ZlibH.gzgetc (some (.in_gzstate_x i)) fs h = .error e → e = .outOfFuel) ∧
    ((s.x.have = 0 → NeedsReadBound (.gzgetc (some (.in_gzstate_x i))) → ReadsFinite fs s.fd) →
      ∃ value fs' after, Zlib.ZlibH.gzgetc (some (.in_gzstate_x i)) fs h = .ok ((value, fs'), after)) ∧
    (∀ value fs' after, Zlib.ZlibH.gzgetc (some (.in_gzstate_x i)) fs h = .ok ((value, fs'), after) →
      FdsKept fs fs' ∧ GzStepPost h i s (.gzgetc (some (.in_gzstate_x i))) fs' after) :=
  gzgetc_macro_all gs inv hfs

end ZlibF.Spec.Public.GzMacro
