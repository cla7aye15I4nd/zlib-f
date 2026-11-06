import ZlibF.Proof.«inffast.c.match»
import ZlibF.Proof.«inflate.c.ring»
import ZlibF.Math.LZ77CopySpec

/-!
# Fast match copying and chronological history

The fast copier may read two window segments and then overlapping output.
The result must equal the independent byte-at-a-time copyBack on those
actual saved bytes. Provenance from earlier calls is a separate invariant.
-/

namespace Zlib.Inffast.Spec.MatchHistory
open C Zlib.Inffast Zlib.Inffast.Proofs ZlibF.Math.LZ77Copy

/-- The saved bytes in chronological order at the window's actual base
offset. No default array access may be selected when the window is used. -/
def saved (window : Array UInt8) (ws wn wh woff : Nat) : List UInt8 :=
  (List.range wh).map fun j =>
    window.getD (woff + Zlib.Inflate.Spec.ringSlot ws wn wh j) 0

/-- All physical branches of the fast array result implement the same
independent match, including wraparound and overlap into current output.
An unused window need not have backing storage. -/
def Goal.match_array_refines_lz77 : Prop :=
  ∀ (window bytes : Array UInt8) (ws wn wh woff bg o dist len : Nat),
    wh ≤ ws → wn ≤ ws →
    (wh ≠ 0 → woff + ws ≤ window.size) →
    bg ≤ o → o + len ≤ bytes.size → 0 < dist →
    dist ≤ wh + (o - bg) →
    writtenBytes (matchArr ws wn woff window bg o dist len bytes)
      (o + len) (o - bg + len) =
      ZlibF.Spec.copyBack (saved window ws wn wh woff) dist len
        (writtenBytes bytes o (o - bg))

/-- Actual source copying is a clean too-far rejection or the independent
match on saved bytes and current output. The complete old input/bit/link
frame is retained. This starts at the internal copyMatch cut point. -/
def Goal.actual_copy_match_refines_lz77 : Prop :=
  ∀ (e : Env) (c : Ctx) (bytes : Array UInt8) (msg : BPtr) (mode : UInt32)
    (l : L) (o : Nat),
    CtxOK e c →
    l.out = .ref (.blk e.ob) o → e.bg ≤ o →
    l.op.toNat = o - e.bg →
    1 ≤ l.dist.toNat → 3 ≤ l.len.toNat →
    o + l.len.toNat ≤ bytes.size → l.broke = false →
    let history := saved e.W e.s0.wsize.toNat e.s0.wnext.toNat e.s0.whave.toNat e.woff
    let current := writtenBytes bytes o (o - e.bg)
    if history.length + current.length < l.dist.toNat then
      ∃ (l' : L) (after : Heap) (p : BPtr),
        C.run (copyMatch c l) (e.heap bytes msg mode) = .ok (l', after) ∧
        l'.in_ = l.in_ ∧ l'.hold = l.hold ∧ l'.bits = l.bits ∧
        l'.againL = l.againL ∧ l'.againD = l.againD ∧
        l'.broke = true ∧ l'.out = l.out ∧ after = e.heap bytes p BAD
    else
      ∃ (l' : L) (after : Heap),
        C.run (copyMatch c l) (e.heap bytes msg mode) = .ok (l', after) ∧
        l'.in_ = l.in_ ∧ l'.hold = l.hold ∧ l'.bits = l.bits ∧
        l'.againL = l.againL ∧ l'.againD = l.againD ∧
        l'.broke = false ∧ l'.out = .ref (.blk e.ob) (o + l.len.toNat) ∧
        let result := matchArr e.s0.wsize.toNat e.s0.wnext.toNat e.woff e.W e.bg o
          l.dist.toNat l.len.toNat bytes
        after = e.heap result msg mode ∧
        writtenBytes result (o + l.len.toNat) (o - e.bg + l.len.toNat) =
          ZlibF.Spec.copyBack history l.dist.toNat l.len.toNat current

end Zlib.Inffast.Spec.MatchHistory
