import ZlibF.Proof.«deflate.c.universal-call-strateval»
import ZlibF.Proof.«deflate.c.universal-call-markerstep»
import ZlibF.Proof.«deflate.c.universal-call-trailerstep»
import ZlibF.Proof.«deflate.c.universal-call-strategy-pars»
import ZlibF.Proof.«deflate.c.universal-call-strategy-range»

/-!
# deflate.c: the strategy phase and the trailer of one call

Owner 2 of the deflate split (`deflate_call`). From the state after the header phase
(`BUSY_STATE` or `FINISH_STATE`, nothing pending), the strategy phase and the trailer keep
`DInv ∧ HeaderInv ∧ CallFacts`, give the call segment (`Seg`: the strategy frame and the owned
blocks), return `Z_OK` or `Z_STREAM_END`, and give the `Z_STREAM_END` facts of `Goal.deflate`.

This module holds the segment algebra (`Seg`), the result form (`TailOut`) and the trailer
alone; `tail_step` is in `deflate.c.universal-call-tailstep`, after batch B's
`deflate.c.universal-strategy-gaps`.
-/

namespace Zlib.Deflate.Universal.Call
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Deflate.Engine.Proofs
open Zlib.Trees.Proofs.Out (TreesInvAt)
set_option autoImplicit false

/-- **The `CallFacts` clause the deflate owner adds** (M18): a finished stream holds no bits. -/
def FinishBits : Prop :=
  ∀ {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState},
    DInv h r ds z d → CallFacts d → d.status = FINISH_STATE → d.bi_valid = 0

/-- A segment of a call: its strategy frame and the owned blocks kept. -/
def Seg (h0 h1 : Heap) (r : ZStreamRef) (ds : Nat) (d0 : DeflateState) (z0 z1 : ZStream) (d1 : DeflateState) : Prop :=
  ∃ used produced, StratFrame h0 h1 r ds d0 z0 z1 used produced ∧ ∀ b, DeflateOwned ds d1 b ↔ DeflateOwned ds d0 b

theorem Seg.trans {h0 h1 h2 : Heap} {r : ZStreamRef} {ds : Nat} {d0 d1 d2 : DeflateState} {z0 z1 z2 : ZStream}
    (one : Seg h0 h1 r ds d0 z0 z1 d1) (two : Seg h1 h2 r ds d1 z1 z2 d2) (good : DGood h0 r ds z0 d0)
    (buffers : StreamBuffers h0 r) : Seg h0 h2 r ds d0 z0 z2 d2 := by
  obtain ⟨u1, p1, f1, o1⟩ := one
  obtain ⟨u2, p2, f2, o2⟩ := two
  exact ⟨u1 + u2, p1 + p2, StratFrame.trans f1 f2 o1 good.uniq (output_target good buffers),
    fun b => (o2 b).trans (o1 b)⟩

/-- The trees of a state under the invariant. -/
theorem inv_trees {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState} (inv : DInv h r ds z d) :
    ∃ pb buf, TreesInvAt h ds d pb buf := by
  obtain ⟨d0, b0, buf0, trees⟩ := inv.good.trees
  have de : d0 = d := Option.some.inj (trees.base.dstate.symm.trans inv.good.live.hs)
  rw [de] at trees
  exact ⟨b0, buf0, trees⟩

/-- What the strategy phase with the trailer concludes. -/
def TailOut (h0 : Heap) (r : ZStreamRef) (ds : Nat) (z0 : ZStream) (d0 : DeflateState) (flush : Int32)
    (run : Except Fault (Int32 × Heap)) : Prop :=
  ∃ rc after z' d', run = .ok (rc, after) ∧ DInv after r ds z' d' ∧ HeaderInv d' ∧ CallFacts d' ∧
    StreamBuffers after r ∧ Seg h0 after r ds d0 z0 z' d' ∧ (rc = Z_OK ∨ rc = Z_STREAM_END) ∧
    (rc = Z_STREAM_END → flush = Z_FINISH ∧ d'.status = FINISH_STATE ∧ z'.avail_in = 0 ∧ d'.pending = 0 ∧
      d'.bi_valid = 0)

/-- The trailer alone. -/
theorem tail_trailer {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv h r ds z d) (header : HeaderInv d) (facts : CallFacts d) (buffers : StreamBuffers h r)
    (out : z.next_out ≠ .null) (flush : Int32)
    (endFacts : flush = Z_FINISH → d.status = FINISH_STATE ∧ d.pending = 0 ∧ z.avail_in = 0 ∧ d.bi_valid = 0) :
    TailOut h r ds z d flush (trailerPhase (some r) (some (.tab ds)) flush h) := by
  obtain ⟨pb, buf, trees⟩ := inv_trees inv
  obtain ⟨rc, after, z1, d1, produced, run, inv1, header1, facts1, buffers1, _, acc, stage, shapeEq, rcs, endF,
    _, _, _⟩ := trailer_step inv header facts trees buffers out flush (fun f => ⟨(endFacts f).1, (endFacts f).2.1⟩)
  refine ⟨rc, after, z1, d1, run, inv1, header1, facts1, buffers1, ⟨0, produced, stage.1, ?_⟩, rcs, ?_⟩
  · intro b; rw [shapeEq]; exact Iff.rfl
  · intro e
    obtain ⟨f, st, p⟩ := endF e
    obtain ⟨_, _, ain, bv⟩ := endFacts f
    refine ⟨f, st, ?_, p, ?_⟩
    · have h3 := acc.2.2.1
      rw [ain] at h3
      exact UInt32.toNat_inj.mp (by simp at h3 ⊢; omega)
    · rw [shapeEq]; exact bv

end Zlib.Deflate.Universal.Call
