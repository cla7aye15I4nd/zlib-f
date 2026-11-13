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

/-- A call moved input or output. -/
def Changed (z z' : ZStream) : Prop := z'.avail_in ≠ z.avail_in ∨ z'.avail_out ≠ z.avail_out

/-- Movement composes: both counts only decrease. -/
theorem changed_after {z0 z1 z2 : ZStream} {u1 p1 u2 p2 : Nat} (a1 : StreamAccounting z0 z1 u1 p1)
    (a2 : StreamAccounting z1 z2 u2 p2) (c : Changed z0 z1 ∨ Changed z1 z2) : Changed z0 z2 := by
  have i1 := a1.2.2.1; have o1 := a1.2.2.2.1; have i2 := a2.2.2.1; have o2 := a2.2.2.2.1
  unfold Changed at c ⊢
  rcases c with (c | c) | (c | c)
  · left; intro e; apply c; apply UInt32.toNat_inj.mp; have := congrArg UInt32.toNat e; omega
  · right; intro e; apply c; apply UInt32.toNat_inj.mp; have := congrArg UInt32.toNat e; omega
  · left; intro e; apply c; apply UInt32.toNat_inj.mp; have := congrArg UInt32.toNat e; omega
  · right; intro e; apply c; apply UInt32.toNat_inj.mp; have := congrArg UInt32.toNat e; omega

/-- Output room at the start and none at the end. -/
theorem changed_full {z z' : ZStream} (room : z.avail_out ≠ 0) (full : z'.avail_out = 0) : Changed z z' :=
  Or.inr (fun e => room (e ▸ full))

/-- A byte delivered. -/
theorem changed_produced {z z' : ZStream} {used produced : Nat} (acc : StreamAccounting z z' used produced)
    (one : 1 ≤ produced) : Changed z z' := by
  right; intro e
  have := acc.2.2.2.1
  rw [e] at this; omega

/-- What the trailer alone gives. -/
def TrailOut (h0 : Heap) (r : ZStreamRef) (ds : Nat) (z0 : ZStream) (d0 : DeflateState) (flush : Int32)
    (run : Except Fault (Int32 × Heap)) : Prop :=
  ∃ rc after z' d', run = .ok (rc, after) ∧ DInv after r ds z' d' ∧ HeaderInv d' ∧ CallFacts d' ∧
    StreamBuffers after r ∧ Seg h0 after r ds d0 z0 z' d' ∧ (rc = Z_OK ∨ rc = Z_STREAM_END) ∧
    (rc = Z_STREAM_END → flush = Z_FINISH ∧ d'.status = FINISH_STATE ∧ z'.avail_in = 0 ∧ d'.pending = 0 ∧
      d'.bi_valid = 0) ∧
    (flush = Z_FINISH → z0.avail_out ≠ 0 → rc = Z_STREAM_END ∨ Changed z0 z')

/-- What the strategy phase and the trailer give: also, with input and output room, a change of
the stream counters. -/
def TailOut (h0 : Heap) (r : ZStreamRef) (ds : Nat) (z0 : ZStream) (d0 : DeflateState) (flush : Int32)
    (run : Except Fault (Int32 × Heap)) : Prop :=
  ∃ rc after z' d', run = .ok (rc, after) ∧ DInv after r ds z' d' ∧ HeaderInv d' ∧ CallFacts d' ∧
    StreamBuffers after r ∧ Seg h0 after r ds d0 z0 z' d' ∧ (rc = Z_OK ∨ rc = Z_STREAM_END) ∧
    (rc = Z_STREAM_END → flush = Z_FINISH ∧ d'.status = FINISH_STATE ∧ z'.avail_in = 0 ∧ d'.pending = 0 ∧
      d'.bi_valid = 0) ∧
    (flush = Z_FINISH → z0.avail_out ≠ 0 → rc = Z_STREAM_END ∨ Changed z0 z') ∧
    (z0.avail_in ≠ 0 → z0.avail_out ≠ 0 → Changed z0 z')

/-- The trailer alone, run when no input is left. -/
theorem TailOut.of_trail {h0 : Heap} {r : ZStreamRef} {ds : Nat} {z0 : ZStream} {d0 : DeflateState}
    {flush : Int32} {run : Except Fault (Int32 × Heap)} (t : TrailOut h0 r ds z0 d0 flush run)
    (empty : z0.avail_in = 0) : TailOut h0 r ds z0 d0 flush run := by
  obtain ⟨rc, after, z', d', e, a, b, c, f, g, i, j, k⟩ := t
  exact ⟨rc, after, z', d', e, a, b, c, f, g, i, j, k, fun ne => absurd empty ne⟩

/-- With `Z_FINISH` and a non-positive `wrap`, the trailer phase returns `Z_STREAM_END` at once. -/
theorem trailer_nonpos {h : Heap} {r : ZStreamRef} {ds : Nat} {d : DeflateState} (hs : h.dstates ds = some d)
    (np : d.wrap ≤ 0) : trailerPhase (some r) (some (.tab ds)) Z_FINISH h = .ok (Z_STREAM_END, h) := by
  unfold trailerPhase
  simp [bind_app, rdD_eq, hs, np, pure_app]

/-- The trailer alone. -/
theorem tail_trailer {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv h r ds z d) (header : HeaderInv d) (facts : CallFacts d) (buffers : StreamBuffers h r)
    (out : z.next_out ≠ .null) (flush : Int32)
    (endFacts : flush = Z_FINISH → d.status = FINISH_STATE ∧ d.pending = 0 ∧ z.avail_in = 0 ∧ d.bi_valid = 0) :
    TrailOut h r ds z d flush (trailerPhase (some r) (some (.tab ds)) flush h) := by
  obtain ⟨pb, buf, trees⟩ := inv_trees inv
  obtain ⟨rc, after, z1, d1, produced, run, inv1, header1, facts1, buffers1, _, acc, stage, shapeEq, rcs, endF,
    _, _, endIff, p2⟩ := trailer_step inv header facts trees buffers out flush (fun f => ⟨(endFacts f).1, (endFacts f).2.1⟩)
  refine ⟨rc, after, z1, d1, run, inv1, header1, facts1, buffers1, ⟨0, produced, stage.1, ?_⟩, rcs, ?_, ?_⟩
  · intro b; rw [shapeEq]; exact Iff.rfl
  · intro e
    obtain ⟨f, st, p⟩ := endF e
    obtain ⟨_, _, ain, bv⟩ := endFacts f
    refine ⟨f, st, ?_, p, ?_⟩
    · have h3 := acc.2.2.1
      rw [ain] at h3
      exact UInt32.toNat_inj.mp (by simp at h3 ⊢; omega)
    · rw [shapeEq]; exact bv
  · intro f room
    rcases rcs with ok | e
    · by_cases w : 0 < d.wrap.toInt
      · exact Or.inr (changed_full room (p2 ok f w))
      · subst f
        have np : d.wrap ≤ 0 := Int32.le_iff_toInt_le.mpr (by change d.wrap.toInt ≤ 0; omega)
        have e := (trailer_nonpos (r := r) inv.good.live.hs np).symm.trans run
        exact Or.inl (Prod.mk.inj (Except.ok.inj e)).1.symm
    · exact Or.inl e

end Zlib.Deflate.Universal.Call
