import ZlibF.Proof.«deflate.c.universal-ops»
import ZlibF.Proof.«deflate.c.init.general-construct»

/-!
# deflate.c: `deflateReset` keeps the invariant (batch A, `operation_step`)

`deflateReset` is `deflateResetKeep` followed by `lm_init`. From `DInv` the run is the one of
`deflateReset_safe`: the stream record becomes `rkZ`, the state `lmD (rkPost (rkMid d))`, and the
`head` table is cleared. The invariant afterwards is shown field by field, as for the result of
`deflateInit2_` (`success_dinv`): the chains are empty because `head` is cleared, the symbol ledger
is empty with the initial frequencies of `init_block` (`resetKeep_initial`).

`deflateResetKeep` alone is not covered here. It keeps `strstart`, `insert`, the window and the hash
tables but sets `lookahead = 0`, and then `Hashing.chains` of `DInv` does not hold: positions
`strstart - 1` and `strstart - 2` can be chain heads, above the insertion frontier `chainTop`
(reported to the owner of `DInv`).
-/

namespace Zlib.Deflate.Universal
open C ZlibF.Spec ZlibF.Spec.Public Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Engine.Proofs
open Zlib.Deflate.Proofs
open Zlib.Trees.Proofs.Out (ibRec trInitRec)
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- The frame of a run that writes the stream record, the state record and the `head` table. -/
theorem reset_frame {h : Heap} {r : ZStreamRef} {ds q : Nat} {z z' : ZStream} {d d1 d2 : DeflateState}
    {a : Array UInt16} (hz : r.get h = some z) (hq : d.head = .ref (.blk q) 0) :
    Frame h (setD (setW (setD (r.put h z') ds d1) q a) ds d2)
      (fun b => StreamRoot r b ∨ DeflateOwned ds d b) := by
  cases r with
  | tab k =>
    have hk : h.streams k = some z := hz
    simp only [Frame, setD, setW, ZStreamRef.put, hk, true_and]
    refine ⟨Nat.le_refl _, Nat.le_refl _, ?_⟩
    intro x _ hn
    have hi : x ≠ ds := fun e => hn (Or.inr (Or.inl e))
    have hk : x ≠ k := fun e => hn (Or.inl (by simpa [StreamRoot] using e))
    have hq' : x ≠ q := fun e => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by simpa [hq] using e.symm))))))
    simp [upd_ne, hi, hk, hq']
  | in_gzstate_strm k =>
    cases hk : h.gzstates k with
    | none =>
      simp [ZStreamRef.get, hk] at hz
    | some g =>
      simp only [Frame, setD, setW, ZStreamRef.put, hk, true_and]
      refine ⟨Nat.le_refl _, Nat.le_refl _, ?_⟩
      intro x _ hn
      have hi : x ≠ ds := fun e => hn (Or.inr (Or.inl e))
      have hk : x ≠ k := fun e => hn (Or.inl (by simpa [StreamRoot] using e))
      have hq' : x ≠ q := fun e => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by simpa [hq] using e.symm))))))
      simp [upd_ne, hi, hk, hq']

/-- A frame over the invariant's owned blocks is a frame over the history's owned blocks. -/
theorem frame_owned {h after : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    {extra : Nat → Prop} (inv : DInv h r ds z d)
    (frame : Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b)) :
    Frame h after (fun b => StreamRoot r b ∨ StreamOwned h r b ∨ extra b) := by
  obtain ⟨s, a, g, n, m, keep⟩ := frame
  refine ⟨s, a, g, n, m, fun x live nc => keep x live (fun c => nc ?_)⟩
  rcases c with root | owned
  · exact Or.inl root
  · exact Or.inr (Or.inl ((inv.owned x).2 owned))

/-- The allocation ledger of a call that keeps the live blocks and the owned blocks. -/
theorem live_same {h after : Heap} {r : ZStreamRef} {ds ds' : Nat} {z z' : ZStream} {d d' : DeflateState}
    (inv : DInv h r ds z d) (inv' : DInv after r ds' z' d') (live : ∀ b, after.live b ↔ h.live b)
    (sameOwned : ∀ b, DeflateOwned ds d b ↔ DeflateOwned ds' d' b) :
    LiveChange h after
      (fun b => StreamOwned after r b ∧ ¬ h.live b)
      (fun b => StreamOwned h r b ∧ ¬ StreamOwned after r b) := by
  intro b
  rw [live b]
  constructor
  · intro l
    refine Or.inl ⟨l, fun ⟨owned, not⟩ => not ?_⟩
    exact (inv'.owned b).2 ((sameOwned b).1 ((inv.owned b).1 owned))
  · rintro (⟨l, _⟩ | ⟨owned, _⟩)
    · exact l
    · exact owned_live inv.good ((sameOwned b).2 ((inv'.owned b).1 owned))

/-- **`deflateReset` keeps the invariant.** For every state of `DInv`: the call returns `Z_OK`,
writes only the stream record and the owned state and `head` table, and allocates and frees
nothing. -/
theorem step_reset {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv h r ds z d) : StepOk h r (.deflateReset (some r)) := by
  have good := inv.good
  obtain ⟨d0, tb, tbuf, hB, -⟩ := good.trees
  have e0 : d0 = d := Option.some.inj (hB.dstate.symm.trans good.live.hs)
  rw [e0] at hB
  obtain ⟨a1, a2, a3, eK, -, -, -, bl, freq⟩ :=
    GeneralInit.resetKeep_initial good.live hB good.inv.wrap_lo good.inv.wrap_hi
  obtain ⟨c1, c2, c3, h1, e1, rfl, -, -, -, good1, live1⟩ := deflateResetKeep_safe good
  have same := eK.symm.trans e1
  simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at same
  have states := congrArg (fun g : Heap => g.dstates ds) same
  simp only [setD_dstates_same, Option.some.injEq] at states
  have l1 : a1 = c1 := by
    have := congrArg DeflateState.dyn_ltree states
    simpa [rkPost, rkPost3, ibRec] using this
  have l2 : a2 = c2 := by
    have := congrArg DeflateState.dyn_dtree states
    simpa [rkPost, rkPost3, ibRec] using this
  have l3 : a3 = c3 := by
    have := congrArg DeflateState.bl_tree states
    simpa [rkPost, rkPost3, ibRec] using this
  subst l1 l2 l3
  obtain ⟨q, qa, h2, e2, hq, hqa, he, good2, live2⟩ := lm_init_safe good1
  have run : C.run (deflateReset (some r)) h = .ok (Z_OK, h2) := by
    have hz1 := good1.live
    unfold deflateReset
    rw [C.run] at e1 ⊢
    simp only [bind_app, e1, beq_self_eq_true, ↓reduceIte, zrd_eq, hz1.hz, hz1.zst, castD, pure_app]
    rw [C.run] at e2
    rw [e2]
  have hq0 : d.head = .ref (.blk q) 0 := by
    simpa [rkPost, rkPost3, rkMid, ibRec, trInitRec] using hq
  have frame : Frame h h2 (fun b => StreamRoot r b ∨ DeflateOwned ds d b) := by
    rw [he]; exact reset_frame good.live.hz hq0
  have hab := absWrap_range good.inv.wrap_lo good.inv.wrap_hi
  have symRoom := inv.shape.symRoom
  have hashPos : 0 < d.hash_size.toNat := by
    rw [good.inv.hsize]; exact Nat.two_pow_pos _
  -- the invariant after the call
  have inv' : DInv h2 r ds (rkZ z d) (lmD (rkPost ds (rkMid d) a1 a2 a3)) := by
    obtain ⟨w, p, q', b, blocks⟩ := good2.inv.blocks
    have qq : q = q' := by
      have hh := blocks.head
      simp only [lmD, rkPost, rkPost3, rkMid, ibRec, trInitRec, hq0] at hh
      cases hh; rfl
    subst qq
    refine ⟨good2, by simpa [rkZ, DefAlloc] using inv.alloc, ?_, ?_, ?_, ?_⟩
    · unfold LibraryGlobals at *; rw [← frame.1]; exact inv.globals
    · refine Shape.mk ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      all_goals first
        | exact good2.inv.hw
        | (simp [lmD, rkPost, rkPost3, rkMid, ibRec, trInitRec, MIN_MATCH_u]; done)
        | (simp [lmD, rkPost, rkPost3, rkMid, ibRec, trInitRec, MIN_MATCH_u]; omega)
        | (intro neg; simp [lmD, rkPost, rkPost3, rkMid, ibRec, trInitRec] at neg; omega)
    · refine ⟨fun _ => ?_, fun one => ?_, fun _ _ three => ?_⟩
      · obtain ⟨wa, hw, -⟩ := blocks.wa
        obtain ⟨pa, hp, -⟩ := blocks.pa
        obtain ⟨qa2, hq2, size2⟩ := blocks.qa
        have eq2 : clearHead qa d.hash_size.toNat = qa2 := by
          rw [he] at hq2
          simpa [setW, rkPost, rkPost3, rkMid, ibRec, trInitRec] using hq2
        unfold Chains
        refine ⟨w, p, q, wa, pa, qa2, blocks.win, blocks.prev, blocks.head, hw, hp, hq2, chains_empty ?_⟩
        intro k hk
        have hk' : k < d.hash_size.toNat := by
          simpa [lmD, rkPost, rkPost3, rkMid, ibRec, trInitRec] using hk
        have qs : d.hash_size.toNat ≤ qa.size := by
          rw [← eq2, size_clearHead] at size2
          simp [lmD, rkPost, rkPost3, rkMid, ibRec, trInitRec] at size2
          omega
        have zero := clear_head_zero qa d.hash_size.toNat hashPos qs k hk'
        rw [← eq2]
        simp only [wfn, Array.getD_eq_getD_getElem?, zero, Option.getD_some]
      · simp [lmD] at one
      · simp [lmD] at three
    · obtain ⟨buf, hb, -⟩ := blocks.ba
      refine ⟨⟨[], ⟨b, buf, blocks.pbuf, hb, ?_⟩, by simp⟩, ⟨?_, ?_, ?_⟩, ?_⟩
      · apply empty_symbol_ledger
        · simp [lmD, rkPost, rkPost3, ibRec]
        · simpa [lmD, rkPost, rkPost3, rkMid, ibRec, trInitRec] using freq
      · intro k hk
        simpa [lmD, rkPost, rkPost3, rkMid, ibRec, trInitRec] using bl k hk
      · simp [lmD, rkPost, rkPost3, ibRec, trInitRec]
      · simp [lmD, rkPost, rkPost3, ibRec, trInitRec]
      · intro _ _ _ nonzero
        simp [lmD, rkPost, rkPost3, ibRec, trInitRec] at nonzero
  refine ⟨Z_OK, h2, heapCall_run run, ⟨ds, _, _, inv'⟩, ?_, ?_⟩
  · have regions : StreamWriteRegions h r (.deflateReset (some r)) = [] := rfl
    rw [regions]
    refine ⟨?_, fun _ mem => by cases mem⟩
    simp only [restoreRegions, List.foldl]
    exact frame_owned inv frame
  · exact live_same inv inv' (fun b => (live2 b).trans (live1 b))
      (fun b => by simp [DeflateOwned, lmD, rkPost, rkPost3, rkMid, ibRec, trInitRec])

end Zlib.Deflate.Universal
