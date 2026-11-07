import ZlibF.Proof.«deflate.c.engine.slow-search»
import ZlibF.Proof.«deflate.c.engine.advance»
import ZlibF.Proof.«deflate.c.engine.fill-resume-empty»

/-! # The slow strategy's first deferred byte

The first search has no previous match or deferred literal. Its decision
therefore consumes one byte without writing a symbol or flushing a block.
-/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
set_option autoImplicit false

def deferOne (d : DeflateState) : DeflateState :=
  { advanceOne d with match_available := 1 }

theorem defer_one_good {h : Heap} {r : ZStreamRef} {ds top : Nat}
    {z : ZStream} {d : DeflateState}
    (good : DGood h r ds z d) (chains : HeapChains h d top)
    (range : d.strstart.toNat + d.lookahead.toNat ≤ d.window_size.toNat)
    (positive : 1 ≤ d.lookahead.toNat) :
    DGood (setD h ds (deferOne d)) r ds z (deferOne d) ∧
      HeapChains (setD h ds (deferOne d)) (deferOne d) top ∧
      (deferOne d).strstart.toNat + (deferOne d).lookahead.toNat ≤ (deferOne d).window_size.toNat := by
  have advanced := advance_one_good good chains range positive
  have inv : DStInv h ds (deferOne d) :=
    { good.inv with blocks := good.inv.blocks_keys rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl }
  refine ⟨good.setD' (d' := deferOne d) rfl good.live.status inv (by trkeep), ?_, advanced.2.2⟩
  obtain ⟨w, p, q, wa, pa, qa, win, prev, head, hw, hp, hq, H⟩ := advanced.2.1
  exact ⟨w, p, q, wa, pa, qa, win, prev, head, hw, hp, hq, H⟩

theorem slow_defer_run {h : Heap} {ds : Nat} {d : DeflateState}
    (state : h.dstates ds = some d)
    (previous : d.prev_length = 2) (available : d.match_available = 0)
    (flush : Int32) (st : LoopS) (candidate : UInt32) :
    slowDecision (some (.tab ds)) flush st candidate h =
      .ok ({ st with hash_head := candidate, bflush := false }, setD h ds (deferOne d)) := by
  unfold slowDecision
  simp only [bind_app, ldDeflateState_tab state, previous,
    show ((2 : UInt32) ≥ MIN_MATCH_u) = False from by decide, Bool.false_and,
    Bool.false_eq_true, if_false, available]
  change (wr (some (.tab ds)) deferOne >>= fun _ =>
    pure { st with hash_head := candidate, bflush := false }) h = _
  simp [wrD_eq, state, deferOne, advanceOne]

/-- A complete slow loop iteration with sufficient lookahead, initial
lazy length and no deferred literal. Actual insertion and matching are
composed with the source decision. No callee contract is a premise. -/
theorem slow_body_first_defer {h : Heap} {r : ZStreamRef} {ds w p q top : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8} {pa qa : Array UInt16}
    (good : DGood h r ds z d) (env : HashEnv h d w q p wa qa pa)
    (chains : HashChains (wfn qa) (wfn pa) (bfn wa) d.hash_size d.hash_shift d.hash_mask
      d.w_size.toNat top (d.strstart.toNat + d.lookahead.toNat))
    (ordered : top ≤ d.strstart.toNat)
    (range : d.strstart.toNat + d.lookahead.toNat ≤ d.window_size.toNat)
    (lookahead : 262 ≤ d.lookahead.toNat)
    (length : d.match_length = 2) (available : d.match_available = 0)
    (form : InsHForm d.hash_shift d.hash_mask (bfn wa) d.strstart.toNat d.ins_h)
    (flush : Int32) (st : LoopS) :
    ∃ key pos len after,
      let result := deferOne (matchState (lazyPrepare { d with ins_h := key }) pos len)
      deflate_slow_body (some (.tab ds)) flush st h =
        .ok ({ st with hash_head := (wfn qa key.toNat).toUInt32, bflush := false }, after) ∧
      DGood after r ds z result ∧ HeapChains after result (d.strstart.toNat + 1) ∧
      result.strstart.toNat = d.strstart.toNat + 1 ∧
      result.lookahead.toNat = d.lookahead.toNat - 1 ∧
      result.strstart.toNat + result.lookahead.toNat ≤ result.window_size.toNat := by
  obtain ⟨key, found, pos, len, search, goodF, chainsF, bound⟩ :=
    slow_search_preserves good env chains ordered range lookahead
      (by rw [length]; decide) form
  let df := matchState (lazyPrepare { d with ins_h := key }) pos len
  have previous : df.prev_length = 2 := by change d.match_length = 2; exact length
  have avail : df.match_available = 0 := available
  have ranged : df.strstart.toNat + df.lookahead.toNat ≤ df.window_size.toNat := range
  have positive : 1 ≤ df.lookahead.toNat := by change 1 ≤ d.lookahead.toNat; omega
  have advanced := defer_one_good goodF chainsF ranged positive
  have counts := advance_one_counts goodF.inv ranged positive
  refine ⟨key, pos, len, setD found ds (deferOne df), ?_, advanced.1, advanced.2.1,
    counts.1, counts.2.1, advanced.2.2⟩
  have enough : ¬ d.lookahead < MIN_LOOKAHEAD_u := by
    rw [UInt32.lt_iff_toNat_lt]
    change ¬ d.lookahead.toNat < 262
    omega
  rw [slow_body_source]
  simp only [bind_app, rdD_eq, good.live.hs, enough, if_false, search]
  exact slow_defer_run goodF.live.hs previous avail flush st _

end Zlib.Deflate.Engine.Proofs
