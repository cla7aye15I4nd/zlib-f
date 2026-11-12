import ZlibF.Proof.«deflate.c.universal-call-tailstep»

/-!
# deflate.c: the rest of one call after the entry phase

Owner 2 of the deflate split (`deflate_call`). After the entry phase of an accepted call with
output space, nothing pending and progress possible, the state is `{ d with last_flush := flush }`.
From there the header phase (skipped in `BUSY_STATE` and `FINISH_STATE`), the strategy phase and
the trailer run; this module gives their result from the state before the call (`TailOut`).
-/

namespace Zlib.Deflate.Universal.Call
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Deflate.Engine.Proofs
open Zlib.Trees.Proofs.Out (TreesInvAt)
set_option autoImplicit false

/-- In `BUSY_STATE` and `FINISH_STATE` the header phase does nothing. -/
theorem header_skip {h : Heap} {r : ZStreamRef} {ds : Nat} {d : DeflateState} (hs : h.dstates ds = some d)
    (busy : d.status = BUSY_STATE ∨ d.status = FINISH_STATE) (flush : Int32) (k : M Int32) :
    headerPhase (some r) (some (.tab ds)) flush k h = k h := by
  have ne : ∀ s, s = INIT_STATE ∨ s = GZIP_STATE ∨ s = EXTRA_STATE ∨ s = NAME_STATE ∨ s = COMMENT_STATE ∨
      s = HCRC_STATE → d.status ≠ s := by
    intro s hs e
    rcases busy with b | b <;> rw [b] at e <;> subst e <;>
      rcases hs with x | x | x | x | x | x <;> exact absurd x (by decide)
  rw [header_stages, wrap_stage_skip hs _ (fun c => ne _ (Or.inl rfl) c.1),
    init_stage_skip hs _ (ne _ (Or.inl rfl)), gzip_stage_skip hs _ (ne _ (Or.inr (Or.inl rfl))),
    extra_stage_skip hs _ (ne _ (Or.inr (Or.inr (Or.inl rfl)))),
    name_stage_skip hs _ (ne _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))),
    comment_stage_skip hs _ (ne _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))),
    hcrc_stage_skip hs _ (ne _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))]

/-- Every status is a header state or `BUSY_STATE` or `FINISH_STATE`. -/
theorem status_cases {d : DeflateState} (good : GoodStatus d.status) :
    Writing d ∨ d.status = BUSY_STATE ∨ d.status = FINISH_STATE := by
  unfold GoodStatus at good
  unfold Writing
  rcases good with e | e | e | e | e | e | e | e
  · exact Or.inl (Or.inl e)
  · exact Or.inl (Or.inr (Or.inl e))
  · exact Or.inl (Or.inr (Or.inr (Or.inl e)))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl e))))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e)))))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr e)))))
  · exact Or.inr (Or.inl e)
  · exact Or.inr (Or.inr e)

/-- **The rest of a call with nothing pending at entry**, from the state before the call: the
entry has stored `last_flush := flush`; then the header phase (or nothing in `BUSY_STATE` and
`FINISH_STATE`), the strategy phase and the trailer. -/
theorem cont_empty (tiny : Block.TinyOverlay) {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState} {flush : Int32}
    (inv : DInv h r ds z d) (header : HeaderInv d) (facts : CallFacts d) (buffers : StreamBuffers h r)
    (active : ActiveHeader h r) (pend : d.pending = 0) (accepted : ¬ DeflateRefuses z d flush)
    (room : z.avail_out ≠ 0) (np : ¬ NoProgress z d flush) :
    TailOut h r ds z d flush
      (headerPhase (some r) (some (.tab ds)) flush
        (strategyPhase (some r) (some (.tab ds)) flush (trailerPhase (some r) (some (.tab ds)) flush))
        (setD h ds { d with last_flush := flush })) := by
  unfold DeflateRefuses at accepted
  have valid : 0 ≤ flush.toInt ∧ flush.toInt ≤ 5 := by omega
  have out : z.next_out ≠ .null := fun e => accepted (Or.inr (Or.inr (Or.inl e)))
  have input : z.avail_in ≠ 0 → z.next_in ≠ .null :=
    fun ne e => accepted (Or.inr (Or.inr (Or.inr (Or.inl ⟨e, ne⟩))))
  have lfNot : flush ≠ -2 := by
    intro e; rw [e] at valid; exact absurd valid.1 (by decide)
  have lfRange : -2 ≤ flush.toInt ∧ flush.toInt ≤ 5 := ⟨by omega, valid.2⟩
  obtain ⟨pb, buf, trees⟩ := inv_trees inv
  obtain ⟨good1, trees1, buffers1⟩ := last_flush_engine (pb := pb) (buf := buf) flush inv.good trees buffers
  have seg0 : Seg h (setD h ds { d with last_flush := flush }) r ds d z z { d with last_flush := flush } :=
    ⟨0, 0, strat_frame_setD inv.good _ rfl, fun _ => Iff.rfl⟩
  rcases status_cases inv.good.live.status with writing | busy
  · have entry : HeaderEntry (setD h ds { d with last_flush := flush }) z { d with last_flush := flush } ds pb buf := by
      have keep : CallerKeep h (setD h ds { d with last_flush := flush }) z ds pb :=
        CallerKeep.of_frame (HeaderFrame.state (r := r) pb inv.good.live.hs { d with last_flush := flush } rfl)
      rcases writing with e | e | e | e | e | e
      · exact fresh_header_entry inv.good trees active keep (stream_accounting_zero z) rfl rfl rfl (Or.inl e) pend room
      · exact fresh_header_entry inv.good trees active keep (stream_accounting_zero z) rfl rfl rfl (Or.inr e) pend room
      all_goals
        have size : 0 < buf.size := by have := trees.base.size; have := trees.base.lit_lo; omega
      · exact resumed_header_entry inv.good trees active header keep (stream_accounting_zero z) rfl rfl rfl rfl
          (Or.inl e) pend size
      · exact resumed_header_entry inv.good trees active header keep (stream_accounting_zero z) rfl rfl rfl rfl
          (Or.inr (Or.inl e)) pend size
      · exact resumed_header_entry inv.good trees active header keep (stream_accounting_zero z) rfl rfl rfl rfl
          (Or.inr (Or.inr (Or.inl e))) pend size
      · exact resumed_header_entry inv.good trees active header keep (stream_accounting_zero z) rfl rfl rfl rfl
          (Or.inr (Or.inr (Or.inr e))) pend size
    have low : d.bi_valid.toInt < 8 := by have := inv.shape.biValid; omega
    obtain ⟨after, z', d', produced, inv', header', buffers', acc, frame, own, out', branch⟩ :=
      header_step_mid inv header good1 trees1 trees.base.pbuf buffers1 (inv.shape.cursor pend) out inv.alloc
        rfl rfl rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) low lfRange lfNot writing entry flush
        (strategyPhase (some r) (some (.tab ds)) flush (trailerPhase (some r) (some (.tab ds)) flush))
    have seg1 := seg0.trans ⟨0, produced, frame.1, own⟩ inv.good buffers
    rcases branch with ⟨run, _, _, facts', full0⟩ | ⟨run, busy', pend', _, lf', facts'⟩
    · exact ⟨Z_OK, after, z', d', run, inv', header', facts', buffers', seg1, Or.inl rfl,
        fun e => absurd e (by decide), fun _ _ => Or.inr (changed_full room full0)⟩
    · rw [run]
      have input' : z'.avail_in ≠ 0 → z'.next_in ≠ .null := by
        intro ne
        have ain : z'.avail_in = z.avail_in := UInt32.toNat_inj.mp (by have := acc.2.2.1; omega)
        have nin : z'.next_in = z.next_in := by rw [acc.2.2.2.2.1]; cases z.next_in <;> rfl
        rw [nin]; exact input (ain ▸ ne)
      obtain ⟨rc, a3, z3, d3, run3, inv3, header3, facts3, buffers3, seg3, rcs, endF, prog3⟩ :=
        tail_step tiny inv' header' facts' buffers' out' input' pend' (Or.inl busy')
          (by rw [lf']; exact lfNot) (fun e => absurd (busy'.symm.trans e) (by decide)) flush
      refine ⟨rc, a3, z3, d3, run3, inv3, header3, facts3, buffers3, seg1.trans seg3 inv.good buffers, rcs, endF,
        fun f _ => ?_⟩
      by_cases full' : z'.avail_out = 0
      · exact Or.inr (seg_changed seg1 seg3 (Or.inl (changed_full room full')))
      · rcases prog3 f full' with e | c
        · exact Or.inl e
        · exact Or.inr (seg_changed seg1 seg3 (Or.inr c))
  · have hs1 : (setD h ds { d with last_flush := flush }).dstates ds = some { d with last_flush := flush } :=
      setD_dstates_same _ _ _
    rw [header_skip hs1 busy]
    obtain ⟨inv1, header1, facts1, _, buffers1', _⟩ :=
      post_store inv facts trees buffers busy d.status flush (Or.inl rfl) lfRange lfNot
    have finIn : d.status = FINISH_STATE → z.avail_in = 0 := fun e =>
      Classical.byContradiction fun ne => np (Or.inr ⟨e, ne⟩)
    obtain ⟨rc, a3, z3, d3, run3, inv3, header3, facts3, buffers3, seg3, rcs, endF, prog3⟩ :=
      tail_step tiny inv1 header1 facts1 buffers1' out input pend busy lfNot finIn flush
    exact ⟨rc, a3, z3, d3, run3, inv3, header3, facts3, buffers3, seg0.trans seg3 inv.good buffers, rcs, endF,
      prog3⟩

end Zlib.Deflate.Universal.Call
