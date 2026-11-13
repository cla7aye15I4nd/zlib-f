import ZlibF.Proof.«deflate.c.universal-init»
import ZlibF.Proof.«deflate.c.universal-ops»
import ZlibF.Proof.«deflate.c.universal-ops-reset»
import ZlibF.Proof.«deflate.c.universal-ops-prime»

/-!
# deflate.c: the header facts `HeaderInv` after init and the stream operations

`HeaderInv d` (`deflate.c.universal-invariant`) holds beside `DInv` in every reachable state: in
a header state no symbol is recorded, and a state that writes the gzip header from a caller's
record keeps that record. This module shows it after a successful `deflateInit2_` and after the
operations that only write the state record.

Each lemma has the form: from a run of the operation and `HeaderInv` of the state before, every
state record at `ds` after the run satisfies `HeaderInv`.
-/

namespace Zlib.Deflate.Proofs.GeneralInit
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Engine.Proofs
open Zlib.Deflate.Universal ZlibF.Spec.Public
open DefaultInit
open Zlib.Trees.Proofs.Out (ibRec trInitRec)
set_option autoImplicit false
set_option maxRecDepth 4096
variable (wrap : Int32) (wb mem : Nat)

/-- The result state of `deflateInit2_` has no symbol and no gzip record state. -/
theorem success_header (h : Heap) (r : ZStreamRef) (level strategy : Int32) (a1 a2 a3 : Array CtData) :
    HeaderInv (resultState wrap wb mem h r level strategy a1 a2 a3) := by
  constructor
  · intro _
    simp [resultState, finalState, lmD, resetState, rkPost, rkPost3, rkMid, ibRec, trInitRec,
      readyState, allocatedState, baseState]
  · intro e
    exfalso
    simp only [resultState, finalState, lmD, resetState, rkPost, rkPost3, rkMid, ibRec, trInitRec,
      readyState, allocatedState, baseState] at e
    revert e
    by_cases c : (absWrap wrap == 2) = true <;> simp only [c, ite_true, ite_false, Bool.false_eq_true] <;> decide

end Zlib.Deflate.Proofs.GeneralInit

namespace Zlib.Deflate.Universal
open C Zlib.Deflate Zlib.Deflate.Spec ZlibF.Spec.Public Zlib.Deflate.Proofs.GeneralInit
open Zlib.Deflate.Proofs Zlib.Deflate.Proofs.DefaultInit
open ZlibF.Spec.Public.Proofs.DeflateInit (globals_trees)
open Zlib.Deflate.Engine.Proofs
open Zlib.Trees.Proofs.Out (setB)
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

/-- **A successful `deflateInit2_` establishes the invariant and the header facts.** The run is
`init2_inv`'s: the success path of `alloc`, whose result state is `resultState`. -/
theorem init2_header {h after : Heap} {r : ZStreamRef} {z : ZStream} {version : BPtr}
    {level method wb mem strategy : Int32}
    (fresh : Fresh h) (uniq : Zlib.Deflate.Spec.Uniq h) (globals : LibraryGlobals h)
    (get : r.get h = some z) (allocators : DefaultOrNull z) (ver : VersionValue h version (some 49))
    (run : C.run (Zlib.Deflate.deflateInit2_ (some r) level method wb mem strategy version 112) h =
      .ok (Z_OK, after)) :
    ∃ ds z' d, DInv after r ds z' d ∧ HeaderInv d := by
  obtain ⟨rc, after', run', facts⟩ := init2_main level method wb mem strategy h r z version fresh uniq globals
    get allocators ver
  have same := run.symm.trans run'
  simp only [Except.ok.injEq, Prod.mk.injEq] at same
  obtain ⟨rcEq, afterEq⟩ := same
  subst afterEq
  subst rcEq
  let zp := preparedStream z
  let hp := r.put h zp
  have hshape := shape_put get zp
  have hfP : Fresh hp := hshape.fresh (by simp [hp]) fresh
  have huP : Uniq hp := hshape.uniq uniq
  have hzP : r.get hp = some zp := ZStreamRef.get_put_same get _
  have haP : DefAlloc zp := prepared_allocators allocators
  have entry : C.run (deflateInit2_ (some r) level method wb mem strategy version 112) h =
      (match ZlibF.Spec.Api.deflInit? level.toInt method.toInt wb.toInt mem.toInt strategy.toInt with
      | none => pure Z_STREAM_ERROR
      | some p => alloc (some r) (Int32.ofNat p.level) (wrapCode p.wrap) p.wbits p.memLevel method strategy) hp := by
    rw [C.run, GeneralInit.entry_run get ver, tail_params]
    rfl
  cases params : ZlibF.Spec.Api.deflInit? level.toInt method.toInt wb.toInt mem.toInt strategy.toInt with
  | none =>
    rw [params] at facts
    exact absurd facts.1 (by decide)
  | some p =>
    rw [params] at facts entry
    dsimp only at facts entry
    obtain ⟨m8, l9, w9, w15, m1, m9, mEq, s0, s4, sEq⟩ := params_ranges params
    have meth : method = 8 := Int32.toInt_inj.mp (by rw [m8]; rfl)
    subst meth
    by_cases first : h.allocOk h.nalloc = false
    · simp only [first, ite_true] at facts
      exact absurd facts.1 (by decide)
    · simp only [first, ite_false, Bool.false_eq_true] at facts
      by_cases all : (List.range 5).all (fun j => h.allocOk (h.nalloc + j)) = true
      · have allok : ∀ j, j < 5 → h.allocOk (h.nalloc + j) = true := by
          simpa only [List.all_eq_true, List.mem_range] using all
        let lev : Int32 := Int32.ofNat p.level
        have levInt : lev.toInt = p.level := Int32.toInt_ofNat_of_lt (by omega)
        have countP : ∀ j, j < 5 → hp.allocOk (hp.nalloc + j) = true := by
          intro j hj
          simpa [hp] using allok j hj
        have hw0 : 0 ≤ (wrapCode p.wrap).toInt := by cases p.wrap <;> decide
        obtain ⟨a1, a2, a3, qa, hsucc, good, bl, frequencies, -⟩ := allocate_success (wrapCode p.wrap)
          p.wbits p.memLevel hfP huP hzP haP (by simpa [hp] using globals_trees globals) countP lev strategy
          (by omega) (by omega) s0 s4 hw0 (by cases p.wrap <;> decide) w9 w15 m1 m9
        have eq := run.symm.trans (entry.trans hsucc)
        simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at eq
        subst eq
        refine ⟨_, _, _, success_dinv (wrapCode p.wrap) p.wbits p.memLevel good ?_ ?_ bl frequencies hw0 m1 m9,
          success_header (wrapCode p.wrap) p.wbits p.memLevel _ _ _ _ _ _ _⟩
        · exact ⟨by simpa [GeneralInit.resultStream, rkZ, GeneralInit.stateStream] using haP.1,
            by simpa [GeneralInit.resultStream, rkZ, GeneralInit.stateStream] using haP.2⟩
        · unfold LibraryGlobals at globals ⊢
          simpa [GeneralInit.successHeap, GeneralInit.readyHeap, GeneralInit.successfulBuffers, GeneralInit.publishedHeap, stateHeap, setW, setD, hp]
            using globals
      · simp only [all, Bool.false_eq_true, ite_false] at facts
        exact absurd facts.2.1 (by decide)

/-- `deflateTune` writes only the four tuning fields. -/
theorem tune_header {h after : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d d' : DeflateState}
    {g m n c rc : Int32} (good : DGood h r ds z d) (header : HeaderInv d)
    (run : C.run (deflateTune (some r) g m n c) h = .ok (rc, after)) (state : after.dstates ds = some d') :
    HeaderInv d' := by
  obtain ⟨_, run', rfl, _, _⟩ := deflateTune_safe good g m n c
  have same := run.symm.trans run'
  simp only [Except.ok.injEq, Prod.mk.injEq] at same
  obtain ⟨-, rfl⟩ := same
  rw [setD_dstates_same] at state
  cases state
  exact header.keep rfl rfl rfl

/-- `deflateSetHeader` before the header is written (`StreamArguments` asks for `INIT_STATE` or
`GZIP_STATE`): the record facts are vacuous there, and no symbol changes. -/
theorem setHeader_header {h after : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d d' : DeflateState}
    {head : GzHeaderPtr} {rc : Int32} (good : DGood h r ds z d) (header : HeaderInv d)
    (started : d.status = INIT_STATE ∨ d.status = GZIP_STATE)
    (run : C.run (deflateSetHeader (some r) head) h = .ok (rc, after)) (state : after.dstates ds = some d') :
    HeaderInv d' := by
  by_cases wrap : d.wrap = 2
  · obtain ⟨_, run', rfl, _, _⟩ := deflateSetHeader_safe good wrap head (gzOk_any h head)
    have same := run.symm.trans run'
    simp only [Except.ok.injEq, Prod.mk.injEq] at same
    obtain ⟨-, rfl⟩ := same
    rw [setD_dstates_same] at state
    cases state
    refine ⟨fun e => header.empty e, fun e => ?_⟩
    exfalso
    change d.status = EXTRA_STATE ∨ d.status = NAME_STATE ∨ d.status = COMMENT_STATE ∨
      d.status = HCRC_STATE at e
    rcases started with st | st <;> rw [st] at e <;> revert e <;> decide
  · have run' := deflateSetHeader_run_other good.live wrap head
    rw [C.run] at run
    have same := run.symm.trans run'
    simp only [Except.ok.injEq, Prod.mk.injEq] at same
    obtain ⟨-, rfl⟩ := same
    rw [good.live.hs] at state
    cases state
    exact header

/-- The state `deflateReset` leaves: `INIT_STATE` (or `BUSY_STATE` for raw deflate), no symbol,
no gzip record state. -/
theorem reset_state_header (ds : Nat) (d : DeflateState) (a1 a2 a3 : Array CtData) :
    HeaderInv (lmD (rkPost ds (rkMid d) a1 a2 a3)) := by
  constructor
  · intro _
    simp [lmD, rkPost, rkPost3, rkMid, Zlib.Trees.Proofs.Out.ibRec, Zlib.Trees.Proofs.Out.trInitRec]
  · intro e
    exfalso
    simp only [lmD, rkPost, rkPost3, rkMid, Zlib.Trees.Proofs.Out.ibRec,
      Zlib.Trees.Proofs.Out.trInitRec] at e
    revert e
    first
      | decide
      | (split <;> decide)
      | (by_cases c : (absWrap d.wrap == 2) = true <;>
          simp only [c, ite_true, ite_false, Bool.false_eq_true] <;> decide)

/-- **`deflateReset`** leaves the header facts, whatever the state before. -/
theorem reset_header {h after : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d d' : DeflateState}
    {rc : Int32} (good : DGood h r ds z d)
    (run : C.run (deflateReset (some r)) h = .ok (rc, after)) (state : after.dstates ds = some d') :
    HeaderInv d' := by
  obtain ⟨c1, c2, c3, h1, e1, rfl, -, -, -, good1, -⟩ := deflateResetKeep_safe good
  obtain ⟨q, qa, h2, e2, -, -, he, -, -⟩ := lm_init_safe good1
  have run' : C.run (deflateReset (some r)) h = .ok (Z_OK, h2) := by
    have hz1 := good1.live
    unfold deflateReset
    rw [C.run] at e1 ⊢
    simp only [bind_app, e1, beq_self_eq_true, ↓reduceIte, zrd_eq, hz1.hz, hz1.zst, castD, pure_app]
    rw [C.run] at e2
    rw [e2]
  have same := run.symm.trans run'
  simp only [Except.ok.injEq, Prod.mk.injEq] at same
  obtain ⟨-, rfl⟩ := same
  rw [he, setD_dstates_same] at state
  cases state
  exact reset_state_header ds d c1 c2 c3

/-- **`deflatePrime`** writes only `pending_buf` and the pending and bit fields of the state. -/
theorem prime_header {h after : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d d' : DeflateState}
    {bits value rc : Int32} (inv : DInv h r ds z d) (header : HeaderInv d)
    (run : C.run (deflatePrime (some r) bits value) h = .ok (rc, after)) (state : after.dstates ds = some d') :
    HeaderInv d' := by
  have good := inv.good
  have hL := good.live
  by_cases range : bits.toInt < 0 ∨ 16 < bits.toInt
  · have same := run.symm.trans (deflatePrime_invalid_count hL bits value range)
    simp only [Except.ok.injEq, Prod.mk.injEq] at same
    obtain ⟨-, rfl⟩ := same
    rw [hL.hs] at state
    cases state
    exact header
  have b0 : 0 ≤ bits.toInt := by omega
  have b16 : bits.toInt ≤ 16 := by omega
  obtain ⟨d0, b, buf, trees⟩ := good.trees
  have e0 : d0 = d := Option.some.inj (trees.base.dstate.symm.trans hL.hs)
  rw [e0] at trees
  obtain ⟨w, p, q, b', blocks⟩ := good.inv.blocks
  have bb : b = b' := by
    have := blocks.pbuf; rw [trees.base.pbuf] at this; cases this; rfl
  subst bb
  obtain ⟨off, pout, offFit⟩ := blocks.pout
  have v0 : 0 ≤ d.bi_valid.toInt := good.inv.bits.1
  have v7 : d.bi_valid.toInt ≤ 7 := inv.shape.biValid
  have notRange : (bits < 0 || bits > 16) = false := by
    have l1 : ¬ bits < 0 := fun lt => by have := Int32.lt_iff_toInt_lt.mp lt; simp at this; omega
    have l2 : ¬ bits > 16 := fun lt => by have := Int32.lt_iff_toInt_lt.mp lt; simp at this; omega
    simp [l1, l2]
  have move : ∃ a, deflatePrime (some r) bits value h =
      primeTail (some (.tab ds)) bits value (setD (setB h b a) ds { d with pending_out := d.pending_buf }) ∧
      a.size = buf.size := by
    by_cases mv : d.pending_out = d.pending_buf
    · refine ⟨buf, ?_, rfl⟩
      have same : ({ d with pending_out := d.pending_buf } : DeflateState) = d := by
        cases d; simp only at mv; subst mv; rfl
      rw [same, self_heap trees.base.bytes hL.hs, prime_split]
      simp [stateCheck_live hL, zrd_eq, hL.hz, hL.zst, castD, ldD_eq, hL.hs, notRange, mv]
    · obtain ⟨st, a, loop, size⟩ := move_loop trees.base.bytes trees.base.rw d.pending (off := off)
        (by have := trees.base.psize; omega)
      have loop' : cwhile moveCond moveBody (d.pending, d.pending_buf, d.pending_out) h = .ok (st, setB h b a) := by
        rw [trees.base.pbuf, pout]; exact loop
      refine ⟨a, ?_, size⟩
      rw [prime_split]
      simp [stateCheck_live hL, zrd_eq, hL.hz, hL.zst, castD, ldD_eq, hL.hs, notRange, mv, loop', wrD_eq]
  obtain ⟨a, runMove, sizeA⟩ := move
  obtain ⟨_, trees1⟩ := move_good good trees sizeA
  obtain ⟨rc', bf, e, runTail, -, -, ⟨p2, w2, v2, u2, rfl⟩, -⟩ :=
    prime_tail bits value trees1 b0 b16 v0 v7
  rw [C.run, runMove, runTail] at run
  simp only [Except.ok.injEq, Prod.mk.injEq] at run
  obtain ⟨-, rfl⟩ := run
  rw [setD_dstates_same] at state
  cases state
  exact header.keep rfl rfl rfl

end Zlib.Deflate.Universal
