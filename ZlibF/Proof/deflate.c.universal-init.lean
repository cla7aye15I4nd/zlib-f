import ZlibF.Proof.«deflate.c.universal-invariant»
import ZlibF.Proof.«deflate.c.init.general-main»

/-!
# deflate.c: a successful `deflateInit2_` establishes the universal invariant

Batch A of the deflate skeleton (`init2_inv`). The success path of `deflateInit2_` is the actual
run of `alloc` (`deflate.c.init.general-success`), for every parameter tuple that
`Api.deflInit?` accepts. Its result state is `resultState`; this module shows `DInv` for it,
field by field. Nothing about the result is assumed: the scalar fields are computed from the
construction, the chains from the cleared `head` table, the symbol ledger and the block costs
from `init_block`.
-/

namespace Zlib.Deflate.Proofs.GeneralInit
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Engine.Proofs
open Zlib.Deflate.Universal ZlibF.Spec.Public
open DefaultInit
open Zlib.Trees.Proofs.Out (TreesBase TreesInvAt ibRec trInitRec InitialFrequencies)
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
variable (wrap : Int32) (wb mem : Nat)

/-- The cleared `head` table gives empty chains, for every content of `prev`. -/
theorem general_chains {h : Heap} {r : ZStreamRef} {z : ZStream} {level strategy : Int32}
    {a1 a2 a3 : Array CtData} {qa : Array UInt16}
    (good : DGood (successHeap wrap wb mem h r z level strategy a1 a2 a3 qa) r h.nextBlk
      (resultStream wrap wb mem h r z level strategy) (resultState wrap wb mem h r level strategy a1 a2 a3)) :
    HeapChains (successHeap wrap wb mem h r z level strategy a1 a2 a3 qa)
      (resultState wrap wb mem h r level strategy a1 a2 a3) 0 := by
  obtain ⟨w, p, q, b, blocks⟩ := good.inv.blocks
  obtain ⟨wa, hw, _⟩ := blocks.wa
  obtain ⟨pa, hp, _⟩ := blocks.pa
  obtain ⟨heads, hq, size⟩ := blocks.qa
  have qid : q = (publishedHeap h r z wrap wb mem).nextBlk + 2 := by
    simpa only [resultState, finalState, lmD, resetState, rkPost, rkPost3, rkMid,
      ibRec, trInitRec, readyState, allocatedState, Ptr.ref.injEq, WRef.blk.injEq, and_true,
      publishedHeap, stateHeap, ZStreamRef.put_nextBlk, Nat.add_assoc] using blocks.head.symm
  have eq : heads = clearHead qa (UInt32.ofNat (2 ^ (mem + 7))).toNat := by
    rw [qid] at hq
    simpa [successHeap, readyHeap, successfulBuffers, publishedHeap, stateHeap, setW,
      Nat.add_assoc] using hq.symm
  have hs : (resultState wrap wb mem h r level strategy a1 a2 a3).hash_size.toNat =
      (UInt32.ofNat (2 ^ (mem + 7))).toNat := by
    simp [resultState, finalState, lmD, resetState, rkPost, rkPost3, rkMid, ibRec, trInitRec,
      readyState, allocatedState, baseState]
  have qs : (UInt32.ofNat (2 ^ (mem + 7))).toNat ≤ qa.size := by
    rw [eq, size_clearHead] at size
    change qa.size = _ at size
    omega
  have hashPositive : 0 < (UInt32.ofNat (2 ^ (mem + 7))).toNat := by
    have positive := Nat.two_pow_pos (resultState wrap wb mem h r level strategy a1 a2 a3).hash_bits.toNat
    rw [← good.inv.hsize] at positive
    simpa [resultState, finalState, lmD, resetState, rkPost, rkPost3, rkMid, ibRec, trInitRec,
      readyState, allocatedState, baseState] using positive
  refine ⟨w, p, q, wa, pa, heads, blocks.win, blocks.prev, blocks.head, hw, hp, hq, ?_⟩
  apply chains_empty
  intro k hk
  have hk' : k < (UInt32.ofNat (2 ^ (mem + 7))).toNat := by
    simpa [resultState, finalState, lmD, resetState, rkPost, rkPost3, rkMid, ibRec, trInitRec,
      readyState, allocatedState, baseState] using hk
  rw [eq]
  have zero := clear_head_zero qa (UInt32.ofNat (2 ^ (mem + 7))).toNat hashPositive qs k hk'
  simp only [wfn, Array.getD_eq_getD_getElem?, zero, Option.getD_some]

/-- The result of a successful `deflateInit2_` satisfies the universal invariant. -/
theorem success_dinv {h : Heap} {r : ZStreamRef} {z : ZStream} {level strategy : Int32}
    {a1 a2 a3 : Array CtData} {qa : Array UInt16}
    (good : DGood (successHeap wrap wb mem h r z level strategy a1 a2 a3 qa) r h.nextBlk
      (resultStream wrap wb mem h r z level strategy) (resultState wrap wb mem h r level strategy a1 a2 a3))
    (allocators : DefAlloc (resultStream wrap wb mem h r z level strategy))
    (globals : LibraryGlobals (successHeap wrap wb mem h r z level strategy a1 a2 a3 qa))
    (bl : ∀ k, k < 19 → a3[k]!.fc = 0) (frequencies : InitialFrequencies a1 a2)
    (hw0 : 0 ≤ wrap.toInt) (memoryLow : 1 ≤ mem) (memoryHigh : mem ≤ 9) :
    DInv (successHeap wrap wb mem h r z level strategy a1 a2 a3 qa) r h.nextBlk
      (resultStream wrap wb mem h r z level strategy) (resultState wrap wb mem h r level strategy a1 a2 a3) := by
  have hw := absWrap_nonneg hw0
  have symEnd : 0 < ((UInt32.ofNat (2 ^ (mem + 6)) - 1) * 3).toNat := by
    rcases ZlibF.Math.DeflateMemLevel.memory_cases memoryLow memoryHigh with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  obtain ⟨w, p, q, b, blocks⟩ := good.inv.blocks
  obtain ⟨buf, hb, -⟩ := blocks.ba
  refine ⟨good, allocators, globals, ?_, ?_, ?_⟩
  · refine Shape.mk ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals first
      | (simp [resultState, finalState, lmD, resetState, rkPost, rkPost3, rkMid, ibRec, trInitRec,
          readyState, allocatedState, baseState, hw, MIN_MATCH_u]; done)
      | (simp [resultState, finalState, lmD, resetState, rkPost, rkPost3, rkMid, ibRec, trInitRec,
          readyState, allocatedState, baseState, hw, MIN_MATCH_u]; omega)
      | (simp only [resultState, finalState, lmD, resetState, rkPost, rkPost3, rkMid, ibRec, trInitRec,
          readyState, allocatedState, baseState]
         simpa using symEnd)
  · refine ⟨fun _ => ?_, fun one => ?_, fun _ _ three => ?_⟩
    · have chains := general_chains wrap wb mem good
      unfold Chains chainTop
      simpa [resultState, finalState, lmD, resetState, rkPost, rkPost3, rkMid, ibRec, trInitRec,
        readyState, allocatedState, baseState] using chains
    · simp [resultState, finalState, lmD] at one
    · simp [resultState, finalState, lmD] at three
  · refine ⟨⟨[], ⟨b, buf, blocks.pbuf, hb, ?_⟩, by simp⟩, ?_, ?_⟩
    · apply empty_symbol_ledger
      · simp [resultState, finalState, lmD, resetState, rkPost, rkPost3, ibRec]
      · simpa [resultState, finalState, lmD, resetState, rkPost, rkPost3, ibRec, trInitRec] using frequencies
    · refine ⟨?_, ?_, ?_⟩
      · intro k hk
        simpa [resultState, finalState, lmD, resetState, rkPost, rkPost3, ibRec, trInitRec] using bl k hk
      · simp [resultState, finalState, lmD, resetState, rkPost, rkPost3, ibRec, trInitRec]
      · simp [resultState, finalState, lmD, resetState, rkPost, rkPost3, ibRec, trInitRec]
    · intro _ _ _ nonzero
      simp [resultState, finalState, lmD, resetState, rkPost, rkPost3, ibRec, trInitRec] at nonzero

/-- The between-calls facts of the initial state: no `deflate` call yet, no lookahead, no symbols,
no lazy state, the block at `strstart = 0`, and not finished. -/
theorem success_callfacts (h : Heap) (r : ZStreamRef) (level strategy : Int32) (a1 a2 a3 : Array CtData) :
    CallFacts (resultState wrap wb mem h r level strategy a1 a2 a3) := by
  refine ⟨fun _ => ?_, fun _ => ?_, fun fin => ?_, fun _ => ?_, fun _ => ?_⟩
  · simp [resultState, finalState, lmD, resetState, rkPost, rkPost3, rkMid, ibRec, trInitRec, MIN_MATCH_u]
  · simp [resultState, finalState, lmD, resetState, rkPost, rkPost3, rkMid, ibRec, trInitRec]
  · simp only [resultState, finalState, lmD, resetState, rkPost, rkPost3, rkMid, ibRec, trInitRec] at fin
    cases e : (absWrap (readyState wrap wb mem r level strategy (h.nextBlk + 1) (h.nextBlk + 2)
        (h.nextBlk + 3) (h.nextBlk + 4)).wrap == 2) <;> simp [e] at fin <;> exact absurd fin (by decide)
  · simp [resultState, finalState, lmD]
  · simp [resultState, finalState, lmD, resetState, rkPost, rkPost3, rkMid, ibRec, trInitRec]

end Zlib.Deflate.Proofs.GeneralInit

namespace Zlib.Deflate.Universal
open C Zlib.Deflate Zlib.Deflate.Spec ZlibF.Spec.Public Zlib.Deflate.Proofs.GeneralInit
open Zlib.Deflate.Proofs Zlib.Deflate.Proofs.DefaultInit
open ZlibF.Spec.Public.Proofs.DeflateInit (globals_trees)
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- **A successful `deflateInit2_` establishes the invariant and the between-calls facts**
(skeleton lemma `init2_inv`), for every argument tuple. The result `Z_OK` occurs only on the success path of `init2_main`; that
path is the actual run of `alloc`, whose result `success_dinv` covers. -/
theorem init2_inv {h after : Heap} {r : ZStreamRef} {z : ZStream} {version : BPtr}
    {level method wb mem strategy : Int32}
    (fresh : Fresh h) (uniq : Zlib.Deflate.Spec.Uniq h) (globals : LibraryGlobals h)
    (get : r.get h = some z) (allocators : DefaultOrNull z) (ver : VersionValue h version (some 49))
    (run : C.run (Zlib.Deflate.deflateInit2_ (some r) level method wb mem strategy version 112) h =
      .ok (Z_OK, after)) :
    ∃ ds z' d, DInv after r ds z' d ∧ CallFacts d := by
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
          success_callfacts (wrapCode p.wrap) p.wbits p.memLevel _ r lev strategy a1 a2 a3⟩
        · exact ⟨by simpa [GeneralInit.resultStream, rkZ, GeneralInit.stateStream] using haP.1,
            by simpa [GeneralInit.resultStream, rkZ, GeneralInit.stateStream] using haP.2⟩
        · unfold LibraryGlobals at globals ⊢
          simpa [GeneralInit.successHeap, GeneralInit.readyHeap, GeneralInit.successfulBuffers, GeneralInit.publishedHeap, stateHeap, setW, setD, hp]
            using globals
      · simp only [all, Bool.false_eq_true, ite_false] at facts
        exact absurd facts.2.1 (by decide)

end Zlib.Deflate.Universal

#print axioms Zlib.Deflate.Universal.init2_inv
