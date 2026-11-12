import ZlibF.Proof.«deflate.c.universal-ops-dictionary-view»
import ZlibF.Proof.«deflate.c.universal-ops-header»

/-!
# deflate.c: `deflateSetDictionary` keeps the invariant, every case (inflate batch 1)

Batch B proved the body of `deflateSetDictionary` when no slide of a level-0 stream is pending
(`setdict_body`, `matches = 0`, `deflate.c.universal-ops-dictionary`). The remaining case is a
level-0 stream with one or two stored slides not yet applied to the hash tables
(`matches` 1 or 2): `fill_window` and the insertion loop then run on tables that `SlidChains`
describes through `slideVal` (one slide) or that no chain fact describes (two). That body is
`SlidBody` here (batch B's Finding 1), proved as `slid_body` from `setdict_body_v`
(`deflate.c.universal-ops-dictionary-view`) with the slid view or with no view. In the slid view
an inserted position `str` appears as `str - w_size` or `NIL`, out of the window distance of every
later frontier, so the walk never follows it and `SlidChains` holds at the end
(`chains_insert_slid`, `deflate.c.engine.view-chains`).

This file gives the agreed statements `step_setDictionary` and the header companions.
-/

namespace Zlib.Deflate.Universal
open C ZlibF.Spec ZlibF.Spec.Public Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Engine.Proofs
open Zlib.Deflate.Proofs
set_option autoImplicit false

/-- The conclusion of `setdict_body`: the run of the body, the invariant, the footprint, and the
header facts beside it. -/
def SetdictBodyOk (h : Heap) (r : ZStreamRef) (ds : Nat) (d : DeflateState) (dict : BPtr) (len : UInt32) : Prop :=
  ∃ after zF dF, setdictBody (some r) (some (.tab ds)) dict len d h = .ok (Z_OK, after) ∧
    DInv after r ds zF dF ∧ Zlib.Deflate.Proofs.Shape h after ∧
    Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) ∧
    after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk ∧ (∀ b, DeflateOwned ds dF b ↔ DeflateOwned ds d b) ∧
    (HeaderInv d → HeaderInv dF) ∧
    (dF.status = d.status ∧ dF.sym_next = d.sym_next ∧ dF.gzhead = d.gzhead ∧ (CallFacts d → CallFacts dF))

/-- **The body of `deflateSetDictionary` on a level-0 stream with pending stored slides**
(`matches` 1 or 2, batch B's Finding 1): `fill_window` and the insertion loop over the slid view of
the tables, or over tables without chain facts. Proved as `slid_body`. -/
def SlidBody : Prop :=
  ∀ {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}, DInv h r ds z d →
    ∀ (dict : BPtr) (len : UInt32), CallerRange h r dict len.toNat false → dict ≠ .null →
    d.«matches» ≠ 0 → d.lookahead = 0 → SetdictBodyOk h r ds d dict len

/-- A representation has the three blocks of the tables: the view with no chain fact holds. -/
theorem vheap_none {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (good : DGood h r ds z d) (top : Nat) : VHeapChains .none h d top := by
  obtain ⟨w, p, q, b, blocks⟩ := good.inv.blocks
  obtain ⟨wa, getW, _⟩ := blocks.wa
  obtain ⟨pa, getP, _⟩ := blocks.pa
  obtain ⟨qa, getQ, _⟩ := blocks.qa
  exact ⟨w, p, q, wa, pa, qa, blocks.win, blocks.prev, blocks.head, getW, getP, getQ, trivial⟩

/-- **`SlidBody` holds**: with one pending slide the body keeps the slid view of the tables
(`setdict_body_v` with `.slid`, from `Hashing.slid`); with two it needs no chain fact
(`setdict_body_v` with `.none`). `matches` is unchanged, the end state has no lookahead, so the
view chains are its whole hash state. -/
theorem slid_body : SlidBody := by
  intro h r ds z d inv dict len args nonnull nz la0
  have level : d.level = 0 := by
    by_cases l : d.level = 0
    · exact l
    · exact absurd (inv.shape.slides.2 l) nz
  have sym0 : d.sym_next = 0 := (inv.shape.levelZero level).2.2
  by_cases one : d.«matches» = 1
  · exact setdict_body_v (v := .slid) inv dict len args nonnull (inv.hashing.slid one)
      (fun _ _ same la chains => ⟨fun zero => absurd (same.symm.trans zero) nz, fun _ => chains,
        fun _ _ large => by rw [la] at large; exact absurd large (by decide)⟩) la0 sym0
  · exact setdict_body_v (v := .none) inv dict len args nonnull (vheap_none inv.good _)
      (fun _ _ same la _ => ⟨fun zero => absurd (same.symm.trans zero) nz,
        fun slid => absurd (same.symm.trans slid) one,
        fun _ _ large => by rw [la] at large; exact absurd large (by decide)⟩) la0 sym0

/-- The body of `deflateSetDictionary` for every pending-slide count. -/
theorem setdict_body_all {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream}
    {d : DeflateState} (inv : DInv h r ds z d) (dict : BPtr) (len : UInt32)
    (args : CallerRange h r dict len.toNat false) (nonnull : dict ≠ .null) (la0 : d.lookahead = 0)
    (sym0 : d.sym_next = 0) :
    SetdictBodyOk h r ds d dict len := by
  by_cases zeroM : d.«matches» = 0
  · exact setdict_body inv dict len args nonnull zeroM la0 sym0
  · exact slid_body inv dict len args nonnull zeroM la0

/-- The refusals and the dispatch to the body. -/
theorem setdict_cases {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv h r ds z d) (dictionary : BPtr) (dictLength : UInt32) :
    deflateSetDictionary (some r) dictionary dictLength h = .ok (Z_STREAM_ERROR, h) ∨
      (dictionary ≠ .null ∧ d.lookahead = 0 ∧
        (d.wrap == 2 || (d.wrap == 1 && d.status != INIT_STATE) || d.lookahead != 0 ||
          (d.wrap == 0 && d.strstart.toUInt64.toInt64 != d.block_start)) = false ∧
        deflateSetDictionary (some r) dictionary dictLength h =
          setdictBody (some r) (some (.tab ds)) dictionary dictLength d h) := by
  have good := inv.good
  have check := stateCheck_live good.live
  by_cases null : dictionary = .null
  · left
    rw [setdict_checks]
    simp [bind_app, check, null]
    all_goals (try rfl)
  have nullB : (dictionary == .null) = false := by simpa using null
  have stateRun : zrd (some r) (·.state) h = .ok (z.state, h) := by rw [zrd_eq, good.live.hz]
  have ldRun : ldDeflateState (some (.tab ds)) h = .ok (d, h) := ldDeflateState_tab good.live.hs
  by_cases refuse : (d.wrap == 2 || (d.wrap == 1 && d.status != INIT_STATE) || d.lookahead != 0 ||
      (d.wrap == 0 && d.strstart.toUInt64.toInt64 != d.block_start)) = true
  · left
    rw [setdict_checks]
    simp only [bind_app, check, nullB, bne_self_eq_false, Bool.false_or, Bool.false_eq_true, ite_false, stateRun,
      good.live.zst, castD, ldRun, refuse, ite_true]
    rfl
  · have la0 : d.lookahead = 0 := by
      by_cases e : d.lookahead = 0
      · exact e
      · exfalso; apply refuse; simp [e]
    refine Or.inr ⟨null, la0, by simpa using refuse, ?_⟩
    rw [setdict_checks]
    simp only [Bool.not_eq_true] at refuse
    simp only [bind_app, check, nullB, bne_self_eq_false, Bool.false_or, Bool.false_eq_true, ite_false, stateRun,
      good.live.zst, castD, ldRun, refuse]

/-- **`deflateSetDictionary` keeps the invariant**, in every state of the invariant (the agreed
statement). -/
theorem step_setDictionary {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream}
    {d : DeflateState} (inv : DInv h r ds z d) (dictionary : BPtr) (dictLength : UInt32)
    (args : CallerRange h r dictionary dictLength.toNat false)
    (header : HeaderInv d) (finished : d.status = FINISH_STATE → d.sym_next = 0) :
    StepOk h r (.deflateSetDictionary (some r) dictionary dictLength) := by
  rcases setdict_cases inv dictionary dictLength with refused | ⟨null, la0, pass, body⟩
  · exact step_unchanged inv Z_STREAM_ERROR (heapCall_run refused) rfl
  · obtain ⟨after, zF, dF, bodyRun, invF, shapeF, frameF, _, _, ownedF, _, _⟩ :=
      setdict_body_all inv dictionary dictLength args null la0
        (setdict_sym0 inv.shape inv.good.inv.wrap_lo inv.good.inv.wrap_hi header finished pass)
    exact step_of_frame inv Z_OK (heapCall_run (body.trans bodyRun)) rfl invF shapeF frameF ownedF

/-- **The header facts of `deflateSetDictionary`** (for batch C), in the form of
`SequenceFacts.setDictionaryHeader`. -/
theorem setDictionary_header {h after : Heap} {r : ZStreamRef} {ds ds' : Nat}
    {z z' : ZStream} {d d' : DeflateState} {dictionary : BPtr} {dictLength : UInt32} {rc : Int32}
    (inv : DInv h r ds z d) (header : HeaderInv d) (args : CallerRange h r dictionary dictLength.toNat false)
    (finished : d.status = FINISH_STATE → d.sym_next = 0)
    (run : C.run (Zlib.Deflate.deflateSetDictionary (some r) dictionary dictLength) h = .ok (rc, after))
    (invAfter : DInv after r ds' z' d') : HeaderInv d' := by
  have run' : deflateSetDictionary (some r) dictionary dictLength h = .ok (rc, after) := run
  rcases setdict_cases inv dictionary dictLength with refused | ⟨null, la0, pass, body⟩
  · have e := run'.symm.trans refused
    simp only [Except.ok.injEq, Prod.mk.injEq] at e
    obtain ⟨-, rfl⟩ := e
    exact header_unchanged inv header invAfter
  · obtain ⟨afterF, zF, dF, bodyRun, invF, -, -, -, -, -, headerF, -⟩ :=
      setdict_body_all inv dictionary dictLength args null la0
        (setdict_sym0 inv.shape inv.good.inv.wrap_lo inv.good.inv.wrap_hi header finished pass)
    have e := run'.symm.trans (body.trans bodyRun)
    simp only [Except.ok.injEq, Prod.mk.injEq] at e
    obtain ⟨-, rfl⟩ := e
    obtain ⟨-, -, rfl⟩ := invF.unique invAfter.good
    exact headerF header

/-- **The between-calls facts of `deflateSetDictionary`**, in the form of
`operation_callfacts_of`'s hypothesis (with the entry's `HeaderInv`). -/
theorem setDictionary_callfacts {h after : Heap} {r : ZStreamRef} {ds ds' : Nat}
    {z z' : ZStream} {d d' : DeflateState} {dictionary : BPtr} {dictLength : UInt32} {rc : Int32}
    (inv : DInv h r ds z d) (header : HeaderInv d) (calls : CallFacts d)
    (args : CallerRange h r dictionary dictLength.toNat false)
    (run : C.run (Zlib.Deflate.deflateSetDictionary (some r) dictionary dictLength) h = .ok (rc, after))
    (invAfter : DInv after r ds' z' d') : CallFacts d' := by
  have run' : deflateSetDictionary (some r) dictionary dictLength h = .ok (rc, after) := run
  rcases setdict_cases inv dictionary dictLength with refused | ⟨null, la0, pass, body⟩
  · have e := run'.symm.trans refused
    simp only [Except.ok.injEq, Prod.mk.injEq] at e
    obtain ⟨-, rfl⟩ := e
    obtain ⟨-, -, e⟩ := inv.unique invAfter.good
    rw [e]; exact calls
  · obtain ⟨afterF, zF, dF, bodyRun, invF, -, -, -, -, -, -, -, -, -, keep⟩ :=
      setdict_body_all inv dictionary dictLength args null la0
        (setdict_sym0 inv.shape inv.good.inv.wrap_lo inv.good.inv.wrap_hi header calls.finishSym pass)
    have e := run'.symm.trans (body.trans bodyRun)
    simp only [Except.ok.injEq, Prod.mk.injEq] at e
    obtain ⟨-, rfl⟩ := e
    obtain ⟨-, -, rfl⟩ := invF.unique invAfter.good
    exact keep calls

/-- **The companion for batch C**: the call's final state, with the invariant and the header
facts beside it. -/
theorem setDictionary_body {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream}
    {d : DeflateState} (inv : DInv h r ds z d) (dictionary : BPtr) (dictLength : UInt32)
    (args : CallerRange h r dictionary dictLength.toNat false)
    (header : HeaderInv d) (finished : d.status = FINISH_STATE → d.sym_next = 0) :
    ∃ rc after zF dF, C.run (Zlib.Deflate.deflateSetDictionary (some r) dictionary dictLength) h = .ok (rc, after) ∧
      DInv after r ds zF dF ∧ (HeaderInv d → HeaderInv dF) := by
  rcases setdict_cases inv dictionary dictLength with refused | ⟨null, la0, pass, body⟩
  · exact ⟨Z_STREAM_ERROR, h, z, d, refused, inv, id⟩
  · obtain ⟨after, zF, dF, bodyRun, invF, -, -, -, -, -, headerF, -⟩ :=
      setdict_body_all inv dictionary dictLength args null la0
        (setdict_sym0 inv.shape inv.good.inv.wrap_lo inv.good.inv.wrap_hi header finished pass)
    exact ⟨Z_OK, after, zF, dF, body.trans bodyRun, invF, headerF⟩

end Zlib.Deflate.Universal
