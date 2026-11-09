import ZlibF.Proof.«inflate.c.codelens-step»
import ZlibF.Proof.«inflate.c.codelens-invariant»
import ZlibF.Proof.«inflate.c.xloop-rank»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false

def ClRegShape (before after : IL) : Prop :=
  after = { before with next := after.next, have_ := after.have_, hold := after.hold, bits := after.bits, here := after.here, copy := after.copy, len := after.len }

theorem ClRegShape.refl (l : IL) : ClRegShape l l := rfl

theorem ClRegShape.trans {a b c : IL} (first : ClRegShape a b) (second : ClRegShape b c) :
    ClRegShape a c := by
  unfold ClRegShape at *
  rw [second, first]

theorem BitInv.put_stream {h : Heap} {l : IL} {bs : List UInt8} (inv : BitInv h l bs)
    (r : ZStreamRef) (z : ZStream) : BitInv (r.put h z) l bs := by
  refine ⟨inv.have_eq, ?_, inv.hold_lt⟩
  rcases inv.next with empty | ⟨ref, array, offset, pointer, get, bound, contents⟩
  · exact Or.inl empty
  · refine Or.inr ⟨ref, array, offset, pointer, ?_, bound, contents⟩
    have borrow : (r.put h z).libcErrorBorrow = h.libcErrorBorrow := by
      cases r <;> simp only [ZStreamRef.put] <;> first | rfl | split <;> rfl
    have same : Space.get (r.put h z) ref = (Space.get h ref : Option (Array UInt8)) := by
      cases ref with
      | str i => exact C.LibcBorrow.str_view_stable (Or.inr borrow)
      | _ => cases r <;> simp only [Space.get, ZStreamRef.put] <;> first | rfl | split <;> rfl
    rw [same]
    exact get

def ClWriteResult (before after : InflateState) : Prop :=
  after = { before with lens := after.lens, «have» := after.«have» } ∧
    after.lens.size = 320 ∧
    after.«have».toNat ≤ before.nlen.toNat + before.ndist.toNat ∧
    before.«have».toNat < after.«have».toNat ∧
    ∀ k, k < after.«have».toNat → (after.lens.getD k 0).toNat ≤ 15

def ClStepOutcome (h : Heap) (r : ZStreamRef) (zs : Nat) (z : ZStream) (s : InflateState)
    (result : Except Ex Bool) (after : Heap) : Prop :=
  match result with
  | .error _ => after = h
  | .ok true => ∃ i, strTable[i]? = some "invalid bit length repeat" ∧ after = tcBadHeap h r zs z s i
  | .ok false => ∃ state, after = setI h zs state ∧ ClWriteResult s state

/-- The final range check and bounded repeat produce either a strict
prefix extension or the actual BAD exit. The bit source is preserved. -/
theorem clFinish_outcome_cursor {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef}
    {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8}
    (hr : c.strm = some r) (hc : c.st = some (.tab zs))
    (hz : r.get h = some z) (hs : h.istates zs = some s)
    (size : s.lens.size = 320) (nlen : s.nlen.toNat ≤ 286) (ndist : s.ndist.toNat ≤ 30)
    (haveBound : s.«have».toNat ≤ s.nlen.toNat + s.ndist.toNat)
    (copyLo : 1 ≤ l.copy.toNat) (copyHi : l.copy.toNat ≤ 138) (value : l.len.toNat ≤ 15)
    (initialized : ∀ k, k < s.«have».toNat → (s.lens.getD k 0).toNat ≤ 15)
    (B : BitInv h l bs) :
    ∃ result regs after,
      runX (clRepeatFinish c) l h = .ok ((result, regs), after) ∧
      BitInv after regs bs ∧ ClRegShape l regs ∧ regs.bits = l.bits ∧
      ClStepOutcome h r zs z s result after ∧ regs.next = l.next := by
  have outcomes := clRepeatFinish_run hr hc hz hs size nlen ndist haveBound copyLo copyHi value initialized
  by_cases overrun : s.«have».toNat + l.copy.toNat > s.nlen.toNat + s.ndist.toNat
  · obtain ⟨i, literal, run⟩ := outcomes.1 overrun
    exact ⟨.ok true, l, tcBadHeap h r zs z s i, run,
      (B.put_stream r _).setI zs _, ClRegShape.refl l, rfl, ⟨i, literal, rfl⟩, rfl⟩
  · obtain ⟨state, run, frame, sz, count, progress, prefixValues⟩ := outcomes.2 (by omega)
    have inv : BitInv h { l with copy := 0xffffffff } bs := ⟨B.have_eq, B.next, B.hold_lt⟩
    refine ⟨.ok false, { l with copy := 0xffffffff }, setI h zs state, run, inv.setI zs _,
      rfl, rfl, ⟨state, rfl, frame, sz, by omega, progress, prefixValues⟩, rfl⟩

/-- Projection retaining the original range-check/write interface. -/
theorem clFinish_outcome {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef}
    {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8}
    (hr : c.strm = some r) (hc : c.st = some (.tab zs))
    (hz : r.get h = some z) (hs : h.istates zs = some s)
    (size : s.lens.size = 320) (nlen : s.nlen.toNat ≤ 286) (ndist : s.ndist.toNat ≤ 30)
    (haveBound : s.«have».toNat ≤ s.nlen.toNat + s.ndist.toNat)
    (copyLo : 1 ≤ l.copy.toNat) (copyHi : l.copy.toNat ≤ 138) (value : l.len.toNat ≤ 15)
    (initialized : ∀ k, k < s.«have».toNat → (s.lens.getD k 0).toNat ≤ 15)
    (B : BitInv h l bs) :
    ∃ result regs after,
      runX (clRepeatFinish c) l h = .ok ((result, regs), after) ∧
      BitInv after regs bs ∧ ClRegShape l regs ∧ regs.bits = l.bits ∧
      ClStepOutcome h r zs z s result after := by
  obtain ⟨result, regs, after, run, inv, shape, bits, post, _⟩ :=
    clFinish_outcome_cursor hr hc hz hs size nlen ndist haveBound copyLo copyHi value initialized B
  exact ⟨result, regs, after, run, inv, shape, bits, post⟩

private theorem clZero_outcome_cursor {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef}
    {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8}
    (hr : c.strm = some r) (hc : c.st = some (.tab zs))
    (hz : r.get h = some z) (hs : h.istates zs = some s)
    (size : s.lens.size = 320) (nlen : s.nlen.toNat ≤ 286) (ndist : s.ndist.toNat ≤ 30)
    (haveBound : s.«have».toNat ≤ s.nlen.toNat + s.ndist.toNat)
    (initialized : ∀ k, k < s.«have».toNat → (s.lens.getD k 0).toNat ≤ 15)
    (B : BitInv h l bs) (here : Code) (extra base : UInt32)
    (width : here.bits.toNat ≤ 7) (extraBound : extra.toNat ≤ 7)
    (baseLo : 3 ≤ base.toNat) (baseHi : base.toNat ≤ 11) :
    ∃ result regs after used,
      runX (do clZeroSetup here extra base; clRepeatFinish c) l h = .ok ((result, regs), after) ∧
      used ≤ bs.length ∧ BitInv after regs (bs.drop used) ∧ ClRegShape l regs ∧
      regs.bits.toNat ≤ max l.bits.toNat 21 ∧ ClStepOutcome h r zs z s result after ∧ regs.next = inputAdvance l.next used ∧
      regs.bits.toNat ≤ l.bits.toNat + 8 * used := by
  obtain ⟨result, prepared, used, setupRun, usedBound, preparedInv, shape, bitBound, counts, cursor, budget⟩ :=
    clZeroSetup_run_cursor B here extra base width extraBound baseLo baseHi
  have shape' : ClRegShape l prepared := by unfold ClRegShape; rw [shape]
  cases result with
  | error fault =>
    refine ⟨.error fault, prepared, h, used, ?_, usedBound, preparedInv, shape', bitBound, rfl, cursor, budget⟩
    rw [runX_bind, setupRun]
  | ok unit =>
    cases unit
    obtain ⟨zero, copyLo, copyHi⟩ := counts rfl
    have value : prepared.len.toNat ≤ 15 := by rw [zero]; decide
    obtain ⟨outcome, regs, after, finishRun, inv, frame, bits, post, next⟩ :=
      clFinish_outcome_cursor hr hc hz hs size nlen ndist haveBound (by omega) copyHi value initialized preparedInv
    refine ⟨outcome, regs, after, used, ?_, usedBound, inv, shape'.trans frame, ?_, post, next.trans cursor, ?_⟩
    · rw [runX_bind, setupRun]
      exact finishRun
    · rw [bits]
      exact bitBound
    · rw [bits]
      exact budget

private theorem clZero_outcome {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef}
    {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8}
    (hr : c.strm = some r) (hc : c.st = some (.tab zs))
    (hz : r.get h = some z) (hs : h.istates zs = some s)
    (size : s.lens.size = 320) (nlen : s.nlen.toNat ≤ 286) (ndist : s.ndist.toNat ≤ 30)
    (haveBound : s.«have».toNat ≤ s.nlen.toNat + s.ndist.toNat)
    (initialized : ∀ k, k < s.«have».toNat → (s.lens.getD k 0).toNat ≤ 15)
    (B : BitInv h l bs) (here : Code) (extra base : UInt32)
    (width : here.bits.toNat ≤ 7) (extraBound : extra.toNat ≤ 7)
    (baseLo : 3 ≤ base.toNat) (baseHi : base.toNat ≤ 11) :
    ∃ result regs after used,
      runX (do clZeroSetup here extra base; clRepeatFinish c) l h = .ok ((result, regs), after) ∧
      used ≤ bs.length ∧ BitInv after regs (bs.drop used) ∧ ClRegShape l regs ∧
      regs.bits.toNat ≤ max l.bits.toNat 21 ∧ ClStepOutcome h r zs z s result after := by
  obtain ⟨result, regs, after, used, run, bound, inv, shape, bits, post, _, _⟩ :=
    clZero_outcome_cursor hr hc hz hs size nlen ndist haveBound initialized B here extra base width extraBound baseLo baseHi
  exact ⟨result, regs, after, used, run, bound, inv, shape, bits, post⟩

theorem clAfterLookup_run_cursor {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef}
    {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8}
    (hr : c.strm = some r) (hc : c.st = some (.tab zs))
    (hz : r.get h = some z) (hs : h.istates zs = some s)
    (size : s.lens.size = 320) (nlen : s.nlen.toNat ≤ 286) (ndist : s.ndist.toNat ≤ 30)
    (haveBound : s.«have».toNat < s.nlen.toNat + s.ndist.toNat)
    (initialized : ∀ k, k < s.«have».toNat → (s.lens.getD k 0).toNat ≤ 15)
    (B : BitInv h l bs) (here : Code) (width : here.bits.toNat ≤ 7)
    (enough : here.bits.toNat ≤ l.bits.toNat) :
    ∃ result regs after used,
      runX (clAfterLookup c here) l h = .ok ((result, regs), after) ∧
      used ≤ bs.length ∧ BitInv after regs (bs.drop used) ∧ ClRegShape l regs ∧
      regs.bits.toNat ≤ max l.bits.toNat 21 ∧ ClStepOutcome h r zs z s result after ∧ regs.next = inputAdvance l.next used ∧
      regs.bits.toNat ≤ l.bits.toNat + 8 * used := by
  by_cases literal : here.val < 16
  · have literalNat : here.val.toNat < 16 := UInt16.lt_iff_toNat_lt.mp literal
    obtain ⟨run, inv, _, count, prefixValues⟩ := clAfterLookup_literal_run hc hs size
      (by omega) literalNat width enough B initialized
    let regs := { l with hold := l.hold >>> here.bits.toUInt32.toUInt64, bits := l.bits - here.bits.toUInt32 }
    have bits : regs.bits.toNat ≤ l.bits.toNat := by
      change (l.bits - here.bits.toUInt32).toNat ≤ _
      rw [UInt32.toNat_sub_of_le _ _ (by apply UInt32.le_iff_toNat_le.mpr; rw [UInt8.toNat_toUInt32]; exact enough)]
      omega
    refine ⟨.ok false, regs, _, 0, run, by omega, ?_, rfl, by omega,
      ⟨clWrite s here.val, rfl, ?_, ?_, ?_, by omega, prefixValues⟩,
      (inputAdvance_zero l.next).symm, by change regs.bits.toNat ≤ l.bits.toNat + 8 * 0; omega⟩
    · simpa only [List.drop_zero] using inv
    · rfl
    · simp only [clWrite, Array.size_set!, size]
    · omega
  · by_cases previous : here.val = 16
    · rw [clAfterLookup_repeat16 c here previous]
      by_cases empty : s.«have» = 0
      · obtain ⟨result, prepared, used, setupRun, usedBound, inv, shape, bitBound, _, cursor, budget⟩ :=
          clNeedDrop_run_cursor B here 2 width (by decide)
        change prepared.bits.toNat ≤ max l.bits.toNat 16 at bitBound
        have shape' : ClRegShape l prepared := by unfold ClRegShape; rw [shape]
        cases result with
        | error fault =>
          refine ⟨.error fault, prepared, h, used, ?_, usedBound, inv, shape', by omega, rfl, cursor, budget⟩
          unfold clRepeat16
          rw [runX_bind, setupRun]
        | ok unit =>
          cases unit
          obtain ⟨i, message, bad⟩ := tcBadMode_run (c := c) "invalid bit length repeat"
            lit_bit_length_repeat hr hc hz hs
          refine ⟨.ok true, prepared, tcBadHeap h r zs z s i, used, ?_, usedBound,
            (inv.put_stream r _).setI zs _, shape', by omega, ⟨i, message, rfl⟩, cursor, budget⟩
          unfold clRepeat16
          rw [runX_bind, setupRun]
          dsimp only
          rw [hc]
          simp [runX_bind, runX_lift, ldI_eq, hs, empty, bad, runX_pure]
      · have positive : 1 ≤ s.«have».toNat := by
          have notZero : s.«have».toNat ≠ 0 := by intro zero; apply empty; exact UInt32.toNat_inj.mp zero
          omega
        obtain ⟨result, prepared, used, usedBound, inv, shape, bitBound, success, failure, cursor, budget⟩ :=
          clRepeat16_nonempty_run_cursor hc hs size positive (by omega) initialized B here width
        have shape' : ClRegShape l prepared := by unfold ClRegShape; rw [shape]
        cases result with
        | error fault =>
          exact ⟨.error fault, prepared, h, used, failure fault rfl, usedBound, inv, shape', by omega, rfl, cursor, budget⟩
        | ok unit =>
          cases unit
          obtain ⟨prefixRun, value, copyLo, copyHi⟩ := success rfl
          obtain ⟨outcome, regs, after, run, finalInv, frame, bits, post, next⟩ :=
            clFinish_outcome_cursor hr hc hz hs size nlen ndist (by omega) (by omega) (by omega)
              value initialized inv
          refine ⟨outcome, regs, after, used, prefixRun.trans run, usedBound,
            finalInv, shape'.trans frame, ?_, post, next.trans cursor, ?_⟩
          · rw [bits]
            omega
          · rw [bits]
            exact budget
    · by_cases zero17 : here.val = 17
      · rw [clAfterLookup_zero17 c here zero17]
        exact clZero_outcome_cursor hr hc hz hs size nlen ndist (by omega) initialized B here 3 3
          width (by decide) (by decide) (by decide)
      · rw [clAfterLookup_zero18 c here literal previous zero17]
        exact clZero_outcome_cursor hr hc hz hs size nlen ndist (by omega) initialized B here 7 11
          width (by decide) (by decide) (by decide)


/-- Projection retaining the original complete code-length step. -/
theorem clAfterLookup_run {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef}
    {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8}
    (hr : c.strm = some r) (hc : c.st = some (.tab zs))
    (hz : r.get h = some z) (hs : h.istates zs = some s)
    (size : s.lens.size = 320) (nlen : s.nlen.toNat ≤ 286) (ndist : s.ndist.toNat ≤ 30)
    (haveBound : s.«have».toNat < s.nlen.toNat + s.ndist.toNat)
    (initialized : ∀ k, k < s.«have».toNat → (s.lens.getD k 0).toNat ≤ 15)
    (B : BitInv h l bs) (here : Code) (width : here.bits.toNat ≤ 7)
    (enough : here.bits.toNat ≤ l.bits.toNat) :
    ∃ result regs after used,
      runX (clAfterLookup c here) l h = .ok ((result, regs), after) ∧
      used ≤ bs.length ∧ BitInv after regs (bs.drop used) ∧ ClRegShape l regs ∧
      regs.bits.toNat ≤ max l.bits.toNat 21 ∧ ClStepOutcome h r zs z s result after := by
  obtain ⟨result, regs, after, used, run, bound, inv, shape, bits, post, _, _⟩ :=
    clAfterLookup_run_cursor hr hc hz hs size nlen ndist haveBound initialized B here width enough
  exact ⟨result, regs, after, used, run, bound, inv, shape, bits, post⟩

/-- One actual CODELENS iteration: root lookup, extra-bit handling,
repetition checks and writes. Every continuing iteration strictly extends
the initialized length prefix; exits preserve a valid bit source. -/
theorem clReadBody_run_cursor {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef}
    {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8}
    (hr : c.strm = some r) (hc : c.st = some (.tab zs))
    (hz : r.get h = some z) (hs : h.istates zs = some s)
    (size : s.lens.size = 320) (mode : s.mode = CODELENS)
    (stateInv : CodeLengthInvariant zs s)
    (more : s.«have».toNat < s.nlen.toNat + s.ndist.toNat) (B : BitInv h l bs) :
    ∃ result regs after used,
      runX (clReadBody c) l h = .ok ((result, regs), after) ∧
      used ≤ bs.length ∧ BitInv after regs (bs.drop used) ∧ ClRegShape l regs ∧
      regs.bits.toNat ≤ max l.bits.toNat 21 ∧ ClStepOutcome h r zs z s result after ∧ regs.next = inputAdvance l.next used ∧
      regs.bits.toNat ≤ l.bits.toNat + 8 * used := by
  obtain ⟨pointer, table, nlen, ndist, _, initialized⟩ := stateInv mode
  have get := CodeRef.get_istate_codes hs
  obtain ⟨lookupResult, looked, used1, lookupRun, _, used1Bound, inv, _, shape, bitBound,
    _, width, _, enough, _, next1, budget1⟩ := lookup1_codes_run_cursor hc hs pointer get table B
  have frame : ClRegShape l looked := by unfold ClRegShape; rw [shape]
  cases lookupResult with
  | error fault =>
    refine ⟨.error fault, looked, h, used1, ?_, used1Bound, inv, frame, by omega, rfl, next1, by omega⟩
    rw [clReadBody_eq, runX_bind, lookupRun]
  | ok unit =>
    cases unit
    have root : s.lenbits.toNat ≤ 7 := table.2.1
    obtain ⟨outcome, regs, after, used2, run, used2Bound, finalInv, regFrame, finalBits, post, next2, budget2⟩ :=
      clAfterLookup_run_cursor hr hc hz hs size nlen ndist more initialized inv looked.here
        (by omega) (enough rfl)
    refine ⟨outcome, regs, after, used1 + used2, ?_, ?_, ?_, frame.trans regFrame, by omega, post, ?_, by omega⟩
    · rw [clReadBody_eq, runX_bind, lookupRun]
      dsimp only
      rw [runX_bind, runX_get]
      exact run
    · simp only [List.length_drop] at used2Bound
      omega
    · simpa only [List.drop_drop, Nat.add_comm] using finalInv

    · rw [next2, next1, inputAdvance_add]


/-- Projection retaining the original CODELENS body interface. -/
theorem clReadBody_run {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef}
    {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8}
    (hr : c.strm = some r) (hc : c.st = some (.tab zs))
    (hz : r.get h = some z) (hs : h.istates zs = some s)
    (size : s.lens.size = 320) (mode : s.mode = CODELENS)
    (stateInv : CodeLengthInvariant zs s)
    (more : s.«have».toNat < s.nlen.toNat + s.ndist.toNat) (B : BitInv h l bs) :
    ∃ result regs after used,
      runX (clReadBody c) l h = .ok ((result, regs), after) ∧
      used ≤ bs.length ∧ BitInv after regs (bs.drop used) ∧ ClRegShape l regs ∧
      regs.bits.toNat ≤ max l.bits.toNat 21 ∧ ClStepOutcome h r zs z s result after := by
  obtain ⟨result, regs, after, used, run, bound, inv, shape, bits, post, _, _⟩ :=
    clReadBody_run_cursor hr hc hz hs size mode stateInv more B
  exact ⟨result, regs, after, used, run, bound, inv, shape, bits, post⟩

def ClReadResult (zs : Nat) (s : InflateState) (l : IL) (bs : List UInt8)
    (outcome : Except Ex Unit) (regs : IL) (after : Heap) : Prop :=
  ∃ state used,
    after.istates zs = some state ∧ used ≤ bs.length ∧
    BitInv after regs (bs.drop used) ∧ ClRegShape l regs ∧
    regs.bits.toNat ≤ max l.bits.toNat 21 ∧
    state = { s with lens := state.lens, «have» := state.«have», mode := state.mode } ∧
    state.lens.size = 320 ∧ state.«have».toNat ≤ s.nlen.toNat + s.ndist.toNat ∧
    (∀ k, k < state.«have».toNat → (state.lens.getD k 0).toNat ≤ 15) ∧
    (state.mode = CODELENS ∨ state.mode = BAD) ∧
    (outcome = .ok () → state.mode = BAD ∨ state.«have».toNat = s.nlen.toNat + s.ndist.toNat)

/-- Retain the stream and exact private-record update as well as the
loop's decoding facts. Only msg may change in the stream record. -/
def ClReadResultFull (h : Heap) (r : ZStreamRef) (z : ZStream) (zs : Nat)
    (s : InflateState) (l : IL) (bs : List UInt8)
    (outcome : Except Ex Unit) (regs : IL) (after : Heap) : Prop :=
  ClReadResult zs s l bs outcome regs after ∧
    ∃ stream, r.get after = some stream ∧ stream = { z with msg := stream.msg } ∧
      ∃ state, after = setI (r.put h stream) zs state

/-- The complete actual CODELENS length-reading loop terminates. The
rank is the remaining number of initialized length slots, obtained from
the actual private state. A repeat may decrease it by several slots.
The constructor suffix and caller restoration are separate source points. -/
theorem clRead_run_full_cursor {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef}
    {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8}
    (hr : c.strm = some r) (hc : c.st = some (.tab zs))
    (hz : r.get h = some z) (hs : h.istates zs = some s)
    (size : s.lens.size = 320) (mode : s.mode = CODELENS)
    (stateInv : CodeLengthInvariant zs s) (B : BitInv h l bs) :
    ∃ outcome regs after, runX (clRead c) l h = .ok ((outcome, regs), after) ∧
      ClReadResultFull h r z zs s l bs outcome regs after ∧
      ∃ used, used ≤ bs.length ∧ BitInv after regs (bs.drop used) ∧
        regs.next = inputAdvance l.next used ∧ regs.bits.toNat ≤ l.bits.toNat + 8 * used := by
  obtain ⟨pointer, table, nlen, ndist, haveBound, initialized⟩ := stateInv mode
  let total := s.nlen.toNat + s.ndist.toNat
  let P : IL → Heap → Prop := fun regs heap => ∃ state used,
    heap = setI h zs state ∧
    state = { s with lens := state.lens, «have» := state.«have» } ∧
    state.lens.size = 320 ∧ state.«have».toNat ≤ total ∧
    (∀ k, k < state.«have».toNat → (state.lens.getD k 0).toNat ≤ 15) ∧
    used ≤ bs.length ∧ BitInv heap regs (bs.drop used) ∧ ClRegShape l regs ∧
    regs.bits.toNat ≤ max l.bits.toNat 21 ∧ regs.next = inputAdvance l.next used ∧
      regs.bits.toNat ≤ l.bits.toNat + 8 * used
  let rank : IL → Heap → Nat := fun _ heap => total - ((heap.istates zs).getD default).«have».toNat
  have loop := xwhileBrk_rank (cond := clReadCond c) (body := clReadBody c) P rank
    (fun outcome regs after => ClReadResultFull h r z zs s l bs outcome regs after ∧
      ∃ used, used ≤ bs.length ∧ BitInv after regs (bs.drop used) ∧
        regs.next = inputAdvance l.next used ∧ regs.bits.toNat ≤ l.bits.toNat + 8 * used) ?_ (l := l) (h := h) ?_ ?_
  · rw [clRead_eq]
    exact loop
  · intro regs heap inv
    obtain ⟨state, used, heapEq, frame, sz, count, prefixValues, usedBound, bitInv, regFrame, bitBound, cursor, budget⟩ := inv
    subst heap
    have get : (setI h zs state).istates zs = some state := by simp
    have stream : r.get (setI h zs state) = some z := by simpa using hz
    have fields : state.nlen = s.nlen ∧ state.ndist = s.ndist ∧ state.mode = CODELENS := by
      rw [frame]
      exact ⟨rfl, rfl, mode⟩
    have sum : (state.nlen + state.ndist).toNat = total := by
      rw [fields.1, fields.2.1, UInt32.toNat_add, Nat.mod_eq_of_lt (by omega)]
    have currentInv : CodeLengthInvariant zs state := by
      intro _
      refine ⟨?_, ?_, ?_, ?_, ?_, prefixValues⟩
      · rw [frame]; exact pointer
      · rw [frame]; exact table
      · rw [fields.1]; exact nlen
      · rw [fields.2.1]; exact ndist
      · rw [fields.1, fields.2.1]; exact count
    have condRun : runX (clReadCond c) regs (setI h zs state) =
        .ok ((.ok (decide (state.«have» < state.nlen + state.ndist)), regs), setI h zs state) := by
      unfold clReadCond
      rw [hc]
      simp [runX_bind, runX_lift, ldI_eq, get, runX_pure]
    by_cases more : state.«have» < state.nlen + state.ndist
    · have moreNat : state.«have».toNat < state.nlen.toNat + state.ndist.toNat := by
        have := UInt32.lt_iff_toNat_lt.mp more
        rw [sum] at this
        rw [fields.1, fields.2.1]
        exact this
      obtain ⟨result, nextRegs, after, consumed, bodyRun, consumedBound, nextInv, nextFrame, nextBits, post, stepCursor, stepBudget⟩ :=
        clReadBody_run_cursor hr hc stream get sz fields.2.2 currentInv moreNat bitInv
      refine ⟨.ok true, regs, setI h zs state, by simpa only [more, decide_true] using condRun,
        result, nextRegs, after, bodyRun, ?_⟩
      have consumedTotal : used + consumed ≤ bs.length := by
        simp only [List.length_drop] at consumedBound
        omega
      have nextInput : BitInv after nextRegs (bs.drop (used + consumed)) := by
        simpa only [List.drop_drop, Nat.add_comm] using nextInv
      have nextCursor : nextRegs.next = inputAdvance l.next (used + consumed) := by
        rw [stepCursor, cursor, inputAdvance_add]
      have nextBudget : nextRegs.bits.toNat ≤ l.bits.toNat + 8 * (used + consumed) := by omega
      have nextShape := regFrame.trans nextFrame
      have nextBound : nextRegs.bits.toNat ≤ max l.bits.toNat 21 := by omega
      cases result with
      | error fault =>
        have same : after = setI h zs state := post
        subst after
        refine ⟨?_, used + consumed, consumedTotal, nextInput, nextCursor, nextBudget⟩
        constructor
        · refine ⟨state, used + consumed, get, consumedTotal, nextInput, nextShape, nextBound,
            ?_, sz, count, prefixValues, Or.inl fields.2.2, ?_⟩
          · rw [frame]
          · intro impossible; cases impossible
        · exact ⟨z, stream, rfl, state, by rw [ZStreamRef.put_self hz]⟩
      | ok decision =>
        cases decision with
        | false =>
          obtain ⟨nextState, afterEq, writeFrame, nextSize, nextCount, progress, nextPrefix⟩ := post
          subst after
          constructor
          · refine ⟨nextState, used + consumed, by simp, ?_, nextSize, ?_, nextPrefix,
              consumedTotal, ?_, nextShape, nextBound, nextCursor, nextBudget⟩
            · rw [writeFrame, frame]
            · rw [fields.1, fields.2.1] at nextCount
              exact nextCount
            · simpa only [setI_setI] using nextInput
          · dsimp only [rank]
            simp only [setI_istates_same, Option.getD_some]
            rw [fields.1, fields.2.1] at nextCount
            omega
        | true =>
          obtain ⟨i, _, afterEq⟩ := post
          subst after
          have badGet : (tcBadHeap (setI h zs state) r zs z state i).istates zs =
              some { state with mode := BAD } := by simp [tcBadHeap]
          refine ⟨?_, used + consumed, consumedTotal, nextInput, nextCursor, nextBudget⟩
          constructor
          · refine ⟨{ state with mode := BAD }, used + consumed, badGet, consumedTotal,
              nextInput, nextShape, nextBound, ?_, sz, count, prefixValues, Or.inr rfl,
              fun _ => Or.inl rfl⟩
            rw [frame]
          · refine ⟨{ z with msg := .ref (.str i) 0 }, ?_, rfl, { state with mode := BAD }, ?_⟩
            · simp [tcBadHeap, hz]
            · simp [tcBadHeap, ZStreamRef.put_setI, setI_setI]
    · have full : state.«have».toNat = total := by
        have notLess := (not_congr UInt32.lt_iff_toNat_lt).mp more
        rw [sum] at notLess
        omega
      refine ⟨.ok false, regs, setI h zs state,
        by simpa only [more, decide_false] using condRun, ?_⟩
      refine ⟨?_, used, usedBound, bitInv, cursor, budget⟩
      constructor
      · refine ⟨state, used, get, usedBound, bitInv, regFrame, bitBound, ?_, sz, count,
          prefixValues, Or.inl fields.2.2, fun _ => Or.inr full⟩
        rw [frame]
      · exact ⟨z, stream, rfl, state, by rw [ZStreamRef.put_self hz]⟩
  · exact ⟨s, 0, (tcSetI_same hs).symm, rfl, size, haveBound, initialized, by omega,
      by simpa only [List.drop_zero] using B, ClRegShape.refl l, by omega, (inputAdvance_zero l.next).symm, by omega⟩
  · dsimp only [rank]
    rw [hs]
    simp only [Option.getD_some]
    unfold fuel total
    omega


/-- Projection retaining the original complete reading-loop interface. -/
theorem clRead_run_full {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef}
    {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8}
    (hr : c.strm = some r) (hc : c.st = some (.tab zs))
    (hz : r.get h = some z) (hs : h.istates zs = some s)
    (size : s.lens.size = 320) (mode : s.mode = CODELENS)
    (stateInv : CodeLengthInvariant zs s) (B : BitInv h l bs) :
    ∃ outcome regs after, runX (clRead c) l h = .ok ((outcome, regs), after) ∧
      ClReadResultFull h r z zs s l bs outcome regs after := by
  obtain ⟨outcome, regs, after, run, result, _⟩ :=
    clRead_run_full_cursor hr hc hz hs size mode stateInv B
  exact ⟨outcome, regs, after, run, result⟩

/-- The safety and initialized-prefix projection of the stronger actual
loop result. The original statement is retained. -/
theorem clRead_run {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef}
    {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8}
    (hr : c.strm = some r) (hc : c.st = some (.tab zs))
    (hz : r.get h = some z) (hs : h.istates zs = some s)
    (size : s.lens.size = 320) (mode : s.mode = CODELENS)
    (stateInv : CodeLengthInvariant zs s) (B : BitInv h l bs) :
    ∃ outcome regs after, runX (clRead c) l h = .ok ((outcome, regs), after) ∧
      ClReadResult zs s l bs outcome regs after := by
  obtain ⟨outcome, regs, after, run, result, _⟩ :=
    clRead_run_full hr hc hz hs size mode stateInv B
  exact ⟨outcome, regs, after, run, result⟩

end Zlib.Inflate.Proofs
