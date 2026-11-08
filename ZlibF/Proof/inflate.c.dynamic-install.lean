import ZlibF.Proof.«inflate.c.main.table5»
import ZlibF.Proof.«inflate.c.table-invariant»
import ZlibF.Proof.«inftrees.c.read-extent»
import ZlibF.Proof.«inftrees.c.decode.prefix-safe»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inftrees
set_option autoImplicit false

def clRead (c : Ctx) : X Unit := do
  -- while (state->have < state->nlen + state->ndist) {
  xwhileBrk
    (do let s ← ldInflateState c.st; return s.have < s.nlen + s.ndist)
    (do
      lookup1 c false
      let here := (← get).here
      -- if (here.val < 16) { DROPBITS(here.bits); state->lens[state->have++] = here.val; }
      if here.val < 16 then
        DROPBITS here.bits.toUInt32
        let s ← ldInflateState c.st
        Ptr.store (← (lensP c.st).add (s.have.toNat : Int)) here.val
        wrS c.st fun s => { s with «have» := s.«have» + 1 }
        return false
      else
        if here.val == 16 then
          NEEDBITS (here.bits.toUInt32 + 2)
          DROPBITS here.bits.toUInt32
          -- if (state->have == 0) { "invalid bit length repeat"; BAD; break; }
          let s ← ldInflateState c.st
          if s.«have» == 0 then
            badMode c "invalid bit length repeat"
            return true
          -- len = state->lens[state->have - 1]; copy = 3 + BITS(2); DROPBITS(2);
          let v ← Ptr.index (lensP c.st) ((s.«have» - 1).toNat : Int)
          let b ← BITS 2
          modify fun l => { l with len := v.toUInt32, copy := 3 + b }
          DROPBITS 2
        else if here.val == 17 then
          NEEDBITS (here.bits.toUInt32 + 3)
          DROPBITS here.bits.toUInt32
          let b ← BITS 3
          modify fun l => { l with len := 0, copy := 3 + b }
          DROPBITS 3
        else
          NEEDBITS (here.bits.toUInt32 + 7)
          DROPBITS here.bits.toUInt32
          let b ← BITS 7
          modify fun l => { l with len := 0, copy := 11 + b }
          DROPBITS 7
        -- if (state->have + copy > state->nlen + state->ndist) { "invalid bit length repeat"; BAD; break; }
        let s ← ldInflateState c.st
        if s.«have» + (← get).copy > s.nlen + s.ndist then
          badMode c "invalid bit length repeat"
          return true
        -- while (copy--) state->lens[state->have++] = (unsigned short)len;
        xwhile
          (do
            let l ← get
            set { l with copy := l.copy - 1 }
            return l.copy != 0)
          (do
            let s ← ldInflateState c.st
            Ptr.store (← (lensP c.st).add (s.«have».toNat : Int)) (← get).len.toUInt16
            wrS c.st fun s => { s with «have» := s.«have» + 1 })
        return false)

def clTables (c : Ctx) : X Unit := do
  -- state->next = state->codes; state->lencode = (const code FAR *)(state->next); state->lenbits = 9;
  wrS c.st fun s => { s with next := codesP c.st, lencode := codesP c.st, lenbits := 9 }
  -- ret = inflate_table(LENS, state->lens, state->nlen, &(state->next), &(state->lenbits), state->work);
  let s ← ldInflateState c.st
  let (r, nx, lb) ← inflate_table LENS (lensP c.st) s.nlen s.next s.lenbits (workP c.st)
  wrS c.st fun s => { s with next := nx, lenbits := lb }
  modify fun l => { l with ret := r }
  -- if (ret) { "invalid literal/lengths set"; BAD; break; }
  if r != 0 then
    badMode c "invalid literal/lengths set"
    return
  -- state->distcode = (const code FAR *)(state->next); state->distbits = 6;
  wrS c.st fun s => { s with distcode := s.next, distbits := 6 }
  -- ret = inflate_table(DISTS, state->lens + state->nlen, state->ndist, &(state->next), &(state->distbits), state->work);
  let s ← ldInflateState c.st
  let (r, nx, db) ← inflate_table DISTS (← (lensP c.st).add (s.nlen.toNat : Int)) s.ndist s.next s.distbits (workP c.st)
  wrS c.st fun s => { s with next := nx, distbits := db }
  modify fun l => { l with ret := r }
  if r != 0 then
    badMode c "invalid distances set"
    return
  -- state->mode = LEN_; if (flush == Z_TREES) goto inf_leave; /* fallthrough */
  setMode c.st LEN_
  if c.flush == Z_TREES then throw Ex.leave
  inflate_LEN_ c

def clAfterLens (c : Ctx) (r : Int32) : X Unit := do
  -- if (ret) { "invalid literal/lengths set"; BAD; break; }
  if r != 0 then
    badMode c "invalid literal/lengths set"
    return
  -- state->distcode = (const code FAR *)(state->next); state->distbits = 6;
  wrS c.st fun s => { s with distcode := s.next, distbits := 6 }
  -- ret = inflate_table(DISTS, state->lens + state->nlen, state->ndist, &(state->next), &(state->distbits), state->work);
  let s ← ldInflateState c.st
  let (r, nx, db) ← inflate_table DISTS (← (lensP c.st).add (s.nlen.toNat : Int)) s.ndist s.next s.distbits (workP c.st)
  wrS c.st fun s => { s with next := nx, distbits := db }
  modify fun l => { l with ret := r }
  if r != 0 then
    badMode c "invalid distances set"
    return
  -- state->mode = LEN_; if (flush == Z_TREES) goto inf_leave; /* fallthrough */
  setMode c.st LEN_
  if c.flush == Z_TREES then throw Ex.leave
  inflate_LEN_ c


def clAfterDist (c : Ctx) (r : Int32) : X Unit := do
  if r != 0 then
    badMode c "invalid distances set"
    return
  -- state->mode = LEN_; if (flush == Z_TREES) goto inf_leave; /* fallthrough */
  setMode c.st LEN_
  if c.flush == Z_TREES then throw Ex.leave
  inflate_LEN_ c


def clTail (c : Ctx) : X Unit := do
  -- if (state->mode == BAD) break;
  if (← rdS c.st (·.mode)) == BAD then return
  -- if (state->lens[256] == 0) { "invalid code -- missing end-of-block"; BAD; break; }
  if (← Ptr.index (lensP c.st) 256) == (0 : UInt16) then
    badMode c "invalid code -- missing end-of-block"
    return
  clTables c

theorem inflate_CODELENS_eq (c : Ctx) : inflate_CODELENS c = (do clRead c; clTail c) := rfl

def clLensPre (zs : Nat) (s : InflateState) : InflateState :=
  { s with next := .ref (.istate_codes zs) 0, lencode := .ref (.istate_codes zs) 0, lenbits := 9 }

def clLensResult (zs : Nat) (s : InflateState) (next : CodePtr) (bits : UInt32)
    (work : Array UInt16) (codes : Array Code) : InflateState :=
  { clLensPre zs s with next := next, lenbits := bits, work := work, codes := codes }

/-- `case CODELENS:` after decoded lengths and the end-of-block check.
The actual LENS call establishes length-table safety and its precise read
extent before the actual distance-construction continuation. Every table
outcome is retained. Bounds and initialized lengths are mode invariants;
no table-validity or callee-correctness premise is assumed. -/
theorem clTables_lens_run_complete {c : Ctx} {l : IL} {h : Heap} {zs : Nat} {s : InflateState}
    (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s)
    (wf : s.WellFormed) (count : s.nlen.toNat ≤ 286)
    (lengths : ∀ k, k < s.nlen.toNat → (s.lens.getD k 0).toNat ≤ 15) :
    ∃ (ret : Int32) (next : CodePtr) (bits : UInt32) (work : Array UInt16) (codes : Array Code),
      work.size = 288 ∧ codes.size = 1444 ∧
      (∃ used, next = .ref (.istate_codes zs) used ∧ used ≤ 852) ∧ bits.toNat ≤ 15 ∧
      runX (clTables c) l h = runX (clAfterLens c ret) { l with ret := ret }
        (setI h zs (clLensResult zs s next bits work codes)) ∧
      (ret = 0 → ∃ used, next = .ref (.istate_codes zs) used ∧ used ≤ 852 ∧
        Zlib.Inffast.Spec.LenTableSafe codes 0 bits.toNat ∧
        Zlib.Inftrees.Spec.TableReadExtent LENS codes 0 bits.toNat used) := by
  obtain ⟨lensSize, workSize, codeSize⟩ := wf
  have stored : (setI h zs (clLensPre zs s)).istates zs = some (clLensPre zs s) := by simp
  have lens : Space.get (setI h zs (clLensPre zs s)) (WRef.istate_lens zs) = some s.lens := by
    simpa [clLensPre] using WRef.get_istate_lens stored
  have work : Space.get (setI h zs (clLensPre zs s)) (WRef.istate_work zs) = some s.work := by
    simpa [clLensPre] using WRef.get_istate_work stored
  have codes : Space.get (setI h zs (clLensPre zs s)) (CodeRef.istate_codes zs) = some s.codes := by
    simpa [clLensPre] using CodeRef.get_istate_codes stored
  let pre : Zlib.Inftrees.Proofs.CallPre (setI h zs (clLensPre zs s)) LENS
      (.istate_lens zs) 0 s.nlen (.istate_codes zs) 0 9 (.istate_work zs) 0 :=
    ⟨s.lens, s.work, s.codes, Or.inr (Or.inl rfl), lens, work, codes, by simp, by simp,
      by omega, by omega, by simp [Zlib.Inftrees.Spec.capOf, LENS, CODES]; omega,
      by simpa using lengths, (by intro impossible; cases impossible),
      fun _ => by omega, (by intro impossible; cases impossible)⟩
  obtain ⟨result, after, run, frame, tables⟩ :=
    Zlib.Inftrees.Proofs.inflate_table_read_extent _ _ _ _ _ _ _ _ _ _ pre
  have bounds := Zlib.Inftrees.Proofs.result_pointer_width_bounds frame (by decide)
    (by
      intro success
      obtain ⟨_, _, _, _, _, extent, _⟩ := tables success
      exact extent.2.1)
  obtain ⟨ret, next, bits⟩ := result
  have pointerBounds : ∃ used, next = .ref (.istate_codes zs) used ∧ used ≤ 852 := by
    obtain ⟨used, bound, pointer⟩ := bounds.1
    exact ⟨used, by simpa using pointer,
      by simpa [Zlib.Inftrees.Spec.capOf, LENS, CODES] using bound⟩
  obtain ⟨wa, ca, heap, waSize, caSize, _, _, _⟩ := frame
  refine ⟨ret, next, bits, wa, ca, waSize.trans workSize, caSize.trans codeSize, pointerBounds, bounds.2, ?_, ?_⟩
  · unfold clTables clAfterLens
    rw [hc]
    have actual := run
    change inflate_table LENS _ _ _ _ _ _ = _ at actual
    simp only [clLensPre] at actual
    rw [heap, put_work_codes stored] at actual
    simp [runX_bind, runX_lift, wrI_eq, ldI_eq, hs, clLensPre, lensP, workP, codesP,
      actual, runX_modify, setI_setI, clLensResult]
  · intro success
    obtain ⟨array, used, get, pointer, bound, extent, _, safe, _⟩ := tables success
    have actualGet : Space.get after (CodeRef.istate_codes zs) = some ca := by
      rw [heap, put_work_codes stored]
      simp [Space.get, setI, clLensPre]
    rw [actualGet] at get
    cases get
    exact ⟨used, by simpa using pointer, by simpa [Zlib.Inftrees.Spec.capOf, LENS, CODES] using bound,
      safe rfl, extent⟩

theorem clTables_lens_run {c : Ctx} {l : IL} {h : Heap} {zs : Nat} {s : InflateState}
    (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s)
    (wf : s.WellFormed) (count : s.nlen.toNat ≤ 286)
    (lengths : ∀ k, k < s.nlen.toNat → (s.lens.getD k 0).toNat ≤ 15) :
    ∃ (ret : Int32) (next : CodePtr) (bits : UInt32) (work : Array UInt16) (codes : Array Code),
      work.size = 288 ∧ codes.size = 1444 ∧
      runX (clTables c) l h = runX (clAfterLens c ret) { l with ret := ret }
        (setI h zs (clLensResult zs s next bits work codes)) ∧
      (ret = 0 → ∃ used, next = .ref (.istate_codes zs) used ∧ used ≤ 852 ∧
        Zlib.Inffast.Spec.LenTableSafe codes 0 bits.toNat ∧
        Zlib.Inftrees.Spec.TableReadExtent LENS codes 0 bits.toNat used) := by
  obtain ⟨ret, next, bits, work, codes, workSize, codeSize, _, _, run, safe⟩ :=
    clTables_lens_run_complete hc hs wf count lengths
  exact ⟨ret, next, bits, work, codes, workSize, codeSize, run, safe⟩

def clDistPre (s : InflateState) : InflateState :=
  { s with distcode := s.next, distbits := 6 }

def clDistResult (s : InflateState) (next : CodePtr) (bits : UInt32)
    (work : Array UInt16) (codes : Array Code) : InflateState :=
  { clDistPre s with next := next, distbits := bits, work := work, codes := codes }

/-- `case CODELENS:` after successful LENS construction.
The actual DISTS call preserves the previously produced length table and
its read extent, and establishes the distance table before its actual
continuation. Its start is the actual returned LENS end. -/
theorem clAfterLens_distance_run_complete {c : Ctx} {l : IL} {h : Heap} {zs : Nat} {s : InflateState}
    (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s)
    (wf : s.WellFormed) (nlen : s.nlen.toNat ≤ 286) (ndist : s.ndist.toNat ≤ 30)
    (lengths : ∀ k, k < s.ndist.toNat → (s.lens.getD (s.nlen.toNat + k) 0).toNat ≤ 15)
    (offset : Nat) (next : s.next = .ref (.istate_codes zs) offset) (room : offset ≤ 852)
    (lensSafe : Zlib.Inffast.Spec.LenTableSafe s.codes 0 s.lenbits.toNat)
    (lensExtent : Zlib.Inftrees.Spec.TableReadExtent LENS s.codes 0 s.lenbits.toNat offset) :
    ∃ (ret : Int32) (next : CodePtr) (bits : UInt32) (work : Array UInt16) (codes : Array Code),
      work.size = 288 ∧ codes.size = 1444 ∧
      (∃ used, next = .ref (.istate_codes zs) (offset + used) ∧ used ≤ 592) ∧ bits.toNat ≤ 15 ∧
      runX (clAfterLens c 0) l h = runX (clAfterDist c ret) { l with ret := ret }
        (setI h zs (clDistResult s next bits work codes)) ∧
      Zlib.Inffast.Spec.LenTableSafe codes 0 s.lenbits.toNat ∧
      Zlib.Inftrees.Spec.TableReadExtent LENS codes 0 s.lenbits.toNat offset ∧
      (ret = 0 → Zlib.Inffast.Spec.DistTableSafe codes offset bits.toNat) := by
  obtain ⟨lensSize, workSize, codeSize⟩ := wf
  have stored : (setI h zs (clDistPre s)).istates zs = some (clDistPre s) := by simp
  have lens : Space.get (setI h zs (clDistPre s)) (WRef.istate_lens zs) = some s.lens := by
    simpa [clDistPre] using WRef.get_istate_lens stored
  have work : Space.get (setI h zs (clDistPre s)) (WRef.istate_work zs) = some s.work := by
    simpa [clDistPre] using WRef.get_istate_work stored
  have codes : Space.get (setI h zs (clDistPre s)) (CodeRef.istate_codes zs) = some s.codes := by
    simpa [clDistPre] using CodeRef.get_istate_codes stored
  let pre : Zlib.Inftrees.Proofs.CallPre (setI h zs (clDistPre s)) DISTS
      (.istate_lens zs) s.nlen.toNat s.ndist (.istate_codes zs) offset 6 (.istate_work zs) 0 :=
    ⟨s.lens, s.work, s.codes, Or.inr (Or.inr rfl), lens, work, codes, by simp, by simp,
      by omega, by omega, by simp [Zlib.Inftrees.Spec.capOf, LENS, DISTS, CODES]; omega,
      lengths, (by intro impossible; cases impossible),
      (by intro impossible; cases impossible), fun _ => by omega⟩
  obtain ⟨result, after, run, frame, tables⟩ :=
    Zlib.Inftrees.Proofs.inflate_table_read_extent _ _ _ _ _ _ _ _ _ _ pre
  obtain ⟨preservedResult, preservedAfter, array, preservedRun, _, getArray, safeLens, extentLens, _⟩ :=
    Zlib.Inftrees.Proofs.inflate_table_dists_preserves_lens pre (by omega)
      lensSafe lensExtent
  rw [run] at preservedRun
  cases preservedRun
  have bounds := Zlib.Inftrees.Proofs.result_pointer_width_bounds frame (by decide)
    (by
      intro success
      obtain ⟨_, _, _, _, _, extent, _⟩ := tables success
      exact extent.2.1)
  obtain ⟨ret, nextResult, bits⟩ := result
  have pointerBounds : ∃ used, nextResult = .ref (.istate_codes zs) (offset + used) ∧ used ≤ 592 := by
    obtain ⟨used, bound, pointer⟩ := bounds.1
    exact ⟨used, pointer, by simpa [Zlib.Inftrees.Spec.capOf, LENS, DISTS, CODES] using bound⟩
  obtain ⟨wa, ca, heap, waSize, caSize, _, _, _⟩ := frame
  have actualGet : Space.get after (CodeRef.istate_codes zs) = some ca := by
    rw [heap, put_work_codes stored]
    simp [Space.get, setI, clDistPre]
  rw [actualGet] at getArray
  have sameArray : ca = array := Option.some.inj getArray
  subst array
  refine ⟨ret, nextResult, bits, wa, ca, waSize.trans workSize, caSize.trans codeSize, pointerBounds, bounds.2, ?_,
    safeLens, extentLens, ?_⟩
  · unfold clAfterLens clAfterDist
    rw [hc]
    have actual := run
    change inflate_table DISTS _ _ _ _ _ _ = _ at actual
    rw [heap, put_work_codes stored] at actual
    have add := Ptr.add_nat_ok (off := 0) (n := s.nlen.toNat) lens (by omega : 0 + s.nlen.toNat ≤ s.lens.size)
    unfold OkOn at add
    simp only [Nat.zero_add, clDistPre, next, setI_setI] at add actual
    simp [runX_bind, runX_lift, wrI_eq, ldI_eq, hs, clDistPre, lensP, workP, codesP,
      next, add, actual, runX_modify, setI_setI, clDistResult]
  · intro success
    obtain ⟨table, _, get, _, _, _, _, _, safe⟩ := tables success
    rw [actualGet] at get
    cases get
    exact safe rfl

theorem clAfterLens_distance_run {c : Ctx} {l : IL} {h : Heap} {zs : Nat} {s : InflateState}
    (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s)
    (wf : s.WellFormed) (nlen : s.nlen.toNat ≤ 286) (ndist : s.ndist.toNat ≤ 30)
    (lengths : ∀ k, k < s.ndist.toNat → (s.lens.getD (s.nlen.toNat + k) 0).toNat ≤ 15)
    (offset : Nat) (next : s.next = .ref (.istate_codes zs) offset) (room : offset ≤ 852)
    (lensSafe : Zlib.Inffast.Spec.LenTableSafe s.codes 0 s.lenbits.toNat)
    (lensExtent : Zlib.Inftrees.Spec.TableReadExtent LENS s.codes 0 s.lenbits.toNat offset) :
    ∃ (ret : Int32) (next : CodePtr) (bits : UInt32) (work : Array UInt16) (codes : Array Code),
      work.size = 288 ∧ codes.size = 1444 ∧
      runX (clAfterLens c 0) l h = runX (clAfterDist c ret) { l with ret := ret }
        (setI h zs (clDistResult s next bits work codes)) ∧
      Zlib.Inffast.Spec.LenTableSafe codes 0 s.lenbits.toNat ∧
      Zlib.Inftrees.Spec.TableReadExtent LENS codes 0 s.lenbits.toNat offset ∧
      (ret = 0 → Zlib.Inffast.Spec.DistTableSafe codes offset bits.toNat) := by
  obtain ⟨ret, nextResult, bits, work, codes, workSize, codeSize, _, _, run, safe, extent, distance⟩ :=
    clAfterLens_distance_run_complete hc hs wf nlen ndist lengths offset next room lensSafe lensExtent
  exact ⟨ret, nextResult, bits, work, codes, workSize, codeSize, run, safe, extent, distance⟩

theorem clAfterDist_success {c : Ctx} {l : IL} {h : Heap} {zs : Nat} {s : InflateState}
    (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s) :
    runX (clAfterDist c 0) l h =
      if c.flush = Z_TREES then .ok ((.error Ex.leave, l), setI h zs { s with mode := LEN_ })
      else runX (inflate_LEN_ c) l (setI h zs { s with mode := LEN_ }) := by
  unfold clAfterDist
  rw [hc]
  by_cases flush : c.flush = Z_TREES
  all_goals simp [runX_bind, runX_lift, setMode, wrI_eq, hs, runX_throw, flush]

/-- `case CODELENS:` the actual consecutive LENS and DISTS construction.
Successful construction installs both decoder-safe tables and activates
the guarded data-table invariant at LEN_. Constructor refusals remain
explicit outcomes. The continuation is the actual LEN_ handler, or the
actual Z_TREES leave; neither is replaced by a model decoder. -/
theorem clTables_data_boundary {c : Ctx} {l : IL} {h : Heap} {zs : Nat} {s : InflateState}
    (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s)
    (wf : s.WellFormed) (nlen : s.nlen.toNat ≤ 286) (ndist : s.ndist.toNat ≤ 30)
    (lengths : ∀ k, k < s.nlen.toNat + s.ndist.toNat → (s.lens.getD k 0).toNat ≤ 15) :
    ∃ (lensRet : Int32) (lensAfter : Heap) (lensState : InflateState),
      lensAfter.istates zs = some lensState ∧
      runX (clTables c) l h = runX (clAfterLens c lensRet) { l with ret := lensRet } lensAfter ∧
      (lensRet = 0 → ∃ (distRet : Int32) (after : Heap) (state : InflateState),
        after.istates zs = some state ∧
        runX (clTables c) l h = runX (clAfterDist c distRet) { l with ret := distRet } after ∧
        (distRet = 0 →
          DataTableInvariant (setI after zs { state with mode := LEN_ }) { state with mode := LEN_ } ∧
          runX (clTables c) l h =
            if c.flush = Z_TREES then
              .ok ((.error Ex.leave, { l with ret := 0 }), setI after zs { state with mode := LEN_ })
            else runX (inflate_LEN_ c) { l with ret := 0 }
              (setI after zs { state with mode := LEN_ }))) := by
  obtain ⟨lensRet, lensNext, lensBits, work1, codes1, workSize1, codeSize1, lensRun, lensSafe⟩ :=
    clTables_lens_run (l := l) hc hs wf nlen (fun k bound => lengths k (by omega))
  let lensState := clLensResult zs s lensNext lensBits work1 codes1
  let lensAfter := setI h zs lensState
  have lensGet : lensAfter.istates zs = some lensState := by simp [lensAfter]
  refine ⟨lensRet, lensAfter, lensState, lensGet, lensRun, ?_⟩
  intro lensOk
  obtain ⟨offset, pointer, room, safeLens, extentLens⟩ := lensSafe lensOk
  have lensWf : lensState.WellFormed := by
    exact ⟨wf.1, workSize1, codeSize1⟩
  have distLengths : ∀ k, k < lensState.ndist.toNat →
      (lensState.lens.getD (lensState.nlen.toNat + k) 0).toNat ≤ 15 := by
    intro k bound
    exact lengths (s.nlen.toNat + k) (by change k < s.ndist.toNat at bound; omega)
  obtain ⟨distRet, distNext, distBits, work2, codes2, workSize2, codeSize2, distRun,
      preservedLens, _, safeDist⟩ :=
    clAfterLens_distance_run (l := { l with ret := 0 }) hc lensGet lensWf nlen ndist
      distLengths offset pointer room safeLens extentLens
  let state := clDistResult lensState distNext distBits work2 codes2
  let after := setI lensAfter zs state
  have get : after.istates zs = some state := by simp [after]
  have run : runX (clTables c) l h = runX (clAfterDist c distRet) { l with ret := distRet } after := by
    rw [lensOk] at lensRun
    exact lensRun.trans distRun
  refine ⟨distRet, after, state, get, run, ?_⟩
  intro distOk
  have lenSafe : Zlib.Inffast.Spec.LenTableSafe codes2 0 lensBits.toNat := preservedLens
  have distanceSafe := safeDist distOk
  have finalGet : (setI after zs { state with mode := LEN_ }).istates zs =
      some { state with mode := LEN_ } := by simp
  have codeGet : Space.get (setI after zs { state with mode := LEN_ })
      (CodeRef.istate_codes zs) = some codes2 := by
    simpa [state, clDistResult] using CodeRef.get_istate_codes finalGet
  constructor
  · intro _
    constructor
    · exact ⟨.istate_codes zs, 0, codes2, rfl, codeGet, lenSafe⟩
    · refine ⟨.istate_codes zs, offset, codes2, ?_, codeGet, distanceSafe⟩
      exact pointer
  · rw [distOk] at run
    exact run.trans (clAfterDist_success hc get)

end Zlib.Inflate.Proofs
