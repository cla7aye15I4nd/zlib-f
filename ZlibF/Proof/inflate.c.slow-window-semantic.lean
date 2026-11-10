import ZlibF.Proof.«inflate.c.slow-match-semantic»
import ZlibF.Proof.«inflate.c.window-public-ring»
import ZlibF.Proof.«inflate.c.match-boundary»
import ZlibF.Proof.«inflate.c.output-invariant»
namespace Zlib.Inflate.Proofs.SlowWindowSemanticPath
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs ZlibF.Math.LZ77Copy
open Zlib.Inflate.Proofs.SlowMatchSemanticPath
set_option autoImplicit false
/-- Chronological window indexing is the actual array cell. -/
theorem ringList_getD (a : Array UInt8) (ws wn wh j : Nat) (inside : j < wh) :
    (ringList a ws wn wh).getD j 0 = a.getD (ringSlot ws wn wh j) 0 := by
  have length : j < (ringList a ws wn wh).length := by simp [ringList]; exact inside
  rw [← List.getElem_eq_getD (h := length) 0]
  simp only [ringList, List.getElem_map, List.getElem_range]
  rfl
/-- The segment before the physical ring end has the chronological cells. -/
theorem ring_before_wrap (ws wn wh back i : Nat)
    (hwh : wh ≤ ws) (hb : back ≤ wh) (hw : wn < back) (hi : i < back - wn) :
    ringSlot ws wn wh (wh - back + i) = ws + wn - back + i := by
  have hfull : ¬ wh ≤ wn := by omega
  have hindex : wh - back + i < wh - wn := by omega
  simp only [ringSlot, hfull, hindex, ite_false, ite_true]
  omega
/-- The segment before the write cursor has the chronological cells. -/
theorem ring_no_wrap (ws wn wh back i : Nat)
    (hb : back ≤ wh) (hw : back ≤ wn) (_hi : i < back) :
    ringSlot ws wn wh (wh - back + i) = wn - back + i := by
  by_cases hfull : wh ≤ wn
  · simp only [ringSlot, hfull, ite_true]
    omega
  · have hindex : ¬ wh - back + i < wh - wn := by omega
    simp only [ringSlot, hfull, hindex, ite_false]
    omega
theorem inflate_MATCH_window_semantics {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (E : Env c h r zs z s) (good : Good h r zs z s) (dict : List UInt8)
    (dictionary : InflateDictionary h s dict) {l : IL} {dest : BRef}
    {output : Array UInt8} {outOffset : Nat}
    (put : l.put = .ref dest outOffset) (outGet : Space.get h dest = some output) (write : Space.ro h dest = false)
    (left : 0 < l.left.toNat) (length : 0 < s.length.toNat) (_offset : 0 < s.offset.toNat)
    (room : outOffset + l.left.toNat ≤ output.size)
    (count : l.left.toNat ≤ l.out_.toNat) (produced : l.out_.toNat - l.left.toNat ≤ outOffset)
    (separate : ∀ w, s.window = .ref (.blk w) 0 → dest ≠ .blk w)
    (inWindow : s.offset > l.out_ - l.left)
    (history : ¬ s.offset - (l.out_ - l.left) > s.whave) :
    ∃ amount regs after array,
      runX (inflate_MATCH c) l h = .ok ((.ok (), regs), after) ∧
      0 < amount.toNat ∧ amount.toNat ≤ l.left.toNat ∧ amount.toNat ≤ s.length.toNat ∧
      Space.get after dest = some array ∧ array.size = output.size ∧
      after.istates zs = some (matchEmitState s amount) ∧
      writtenBytes array (outOffset + amount.toNat)
          (l.out_.toNat - l.left.toNat + amount.toNat) =
        copyBack dict s.offset.toNat amount.toNat
          (writtenBytes output outOffset (l.out_.toNat - l.left.toNat)) := by
  have window := good.inv.win
  have leftNe : l.left ≠ 0 := by intro zero; rw [zero] at left; contradiction
  have outSub : (l.out_ - l.left).toNat = l.out_.toNat - l.left.toNat :=
  UInt32.toNat_sub_of_le _ _ (by exact count)
  have inWindowNat : (l.out_ - l.left).toNat < s.offset.toNat := UInt32.lt_iff_toNat_lt.mp inWindow
  let distance := s.offset - (l.out_ - l.left)
  have distSub : distance.toNat = s.offset.toNat - (l.out_ - l.left).toNat :=
    UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (Nat.le_of_lt inWindowNat))
  have distPositive : 0 < distance.toNat := by omega
  have hist : distance.toNat ≤ s.whave.toNat := by
    simpa only [UInt32.lt_iff_toNat_lt, Nat.not_lt] using history
  have wsPositive : 0 < s.wsize.toNat := by have := window.hv; omega
  have ws : s.wsize.toNat = 2 ^ s.wbits.toNat := by rcases window.ws with zero | eq; omega; exact eq
  obtain ⟨w, saved, winPtr, savedGet, _, savedSize⟩ :
      ∃ w saved, s.window = .ref (.blk w) 0 ∧ h.bytes w = some saved ∧ h.ro w = false ∧ saved.size = 2 ^ s.wbits.toNat := by
    rcases window.block with null | live
    · have zero := window.nullws null
      rw [zero] at wsPositive
      contradiction
    · exact live
  have physical : dict = ringList saved s.wsize.toNat s.wnext.toNat s.whave.toNat :=
    (inflateDictionary_eq_ring good winPtr savedGet savedSize).mp dictionary
  have dictLength : dict.length = s.whave.toNat := by rw [physical]; simp [ringList]
  have runSegment (copy : UInt32) (sourceOffset : Nat)
      (positive : 0 < copy.toNat) (copyLeft : copy.toNat ≤ l.left.toNat)
      (copyLength : copy.toNat ≤ s.length.toNat)
      (sourceFit : sourceOffset + copy.toNat ≤ saved.size)
      (segment : copy.toNat ≤ s.offset.toNat - (l.out_.toNat - l.left.toNat))
      (contents : ∀ i, i < copy.toNat → saved.getD (sourceOffset + i) 0 =
        dict.getD (dict.length + (l.out_.toNat - l.left.toNat) - s.offset.toNat + i) 0)
      (selection : runX (matchSelect c) l h = runX (matchEmit c copy (.ref (.blk w) sourceOffset)) l h) :
      ∃ amount regs after array,
        runX (inflate_MATCH c) l h = .ok ((.ok (), regs), after) ∧
        0 < amount.toNat ∧ amount.toNat ≤ l.left.toNat ∧ amount.toNat ≤ s.length.toNat ∧
        Space.get after dest = some array ∧ array.size = output.size ∧
        after.istates zs = some (matchEmitState s amount) ∧
        writtenBytes array (outOffset + amount.toNat)
            (l.out_.toNat - l.left.toNat + amount.toNat) =
          copyBack dict s.offset.toNat amount.toNat
            (writtenBytes output outOffset (l.out_.toNat - l.left.toNat)) := by
    obtain ⟨regs, after, array, emit, get, size, state, bytes⟩ :=
      matchEmit_saved_semantics E put outGet write (source := .blk w) (by exact savedGet)
        (Ne.symm (separate w winPtr)) positive produced (by rw [← outSub]; exact inWindowNat)
        dict (by rw [dictLength, ← outSub]; omega) segment (by omega) sourceFit contents
    refine ⟨copy, regs, after, array, ?_, positive, copyLeft, copyLength, get, size, state, bytes⟩
    rw [inflate_MATCH_select_cut, selection]
    exact emit
  have distinct : (.blk w : BRef) ≠ dest := (separate w winPtr).symm
  have sourceGet : Space.get h (BRef.blk w) = some (if (.blk w : BRef) = dest then output else saved) := by
    simpa only [ite_eq_right distinct, Space.get] using savedGet
  have wn : s.wnext.toNat < s.wsize.toNat := by rcases window.wn with lt | ⟨zero, _⟩; exact lt; omega
  have distSize : distance.toNat ≤ saved.size := by have := window.hv; omega
  by_cases wrap : distance > s.wnext
  · have wrapNat : s.wnext.toNat < distance.toNat := UInt32.lt_iff_toNat_lt.mp wrap
    let span := distance - s.wnext
    let start := s.wsize - span
    let capped := if span > s.length then s.length else span
    let copy := if capped > l.left then l.left else capped
    have spanNat : span.toNat = distance.toNat - s.wnext.toNat :=
      UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (Nat.le_of_lt wrapNat))
    have spanPositive : 0 < span.toNat := by omega
    have spanFit : span.toNat ≤ s.wsize.toNat := by have := window.hv; omega
    have startNat : start.toNat = s.wsize.toNat - span.toNat := UInt32.toNat_sub_of_le _ _ (by exact spanFit)
    have cappedBounds : 0 < capped.toNat ∧ capped.toNat ≤ span.toNat ∧ capped.toNat ≤ s.length.toNat := by
      unfold capped
      split <;> simp only [UInt32.lt_iff_toNat_lt] at * <;> omega
    have bounds : 0 < copy.toNat ∧ copy.toNat ≤ capped.toNat ∧ copy.toNat ≤ l.left.toNat := by
      unfold copy
      split <;> simp only [UInt32.lt_iff_toNat_lt] at * <;> omega
    have address : s.window.add (start.toNat : Int) h = .ok (.ref (.blk w) start.toNat, h) := by
      rw [winPtr]
      simpa only [OkOn, Nat.zero_add] using Ptr.add_nat_ok (r := BRef.blk w) (off := 0)
        (by exact savedGet) (by omega : 0 + start.toNat ≤ saved.size)
    apply runSegment copy start.toNat bounds.1 bounds.2.2 (by omega) (by omega)
      (by rw [distSub, outSub] at *; omega)
    · intro i inside
      rw [dictLength, physical, ringList_getD saved _ _ _ _ (by omega)]
      rw [show s.whave.toNat + (l.out_.toNat - l.left.toNat) - s.offset.toNat + i =
          s.whave.toNat - distance.toNat + i by omega]
      rw [ring_before_wrap _ _ _ _ _ window.hv (by omega) wrapNat (by omega)]
      congr 1
      omega
    · exact matchSelect_wrap_cut E l leftNe inWindow history wrap address
  · let start := s.wnext - distance
    let capped := if distance > s.length then s.length else distance
    let copy := if capped > l.left then l.left else capped
    have distNext : distance.toNat ≤ s.wnext.toNat := by simpa only [UInt32.lt_iff_toNat_lt, Nat.not_lt] using wrap
    have startNat : start.toNat = s.wnext.toNat - distance.toNat := UInt32.toNat_sub_of_le _ _ (by exact distNext)
    have cappedBounds : 0 < capped.toNat ∧ capped.toNat ≤ distance.toNat ∧ capped.toNat ≤ s.length.toNat := by
      unfold capped
      split <;> simp only [UInt32.lt_iff_toNat_lt] at * <;> omega
    have bounds : 0 < copy.toNat ∧ copy.toNat ≤ capped.toNat ∧ copy.toNat ≤ l.left.toNat := by
      unfold copy
      split <;> simp only [UInt32.lt_iff_toNat_lt] at * <;> omega
    have address : s.window.add (start.toNat : Int) h = .ok (.ref (.blk w) start.toNat, h) := by
      rw [winPtr]
      simpa only [OkOn, Nat.zero_add] using Ptr.add_nat_ok (r := BRef.blk w) (off := 0)
        (by exact savedGet) (by omega : 0 + start.toNat ≤ saved.size)
    apply runSegment copy start.toNat bounds.1 bounds.2.2 (by omega) (by omega)
      (by rw [distSub, outSub] at *; omega)
    · intro i inside
      rw [dictLength, physical, ringList_getD saved _ _ _ _ (by omega)]
      rw [show s.whave.toNat + (l.out_.toNat - l.left.toNat) - s.offset.toNat + i =
          s.whave.toNat - distance.toNat + i by omega]
      rw [ring_no_wrap _ _ _ _ _ (by omega) distNext (by omega)]
      congr 1
      omega
    · exact matchSelect_window_cut E l leftNe inWindow history wrap address

/-- Physical dictionary contents have the exact retained byte count. -/
theorem inflateDictionary_length
    {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState} {dict : List UInt8}
    (good : Good h r zs z s) (dictionary : InflateDictionary h s dict) : dict.length = s.whave.toNat := by
  rcases good.inv.win.block with null | ⟨w, a, win, get, ro, size⟩
  · rcases dictionary with ⟨zero, nil⟩ | ⟨ref, off, array, pointer, _⟩
    · rw [nil, zero]; rfl
    · rw [null] at pointer; cases pointer
  · rw [(inflateDictionary_eq_ring good win get size).mp dictionary]
    simp [ringList]

/-- Every valid positive MATCH segment, whether its physical source is in
the window or current output, appends the same independent copyBack bytes. -/
theorem inflate_MATCH_valid_segment
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (E : Env c h r zs z s) (good : Good h r zs z s) (dict : List UInt8)
    (dictionary : InflateDictionary h s dict) {l : IL} {dest : BRef}
    {output : Array UInt8} {outOffset : Nat}
    (put : l.put = .ref dest outOffset) (get : Space.get h dest = some output) (write : Space.ro h dest = false)
    (left : 0 < l.left.toNat) (length : 0 < s.length.toNat) (distance : 0 < s.offset.toNat)
    (room : outOffset + l.left.toNat ≤ output.size)
    (count : l.left.toNat ≤ l.out_.toNat) (produced : l.out_.toNat - l.left.toNat ≤ outOffset)
    (separate : ∀ w, s.window = .ref (.blk w) 0 → dest ≠ .blk w)
    (available : s.offset.toNat ≤ dict.length + (l.out_.toNat - l.left.toNat)) :
    ∃ amount regs after array,
      runX (inflate_MATCH c) l h = .ok ((.ok (), regs), after) ∧
      0 < amount.toNat ∧ amount.toNat ≤ l.left.toNat ∧ amount.toNat ≤ s.length.toNat ∧
      Space.get after dest = some array ∧ array.size = output.size ∧
      after.istates zs = some (matchEmitState s amount) ∧
      writtenBytes array (outOffset + amount.toNat)
          (l.out_.toNat - l.left.toNat + amount.toNat) =
        copyBack dict s.offset.toNat amount.toNat
          (writtenBytes output outOffset (l.out_.toNat - l.left.toNat)) := by
  have outSub : (l.out_ - l.left).toNat = l.out_.toNat - l.left.toNat :=
    UInt32.toNat_sub_of_le _ _ count
  by_cases inWindow : s.offset > l.out_ - l.left
  · have availableHistory : ¬ s.offset - (l.out_ - l.left) > s.whave := by
      have inWindowNat := UInt32.lt_iff_toNat_lt.mp inWindow
      have sub : (s.offset - (l.out_ - l.left)).toNat = s.offset.toNat - (l.out_ - l.left).toNat :=
        UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by omega))
      rw [inflateDictionary_length good dictionary] at available
      simp only [UInt32.lt_iff_toNat_lt, sub, outSub]
      omega
    exact inflate_MATCH_window_semantics E good dict dictionary put get write left length distance
      room count produced separate inWindow availableHistory
  · obtain ⟨regs, after, array, amount, run, _amount, positive, copyLeft, copyLength, getAfter,
      size, state, bytes⟩ :=
      inflate_MATCH_output_semantics E put get write left length distance produced count rfl
        (by simpa only [UInt32.lt_iff_toNat_lt, outSub, Nat.not_lt] using inWindow) room dict
    exact ⟨amount, regs, after, array, run, positive, copyLeft, copyLength, getAfter, size, state, bytes⟩

/-- The real independent MATCH segment also retains the existing safety
and unread-source clauses on the same execution. Physical ring contents
supply all byte premises, and public Separate covers disjoint same-object
input/output ranges. -/
theorem inflate_MATCH_valid_segment_safe
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (E : Env c h r zs z s) (good : Good h r zs z s) (tables : DataTablesSafe h s)
    {dict : List UInt8} (dictionary : InflateDictionary h s dict)
    {l : IL} {bs : List UInt8} {dest : BRef} {output : Array UInt8} {outOffset : Nat}
    (B : BitInv h l bs) (mode : s.mode = MATCH) (sane : s.sane ≠ 0)
    (put : l.put = .ref dest outOffset) (get : Space.get h dest = some output) (write : Space.ro h dest = false)
    (left : 0 < l.left.toNat) (length : 0 < s.length.toNat) (distance : 0 < s.offset.toNat)
    (room : outOffset + l.left.toNat ≤ output.size)
    (count : l.left.toNat ≤ l.out_.toNat) (produced : l.out_.toNat - l.left.toNat ≤ outOffset)
    (privateWindow : ∀ w, s.window = .ref (.blk w) 0 → dest ≠ .blk w)
    (separate : Separate l.next l.have_.toNat l.put l.left.toNat)
    (available : s.offset.toNat ≤ dict.length + (l.out_.toNat - l.left.toNat)) :
    ∃ amount regs after array stream,
      runX (inflate_MATCH c) l h = .ok ((.ok (), regs), after) ∧
      0 < amount.toNat ∧ amount.toNat ≤ l.left.toNat ∧ amount.toNat ≤ s.length.toNat ∧
      Good after r zs stream (matchEmitState s amount) ∧
      DataTableInvariant after (matchEmitState s amount) ∧ BitInv after regs bs ∧
      DecodeStateFrame s (matchEmitState s amount) ∧
      Space.get after dest = some array ∧ array.size = output.size ∧
      writtenBytes array (outOffset + amount.toNat)
          (l.out_.toNat - l.left.toNat + amount.toNat) =
        copyBack dict s.offset.toNat amount.toNat
          (writtenBytes output outOffset (l.out_.toNat - l.left.toNat)) := by
  obtain ⟨amount, regs, after, array, actual, positive, copyLeft, copyLength, getAfter,
    size, stateGet, bytes⟩ :=
    inflate_MATCH_valid_segment E good dict dictionary put get write left length distance room count produced
      privateWindow available
  have nonzero : l.left ≠ 0 := by intro zero; rw [zero] at left; contradiction
  obtain ⟨outcome, currentRegs, heap, stream, state, safetyRun, current, currentTables, inv, frame, kinds⟩ :=
    inflate_MATCH_boundary_ranges E good tables B put get write mode length distance sane room count produced
      privateWindow (B.output_positions put nonzero separate)
  have same := Except.ok.inj (actual.symm.trans safetyRun)
  cases same
  have stateEq : state = matchEmitState s amount := Option.some.inj (current.live.hs.symm.trans stateGet)
  subst state
  exact ⟨amount, regs, after, array, stream, actual, positive, copyLeft, copyLength, current,
    currentTables, inv, frame, getAfter, size, bytes⟩

#print axioms ringList_getD
#print axioms ring_before_wrap
#print axioms ring_no_wrap
#print axioms inflate_MATCH_window_semantics
#print axioms inflateDictionary_length
#print axioms inflate_MATCH_valid_segment
#print axioms inflate_MATCH_valid_segment_safe
end Zlib.Inflate.Proofs.SlowWindowSemanticPath
