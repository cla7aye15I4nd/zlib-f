import ZlibF.Proof.«trees.c.compress-literals»
import ZlibF.Math.DeflatePayloadFields

/-! # Actual payload symbols, including length and distance extras -/

namespace Zlib.Trees.Proofs
open C Zlib.Trees Out
set_option autoImplicit false
set_option maxRecDepth 10000

/-- Words from the installed fixed distance table. -/
def fixedDistanceWords (k : Nat) : UInt16 × UInt16 :=
  (static_dtree_tab[k]!.fc, static_dtree_tab[k]!.dl)

set_option maxHeartbeats 1000000 in
/-- Every used fixed length code fits in at most eight bits. -/
theorem fixed_length_fits (k : Nat) (bound : k < 29) :
    CodeFits fixedLiteralWords (k + 257) ∧ (fixedLiteralWords (k + 257)).2.toNat ≤ 8 := by
  have table : ∀ i : Fin 29,
      CodeFits fixedLiteralWords (i.val + 257) ∧ (fixedLiteralWords (i.val + 257)).2.toNat ≤ 8 := by
    unfold CodeFits
    decide +kernel
  exact table ⟨k, bound⟩

set_option maxHeartbeats 1000000 in
/-- Every used fixed distance code is a fitted five-bit word. -/
theorem fixed_distance_fits (k : Nat) (bound : k < 30) :
    CodeFits fixedDistanceWords k ∧ (fixedDistanceWords k).2.toNat = 5 := by
  have table : ∀ i : Fin 30,
      CodeFits fixedDistanceWords i.val ∧ (fixedDistanceWords i.val).2.toNat = 5 := by
    unfold CodeFits
    decide +kernel
  exact table ⟨k, bound⟩

/-- The fixed-table payload has at most 31 bits per legal symbol. The
length-258 code has no extra-bit write, despite its unused zero base. -/
theorem fixed_payload_symbol_length (dist lc : Nat) (distance : dist ≤ 32768) (length : lc < 256) :
    (payloadSymBits fixedLiteralWords fixedDistanceWords (dist, lc)).length ≤ 31 := by
  by_cases zero : dist = 0
  · simp only [payloadSymBits, zero, ite_true, codeBits, natBits_length]
    have fits := fixed_literal_fits lc length
    omega
  · obtain ⟨lk, le0, le5, lb0, lb, _lf⟩ := length_payload_checked_fields lc length
    obtain ⟨dk, de0, de13, db0, db, _df⟩ := distance_payload_fields (dist - 1) (by omega)
    have fitL := (fixed_length_fits (lcodeN lc) lk).2
    have fitD := (fixed_distance_fits (dcodeN (dist - 1)) dk).2
    simp only [payloadSymBits, zero, ite_false, codeBits, natBits_length, List.length_append, fitD]
    omega

/-- Read one represented static element at the exact source index. -/
theorem payload_index_get {α Ref : Type} [Space Heap Ref α] {h : Heap} {ref : Ref} {a : Array α}
    [Inhabited α] (get : Space.get h ref = some a) (i : Nat) (bound : i < a.size) :
    Ptr.index (.ref ref 0 : Ptr Ref) (i : Int) h = .ok (a[i]!, h) := by
  have run := Ptr.index_ok (off := 0) (i := i) get (by omega)
  unfold OkOn at run
  simpa only [Nat.zero_add, getElem!_pos a i bound] using run

/-- Small unsigned payload values retain their natural value after the
source's unsigned-to-signed conversion. -/
theorem payload_u2i (x : UInt32) (small : x.toNat < 2147483648) :
    (u2i x).toInt = x.toNat := by
  unfold u2i
  rw [ite_eq_right (by omega)]
  exact i32_ofInt_toInt (by omega) (by omega)


/-- Source suffix for the distance code and its extra bits. -/
def cbDistance (s : DeflateStatePtr) (dtree : CtDataPtr) (dist : UInt32) : M Unit := do
  let dist := dist - 1
  let code := (← d_code dist).toUInt32
  send_code s code.toNat dtree
  let extra ← Ptr.index (.ref .st_extra_dbits 0 : IPtr) code.toNat
  if extra != 0 then
    let dist := dist - (i2u (← Ptr.index (.ref .st_base_dist 0 : IPtr) code.toNat))
    send_bits s (u2i dist) extra

/-- Actual distance selection, code loads, unsigned subtraction and
extra-bit write retain the exact emitted prefix. The room premise is a
bit count to be derived by the fixed or dynamic block producer. -/
theorem cbDistance_run {h0 h : Heap} {id b : Nat} {d0 d : DeflateState} {buf0 buf : Array UInt8}
    {w : List Bool} (ht : EmitState id b h0 d0 buf0 w h d buf)
    (tree : PayloadTree) (dist : UInt32) (positive : 0 < dist.toNat) (bound : dist.toNat ≤ 32768)
    (index : dcodeN (dist.toNat - 1) < (tree.arr d0).size)
    (fits : CodeFits (tree.words d0) (dcodeN (dist.toNat - 1)))
    (total : Nat)
    (budget : w.length + (codeBits (tree.words d0) (dcodeN (dist.toNat - 1))).length +
      extra_dbits_tab[dcodeN (dist.toNat - 1)]!.toInt.toNat ≤ total)
    (room : 8 * d0.pending.toNat + d0.bi_valid.toInt.toNat + total ≤ 8 * buf0.size) :
    EWP (cbDistance (Sp id) (.ref (tree.ref id) 0) dist) h
      (fun _ H => ∃ D B, EmitState id b h0 d0 buf0
        (w ++ codeBits (tree.words d0) (dcodeN (dist.toNat - 1)) ++
          natBits (dist.toNat - 1 - base_dist_tab[dcodeN (dist.toNat - 1)]!.toInt.toNat)
            extra_dbits_tab[dcodeN (dist.toNat - 1)]!.toInt.toNat) H D B) := by
  have sub : (dist - 1).toNat = dist.toNat - 1 := by
    rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; change 1 ≤ dist.toNat; omega)]
    rfl
  obtain ⟨code, codeRun, codeValue, _codeBound⟩ := d_code_run ht.inv.base.static (dist - 1) (by rw [sub]; omega)
  rw [sub] at codeValue
  have codeNat : code.toUInt32.toNat = dcodeN (dist.toNat - 1) := by rw [UInt8.toNat_toUInt32, codeValue]
  obtain ⟨codeBound, extraLo, extraHi, baseLo, baseBound, fitted⟩ :=
    distance_payload_fields (dist.toNat - 1) (by omega)
  unfold cbDistance
  refine EWP.read codeRun ?_
  simp only [codeNat]
  have codeRoom : 8 * d.pending.toNat + d.bi_valid.toInt.toNat +
      (tree.words d0 (dcodeN (dist.toNat - 1))).2.toNat ≤ 8 * buf.size := by
    apply ht.room _ total
    · simpa only [codeBits, natBits_length] using Nat.le_trans (by omega :
        w.length + (codeBits (tree.words d0) (dcodeN (dist.toNat - 1))).length ≤
        w.length + (codeBits (tree.words d0) (dcodeN (dist.toNat - 1))).length +
          extra_dbits_tab[dcodeN (dist.toNat - 1)]!.toInt.toNat) budget
    · exact room
  refine EWP.bind (ht.payload_code tree _ index fits codeRoom) ?_
  rintro _ H ⟨D, B, trace⟩
  have extraGet : Space.get H IRef.st_extra_dbits = some extra_dbits_tab := by
    simp [Space.get, trace.inv.base.static.extra_dbits]
  have extraRead := payload_index_get extraGet (dcodeN (dist.toNat - 1)) (by change _ < 30; exact codeBound)
  refine EWP.read extraRead ?_
  by_cases zero : extra_dbits_tab[dcodeN (dist.toNat - 1)]! = 0
  · simp only [zero, bne_self_eq_false, Bool.false_eq_true, ite_false]
    exact EWP.pure ⟨D, B, by simpa [zero, natBits] using trace⟩
  · simp only [show (extra_dbits_tab[dcodeN (dist.toNat - 1)]! != 0) = true from bne_iff_ne.mpr zero, ite_true]
    have baseGet : Space.get H IRef.st_base_dist = some base_dist_tab := by
      simp [Space.get, trace.inv.base.static.base_dist]
    have baseRead := payload_index_get baseGet (dcodeN (dist.toNat - 1)) (by change _ < 30; exact codeBound)
    refine EWP.read baseRead ?_
    have baseSmall : base_dist_tab[dcodeN (dist.toNat - 1)]!.toInt.toNat < 4294967296 := by omega
    have baseUnsigned : (i2u base_dist_tab[dcodeN (dist.toNat - 1)]!).toNat =
        base_dist_tab[dcodeN (dist.toNat - 1)]!.toInt.toNat := by
      unfold i2u
      rw [Int.emod_eq_of_lt baseLo (by omega), UInt32.toNat_ofNat', Nat.mod_eq_of_lt baseSmall]
    have remaining : ((dist - 1) - i2u base_dist_tab[dcodeN (dist.toNat - 1)]!).toNat =
        dist.toNat - 1 - base_dist_tab[dcodeN (dist.toNat - 1)]!.toInt.toNat := by
      rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le, sub, baseUnsigned]; exact baseBound),
        sub, baseUnsigned]
    have scalar : (u2i ((dist - 1) - i2u base_dist_tab[dcodeN (dist.toNat - 1)]!)).toInt =
        (dist.toNat - 1 - base_dist_tab[dcodeN (dist.toNat - 1)]!.toInt.toNat : Nat) := by
      rw [payload_u2i _ (by rw [remaining]; omega), remaining]
    have emitted := trace.extra_bits (u2i ((dist - 1) - i2u base_dist_tab[dcodeN (dist.toNat - 1)]!))
      extra_dbits_tab[dcodeN (dist.toNat - 1)]!
      (dist.toNat - 1 - base_dist_tab[dcodeN (dist.toNat - 1)]!.toInt.toNat)
      extra_dbits_tab[dcodeN (dist.toNat - 1)]!.toInt.toNat
      (st_v16 _ _ scalar (by omega)) rfl extraLo (by omega) fitted
      (trace.room _ total (by simpa only [List.length_append] using budget) room)
    exact emitted


/-- Source suffix for the conditional length-extra write. -/
def cbLengthExtra (s : DeflateStatePtr) (lc : Int32) (code : UInt32) : M Unit := do
  let extra ← Ptr.index (.ref .st_extra_lbits 0 : IPtr) code.toNat
  if extra != 0 then
    let lc ← isub lc (← Ptr.index (.ref .st_base_length 0 : IPtr) code.toNat)
    send_bits s lc extra

/-- Actual length-extra execution respects the zero-extra branch, which
includes the special length-258 entry. The checked subtraction is used
only on the nonzero-extra source path. -/
theorem cbLengthExtra_run {h0 h : Heap} {id b : Nat} {d0 d : DeflateState} {buf0 buf : Array UInt8}
    {w : List Bool} (ht : EmitState id b h0 d0 buf0 w h d buf)
    (lc : Int32) (code : UInt32) (lo : 0 ≤ lc.toInt) (hi : lc.toInt < 256)
    (codeValue : code.toNat = lcodeN lc.toInt.toNat) (total : Nat)
    (budget : w.length + extra_lbits_tab[lcodeN lc.toInt.toNat]!.toInt.toNat ≤ total)
    (room : 8 * d0.pending.toNat + d0.bi_valid.toInt.toNat + total ≤ 8 * buf0.size) :
    EWP (cbLengthExtra (Sp id) lc code) h
      (fun _ H => ∃ D B, EmitState id b h0 d0 buf0
        (w ++ natBits (lc.toInt.toNat - base_length_tab[lcodeN lc.toInt.toNat]!.toInt.toNat)
          extra_lbits_tab[lcodeN lc.toInt.toNat]!.toInt.toNat) H D B) := by
  obtain ⟨codeBound, extraLo, extraHi, baseLo, baseBound, fitted⟩ :=
    length_payload_checked_fields lc.toInt.toNat (by omega)
  have extraGet : Space.get h IRef.st_extra_lbits = some extra_lbits_tab := by
    simp [Space.get, ht.inv.base.static.extra_lbits]
  have extraRead := payload_index_get extraGet (lcodeN lc.toInt.toNat) (by change _ < 29; exact codeBound)
  unfold cbLengthExtra
  rw [codeValue]
  refine EWP.read extraRead ?_
  by_cases zero : extra_lbits_tab[lcodeN lc.toInt.toNat]! = 0
  · simp only [zero, bne_self_eq_false, Bool.false_eq_true, ite_false]
    exact EWP.pure ⟨d, buf, by simpa [zero, natBits] using ht⟩
  · simp only [show (extra_lbits_tab[lcodeN lc.toInt.toNat]! != 0) = true from bne_iff_ne.mpr zero, ite_true]
    have baseGet : Space.get h IRef.st_base_length = some base_length_tab := by
      simp [Space.get, ht.inv.base.static.base_length]
    have baseRead := payload_index_get baseGet (lcodeN lc.toInt.toNat) (by change _ < 29; exact codeBound)
    refine EWP.read baseRead ?_
    have scalar : lc.toInt - base_length_tab[lcodeN lc.toInt.toNat]!.toInt =
        (lc.toInt.toNat - base_length_tab[lcodeN lc.toInt.toNat]!.toInt.toNat : Nat) := by omega
    rw [st_isub lc _ (by omega) (by omega)]
    refine EWP.read (rfl : (pure (Int32.ofInt (lc.toInt - base_length_tab[lcodeN lc.toInt.toNat]!.toInt)) : M Int32) h = _) ?_
    have value : (Int32.ofInt (lc.toInt - base_length_tab[lcodeN lc.toInt.toNat]!.toInt)).toInt =
        (lc.toInt.toNat - base_length_tab[lcodeN lc.toInt.toNat]!.toInt.toNat : Nat) := by
      rw [i32_ofInt_toInt (by omega) (by omega), scalar]
    have nonzero : extra_lbits_tab[lcodeN lc.toInt.toNat]!.toInt ≠ 0 := by
      intro equal
      exact zero (Int32.toInt_inj.mp equal)
    have emitted := ht.extra_bits (Int32.ofInt (lc.toInt - base_length_tab[lcodeN lc.toInt.toNat]!.toInt))
      extra_lbits_tab[lcodeN lc.toInt.toNat]!
      (lc.toInt.toNat - base_length_tab[lcodeN lc.toInt.toNat]!.toInt.toNat)
      extra_lbits_tab[lcodeN lc.toInt.toNat]!.toInt.toNat
      (st_v16 _ _ value (by omega)) rfl extraLo (by omega) (fitted nonzero)
      (ht.room _ total budget room)
    exact emitted

set_option maxRecDepth 10000 in
/-- The match source splits exactly after its length and distance writes.
This equality changes no translated statement or execution order. -/
theorem cbSymbol_match_source (s : DeflateStatePtr) (ltree dtree : CtDataPtr)
    (dist : UInt32) (lc : Int32) (nonzero : dist ≠ 0) :
    cbSymbol s ltree dtree dist lc = (do
      let code := (← Ptr.index (.ref .st_length_code 0 : BPtr) lc.toInt).toUInt32
      send_code s (code + i2u LITERALS + 1).toNat ltree
      cbLengthExtra s lc code
      cbDistance s dtree dist) := by
  unfold cbSymbol cbLengthExtra cbDistance
  simp only [show (dist == 0) = false from beq_eq_false_iff_ne.mpr nonzero,
    Bool.false_eq_true, ite_false, M_bind_assoc, M_pure_bind, merge_ite_bind]

/-- One complete actual match symbol, for either stored dynamic or fixed
code arrays. Only data facts about code words and exact total bit room
are premises. The actual callees are proved and composed on one heap. -/
theorem cbMatchSymbol_run {h0 h : Heap} {id b : Nat} {d0 d : DeflateState} {buf0 buf : Array UInt8}
    {w : List Bool} (ht : EmitState id b h0 d0 buf0 w h d buf)
    (lt dt : PayloadTree) (dist : UInt32) (lc : Int32)
    (distLo : 0 < dist.toNat) (distHi : dist.toNat ≤ 32768) (lcLo : 0 ≤ lc.toInt) (lcHi : lc.toInt < 256)
    (litIndex : lcodeN lc.toInt.toNat + 257 < (lt.arr d0).size)
    (distIndex : dcodeN (dist.toNat - 1) < (dt.arr d0).size)
    (litFits : CodeFits (lt.words d0) (lcodeN lc.toInt.toNat + 257))
    (distFits : CodeFits (dt.words d0) (dcodeN (dist.toNat - 1)))
    (total : Nat) (budget : w.length + (payloadSymBits (lt.words d0) (dt.words d0)
      (dist.toNat, lc.toInt.toNat)).length ≤ total)
    (room : 8 * d0.pending.toNat + d0.bi_valid.toInt.toNat + total ≤ 8 * buf0.size) :
    EWP (cbSymbol (Sp id) (.ref (lt.ref id) 0) (.ref (dt.ref id) 0) dist lc) h
      (fun _ H => ∃ D B, EmitState id b h0 d0 buf0
        (w ++ payloadSymBits (lt.words d0) (dt.words d0) (dist.toNat, lc.toInt.toNat)) H D B) := by
  have distNe : dist ≠ 0 := by intro zero; rw [zero] at distLo; contradiction
  have distNatNe : dist.toNat ≠ 0 := by omega
  have codeBound := (length_payload_checked_fields lc.toInt.toNat (by omega)).1
  have get : Space.get h BRef.st_length_code = some length_code_tab := by
    simp [Space.get, ht.inv.base.static.length_code]
  have read := payload_index_get get lc.toInt.toNat (by rw [length_code_tab_size]; omega)
  have lcValue : lc.toInt = (lc.toInt.toNat : Int) := by omega
  rw [← lcValue] at read
  have codeValue : length_code_tab[lc.toInt.toNat]!.toUInt32.toNat = lcodeN lc.toInt.toNat := by
    rw [UInt8.toNat_toUInt32]
    rfl
  have sendIndex : (length_code_tab[lc.toInt.toNat]!.toUInt32 + i2u LITERALS + 1).toNat =
      lcodeN lc.toInt.toNat + 257 := by
    rw [UInt32.toNat_add, UInt32.toNat_add, codeValue]
    change ((lcodeN lc.toInt.toNat + 256) % 4294967296 + 1) % 4294967296 = _
    omega
  have costs : w.length + (lt.words d0 (lcodeN lc.toInt.toNat + 257)).2.toNat +
      extra_lbits_tab[lcodeN lc.toInt.toNat]!.toInt.toNat +
      (dt.words d0 (dcodeN (dist.toNat - 1))).2.toNat +
      extra_dbits_tab[dcodeN (dist.toNat - 1)]!.toInt.toNat ≤ total := by
    simpa only [payloadSymBits, distNatNe, ite_false, List.length_append, codeBits, natBits_length,
      Nat.add_assoc] using budget
  rw [cbSymbol_match_source _ _ _ _ _ distNe]
  refine EWP.read read ?_
  simp only [sendIndex]
  have codeRoom := ht.room (lt.words d0 (lcodeN lc.toInt.toNat + 257)).2.toNat total (by omega) room
  refine EWP.bind (ht.payload_code lt _ litIndex litFits codeRoom) ?_
  rintro _ H ⟨D, B, trace⟩
  refine EWP.bind (cbLengthExtra_run trace lc _ lcLo lcHi codeValue total
    (by simpa only [List.length_append, codeBits, natBits_length] using (by omega :
      w.length + (lt.words d0 (lcodeN lc.toInt.toNat + 257)).2.toNat +
        extra_lbits_tab[lcodeN lc.toInt.toNat]!.toInt.toNat ≤ total)) room) ?_
  rintro _ H1 ⟨D1, B1, trace1⟩
  have distanceRun := cbDistance_run trace1 dt dist distLo distHi distIndex distFits total
    (by simpa only [List.length_append, codeBits, natBits_length] using costs) room
  simpa only [payloadSymBits, distNatNe, ite_false, List.append_assoc] using distanceRun

end Zlib.Trees.Proofs
