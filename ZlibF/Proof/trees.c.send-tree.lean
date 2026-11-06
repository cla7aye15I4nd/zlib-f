import ZlibF.Proof.«trees.c.scan-tree»
import ZlibF.Proof.«trees.c.emit-state»

/-! # trees.c: actual run-length tree-description output -/

namespace Zlib.Trees.Proofs
open C Zlib.Trees Out

/-- The actual direct-code repeat, including the final decrement. -/
def stRepeat (s : DeflateStatePtr) (cur count : Int32) : M Int32 :=
  cdoWhile
    (fun c => do send_code s cur.toInt (← pBltree s); pure c)
    (fun c => do let c ← isub c 1; pure (c != 0, c)) count

/-- One actual bit-length-code call, including its pointer read. -/
def stCode (s : DeflateStatePtr) (c : Int) : M Unit := do
  send_code s c (← pBltree s)

/-- Every output branch of the actual send_tree body, in source order. -/
def stSend (s : DeflateStatePtr) (cur prev count0 minc : Int32) : M Int32 := do
  let mut count := count0
  if count.toInt < minc.toInt then
    count ← stRepeat s cur count
  else if cur != 0 then
    if cur != prev then
      stCode s cur.toInt
      count ← isub count 1
    stCode s REP_3_6.toInt
    send_bits s (← isub count 3) 2
  else if count.toInt ≤ 10 then
    stCode s REPZ_3_10.toInt
    send_bits s (← isub count 3) 3
  else
    stCode s REPZ_11_138.toInt
    send_bits s (← isub count 11) 7
  pure count

/-- The actual body, including the source early continue and local tail. -/
def stBody (s : DeflateStatePtr) (tree : CtDataPtr) : SCLocals → M SCLocals :=
  fun (n, prevlen, nextlen, count, max_count, min_count, _) => do
    let curlen := nextlen
    let nextlen := u16i (← getDl tree (← iadd n 1).toInt)
    let count ← iadd count 1
    if count.toInt < max_count.toInt ∧ curlen == nextlen then
      return (n, prevlen, nextlen, count, max_count, min_count, 0)
    let _ ← stSend s curlen prevlen count min_count
    pure (scTail n curlen nextlen)

def stLoop (s : DeflateStatePtr) (tree : CtDataPtr) (mc : Int32) (r : SCLocals) : M SCLocals :=
  cfor (fun (n, _) => pure (decide (n.toInt ≤ mc.toInt)))
    (fun (n, rest) => do pure (← iadd n 1, rest)) (stBody s tree) r

/-- Complete source equality, independent of the execution proofs below. -/
theorem send_tree_eq (s : DeflateStatePtr) (tree : CtDataPtr) (mc : Int32) :
    send_tree s tree mc = (do
      let nextlen0 := u16i (← getDl tree 0)
      let (mx0, mn0) : Int32 × Int32 := if nextlen0 == 0 then (138, 3) else (7, 4)
      let _ ← stLoop s tree mc (0, -1, nextlen0, 0, mx0, mn0, 0)
      pure ()) := by
  unfold send_tree stLoop stBody stSend stRepeat stCode scTail
  simp only [M_bind_assoc, M_pure_bind, merge_ite_bind]

/-- Scalar checked arithmetic used by the actual output loops. -/
theorem st_isub (a b : Int32) (hlo : -2147483648 ≤ a.toInt - b.toInt)
    (hhi : a.toInt - b.toInt ≤ 2147483647) :
    isub a b = pure (Int32.ofInt (a.toInt - b.toInt)) := by
  simp only [isub, ck, hlo, hhi, and_self, ite_true]

theorem st_iadd (a b : Int32) (hlo : -2147483648 ≤ a.toInt + b.toInt)
    (hhi : a.toInt + b.toInt ≤ 2147483647) :
    iadd a b = pure (Int32.ofInt (a.toInt + b.toInt)) := by
  simp only [iadd, ck, hlo, hhi, and_self, ite_true]

theorem st_v16 (a : Int32) (A : Nat) (ha : a.toInt = A) (hA : A < 65536) : v16 a = A := by
  unfold v16 i2us
  rw [ha]
  have hm : ((A : Int) % 65536).toNat = A := by omega
  rw [UInt16.toNat_ofNat', hm]
  exact Nat.mod_eq_of_lt hA

theorem st_rep_succ {α : Type} (n : Nat) (xs : List α) :
    (List.replicate (n + 1) xs).flatten = (List.replicate n xs).flatten ++ xs := by
  rw [List.replicate_succ', List.flatten_append]
  simp

theorem st_rep_length {α : Type} (n : Nat) (xs : List α) :
    (List.replicate n xs).flatten.length = n * xs.length := by
  induction n with
  | zero => simp
  | succ n ih => rw [st_rep_succ, List.length_append, ih, Nat.succ_mul]

/-- The actual direct-repeat loop emits exactly count copies and executes
its final signed decrement. The loop measure proves termination. -/
theorem stRepeat_run {h0 h : Heap} {id b : Nat} {d0 d : DeflateState} {buf0 buf : Array UInt8}
    {w : List Bool} (ht : EmitState id b h0 d0 buf0 w h d buf)
    (cur count : Int32) (C K total : Nat) (hcur : cur.toInt = C) (hc : C < 19)
    (hk : count.toInt = K) (hK0 : 1 ≤ K) (hK : K ≤ 138)
    (hfit : CodeFits (blWords d0) C)
    (hp : w.length + K * (codeBits (blWords d0) C).length ≤ total)
    (hr : 8 * d0.pending.toNat + d0.bi_valid.toInt.toNat + total ≤ 8 * buf0.size) :
    EWP (stRepeat (some (.tab id)) cur count) h (fun c h' => c = 0 ∧ ∃ d' buf',
      EmitState id b h0 d0 buf0 (w ++ (List.replicate K (codeBits (blWords d0) C)).flatten) h' d' buf') := by
  let bits := codeBits (blWords d0) C
  change w.length + K * bits.length ≤ total at hp
  let P := fun k (c : Int32) H => k < K ∧ c.toInt = (k + 1 : Nat) ∧ ∃ D B,
    EmitState id b h0 d0 buf0 (w ++ (List.replicate (K - 1 - k) bits).flatten) H D B
  let Q := fun (c : Int32) H => c = 0 ∧ ∃ D B,
    EmitState id b h0 d0 buf0 (w ++ (List.replicate K bits).flatten) H D B
  have step : ∀ k c H, P (k + 1) c H → ∃ c1 H1 c2 H2,
      (do send_code (some (.tab id)) cur.toInt (← pBltree (some (.tab id))); pure c) H = .ok (c1, H1) ∧
      (do let c ← isub c1 1; pure (c != 0, c)) H1 = .ok ((true, c2), H2) ∧ P k c2 H2 := by
    rintro k c H ⟨hkl, hcv, D, B, htrace⟩
    have hs : (K - 1 - (k + 1)) + 1 ≤ K := by omega
    have hmul := Nat.mul_le_mul_right bits.length hs
    have hlen : (w ++ (List.replicate (K - 1 - (k + 1)) bits).flatten).length + bits.length ≤ total := by
      rw [List.length_append, st_rep_length]
      rw [Nat.succ_mul] at hmul
      omega
    have hroom := htrace.room bits.length total hlen hr
    have hbitslen : bits.length = (blWords d0 C).2.toNat := by simp [bits, codeBits, natBits]
    rw [hbitslen] at hroom
    obtain ⟨a, H1, hsnd, D1, B1, htrace1⟩ := htrace.bl_code C hc hfit hroom
    have ha : a = () := Subsingleton.elim _ _
    subst a
    have hbody : (do send_code (some (.tab id)) cur.toInt (← pBltree (some (.tab id))); pure c) H = .ok (c, H1) := by
      rw [hcur, ← M_bind_assoc, bind_app, hsnd]
      rfl
    let cv := Int32.ofInt (c.toInt - 1)
    have hsub : isub c 1 = pure cv := st_isub c 1 (by change -2147483648 ≤ c.toInt - 1; omega)
      (by change c.toInt - 1 ≤ 2147483647; omega)
    have hcv' : cv.toInt = (k + 1 : Nat) := by
      dsimp [cv]
      rw [ofInt_toInt' _ (by omega) (by omega)]
      omega
    have hne : (cv != 0) = true := by
      rw [bne_iff_ne, ne_eq, ← Int32.toInt_inj, hcv']
      change ¬ (k + 1 : Int) = 0
      omega
    refine ⟨c, H1, cv, H1, hbody, ?_, by omega, hcv', D1, B1, ?_⟩
    · rw [hsub]
      simp only [M_pure_bind, hne]
      rfl
    · have he : K - 1 - k = (K - 1 - (k + 1)) + 1 := by omega
      rw [he, st_rep_succ, ← List.append_assoc]
      exact htrace1
  have last : ∀ c H, P 0 c H → ∃ c1 H1 c2 H2,
      (do send_code (some (.tab id)) cur.toInt (← pBltree (some (.tab id))); pure c) H = .ok (c1, H1) ∧
      (do let c ← isub c1 1; pure (c != 0, c)) H1 = .ok ((false, c2), H2) ∧ Q c2 H2 := by
    rintro c H ⟨hkl, hcv, D, B, htrace⟩
    have hlen : (w ++ (List.replicate (K - 1 - 0) bits).flatten).length + bits.length ≤ total := by
      rw [List.length_append, st_rep_length]
      have hm : (K - 1) * bits.length + bits.length = K * bits.length := by
        rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hK0]
      simp only [Nat.sub_zero]
      omega
    have hroom := htrace.room bits.length total hlen hr
    have hbitslen : bits.length = (blWords d0 C).2.toNat := by simp [bits, codeBits, natBits]
    rw [hbitslen] at hroom
    obtain ⟨a, H1, hsnd, D1, B1, htrace1⟩ := htrace.bl_code C hc hfit hroom
    have ha : a = () := Subsingleton.elim _ _
    subst a
    refine ⟨c, H1, 0, H1, ?_, ?_, rfl, D1, B1, ?_⟩
    · rw [hcur, ← M_bind_assoc, bind_app, hsnd]
      rfl
    · rw [st_isub c 1 (by change -2147483648 ≤ c.toInt - 1; omega)
        (by change c.toInt - 1 ≤ 2147483647; omega)]
      have he : Int32.ofInt (c.toInt - (1 : Int32).toInt) = 0 := by
        rw [hcv]
        rfl
      rw [he]
      rfl
    · have he : K = (K - 1 - 0) + 1 := by omega
      rw [he, st_rep_succ, ← List.append_assoc]
      exact htrace1
  have hstart : P (K - 1) count h := by
    refine ⟨by omega, by omega, d, buf, ?_⟩
    simpa using ht
  obtain ⟨c, H, hrun, hQ⟩ := _root_.C.cdoWhile_run P Q step last hstart (by unfold fuel; omega)
  exact ⟨c, H, hrun, hQ⟩

/-- A repetition symbol followed by its checked extra-bit subtraction. -/
theorem stCode_extra {h0 h : Heap} {id b : Nat} {d0 d : DeflateState} {buf0 buf : Array UInt8}
    {w : List Bool} (ht : EmitState id b h0 d0 buf0 w h d buf)
    (code count off len : Int32) (K V L total : Nat)
    (hcode : code.toInt = K) (hK : K < 19)
    (hV : count.toInt - off.toInt = V) (hV16 : V < 65536)
    (hL : len.toInt = L) (hL15 : L ≤ 15) (hfit : V < 2 ^ L)
    (hc : CodeFits (blWords d0) K)
    (hp : w.length + (codeBits (blWords d0) K).length + L ≤ total)
    (hr : 8 * d0.pending.toNat + d0.bi_valid.toInt.toNat + total ≤ 8 * buf0.size) :
    EWP (do stCode (some (.tab id)) code.toInt
            send_bits (some (.tab id)) (← isub count off) len) h
      (fun _ h' => ∃ d' buf', EmitState id b h0 d0 buf0
        (w ++ codeBits (blWords d0) K ++ natBits V L) h' d' buf') := by
  have hbl : (codeBits (blWords d0) K).length = (blWords d0 K).2.toNat := by simp [codeBits, natBits]
  have hroom := ht.room (blWords d0 K).2.toNat total (by omega) hr
  unfold stCode
  rw [hcode]
  refine EWP.bind (ht.bl_code K hK hc hroom) ?_
  rintro _ H ⟨D, B, hs⟩
  rw [st_isub count off (by omega) (by omega)]
  refine EWP.bind (EWP.pure (Q := fun v H' => v = Int32.ofInt (count.toInt - off.toInt) ∧ H' = H) ⟨rfl, rfl⟩) ?_
  rintro _ _ ⟨rfl, rfl⟩
  have hv : (Int32.ofInt (count.toInt - off.toInt)).toInt = V := by
    rw [ofInt_toInt' _ (by omega) (by omega), hV]
  exact hs.extra_bits _ len V L (st_v16 _ V hv hV16) (by rw [hL]; simp) (by omega) (by omega) hfit
    (hs.room L total (by simpa only [List.length_append] using hp) hr)

theorem Out.EWP.keep {α : Type} {h : Heap} {m : M Unit} {Q : Heap → Prop}
    (hm : EWP m h (fun _ H => Q H)) (a : α) :
    EWP (m >>= fun _ => (Pure.pure a : M α)) h (fun _ H => Q H) :=
  EWP.bind hm (by intro _ H hq; exact EWP.pure hq)

/-- Exact output for a finished run in the actual send_tree body. The
code premises describe only entries used by this run. -/
theorem stSend_run {h0 h : Heap} {id b : Nat} {d0 d : DeflateState} {buf0 buf : Array UInt8}
    {w : List Bool} (ht : EmitState id b h0 d0 buf0 w h d buf)
    (cur prev count minc : Int32) (s : RunSt) (total : Nat)
    (hc : cur.toInt = s.next) (hpv : prev.toInt = s.prev)
    (hcnt : count.toInt = (s.cnt + 1 : Nat)) (hmn : minc.toInt = s.mn)
    (hi : RunInv s) (hcur : s.next ≤ 15)
    (hcodes : ∀ k < 19, 0 < runFreq (some (s.next, s.prev, s.cnt + 1, s.mn)) k →
      CodeFits (blWords d0) k)
    (hp : w.length + (runBits (blWords d0) (some (s.next, s.prev, s.cnt + 1, s.mn))).length ≤ total)
    (hr : 8 * d0.pending.toNat + d0.bi_valid.toInt.toNat + total ≤ 8 * buf0.size) :
    EWP (stSend (some (.tab id)) cur prev count minc) h (fun _ h' => ∃ d' buf',
      EmitState id b h0 d0 buf0 (w ++ runBits (blWords d0) (some (s.next, s.prev, s.cnt + 1, s.mn))) h' d' buf') := by
  have hmx : s.mx ≤ 138 := by
    by_cases hz : s.next = 0
    · rw [(hi.2.1 hz).1]
      omega
    · rcases hi.2.2.1 hz with ⟨h, rest⟩ | ⟨h, rest⟩ <;> omega
  have hmn3 : 3 ≤ s.mn := by
    by_cases hz : s.next = 0
    · rw [(hi.2.1 hz).2]
      omega
    · rcases hi.2.2.1 hz with ⟨h, h', rest⟩ | ⟨h, h', rest⟩ <;> omega
  have hsmall : count.toInt < minc.toInt ↔ s.cnt + 1 < s.mn := by omega
  have hzero : ((cur != 0) = true) ↔ s.next ≠ 0 := by
    rw [bne_iff_ne, ne_eq, ← Int32.toInt_inj, hc]
    change ¬ (s.next : Int) = 0 ↔ s.next ≠ 0
    omega
  have hprev : ((cur != prev) = true) ↔ (s.next : Int) ≠ s.prev := by
    rw [bne_iff_ne, ne_eq, ← Int32.toInt_inj, hc, hpv]
  unfold stSend
  simp only [hsmall, hzero, hprev]
  by_cases hs : s.cnt + 1 < s.mn
  · simp only [hs, ite_true]
    have hfit : CodeFits (blWords d0) s.next := hcodes s.next (by omega) (by
      simp only [runFreq, ite_eq_left hs, ite_true]
      omega)
    have hp' : w.length + (s.cnt + 1) * (codeBits (blWords d0) s.next).length ≤ total := by
      simpa only [runBits, ite_eq_left hs, st_rep_length] using hp
    refine EWP.bind (stRepeat_run ht cur count s.next (s.cnt + 1) total hc (by omega) hcnt
      (by omega) (by have := hi.1; omega) hfit hp' hr) ?_
    rintro c H ⟨hc0, D, B, htrace⟩
    refine EWP.pure ⟨D, B, ?_⟩
    simpa only [runBits, ite_eq_left hs] using htrace
  · simp only [hs, ite_false]
    by_cases hz : s.next ≠ 0
    · simp only [ite_eq_left hz]
      have h16 := hcodes 16 (by omega) (by
        simp only [runFreq, ite_eq_right hs, ite_eq_left hz, ite_true]
        omega)
      by_cases hneq : (s.next : Int) ≠ s.prev
      · simp only [ite_eq_left hneq]
        have h7 : s.mx = 7 ∧ s.mn = 4 := by
          rcases hi.2.2.1 hz with h | h
          · exact False.elim (hneq h.2.2)
          · exact ⟨h.1, h.2.1⟩
        have hf := hcodes s.next (by omega) (by
          simp only [runFreq, ite_eq_right hs, ite_eq_left hz, and_true, ite_eq_left hneq]
          omega)
        simp only [runBits, ite_eq_right hs, ite_eq_left hz, ite_eq_left hneq,
          List.length_append, codeBits, natBits, List.length_map, List.length_range] at hp
        have hrC := ht.room (blWords d0 s.next).2.toNat total (by omega) hr
        rw [hc]
        refine EWP.bind (ht.bl_code s.next (by omega) hf hrC) ?_
        rintro _ H ⟨D, B, ht1⟩
        rw [st_isub count 1 (by change -2147483648 ≤ count.toInt - 1; omega)
          (by change count.toInt - 1 ≤ 2147483647; have := hi.1; omega), M_pure_bind]
        let cv := Int32.ofInt (count.toInt - (1 : Int32).toInt)
        have hcv : cv.toInt = s.cnt := by
          dsimp [cv]
          rw [ofInt_toInt' _ (by have := hi.1; omega) (by have := hi.1; omega)]
          change count.toInt - 1 = (s.cnt : Int)
          omega
        have he := stCode_extra ht1 REP_3_6 cv 3 2 16 (s.cnt + 1 - 1 - 3) 2 total
          rfl (by omega) (by change cv.toInt - 3 = _; rw [hcv]; omega)
          (by have := hi.1; omega) rfl (by omega) (by change _ < 4; have := hi.1; omega) h16
          (by simp only [List.length_append, codeBits, natBits, List.length_map, List.length_range]; omega) hr
        apply EWP.mono (by simpa only [M_bind_assoc] using he.keep cv)
        rintro _ H' ⟨D', B', ht2⟩
        refine ⟨D', B', ?_⟩
        simpa only [runBits, ite_eq_right hs, ite_eq_left hz, ite_eq_left hneq, List.append_assoc] using ht2
      · simp only [ite_eq_right hneq]
        have heq : (s.next : Int) = s.prev := by omega
        have h6 : s.mx = 6 ∧ s.mn = 3 := by
          rcases hi.2.2.1 hz with h | h
          · exact ⟨h.1, h.2.1⟩
          · exact False.elim (h.2.2 heq)
        have hlen : w.length + (codeBits (blWords d0) 16).length + 2 ≤ total := by
          simpa only [runBits, ite_eq_right hs, ite_eq_left hz, ite_eq_right hneq,
            List.length_append, natBits, List.length_map, List.length_range, Nat.add_assoc] using hp
        have he := stCode_extra ht REP_3_6 count 3 2 16 (s.cnt + 1 - 3) 2 total rfl (by omega)
          (by change count.toInt - 3 = _; omega) (by have := hi.1; omega) rfl (by omega)
          (by change _ < 4; have := hi.1; omega) h16 hlen hr
        apply EWP.mono (by simpa only [M_bind_assoc] using he.keep count)
        rintro _ H' ⟨D', B', ht2⟩
        refine ⟨D', B', ?_⟩
        simpa only [runBits, ite_eq_right hs, ite_eq_left hz, ite_eq_right hneq, List.append_assoc] using ht2
    · simp only [hz, ite_false]
      have hcount0 : 3 ≤ s.cnt + 1 := by omega
      have hcond : count.toInt ≤ 10 ↔ s.cnt + 1 ≤ 10 := by omega
      simp only [hcond]
      by_cases h10 : s.cnt + 1 ≤ 10
      · simp only [h10, ite_true]
        have hf := hcodes 17 (by omega) (by simp only [runFreq, ite_eq_right hs, ite_eq_right hz, ite_eq_left h10, ite_true]; omega)
        have hlen : w.length + (codeBits (blWords d0) 17).length + 3 ≤ total := by
          simpa only [runBits, ite_eq_right hs, ite_eq_right hz, ite_eq_left h10,
            List.length_append, natBits, List.length_map, List.length_range, Nat.add_assoc] using hp
        have he := stCode_extra ht REPZ_3_10 count 3 3 17 (s.cnt + 1 - 3) 3 total rfl (by omega)
          (by change count.toInt - 3 = _; omega) (by omega) rfl (by omega) (by change _ < 8; omega) hf hlen hr
        apply EWP.mono (by simpa only [M_bind_assoc] using he.keep count)
        rintro _ H' ⟨D', B', ht2⟩
        refine ⟨D', B', ?_⟩
        simpa only [runBits, ite_eq_right hs, ite_eq_right hz, ite_eq_left h10, List.append_assoc] using ht2
      · simp only [h10, ite_false]
        have hf := hcodes 18 (by omega) (by simp only [runFreq, ite_eq_right hs, ite_eq_right hz, ite_eq_right h10, ite_true]; omega)
        have hlen : w.length + (codeBits (blWords d0) 18).length + 7 ≤ total := by
          simpa only [runBits, ite_eq_right hs, ite_eq_right hz, ite_eq_right h10,
            List.length_append, natBits, List.length_map, List.length_range, Nat.add_assoc] using hp
        have he := stCode_extra ht REPZ_11_138 count 11 7 18 (s.cnt + 1 - 11) 7 total rfl (by omega)
          (by change count.toInt - 11 = _; omega) (by have := hi.1; omega) rfl (by omega)
          (by change _ < 128; have := hi.1; omega) hf hlen hr
        apply EWP.mono (by simpa only [M_bind_assoc] using he.keep count)
        rintro _ H' ⟨D', B', ht2⟩
        refine ⟨D', B', ?_⟩
        simpa only [runBits, ite_eq_right hs, ite_eq_right hz, ite_eq_right h10, List.append_assoc] using ht2

/-- Every dynamic-tree array is outside the bit-output write footprint. -/
theorem emitState_tk_arr {h0 h : Heap} {id b : Nat} {d0 d : DeflateState} {buf0 buf : Array UInt8}
    {w : List Bool} (ht : EmitState id b h0 d0 buf0 w h d buf) (tk : TK) : tk.arr d = tk.arr d0 := by
  cases tk
  · exact ht.tree_arrays.1
  · exact ht.tree_arrays.2.1
  · exact ht.tree_arrays.2.2

/-- One actual body preserves the local/model correspondence and emits
exactly this iteration's model bits, including an empty early continue. -/
theorem stBody_run {h0 h : Heap} {id b : Nat} {d0 d : DeflateState} {buf0 buf : Array UInt8}
    {w : List Bool} (ht : EmitState id b h0 d0 buf0 w h d buf)
    (tk : TK) (L : Nat → Nat) (n : Nat) (s : RunSt) (r : SCLocals) (total : Nat)
    (hcorr : SCCorr r n s) (hi : RunInv s) (hn : n ≤ 285)
    (hread : n + 1 < (tk.arr d0).size) (hl : (tk.arr d0)[n + 1]!.dl.toNat = L (n + 1))
    (hcur : s.next ≤ 15)
    (hcodes : ∀ k < 19, 0 < runFreq (runStep L n s).2 k → CodeFits (blWords d0) k)
    (hp : w.length + (runBits (blWords d0) (runStep L n s).2).length ≤ total)
    (hr : 8 * d0.pending.toNat + d0.bi_valid.toInt.toNat + total ≤ 8 * buf0.size) :
    EWP (stBody (some (.tab id)) (.ref (tk.ref id) 0) r) h (fun r' H =>
      SCCorr r' n (runStep L n s).1 ∧ ∃ D B,
        EmitState id b h0 d0 buf0 (w ++ runBits (blWords d0) (runStep L n s).2) H D B) := by
  rcases r with ⟨ni, pi, ci, ki, mi, mni, unused⟩
  obtain ⟨hnc, hpc, hcc, hkc, hmc, hmnc⟩ := hcorr
  dsimp only at hnc hpc hcc hkc hmc hmnc
  have hone : (1 : Int32).toInt = 1 := rfl
  have hmx : s.mx ≤ 138 := by
    by_cases hz : s.next = 0
    · rw [(hi.2.1 hz).1]
      omega
    · rcases hi.2.2.1 hz with ⟨hh, rest⟩ | ⟨hh, rest⟩ <;> omega
  have hn1 : (Int32.ofInt (ni.toInt + (1 : Int32).toInt)).toInt = (n + 1 : Nat) := by
    rw [ofInt_toInt' _ (by omega) (by omega)]
    change ni.toInt + 1 = _
    omega
  have htarr := emitState_tk_arr ht tk
  have hg := tk_get (h0 := h) (id := id) (d := d) tk
  rw [Zlib.Trees.Proofs.setD_self ht.inv.base.dstate] at hg
  have hidx : (Int32.ofInt (ni.toInt + (1 : Int32).toInt)).toInt = ((n + 1 : Nat) : Int) := hn1
  have hload : getDl (.ref (tk.ref id) 0) (Int32.ofInt (ni.toInt + (1 : Int32).toInt)).toInt h =
      .ok ((tk.arr d0)[n + 1]!.dl, h) := by
    rw [hidx]
    have hs := getDl_gen hg (by rw [htarr]; exact hread)
    simpa only [getElem!_pos, htarr, hread] using hs
  have hk1 : (Int32.ofInt (ki.toInt + (1 : Int32).toInt)).toInt = (s.cnt + 1 : Nat) := by
    rw [ofInt_toInt' _ (by have := hi.1; omega) (by have := hi.1; omega)]
    change ki.toInt + 1 = _
    omega
  have hnx : (u16i (tk.arr d0)[n + 1]!.dl).toInt = L (n + 1) := by rw [u16i_toInt, hl]
  have hsame : ((ci == u16i (tk.arr d0)[n + 1]!.dl) = true) ↔ s.next = L (n + 1) := by
    rw [beq_iff_eq, ← Int32.toInt_inj, hcc, hnx, Int.natCast_inj]
  have hcond : (Int32.ofInt (ki.toInt + (1 : Int32).toInt)).toInt < mi.toInt ∧
      (ci == u16i (tk.arr d0)[n + 1]!.dl) = true ↔ s.cnt + 1 < s.mx ∧ s.next = L (n + 1) := by
    rw [hk1, hmc, hsame]
    omega
  unfold stBody
  dsimp only
  rw [st_iadd ni 1 (by change -2147483648 ≤ ni.toInt + 1; omega)
    (by change ni.toInt + 1 ≤ 2147483647; omega), M_pure_bind]
  refine EWP.read hload ?_
  rw [st_iadd ki 1 (by change -2147483648 ≤ ki.toInt + 1; omega)
    (by change ki.toInt + 1 ≤ 2147483647; have := hi.1; omega), M_pure_bind]
  simp only [hcond]
  by_cases ha : s.cnt + 1 < s.mx ∧ s.next = L (n + 1)
  · simp only [ite_eq_left ha]
    refine EWP.pure ⟨?_, d, buf, ?_⟩
    · simp only [runStep, ite_eq_left ha, SCCorr]
      exact ⟨hnc, hpc, hnx, hk1, hmc, hmnc⟩
    · simpa only [runStep, ite_eq_left ha, runBits, List.append_nil] using ht
  · simp only [ite_eq_right ha]
    have hcodes' : ∀ k < 19, 0 < runFreq (some (s.next, s.prev, s.cnt + 1, s.mn)) k → CodeFits (blWords d0) k := by
      simpa only [runStep, ite_eq_right ha] using hcodes
    have hp' : w.length + (runBits (blWords d0) (some (s.next, s.prev, s.cnt + 1, s.mn))).length ≤ total := by
      simpa only [runStep, ite_eq_right ha] using hp
    refine EWP.bind (stSend_run ht ci pi _ mni s total hcc hpc hk1 hmnc hi hcur hcodes' hp' hr) ?_
    rintro _ H ⟨D, B, htrace⟩
    refine EWP.pure ⟨?_, D, B, ?_⟩
    · simp only [runStep, ite_eq_right ha]
      exact scTail_corr _ _ _ _ _ _ hnc hcc hnx
    · simpa only [runStep, ite_eq_right ha] using htrace

theorem st_scanFreq_mono (L : Nat → Nat) (k : Nat) {i j : Nat} (hij : i ≤ j) :
    scanFreqUpTo L i k ≤ scanFreqUpTo L j k := by
  induction j with
  | zero => have he : i = 0 := by omega
            subst he
            exact Nat.le_refl _
  | succ j ih =>
    by_cases he : i = j + 1
    · subst he
      exact Nat.le_refl _
    · have hb := ih (by omega)
      simp only [scanFreqUpTo]
      omega

theorem st_runFreq_le (L : Nat → Nat) (n m k : Nat) (hn : n < m) :
    runFreq (runStep L n (runAt L n)).2 k ≤ scanFreqUpTo L m k := by
  have hm := st_scanFreq_mono L k (i := n + 1) (j := m) (by omega)
  simp only [scanFreqUpTo] at hm
  omega

/-- A whole actual iteration, including n++, preserves the emitted prefix.
Required code entries derive from the complete source scan's used symbols. -/
theorem stIteration_run {h0 h : Heap} {id b : Nat} {d0 d : DeflateState} {buf0 buf : Array UInt8}
    (tk : TK) (L : Nat → Nat) (n M : Nat) (r : SCLocals)
    (ht : EmitState id b h0 d0 buf0 (treeBitsUpTo (blWords d0) L n) h d buf)
    (hn : n ≤ M) (hM : M ≤ 285) (hT : M + 1 < (tk.arr d0).size)
    (hread : ∀ i ≤ M + 1, (tk.arr d0)[i]!.dl.toNat = L i)
    (h16 : ∀ i, L i < 65536) (h15 : ∀ i ≤ M, L i ≤ 15)
    (hcodes : ∀ k < 19, 0 < scanFreqUpTo L (M + 1) k → CodeFits (blWords d0) k)
    (hr : 8 * d0.pending.toNat + d0.bi_valid.toInt.toNat + (sendTreeBits (blWords d0) L M).length ≤ 8 * buf0.size)
    (hcorr : SCCorr r n (runAt L n)) :
    EWP (do let (ni, rest) ← stBody (some (.tab id)) (.ref (tk.ref id) 0) r
            pure (← iadd ni 1, rest)) h (fun r' H =>
      SCCorr r' (n + 1) (runAt L (n + 1)) ∧ ∃ D B,
        EmitState id b h0 d0 buf0 (treeBitsUpTo (blWords d0) L (n + 1)) H D B) := by
  have hcur : (runAt L n).next ≤ 15 := by rw [runAt_next]; exact h15 n hn
  have hfit : ∀ k < 19, 0 < runFreq (runStep L n (runAt L n)).2 k → CodeFits (blWords d0) k := by
    intro k hk hused
    have hb := st_runFreq_le L n (M + 1) k (by omega)
    exact hcodes k hk (by omega)
  have hprefix : (treeBitsUpTo (blWords d0) L n).length +
      (runBits (blWords d0) (runStep L n (runAt L n)).2).length ≤ (sendTreeBits (blWords d0) L M).length := by
    have hm := treeBitsUpTo_mono (blWords d0) L (i := n + 1) (j := M + 1) (by omega)
    simpa only [sendTreeBits, treeBitsUpTo, List.length_append] using hm
  refine EWP.bind (stBody_run ht tk L n (runAt L n) r _ hcorr (runInv_runAt L h16 n) (by omega)
    (by omega) (hread (n + 1) (by omega)) hcur hfit hprefix hr) ?_
  rintro ⟨ni, rest⟩ H ⟨hc, D, B, htrace⟩
  have hni := hc.1
  dsimp only at hni ⊢
  have hone : (1 : Int32).toInt = 1 := rfl
  rw [st_iadd ni 1 (by omega) (by omega), M_pure_bind]
  refine EWP.pure ⟨?_, D, B, ?_⟩
  · exact ⟨by rw [ofInt_toInt' _ (by omega) (by omega) ]; omega, hc.2⟩
  · simpa only [treeBitsUpTo] using htrace

/-- The complete actual for loop terminates and emits its whole model
prefix. The source arrays and code words are retained at every iteration. -/
theorem stLoop_run {h0 h : Heap} {id b : Nat} {d0 d : DeflateState} {buf0 buf : Array UInt8}
    (tk : TK) (L : Nat → Nat) (M : Nat) (mc : Int32) (r : SCLocals)
    (ht : EmitState id b h0 d0 buf0 [] h d buf)
    (hmc : mc.toInt = M) (hM : M ≤ 285) (hT : M + 1 < (tk.arr d0).size)
    (hread : ∀ i ≤ M + 1, (tk.arr d0)[i]!.dl.toNat = L i)
    (h16 : ∀ i, L i < 65536) (h15 : ∀ i ≤ M, L i ≤ 15)
    (hcodes : ∀ k < 19, 0 < scanFreqUpTo L (M + 1) k → CodeFits (blWords d0) k)
    (hr : 8 * d0.pending.toNat + d0.bi_valid.toInt.toNat + (sendTreeBits (blWords d0) L M).length ≤ 8 * buf0.size)
    (hcorr : SCCorr r 0 (runAt L 0)) :
    EWP (stLoop (some (.tab id)) (.ref (tk.ref id) 0) mc r) h (fun _ H => ∃ D B,
      EmitState id b h0 d0 buf0 (sendTreeBits (blWords d0) L M) H D B) := by
  let cond := fun r : SCLocals => do
    pure (← (pure (decide (r.1.toInt ≤ mc.toInt)) : _root_.C.M Bool), r)
  let body := fun r : SCLocals => do
    let (ni, rest) ← stBody (some (.tab id)) (.ref (tk.ref id) 0) r
    pure (← iadd ni 1, rest)
  let P := fun k r H => k ≤ M + 1 ∧ SCCorr r (M + 1 - k) (runAt L (M + 1 - k)) ∧ ∃ D B,
    EmitState id b h0 d0 buf0 (treeBitsUpTo (blWords d0) L (M + 1 - k)) H D B
  let Q := fun (_ : SCLocals) H => ∃ D B, EmitState id b h0 d0 buf0 (sendTreeBits (blWords d0) L M) H D B
  have step : ∀ k r H, P (k + 1) r H → ∃ r1 H1 r2 H2,
      cond r H = .ok ((true, r1), H1) ∧ body r1 H1 = .ok (r2, H2) ∧ P k r2 H2 := by
    rintro k rr H ⟨hk, hc, D, B, htrace⟩
    have hle : rr.1.toInt ≤ mc.toInt := by rw [hc.1, hmc]; omega
    obtain ⟨r2, H2, hbody, hcorr2, D2, B2, htrace2⟩ :=
      stIteration_run tk L (M + 1 - (k + 1)) M rr htrace (by omega) hM hT hread h16 h15 hcodes hr hc
    refine ⟨rr, H, r2, H2, ?_, hbody, by omega, ?_, D2, B2, ?_⟩
    · simp only [cond, bind_app, pure_app, hle, decide_true]
    · have he : M + 1 - k = M + 1 - (k + 1) + 1 := by omega
      rw [he]
      exact hcorr2
    · have he : M + 1 - k = M + 1 - (k + 1) + 1 := by omega
      rw [he]
      exact htrace2
  have stop : ∀ r H, P 0 r H → ∃ r1 H1, cond r H = .ok ((false, r1), H1) ∧ Q r1 H1 := by
    rintro rr H ⟨hk, hc, D, B, htrace⟩
    have hno : ¬ rr.1.toInt ≤ mc.toInt := by rw [hc.1, hmc]; omega
    refine ⟨rr, H, ?_, D, B, ?_⟩
    · simp only [cond, bind_app, pure_app, hno, decide_false]
    · simpa only [Nat.sub_zero, sendTreeBits] using htrace
  have hstart : P (M + 1) r h := by
    refine ⟨Nat.le_refl _, ?_, d, buf, ?_⟩
    · simpa only [Nat.sub_self] using hcorr
    · simpa only [Nat.sub_self, treeBitsUpTo] using ht
  obtain ⟨rf, Hf, hrun, hQ⟩ := _root_.C.cwhile_run P Q step stop hstart (by unfold fuel; omega)
  exact ⟨rf, Hf, hrun, hQ⟩

/-- `local void send_tree(deflate_state *s, ct_data *tree, int max_code)`.
The internal alphabet maximum is at most 285. Actual lengths are at most
15; only entries with positive complete-scan frequency require fitted code
data. Exact total bit room remains an internal caller obligation. -/
theorem send_tree_emit {h : Heap} {id b : Nat} {d : DeflateState} {buf : Array UInt8}
    (hI : TreesInvAt h id d b buf) (tk : TK) (L : Nat → Nat) (M : Nat) (mc : Int32)
    (hmc : mc.toInt = M) (hM : M ≤ 285) (hT : M + 1 < (tk.arr d).size)
    (hread : ∀ i ≤ M + 1, (tk.arr d)[i]!.dl.toNat = L i)
    (h16 : ∀ i, L i < 65536) (h15 : ∀ i ≤ M, L i ≤ 15)
    (hcodes : ∀ k < 19, 0 < scanFreqUpTo L (M + 1) k → CodeFits (blWords d) k)
    (hr : 8 * d.pending.toNat + d.bi_valid.toInt.toNat + (sendTreeBits (blWords d) L M).length ≤ 8 * buf.size) :
    Emit id b (send_tree (some (.tab id)) (.ref (tk.ref id) 0) mc) h d buf
      (sendTreeBits (blWords d) L M) (d.bi_valid.toInt.toNat + (sendTreeBits (blWords d) L M).length) := by
  have hget := tk_get (h0 := h) (id := id) (d := d) tk
  rw [Zlib.Trees.Proofs.setD_self hI.base.dstate] at hget
  have hread0 := getDl_gen hget (i := 0) (by omega)
  have hload : getDl (.ref (tk.ref id) 0) 0 h = .ok ((tk.arr d)[0]!.dl, h) := by
    simpa only [getElem!_pos, show 0 < (tk.arr d).size by omega, Int.natCast_zero] using hread0
  let nx := u16i (tk.arr d)[0]!.dl
  have hnx : nx.toInt = L 0 := by rw [u16i_toInt, hread 0 (by omega)]
  have hz : ((nx == 0) = true) ↔ L 0 = 0 := by
    rw [beq_iff_eq, ← Int32.toInt_inj, hnx]
    change (L 0 : Int) = 0 ↔ L 0 = 0
    omega
  let mxmn : Int32 × Int32 := if nx == 0 then (138, 3) else (7, 4)
  have hc : SCCorr (0, -1, nx, 0, mxmn.1, mxmn.2, 0) 0 (runAt L 0) := by
    dsimp only [mxmn]
    simp only [hz, runAt, runInit]
    by_cases h0 : L 0 = 0
    · simp only [ite_eq_left h0]
      exact ⟨rfl, rfl, hnx, rfl, rfl, rfl⟩
    · simp only [ite_eq_right h0]
      exact ⟨rfl, rfl, hnx, rfl, rfl, rfl⟩
  obtain ⟨rf, H, hloop, D, B, ht⟩ := stLoop_run tk L M mc (0, -1, nx, 0, mxmn.1, mxmn.2, 0)
    (EmitState.start hI) hmc hM hT hread h16 h15 hcodes hr hc
  apply ht.emit
  rw [send_tree_eq, bind_app, hload]
  change (stLoop (some (.tab id)) (.ref (tk.ref id) 0) mc
    (0, -1, nx, 0, mxmn.1, mxmn.2, 0) >>= fun _ => pure ()) h = .ok ((), H)
  rw [bind_app, hloop]
  rfl

end Zlib.Trees.Proofs
