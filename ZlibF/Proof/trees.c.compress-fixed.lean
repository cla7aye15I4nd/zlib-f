import ZlibF.Proof.«trees.c.compress-match»

/-! # Complete fixed-table payload execution on literals and matches

The shared pending/symbol allocation has four bytes per symbol slot.
At most 31 bits per fixed-table symbol derive both the unread-byte
boundary and every output-room check. No room contract is assumed.
-/

namespace Zlib.Trees.Proofs
open C Zlib.Trees Out
set_option autoImplicit false

def fixedPayloadPrefix (buf : Array UInt8) (offset n : Nat) : List Bool :=
  payloadPrefixBits fixedLiteralWords fixedDistanceWords buf offset n

theorem fixedPayloadPrefix_succ (buf : Array UInt8) (offset n : Nat) :
    fixedPayloadPrefix buf offset (n + 1) = fixedPayloadPrefix buf offset n ++
      payloadSymBits fixedLiteralWords fixedDistanceWords (payloadSymAt buf offset n) :=
  payloadPrefixBits_succ _ _ _ _ _

/-- Original buffered symbols bound every completed fixed-code prefix. -/
theorem fixedPayloadPrefix_length (buf : Array UInt8) (offset n : Nat)
    (legal : ∀ i, i < n → (payloadSymAt buf offset i).1 ≤ 32768) :
    (fixedPayloadPrefix buf offset n).length ≤ 31 * n := by
  induction n with
  | zero => simp [fixedPayloadPrefix, payloadPrefixBits]
  | succ n ih =>
    have before := ih (fun i hi => legal i (by omega))
    have symbol := fixed_payload_symbol_length (payloadSymAt buf offset n).1 (payloadSymAt buf offset n).2
      (legal n (by omega)) (UInt8.toNat_lt _)
    change (payloadSymBits fixedLiteralWords fixedDistanceWords (payloadSymAt buf offset n)).length ≤ 31 at symbol
    rw [fixedPayloadPrefix_succ, List.length_append]
    omega

/-- One actual fixed-table symbol sends either a literal or a complete
length/distance pair, with exact emitted bits and the same heap frame. -/
theorem cbFixedSymbol_run {h0 h : Heap} {id b : Nat} {d0 d : DeflateState} {buf0 buf : Array UInt8}
    {w : List Bool} (ht : EmitState id b h0 d0 buf0 w h d buf)
    (dist : UInt32) (lc : UInt8) (bound : dist.toNat ≤ 32768) (total : Nat)
    (budget : w.length + (payloadSymBits fixedLiteralWords fixedDistanceWords (dist.toNat, lc.toNat)).length ≤ total)
    (room : 8 * d0.pending.toNat + d0.bi_valid.toInt.toNat + total ≤ 8 * buf0.size) :
    EWP (cbSymbol (Sp id) (.ref .st_static_ltree 0) (.ref .st_static_dtree 0) dist (u8i lc)) h
      (fun _ H => ∃ D B, EmitState id b h0 d0 buf0
        (w ++ payloadSymBits fixedLiteralWords fixedDistanceWords (dist.toNat, lc.toNat)) H D B) := by
  have wordsL : PayloadTree.words .fixedLit d0 = fixedLiteralWords := rfl
  have wordsD : PayloadTree.words .fixedDist d0 = fixedDistanceWords := rfl
  by_cases zero : dist = 0
  · have fits := (fixed_literal_fits lc.toNat lc.toNat_lt).1
    have codeRoom : 8 * d.pending.toNat + d.bi_valid.toInt.toNat +
        (fixedLiteralWords lc.toNat).2.toNat ≤ 8 * buf.size := by
      apply ht.room _ total
      · simpa only [zero, UInt32.toNat_zero, payloadSymBits, ite_true, codeBits, natBits_length] using budget
      · exact room
    have sent := ht.payload_code .fixedLit lc.toNat
      (by change _ < static_ltree_tab.size; rw [static_ltree_tab_size]; have small := lc.toNat_lt; omega) fits codeRoom
    rw [← u8i_toInt lc] at sent
    simpa only [cbSymbol, zero, BEq.rfl, ite_true, UInt32.toNat_zero, payloadSymBits, PayloadTree.ref, wordsL] using sent
  · have positive : 0 < dist.toNat := by
      have ne : dist.toNat ≠ 0 := fun equal => zero (UInt32.toNat_inj.mp equal)
      omega
    have lcValue := u8i_toInt lc
    have length := lc.toNat_lt
    have codeBound := (length_payload_checked_fields lc.toNat length).1
    have distanceBound := (distance_payload_fields (dist.toNat - 1) (by omega)).1
    have sent := cbMatchSymbol_run ht .fixedLit .fixedDist dist (u8i lc) positive bound
      (by rw [lcValue]; omega) (by rw [lcValue]; omega)
      (by change _ < static_ltree_tab.size; rw [static_ltree_tab_size]; simp only [lcValue, Int.toNat_natCast]; omega)
      (by change _ < static_dtree_tab.size; rw [static_dtree_tab_size]; omega)
      (by simpa only [wordsL, lcValue, Int.toNat_natCast] using (fixed_length_fits (lcodeN lc.toNat) codeBound).1)
      (by simpa only [wordsD] using (fixed_distance_fits _ distanceBound).1) total
      (by simpa only [wordsL, wordsD, lcValue, Int.toNat_natCast] using budget) room
    simpa only [PayloadTree.ref, wordsL, wordsD, lcValue, Int.toNat_natCast] using sent

/-- All original symbol bytes are read before writes for that symbol.
The 31-bit prefix bound derives the unread-byte boundary even though
output and symbols share an allocation. Literal and match paths are both
included. -/
theorem cbFixedBody_run {h0 h : Heap} {id b : Nat} {d0 d : DeflateState}
    {buf0 buf : Array UInt8} {n i : Nat} (sx : UInt32)
    (ht : EmitState id b h0 d0 buf0 (fixedPayloadPrefix buf0 d0.lit_bufsize.toNat i) h d buf)
    (pending : d0.pending = 0) (bits : d0.bi_valid.toInt ≤ 10)
    (capacity : n + 1 ≤ d0.lit_bufsize.toNat) (step : i < n) (counter : sx.toNat = 3 * i)
    (legal : ∀ j, j < n → (payloadSymAt buf0 d0.lit_bufsize.toNat j).1 ≤ 32768) :
    EWP (cbReadBody (Sp id) (.ref .st_static_ltree 0) (.ref .st_static_dtree 0) sx) h
      (fun next H => next.toNat = 3 * (i + 1) ∧ ∃ D B,
        EmitState id b h0 d0 buf0 (fixedPayloadPrefix buf0 d0.lit_bufsize.toNat (i + 1)) H D B) := by
  have size : buf0.size = 4 * d0.lit_bufsize.toNat := by
    rw [← ht.size, ht.inv.base.size, ht.payload_fields.2.2]
  have lower : 128 ≤ d0.lit_bufsize.toNat := by rw [← ht.payload_fields.2.2]; exact ht.inv.base.lit_lo
  have upper : d0.lit_bufsize.toNat ≤ 32768 := by rw [← ht.payload_fields.2.2]; exact ht.inv.base.lit_hi
  have length := fixedPayloadPrefix_length buf0 d0.lit_bufsize.toNat i (fun j hj => legal j (by omega))
  have read := cbReadSymbol_run ht sx (3 * i) d0.lit_bufsize.toNat counter
    (by omega) rfl (by omega) (by simp only [pending, UInt64.toNat_zero]; omega)
  let dist := UInt32.ofNat (payloadSymAt buf0 d0.lit_bufsize.toNat i).1
  let lc := buf0[d0.lit_bufsize.toNat + 3 * i + 2]!
  have distNat : dist.toNat = (payloadSymAt buf0 d0.lit_bufsize.toNat i).1 := by
    rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by have bound := legal i step; omega)]
  have bound : dist.toNat ≤ 32768 := by rw [distNat]; exact legal i step
  have cost := fixed_payload_symbol_length dist.toNat lc.toNat bound lc.toNat_lt
  have totalRoom : 8 * d0.pending.toNat + d0.bi_valid.toInt.toNat + 31 * (i + 1) ≤ 8 * buf0.size := by
    rw [pending, size]
    simp only [UInt64.toNat_zero]
    omega
  unfold cbReadBody
  refine EWP.read read ?_
  simp only []
  refine EWP.bind (cbFixedSymbol_run ht dist lc bound (31 * (i + 1)) (by omega) totalRoom) ?_
  rintro _ H ⟨D, B, trace⟩
  refine EWP.pure ⟨?_, D, B, ?_⟩
  · rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [fixedPayloadPrefix_succ]
    simpa only [distNat, lc, payloadSymAt] using trace

/-- The complete actual do-while loop consumes the original literal/match buffer
and terminates. Every intermediate read is protected by the derived prefix
bound in `cbFixedBody_run`. -/
theorem cbFixedLoop_run {h : Heap} {id b : Nat} {d : DeflateState} {buf : Array UInt8}
    (hI : TreesInvAt h id d b buf) (hp : d.pending = 0) (hv : d.bi_valid.toInt ≤ 10)
    (n : Nat) (hn : 0 < n) (hcount : d.sym_next.toNat = 3 * n)
    (legal : ∀ i, i < n → (payloadSymAt buf d.lit_bufsize.toNat i).1 ≤ 32768) :
    EWP (cdoWhile (cbReadBody (Sp id) (.ref .st_static_ltree 0) (.ref .st_static_dtree 0))
      (cbCondition (Sp id)) 0) h (fun sx H => sx.toNat = 3 * n ∧ ∃ D B,
        EmitState id b h d buf (fixedPayloadPrefix buf d.lit_bufsize.toNat n) H D B) := by
  have hcapacity : n + 1 ≤ d.lit_bufsize.toNat := by
    have hbound := hI.run.sym_next_le
    rw [hcount, hI.base.sym_end] at hbound
    have hlo := hI.base.lit_lo
    omega
  let P := fun k (sx : UInt32) H => k < n ∧ sx.toNat = 3 * (n - k - 1) ∧ ∃ D B,
    EmitState id b h d buf (fixedPayloadPrefix buf d.lit_bufsize.toNat (n - k - 1)) H D B
  let Q := fun (sx : UInt32) H => sx.toNat = 3 * n ∧ ∃ D B,
    EmitState id b h d buf (fixedPayloadPrefix buf d.lit_bufsize.toNat n) H D B
  have step : ∀ k sx H, P (k + 1) sx H → ∃ sx1 H1 sx2 H2,
      cbReadBody (Sp id) (.ref .st_static_ltree 0) (.ref .st_static_dtree 0) sx H = .ok (sx1, H1) ∧
      cbCondition (Sp id) sx1 H1 = .ok ((true, sx2), H2) ∧ P k sx2 H2 := by
    rintro k sx H ⟨hk, hsx, D, B, ht⟩
    obtain ⟨next, H', hbody, hnext, D', B', ht'⟩ := cbFixedBody_run sx ht hp hv hcapacity
      (by omega) hsx legal
    have hcounter := ht'.payload_fields.2.1
    have cont : next < D'.sym_next := by
      rw [UInt32.lt_iff_toNat_lt, hcounter, hcount, hnext]
      omega
    refine ⟨next, H', next, H', hbody, ?_, by omega, ?_, D', B', ?_⟩
    · simp only [cbCondition, bind_app, rd_run ht'.inv.base.dstate, cont, decide_true, pure_app]
    · omega
    · have heq : n - (k + 1) - 1 + 1 = n - k - 1 := by omega
      rwa [heq] at ht'
  have last : ∀ sx H, P 0 sx H → ∃ sx1 H1 sx2 H2,
      cbReadBody (Sp id) (.ref .st_static_ltree 0) (.ref .st_static_dtree 0) sx H = .ok (sx1, H1) ∧
      cbCondition (Sp id) sx1 H1 = .ok ((false, sx2), H2) ∧ Q sx2 H2 := by
    rintro sx H ⟨hk, hsx, D, B, ht⟩
    obtain ⟨next, H', hbody, hnext, D', B', ht'⟩ := cbFixedBody_run sx ht hp hv hcapacity
      (by omega) hsx legal
    have hcounter := ht'.payload_fields.2.1
    have stop : ¬ next < D'.sym_next := by
      rw [UInt32.lt_iff_toNat_lt, hcounter, hcount, hnext]
      omega
    refine ⟨next, H', next, H', hbody, ?_, ?_, D', B', ?_⟩
    · simp only [cbCondition, bind_app, rd_run ht'.inv.base.dstate, stop, decide_false, pure_app]
    · omega
    · have heq : n - 0 - 1 + 1 = n := by omega
      rwa [heq] at ht'
  have initial : P (n - 1) 0 h := by
    refine ⟨by omega, by simp; omega, d, buf, ?_⟩
    simpa [fixedPayloadPrefix, payloadPrefixBits, show n - (n - 1) - 1 = 0 by omega] using EmitState.start hI
  have hsmall := hI.base.lit_hi
  obtain ⟨sx, H, hrun, hQ⟩ := C.cdoWhile_run P Q step last initial (by unfold fuel; omega)
  exact ⟨sx, H, hrun, hQ⟩

set_option maxRecDepth 4096 in
/-- `local void compress_block(deflate_state *s, const ct_data *ltree, const ct_data *dtree)`.
The entire actual fixed-table call executes on all legal buffered literals and matches,
including the empty case and END_BLOCK. All output room and original-byte
preservation facts are derived. This internal milestone assumes initialized
tree/output storage, pending = 0 and at most ten entry bits. It does not
establish initialization, block selection or the public deflate theorem. -/
theorem compress_block_fixed_emit {h : Heap} {id b : Nat} {d : DeflateState} {buf : Array UInt8}
    (hI : TreesInvAt h id d b buf) (hp : d.pending = 0) (hv : d.bi_valid.toInt ≤ 10)
    (n : Nat) (hcount : d.sym_next.toNat = 3 * n)
    (legal : ∀ i, i < n → (payloadSymAt buf d.lit_bufsize.toNat i).1 ≤ 32768) :
    Emit id b (compress_block (Sp id) (.ref .st_static_ltree 0) (.ref .st_static_dtree 0)) h d buf
      (fixedPayloadPrefix buf d.lit_bufsize.toNat n ++ codeBits fixedLiteralWords 256)
      (d.bi_valid.toInt.toNat + (fixedPayloadPrefix buf d.lit_bufsize.toNat n).length + 7) := by
  have hcapacity : n + 1 ≤ d.lit_bufsize.toNat := by
    have bound := hI.run.sym_next_le
    rw [hcount, hI.base.sym_end] at bound
    have hlo := hI.base.lit_lo
    omega
  have hrun : EWP (compress_block (Sp id) (.ref .st_static_ltree 0) (.ref .st_static_dtree 0)) h
      (fun _ H => ∃ D B, EmitState id b h d buf
        (fixedPayloadPrefix buf d.lit_bufsize.toNat n ++ codeBits fixedLiteralWords 256) H D B) := by
    rw [compress_block_eq]
    refine EWP.read (rd_run hI.base.dstate) ?_
    have emitted_prefix : EWP (if d.sym_next != 0 then do
        let _ ← cdoWhile (cbReadBody (Sp id) (.ref .st_static_ltree 0) (.ref .st_static_dtree 0))
          (cbCondition (Sp id)) 0
        pure () else pure ()) h
        (fun _ H => ∃ D B, EmitState id b h d buf (fixedPayloadPrefix buf d.lit_bufsize.toNat n) H D B) := by
      by_cases empty : n = 0
      · have hz : d.sym_next = 0 := by apply UInt32.toNat_inj.mp; simp only [UInt32.toNat_zero]; omega
        simp only [hz, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
        exact EWP.pure ⟨d, buf, by simpa [fixedPayloadPrefix, payloadPrefixBits, empty] using EmitState.start hI⟩
      · have hz : d.sym_next ≠ 0 := by intro eq; rw [eq] at hcount; simp at hcount; omega
        simp only [bne_iff_ne]
        rw [ite_eq_left hz]
        refine EWP.bind (cbFixedLoop_run hI hp hv n (by omega) hcount legal) ?_
        rintro sx H ⟨_, D, B, ht⟩
        exact EWP.pure ⟨D, B, ht⟩
    have regroup :
        ((if d.sym_next != 0 then do
          let _ ← cdoWhile (cbReadBody (Sp id) (.ref .st_static_ltree 0) (.ref .st_static_dtree 0))
            (cbCondition (Sp id)) 0
          pure () else pure ()) >>= fun _ =>
            send_code (Sp id) END_BLOCK.toInt (.ref .st_static_ltree 0)) =
        (if d.sym_next != 0 then do
          let _ ← cdoWhile (cbReadBody (Sp id) (.ref .st_static_ltree 0) (.ref .st_static_dtree 0))
            (cbCondition (Sp id)) 0
          send_code (Sp id) END_BLOCK.toInt (.ref .st_static_ltree 0)
        else send_code (Sp id) END_BLOCK.toInt (.ref .st_static_ltree 0)) := by
      rw [merge_ite_bind]
      simp only [M_bind_assoc, M_pure_bind]
    rw [← regroup]
    refine EWP.bind emitted_prefix ?_
    rintro _ H ⟨D, B, ht⟩
    have length := fixedPayloadPrefix_length buf d.lit_bufsize.toNat n legal
    have room : 8 * D.pending.toNat + D.bi_valid.toInt.toNat + 7 ≤ 8 * B.size := by
      apply ht.room 7 (31 * n + 7)
      · omega
      · rw [hp, hI.base.size]
        simp only [UInt64.toNat_zero]
        omega
    have fits : CodeFits fixedLiteralWords 256 := by
      unfold CodeFits
      rw [fixed_literal_end]
      decide +kernel
    have he := ht.payload_code .fixedLit 256
      (by change 256 < static_ltree_tab.size; rw [static_ltree_tab_size]; omega) fits room
    rw [show PayloadTree.words .fixedLit d = fixedLiteralWords from rfl] at he
    have index : ((256 : Nat) : Int) = END_BLOCK.toInt := by decide +kernel
    rw [index] at he
    exact he
  obtain ⟨v, H, hr, D, B, ht⟩ := hrun
  have hu : v = () := Subsingleton.elim _ _
  subst v
  have he := ht.emit hr
  simpa only [List.length_append, codeBits, fixed_literal_end, natBits_length,
    show (7 : UInt16).toNat = 7 from rfl, Nat.add_assoc] using he



/-- `local void compress_block(deflate_state *s, const ct_data *ltree, const ct_data *dtree)`.
For default memLevel 8, the entire fixed-table payload, including every
legal match and END_BLOCK, writes at most 63486 pending bytes into its
65536-byte shared allocation. Unread symbols and all output-room checks
follow from the prefix bound. Initialization and block selection are
separate, and the public deflate domain is unchanged. -/
theorem compress_block_default_fixed {h : Heap} {id b : Nat} {d : DeflateState} {buf : Array UInt8}
    (inv : TreesInvAt h id d b buf) (memory : d.lit_bufsize.toNat = 16384)
    (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 10)
    (n : Nat) (count : d.sym_next.toNat = 3 * n)
    (legal : ∀ i, i < n → (payloadSymAt buf d.lit_bufsize.toNat i).1 ≤ 32768) :
    ∃ D B, compress_block (Sp id) (.ref .st_static_ltree 0) (.ref .st_static_dtree 0) h =
        .ok ((), Out.setD (Out.setB h b B) id D) ∧
      TreesInvAt (Out.setD (Out.setB h b B) id D) id D b B ∧
      outBits B D = outBits buf d ++
        (fixedPayloadPrefix buf 16384 n ++ codeBits fixedLiteralWords 256) ∧
      B.size = 65536 ∧ D.pending.toNat ≤ 63486 := by
  obtain ⟨B, D, run, invA, output, size, _frame, _lower, _upper, _fields⟩ :=
    compress_block_fixed_emit inv pending bits n count legal
  have bound := inv.run.sym_next_le
  rw [count, inv.base.sym_end, memory] at bound
  have length := fixedPayloadPrefix_length buf d.lit_bufsize.toNat n legal
  rw [memory] at output length
  have bitCount := congrArg List.length output
  simp only [outBits_length, List.length_append, codeBits, fixed_literal_end,
    natBits_length, show (7 : UInt16).toNat = 7 from rfl, pending, UInt64.toNat_zero] at bitCount
  have nonnegative := invA.run.bi_lo
  refine ⟨D, B, run, invA, output, ?_, by omega⟩
  rw [size, inv.base.size, memory]

end Zlib.Trees.Proofs
