import ZlibF.Proof.«trees.c.compress-source»

/-! # trees.c: complete fixed-code literal payload execution

This milestone covers every permitted symbol-buffer size, including the
default memLevel 8. The symbol buffer contains literals only. The entry
pending count is zero and at most ten bits are buffered, allowing the usual
seven entry bits plus a fixed-block header. No output-room or callee
contract is assumed. Initialization and block selection are outside its scope.
-/

namespace Zlib.Trees.Proofs
open C Zlib.Trees Out
set_option autoImplicit false

/-- Words from the actual installed fixed literal/length table. -/
def fixedLiteralWords (k : Nat) : UInt16 × UInt16 :=
  (static_ltree_tab[k]!.fc, static_ltree_tab[k]!.dl)

set_option maxHeartbeats 1000000 in
/-- The finite table check includes every literal and its stored code word. -/
theorem fixed_literal_fits (k : Nat) (hk : k < 256) :
    CodeFits fixedLiteralWords k ∧ (fixedLiteralWords k).2.toNat ≤ 9 := by
  have checked : ∀ i : Fin 256,
      CodeFits fixedLiteralWords i.val ∧ (fixedLiteralWords i.val).2.toNat ≤ 9 := by
    unfold CodeFits
    decide +kernel
  exact checked ⟨k, hk⟩

/-- The actual fixed END_BLOCK entry is a seven-bit zero word. -/
theorem fixed_literal_end : fixedLiteralWords 256 = (0, 7) := by decide +kernel

/-- Fixed code bits for the first n original three-byte literal symbols. -/
def fixedLiteralPrefix (buf : Array UInt8) (offset n : Nat) : List Bool :=
  (List.range n).flatMap (fun i => codeBits fixedLiteralWords buf[offset + 3 * i + 2]!.toNat)

theorem fixedLiteralPrefix_succ (buf : Array UInt8) (offset n : Nat) :
    fixedLiteralPrefix buf offset (n + 1) = fixedLiteralPrefix buf offset n ++
      codeBits fixedLiteralWords buf[offset + 3 * n + 2]!.toNat := by
  simp [fixedLiteralPrefix, List.range_succ, List.flatMap_append]

theorem fixedLiteralPrefix_length (buf : Array UInt8) (offset n : Nat) :
    (fixedLiteralPrefix buf offset n).length ≤ 9 * n := by
  induction n with
  | zero => simp [fixedLiteralPrefix]
  | succ n ih =>
    rw [fixedLiteralPrefix_succ, List.length_append]
    have cost := (fixed_literal_fits buf[offset + 3 * n + 2]!.toNat
      (UInt8.toNat_lt _)).2
    simp only [codeBits, natBits_length]
    omega

/-- One actual loop body reads its original three bytes before writing.
The unread-byte and nine-bit emission bounds are derived from the entry
state and the completed prefix, rather than assumed as room contracts. -/
theorem cbFixedLiteralBody_run {h0 h : Heap} {id b : Nat} {d0 d : DeflateState}
    {buf0 buf : Array UInt8} {n i : Nat} (sx : UInt32)
    (ht : EmitState id b h0 d0 buf0 (fixedLiteralPrefix buf0 d0.lit_bufsize.toNat i) h d buf)
    (hp : d0.pending = 0) (hv : d0.bi_valid.toInt ≤ 10)
    (hcapacity : n + 1 ≤ d0.lit_bufsize.toNat) (hi : i < n) (hsx : sx.toNat = 3 * i)
    (hzero : buf0[d0.lit_bufsize.toNat + 3 * i]! = 0 ∧
      buf0[d0.lit_bufsize.toNat + 3 * i + 1]! = 0) :
    EWP (cbReadBody (Sp id) (.ref .st_static_ltree 0) (.ref .st_static_dtree 0) sx) h
      (fun next H => next.toNat = 3 * (i + 1) ∧ ∃ D B,
        EmitState id b h0 d0 buf0 (fixedLiteralPrefix buf0 d0.lit_bufsize.toNat (i + 1)) H D B) := by
  have hsize : buf0.size = 4 * d0.lit_bufsize.toNat := by
    rw [← ht.size, ht.inv.base.size, ht.payload_fields.2.2]
  have hlo : 128 ≤ d0.lit_bufsize.toNat := by
    rw [← ht.payload_fields.2.2]
    exact ht.inv.base.lit_lo
  have hhi : d0.lit_bufsize.toNat ≤ 32768 := by
    rw [← ht.payload_fields.2.2]
    exact ht.inv.base.lit_hi
  have hlen := fixedLiteralPrefix_length buf0 d0.lit_bufsize.toNat i
  have hread := cbReadSymbol_run ht sx (3 * i) d0.lit_bufsize.toNat hsx
    (by omega) rfl (by omega) (by simp only [hp, UInt64.toNat_zero]; omega)
  rw [hzero.1, hzero.2] at hread
  simp only [UInt8.toNat_zero, Nat.mul_zero, Nat.zero_add,
    show UInt32.ofNat 0 = 0 from rfl] at hread
  unfold cbReadBody
  refine EWP.read hread ?_
  simp only []
  unfold cbSymbol
  simp only [show ((0 : UInt32) == 0) = true from rfl, ite_true]
  have hbyte := UInt8.toNat_lt buf0[d0.lit_bufsize.toNat + 3 * i + 2]!
  have hfit := fixed_literal_fits _ hbyte
  have hroom : 8 * d.pending.toNat + d.bi_valid.toInt.toNat +
      (fixedLiteralWords buf0[d0.lit_bufsize.toNat + 3 * i + 2]!.toNat).2.toNat ≤ 8 * buf.size := by
    apply ht.room _ (9 * i + 9)
    · omega
    · simp only [hp, UInt64.toNat_zero]
      omega
  have he := ht.payload_code .fixedLit buf0[d0.lit_bufsize.toNat + 3 * i + 2]!.toNat
    (by change _ < static_ltree_tab.size; rw [static_ltree_tab_size]; omega) hfit.1 hroom
  rw [← u8i_toInt buf0[d0.lit_bufsize.toNat + 3 * i + 2]!] at he
  refine EWP.bind he ?_
  rintro _ H ⟨D, B, htrace⟩
  refine EWP.pure ⟨?_, D, B, ?_⟩
  · rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [fixedLiteralPrefix_succ]
    exact htrace

/-- The complete actual do-while loop consumes the original literal buffer
and terminates. Every intermediate read is protected by the derived prefix
bound in `cbFixedLiteralBody_run`. -/
theorem cbFixedLiteralLoop_run {h : Heap} {id b : Nat} {d : DeflateState} {buf : Array UInt8}
    (hI : TreesInvAt h id d b buf) (hp : d.pending = 0) (hv : d.bi_valid.toInt ≤ 10)
    (n : Nat) (hn : 0 < n) (hcount : d.sym_next.toNat = 3 * n)
    (hzero : ∀ i, i < n → buf[d.lit_bufsize.toNat + 3 * i]! = 0 ∧
      buf[d.lit_bufsize.toNat + 3 * i + 1]! = 0) :
    EWP (cdoWhile (cbReadBody (Sp id) (.ref .st_static_ltree 0) (.ref .st_static_dtree 0))
      (cbCondition (Sp id)) 0) h (fun sx H => sx.toNat = 3 * n ∧ ∃ D B,
        EmitState id b h d buf (fixedLiteralPrefix buf d.lit_bufsize.toNat n) H D B) := by
  have hcapacity : n + 1 ≤ d.lit_bufsize.toNat := by
    have hbound := hI.run.sym_next_le
    rw [hcount, hI.base.sym_end] at hbound
    have hlo := hI.base.lit_lo
    omega
  let P := fun k (sx : UInt32) H => k < n ∧ sx.toNat = 3 * (n - k - 1) ∧ ∃ D B,
    EmitState id b h d buf (fixedLiteralPrefix buf d.lit_bufsize.toNat (n - k - 1)) H D B
  let Q := fun (sx : UInt32) H => sx.toNat = 3 * n ∧ ∃ D B,
    EmitState id b h d buf (fixedLiteralPrefix buf d.lit_bufsize.toNat n) H D B
  have step : ∀ k sx H, P (k + 1) sx H → ∃ sx1 H1 sx2 H2,
      cbReadBody (Sp id) (.ref .st_static_ltree 0) (.ref .st_static_dtree 0) sx H = .ok (sx1, H1) ∧
      cbCondition (Sp id) sx1 H1 = .ok ((true, sx2), H2) ∧ P k sx2 H2 := by
    rintro k sx H ⟨hk, hsx, D, B, ht⟩
    obtain ⟨next, H', hbody, hnext, D', B', ht'⟩ := cbFixedLiteralBody_run sx ht hp hv hcapacity
      (by omega) hsx (hzero _ (by omega))
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
    obtain ⟨next, H', hbody, hnext, D', B', ht'⟩ := cbFixedLiteralBody_run sx ht hp hv hcapacity
      (by omega) hsx (hzero _ (by omega))
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
    simpa [fixedLiteralPrefix, show n - (n - 1) - 1 = 0 by omega] using EmitState.start hI
  have hsmall := hI.base.lit_hi
  obtain ⟨sx, H, hrun, hQ⟩ := C.cdoWhile_run P Q step last initial (by unfold fuel; omega)
  exact ⟨sx, H, hrun, hQ⟩

set_option maxRecDepth 4096 in
/-- `local void compress_block(deflate_state *s, const ct_data *ltree, const ct_data *dtree)`.
The entire actual fixed-table call executes on literal-only buffered symbols,
including the empty case and END_BLOCK. All output room and original-byte
preservation facts are derived. This internal milestone assumes initialized
tree/output storage, pending = 0 and at most ten entry bits. It does not
establish initialization, block selection or the public deflate theorem. -/
theorem compress_block_fixed_literals_emit {h : Heap} {id b : Nat} {d : DeflateState} {buf : Array UInt8}
    (hI : TreesInvAt h id d b buf) (hp : d.pending = 0) (hv : d.bi_valid.toInt ≤ 10)
    (n : Nat) (hcount : d.sym_next.toNat = 3 * n)
    (hzero : ∀ i, i < n → buf[d.lit_bufsize.toNat + 3 * i]! = 0 ∧
      buf[d.lit_bufsize.toNat + 3 * i + 1]! = 0) :
    Emit id b (compress_block (Sp id) (.ref .st_static_ltree 0) (.ref .st_static_dtree 0)) h d buf
      (fixedLiteralPrefix buf d.lit_bufsize.toNat n ++ codeBits fixedLiteralWords 256)
      (d.bi_valid.toInt.toNat + (fixedLiteralPrefix buf d.lit_bufsize.toNat n).length + 7) := by
  have hcapacity : n + 1 ≤ d.lit_bufsize.toNat := by
    have bound := hI.run.sym_next_le
    rw [hcount, hI.base.sym_end] at bound
    have hlo := hI.base.lit_lo
    omega
  have hrun : EWP (compress_block (Sp id) (.ref .st_static_ltree 0) (.ref .st_static_dtree 0)) h
      (fun _ H => ∃ D B, EmitState id b h d buf
        (fixedLiteralPrefix buf d.lit_bufsize.toNat n ++ codeBits fixedLiteralWords 256) H D B) := by
    rw [compress_block_eq]
    refine EWP.read (rd_run hI.base.dstate) ?_
    have emitted_prefix : EWP (if d.sym_next != 0 then do
        let _ ← cdoWhile (cbReadBody (Sp id) (.ref .st_static_ltree 0) (.ref .st_static_dtree 0))
          (cbCondition (Sp id)) 0
        pure () else pure ()) h
        (fun _ H => ∃ D B, EmitState id b h d buf (fixedLiteralPrefix buf d.lit_bufsize.toNat n) H D B) := by
      by_cases empty : n = 0
      · have hz : d.sym_next = 0 := by apply UInt32.toNat_inj.mp; simp only [UInt32.toNat_zero]; omega
        simp only [hz, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
        exact EWP.pure ⟨d, buf, by simpa [fixedLiteralPrefix, empty] using EmitState.start hI⟩
      · have hz : d.sym_next ≠ 0 := by intro eq; rw [eq] at hcount; simp at hcount; omega
        simp only [bne_iff_ne]
        rw [ite_eq_left hz]
        refine EWP.bind (cbFixedLiteralLoop_run hI hp hv n (by omega) hcount hzero) ?_
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
    have length := fixedLiteralPrefix_length buf d.lit_bufsize.toNat n
    have room : 8 * D.pending.toNat + D.bi_valid.toInt.toNat + 7 ≤ 8 * B.size := by
      apply ht.room 7 (9 * n + 7)
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
Concrete default-memory literal milestone: a complete fixed-table call,
including END_BLOCK, writes at most 18433 pending bytes in its 65536-byte
buffer. The explicit storage equation is the memLevel 8 configuration;
successful initialization and the other deflate branches are separate. -/
theorem compress_block_default_literals {h : Heap} {id b : Nat} {d : DeflateState} {buf : Array UInt8}
    (hI : TreesInvAt h id d b buf) (hmem : d.lit_bufsize.toNat = 16384)
    (hp : d.pending = 0) (hv : d.bi_valid.toInt ≤ 10)
    (n : Nat) (hcount : d.sym_next.toNat = 3 * n)
    (hzero : ∀ i, i < n → buf[d.lit_bufsize.toNat + 3 * i]! = 0 ∧
      buf[d.lit_bufsize.toNat + 3 * i + 1]! = 0) :
    ∃ D B, compress_block (Sp id) (.ref .st_static_ltree 0) (.ref .st_static_dtree 0) h =
        .ok ((), Out.setD (Out.setB h b B) id D) ∧
      TreesInvAt (Out.setD (Out.setB h b B) id D) id D b B ∧
      outBits B D = outBits buf d ++
        (fixedLiteralPrefix buf 16384 n ++ codeBits fixedLiteralWords 256) ∧
      B.size = 65536 ∧ D.pending.toNat ≤ 18433 := by
  obtain ⟨B, D, hr, hID, ho, hsize, hframe, lower, upper, fields⟩ :=
    compress_block_fixed_literals_emit hI hp hv n hcount hzero
  have hbound := hI.run.sym_next_le
  rw [hcount, hI.base.sym_end, hmem] at hbound
  have hlen := fixedLiteralPrefix_length buf 16384 n
  rw [hmem] at ho
  have hbits := congrArg List.length ho
  simp only [outBits_length, List.length_append, codeBits, fixed_literal_end,
    natBits_length, show (7 : UInt16).toNat = 7 from rfl, hp, UInt64.toNat_zero] at hbits
  have hnonneg := hID.run.bi_lo
  refine ⟨D, B, hr, hID, ho, ?_, by omega⟩
  rw [hsize, hI.base.size, hmem]

end Zlib.Trees.Proofs
