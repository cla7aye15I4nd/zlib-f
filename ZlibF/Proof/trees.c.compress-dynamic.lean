import ZlibF.Proof.«trees.c.compress-match»
import ZlibF.Proof.«trees.c.source-code-facts»

/-! # Dynamic payload execution with explicit stored-code and prefix data -/

namespace Zlib.Trees.Proofs
open C Zlib.Trees Out
set_option autoImplicit false

def dynamicPayloadPrefix (d : DeflateState) (buf : Array UInt8) (n : Nat) : List Bool :=
  payloadPrefixBits (sourceWords d .lit) (sourceWords d .dist) buf d.lit_bufsize.toNat n

theorem dynamicPayloadPrefix_succ (d : DeflateState) (buf : Array UInt8) (n : Nat) :
    dynamicPayloadPrefix d buf (n + 1) = dynamicPayloadPrefix d buf n ++
      payloadSymBits (sourceWords d .lit) (sourceWords d .dist) (payloadSymAt buf d.lit_bufsize.toNat n) :=
  payloadPrefixBits_succ _ _ _ _ _

def dynamicLiteralKey (sym : Nat × Nat) : Nat := if sym.1 = 0 then sym.2 else lcodeN sym.2 + 257

/-- Stored code values and exact byte-prefix geometry. These are data
premises for the loop, not specifications of called functions. The engine
derives them from its original ledger and actual tree/header execution. -/
structure DynamicPayloadData (d : DeflateState) (buf : Array UInt8) (n : Nat) : Prop where
  legal : ∀ i, i < n → (payloadSymAt buf d.lit_bufsize.toNat i).1 ≤ 32768
  literal : ∀ i, i < n → CodeFits (sourceWords d .lit) (dynamicLiteralKey (payloadSymAt buf d.lit_bufsize.toNat i))
  distance : ∀ i, i < n → (payloadSymAt buf d.lit_bufsize.toNat i).1 ≠ 0 →
    CodeFits (sourceWords d .dist) (dcodeN ((payloadSymAt buf d.lit_bufsize.toNat i).1 - 1))
  end_marker : CodeFits (sourceWords d .lit) 256
  prefix_room : ∀ k, k ≤ n → 8 * d.pending.toNat + d.bi_valid.toInt.toNat +
    (dynamicPayloadPrefix d buf k).length + 15 ≤ 8 * (d.lit_bufsize.toNat + 3 * k)
  block_room : 8 * d.pending.toNat + d.bi_valid.toInt.toNat +
    (dynamicPayloadPrefix d buf n).length + 15 ≤ 8 * buf.size

/-- One actual dynamic symbol sends a literal or a complete length/distance
pair from the actual stored arrays. Every subcall is a proved execution. -/
theorem cbDynamicSymbol_run {h0 h : Heap} {id b : Nat} {d0 d : DeflateState} {buf0 buf : Array UInt8}
    {w : List Bool} (trace : EmitState id b h0 d0 buf0 w h d buf)
    (dist : UInt32) (lc : UInt8) (bound : dist.toNat ≤ 32768)
    (literalFit : CodeFits (sourceWords d0 .lit) (dynamicLiteralKey (dist.toNat, lc.toNat)))
    (distanceFit : dist.toNat ≠ 0 → CodeFits (sourceWords d0 .dist) (dcodeN (dist.toNat - 1)))
    (total : Nat)
    (budget : w.length + (payloadSymBits (sourceWords d0 .lit) (sourceWords d0 .dist) (dist.toNat, lc.toNat)).length ≤ total)
    (room : 8 * d0.pending.toNat + d0.bi_valid.toInt.toNat + total ≤ 8 * buf0.size) :
    EWP (cbSymbol (Sp id) (.ref (TK.lit.ref id) 0) (.ref (TK.dist.ref id) 0) dist (u8i lc)) h
      (fun _ H => ∃ D B, EmitState id b h0 d0 buf0
        (w ++ payloadSymBits (sourceWords d0 .lit) (sourceWords d0 .dist) (dist.toNat, lc.toNat)) H D B) := by
  have literalSize : d0.dyn_ltree.size = 573 := by rw [← trace.tree_arrays.1]; exact trace.inv.base.wf.1
  have distanceSize : d0.dyn_dtree.size = 61 := by rw [← trace.tree_arrays.2.1]; exact trace.inv.base.wf.2.1
  by_cases zero : dist = 0
  · have fits : CodeFits (sourceWords d0 .lit) lc.toNat := by
      simpa only [dynamicLiteralKey, zero, UInt32.toNat_zero, ite_true] using literalFit
    have codeRoom : 8 * d.pending.toNat + d.bi_valid.toInt.toNat + (sourceWords d0 .lit lc.toNat).2.toNat ≤ 8 * buf.size := by
      apply trace.room _ total
      · simpa only [zero, UInt32.toNat_zero, payloadSymBits, ite_true, codeBits, natBits_length] using budget
      · exact room
    have sent := trace.payload_code (.dynamic .lit) lc.toNat
      (by change lc.toNat < d0.dyn_ltree.size; rw [literalSize]; have small := lc.toNat_lt; omega) fits codeRoom
    rw [← u8i_toInt lc] at sent
    simpa only [cbSymbol, zero, BEq.rfl, ite_true, UInt32.toNat_zero, payloadSymBits, PayloadTree.ref, TK.ref, sourceWords] using sent
  · have positive : 0 < dist.toNat := by
      have ne : dist.toNat ≠ 0 := fun same => zero (UInt32.toNat_inj.mp same)
      omega
    have lcValue := u8i_toInt lc
    have codeBound := (length_payload_checked_fields lc.toNat lc.toNat_lt).1
    have distanceBound := (distance_payload_fields (dist.toNat - 1) (by omega)).1
    have fits : CodeFits (sourceWords d0 .lit) (lcodeN lc.toNat + 257) := by
      simpa only [dynamicLiteralKey, show dist.toNat ≠ 0 by omega, ite_false] using literalFit
    have sent := cbMatchSymbol_run trace (.dynamic .lit) (.dynamic .dist) dist (u8i lc) positive bound
      (by rw [lcValue]; omega) (by rw [lcValue]; have small := lc.toNat_lt; omega)
      (by change lcodeN (u8i lc).toInt.toNat + 257 < d0.dyn_ltree.size; rw [lcValue, Int.toNat_natCast, literalSize]; omega)
      (by change dcodeN (dist.toNat - 1) < d0.dyn_dtree.size; rw [distanceSize]; omega)
      (by simpa only [lcValue, Int.toNat_natCast, sourceWords] using fits)
      (distanceFit (by omega)) total (by simpa only [lcValue, Int.toNat_natCast, sourceWords] using budget) room
    simpa only [PayloadTree.ref, TK.ref, lcValue, Int.toNat_natCast, sourceWords] using sent

/-- All three original symbol bytes are read before that symbol's output.
The supplied prefix data protects the next unread symbol as the shared
allocation is overwritten by compressed output. -/
theorem cbDynamicBody_run {h0 h : Heap} {id b : Nat} {d0 d : DeflateState}
    {buf0 buf : Array UInt8} {n i : Nat} (sx : UInt32)
    (trace : EmitState id b h0 d0 buf0 (dynamicPayloadPrefix d0 buf0 i) h d buf)
    (data : DynamicPayloadData d0 buf0 n) (capacity : n + 1 ≤ d0.lit_bufsize.toNat)
    (step : i < n) (counter : sx.toNat = 3 * i) :
    EWP (cbReadBody (Sp id) (.ref (TK.lit.ref id) 0) (.ref (TK.dist.ref id) 0) sx) h
      (fun next H => next.toNat = 3 * (i + 1) ∧ ∃ D B,
        EmitState id b h0 d0 buf0 (dynamicPayloadPrefix d0 buf0 (i + 1)) H D B) := by
  have size : buf0.size = 4 * d0.lit_bufsize.toNat := by
    rw [← trace.size, trace.inv.base.size, trace.payload_fields.2.2]
  have upper : d0.lit_bufsize.toNat ≤ 32768 := by rw [← trace.payload_fields.2.2]; exact trace.inv.base.lit_hi
  have prefixRoom := data.prefix_room i (by omega)
  have read := cbReadSymbol_run trace sx (3 * i) d0.lit_bufsize.toNat counter
    (by omega) rfl (by omega) (by omega)
  let dist := UInt32.ofNat (payloadSymAt buf0 d0.lit_bufsize.toNat i).1
  let lc := buf0[d0.lit_bufsize.toNat + 3 * i + 2]!
  have distNat : dist.toNat = (payloadSymAt buf0 d0.lit_bufsize.toNat i).1 := by
    rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by have small := data.legal i step; omega)]
  have literalFit : CodeFits (sourceWords d0 .lit) (dynamicLiteralKey (dist.toNat, lc.toNat)) := by
    simpa only [distNat, lc, payloadSymAt] using data.literal i step
  have distanceFit : dist.toNat ≠ 0 → CodeFits (sourceWords d0 .dist) (dcodeN (dist.toNat - 1)) := by
    rw [distNat]
    exact data.distance i step
  have monotone := payloadPrefixBits_mono (sourceWords d0 .lit) (sourceWords d0 .dist) buf0
    d0.lit_bufsize.toNat (show i + 1 ≤ n by omega)
  change (dynamicPayloadPrefix d0 buf0 (i + 1)).length ≤ (dynamicPayloadPrefix d0 buf0 n).length at monotone
  have totalRoom : 8 * d0.pending.toNat + d0.bi_valid.toInt.toNat +
      (dynamicPayloadPrefix d0 buf0 (i + 1)).length ≤ 8 * buf0.size := by
    have room := data.block_room
    omega
  have symbolBudget : (dynamicPayloadPrefix d0 buf0 i).length +
      (payloadSymBits (sourceWords d0 .lit) (sourceWords d0 .dist) (dist.toNat, lc.toNat)).length ≤
        (dynamicPayloadPrefix d0 buf0 (i + 1)).length := by
    rw [dynamicPayloadPrefix_succ, List.length_append, distNat]
    exact Nat.le_refl _
  unfold cbReadBody
  refine EWP.read read ?_
  refine EWP.bind (cbDynamicSymbol_run trace dist lc (by rw [distNat]; exact data.legal i step)
    literalFit distanceFit _ symbolBudget totalRoom) ?_
  rintro _ H ⟨D, B, nextTrace⟩
  refine EWP.pure ⟨?_, D, B, ?_⟩
  · rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [dynamicPayloadPrefix_succ]
    simpa only [distNat, lc, payloadSymAt] using nextTrace

/-- The actual do-while loop consumes every original symbol and terminates. -/
theorem cbDynamicLoop_run {h : Heap} {id b : Nat} {d : DeflateState} {buf : Array UInt8}
    (hI : TreesInvAt h id d b buf)
    (n : Nat) (hn : 0 < n) (hcount : d.sym_next.toNat = 3 * n)
    (data : DynamicPayloadData d buf n) :
    EWP (cdoWhile (cbReadBody (Sp id) (.ref (TK.lit.ref id) 0) (.ref (TK.dist.ref id) 0))
      (cbCondition (Sp id)) 0) h (fun sx H => sx.toNat = 3 * n ∧ ∃ D B,
        EmitState id b h d buf (dynamicPayloadPrefix d buf n) H D B) := by
  have hcapacity : n + 1 ≤ d.lit_bufsize.toNat := by
    have hbound := hI.run.sym_next_le
    rw [hcount, hI.base.sym_end] at hbound
    have hlo := hI.base.lit_lo
    omega
  let P := fun k (sx : UInt32) H => k < n ∧ sx.toNat = 3 * (n - k - 1) ∧ ∃ D B,
    EmitState id b h d buf (dynamicPayloadPrefix d buf (n - k - 1)) H D B
  let Q := fun (sx : UInt32) H => sx.toNat = 3 * n ∧ ∃ D B,
    EmitState id b h d buf (dynamicPayloadPrefix d buf n) H D B
  have step : ∀ k sx H, P (k + 1) sx H → ∃ sx1 H1 sx2 H2,
      cbReadBody (Sp id) (.ref (TK.lit.ref id) 0) (.ref (TK.dist.ref id) 0) sx H = .ok (sx1, H1) ∧
      cbCondition (Sp id) sx1 H1 = .ok ((true, sx2), H2) ∧ P k sx2 H2 := by
    rintro k sx H ⟨hk, hsx, D, B, ht⟩
    obtain ⟨next, H', hbody, hnext, D', B', ht'⟩ := cbDynamicBody_run sx ht data hcapacity
      (by omega) hsx
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
      cbReadBody (Sp id) (.ref (TK.lit.ref id) 0) (.ref (TK.dist.ref id) 0) sx H = .ok (sx1, H1) ∧
      cbCondition (Sp id) sx1 H1 = .ok ((false, sx2), H2) ∧ Q sx2 H2 := by
    rintro sx H ⟨hk, hsx, D, B, ht⟩
    obtain ⟨next, H', hbody, hnext, D', B', ht'⟩ := cbDynamicBody_run sx ht data hcapacity
      (by omega) hsx
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
    simpa [dynamicPayloadPrefix, payloadPrefixBits, show n - (n - 1) - 1 = 0 by omega] using EmitState.start hI
  have hsmall := hI.base.lit_hi
  obtain ⟨sx, H, hrun, hQ⟩ := C.cdoWhile_run P Q step last initial (by unfold fuel; omega)
  exact ⟨sx, H, hrun, hQ⟩

set_option maxRecDepth 4096 in
/-- `local void compress_block(deflate_state *s, const ct_data *ltree, const ct_data *dtree)`.
The complete actual dynamic call consumes literals and matches, including
the empty case and end marker. Code fit and prefix room are explicit data;
the engine supplies them from actual construction and header emission. -/
theorem compress_block_dynamic_emit {h : Heap} {id b : Nat} {d : DeflateState} {buf : Array UInt8}
    (trees : TreesInvAt h id d b buf) (n : Nat) (count : d.sym_next.toNat = 3 * n)
    (data : DynamicPayloadData d buf n) :
    Emit id b (compress_block (Sp id) (.ref (TK.lit.ref id) 0) (.ref (TK.dist.ref id) 0)) h d buf
      (dynamicPayloadPrefix d buf n ++ codeBits (sourceWords d .lit) 256)
      (d.bi_valid.toInt.toNat + (dynamicPayloadPrefix d buf n).length + (sourceWords d .lit 256).2.toNat) := by
  have execution : EWP (compress_block (Sp id) (.ref (TK.lit.ref id) 0) (.ref (TK.dist.ref id) 0)) h
      (fun _ H => ∃ D B, EmitState id b h d buf
        (dynamicPayloadPrefix d buf n ++ codeBits (sourceWords d .lit) 256) H D B) := by
    rw [compress_block_eq]
    refine EWP.read (rd_run trees.base.dstate) ?_
    have symbols : EWP (if d.sym_next != 0 then do
        let _ ← cdoWhile (cbReadBody (Sp id) (.ref (TK.lit.ref id) 0) (.ref (TK.dist.ref id) 0))
          (cbCondition (Sp id)) 0
        pure () else pure ()) h
        (fun _ H => ∃ D B, EmitState id b h d buf (dynamicPayloadPrefix d buf n) H D B) := by
      by_cases empty : n = 0
      · have zero : d.sym_next = 0 := by
          apply UInt32.toNat_inj.mp
          simp only [UInt32.toNat_zero]
          omega
        simp only [zero, bne_self_eq_false, Bool.false_eq_true, ite_false]
        exact EWP.pure ⟨d, buf, by simpa [dynamicPayloadPrefix, payloadPrefixBits, empty] using EmitState.start trees⟩
      · have nonzero : d.sym_next ≠ 0 := by intro zero; rw [zero] at count; simp at count; omega
        simp only [bne_iff_ne]
        rw [ite_eq_left nonzero]
        refine EWP.bind (cbDynamicLoop_run trees n (by omega) count data) ?_
        rintro sx H ⟨_counter, D, B, trace⟩
        exact EWP.pure ⟨D, B, trace⟩
    have regroup :
        ((if d.sym_next != 0 then do
          let _ ← cdoWhile (cbReadBody (Sp id) (.ref (TK.lit.ref id) 0) (.ref (TK.dist.ref id) 0))
            (cbCondition (Sp id)) 0
          pure () else pure ()) >>= fun _ =>
            send_code (Sp id) END_BLOCK.toInt (.ref (TK.lit.ref id) 0)) =
        (if d.sym_next != 0 then do
          let _ ← cdoWhile (cbReadBody (Sp id) (.ref (TK.lit.ref id) 0) (.ref (TK.dist.ref id) 0))
            (cbCondition (Sp id)) 0
          send_code (Sp id) END_BLOCK.toInt (.ref (TK.lit.ref id) 0)
        else send_code (Sp id) END_BLOCK.toInt (.ref (TK.lit.ref id) 0)) := by
      rw [merge_ite_bind]
      simp only [M_bind_assoc, M_pure_bind]
    rw [← regroup]
    refine EWP.bind symbols ?_
    rintro _ H ⟨D, B, trace⟩
    have room : 8 * D.pending.toNat + D.bi_valid.toInt.toNat + (sourceWords d .lit 256).2.toNat ≤ 8 * B.size := by
      apply trace.room _ ((dynamicPayloadPrefix d buf n).length + 15)
      · have bound := data.end_marker.1
        omega
      · exact data.block_room
    have sent := trace.payload_code (.dynamic .lit) 256
      (by change 256 < d.dyn_ltree.size; rw [trees.base.wf.1]; decide +kernel) data.end_marker room
    have index : ((256 : Nat) : Int) = END_BLOCK.toInt := by decide +kernel
    rw [index] at sent
    exact sent
  obtain ⟨value, after, run, result, output, trace⟩ := execution
  have unit : value = () := Subsingleton.elim _ _
  subst value
  have emitted := trace.emit run
  simpa only [List.length_append, codeBits, natBits_length, Nat.add_assoc] using emitted

end Zlib.Trees.Proofs
