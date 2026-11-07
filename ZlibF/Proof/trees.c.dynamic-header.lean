import ZlibF.Proof.«trees.c.prepared-header-data»
import ZlibF.Proof.«trees.c.header-budget»
import ZlibF.Proof.«trees.c.flush-source»

/-! # Actual dynamic block tag and complete header emission -/

namespace Zlib.Trees.Proofs
open C Zlib.Trees Out
set_option autoImplicit false

theorem PreparedHeaderData.bitsDiff {before after : DeflateState} {mb : Int32}
    (data : PreparedHeaderData before mb) (diff : BitsDiff before after) : PreparedHeaderData after mb := by
  have lit := data.all.lit_data.bitsDiff .lit diff
  have dist := data.all.dist_data.bitsDiff .dist diff
  have literalDesc : after.l_desc = before.l_desc := by obtain ⟨_, _, _, _, equal⟩ := diff; rw [equal]
  have distanceDesc : after.d_desc = before.d_desc := by obtain ⟨_, _, _, _, equal⟩ := diff; rw [equal]
  have blDesc : after.bl_desc = before.bl_desc := by obtain ⟨_, _, _, _, equal⟩ := diff; rw [equal]
  have blTree : after.bl_tree = before.bl_tree := by obtain ⟨_, _, _, _, equal⟩ := diff; rw [equal]
  have literalLens : lens (sendLengths after .lit) (after.l_desc.max_code.toInt.toNat + 1) =
      lens (sendLengths before .lit) (before.l_desc.max_code.toInt.toNat + 1) := by
    obtain ⟨_, _, _, _, equal⟩ := diff
    rw [equal]
    rfl
  have distanceLens : lens (sendLengths after .dist) (after.d_desc.max_code.toInt.toNat + 1) =
      lens (sendLengths before .dist) (before.d_desc.max_code.toInt.toNat + 1) := by
    obtain ⟨_, _, _, _, equal⟩ := diff
    rw [equal]
    rfl
  refine ⟨?_, ?_, ?_, ?_, data.minimum, data.maximum⟩
  · refine ⟨?_, ?_, ?_, ?_, data.all.bl_min, data.all.bl_max, ?_, ?_, lit, dist, ?_⟩
    · rw [literalDesc]; exact data.all.lit_min
    · rw [literalDesc]; exact data.all.lit_max
    · rw [distanceDesc]; exact data.all.dist_min
    · rw [distanceDesc]; exact data.all.dist_max
    · rw [literalDesc]; exact data.all.lit_count
    · rw [distanceDesc]; exact data.all.dist_count
    · rw [blTree]; exact data.all.bl_lengths
  · refine ⟨?_, ?_, ?_, ?_⟩
    · rw [blDesc]; exact data.table.max_lt
    · rw [blDesc, blTree]; exact data.table.upper_zero
    · rw [blTree]; exact data.table.omitted_zero
    · rw [blTree]; exact data.table.acceptable
  · refine ⟨?_, ?_, ?_⟩
    · rw [literalLens]; exact data.format.lit
    · rw [distanceLens]; exact data.format.dist
    · rw [literalLens]; exact data.format.eob
  · intro tk ne
    obtain ⟨_, _, _, _, equal⟩ := diff
    rw [equal]
    cases tk with
    | lit => exact data.guards .lit ne
    | dist => exact data.guards .dist ne
    | bl => exact False.elim (ne rfl)

theorem dynamicHeaderBits_bitsDiff {before after : DeflateState} (mb : Int32)
    (diff : BitsDiff before after) : dynamicHeaderBits after mb = dynamicHeaderBits before mb := by
  obtain ⟨p, word, valid, used, fields⟩ := diff
  rw [fields]
  rfl

def dynamicTag (last : Bool) : List Bool := natBits (if last then 5 else 4) 3

def dynamicBlockHeader (s : DeflateStatePtr) (last : Int32) (mb : Int32) : M Unit := do
  send_bits s (← iadd (DYN_TREES <<< 1) last) 3
  atCall s mb

theorem dynamic_header_arithmetic (last : Bool) :
    iadd (DYN_TREES <<< 1) (if last then 1 else 0) = pure (if last then 5 else 4) := by
  cases last <;> rfl

set_option maxRecDepth 10000 in
/-- The complete actual flush source contains exactly this dynamic header
fragment. Cost computation, branch selection, payload and tail stay in
source order. This equation does not assume that the dynamic path is taken. -/
theorem flush_block_dynamic_header_source (s : DeflateStatePtr) (buf : BPtr) (stored_len : UInt64) (last : Int32) :
    «_tr_flush_block» s buf stored_len last = (do
  -- int max_blindex = 0;
  let mut max_blindex : Int32 := 0
  let mut opt_lenb : UInt64 := 0
  let mut static_lenb : UInt64 := 0
  if (← rd s).level.toInt > 0 then
    -- if (s->strm->data_type == Z_UNKNOWN) s->strm->data_type = detect_data_type(s);
    let strm := (← rd s).strm
    if (← ldZStream strm).data_type == Z_UNKNOWN then
      let t ← detect_data_type s
      stZStream strm { (← ldZStream strm) with data_type := t }
    build_tree s (← pLdesc s)
    build_tree s (← pDdesc s)
    max_blindex ← build_bl_tree s
    -- opt_lenb = (s->opt_len + 3 + 7) >> 3; static_lenb = (s->static_len + 3 + 7) >> 3;
    opt_lenb := ((← rd s).opt_len + 3 + 7) >>> 3
    static_lenb := ((← rd s).static_len + 3 + 7) >>> 3
    -- if (static_lenb <= opt_lenb || s->strategy == Z_FIXED) opt_lenb = static_lenb;
    if static_lenb ≤ opt_lenb ∨ (← rd s).strategy == Z_FIXED then opt_lenb := static_lenb
  else
    -- opt_lenb = static_lenb = stored_len + 5;
    opt_lenb := stored_len + 5
    static_lenb := stored_len + 5
  if stored_len + 4 ≤ opt_lenb ∧ buf != .null then
    «_tr_stored_block» s buf stored_len last
  else if static_lenb == opt_lenb then
    fixedBlockPayload s last
  else
    dynamicBlockHeader s last max_blindex
    compress_block s (← pLtree s) (← pDtree s)
  flushBlockTail s last) := by
  rw [flush_block_source]
  unfold dynamicBlockHeader atCall
  simp only [M_bind_assoc, M_pure_bind, merge_ite_bind]

/-- The real dynamic tag and all three count arguments precede the real
header writer. Exact combined bit room is sufficient; no call contract is
assumed. The same source arrays remain available for the payload. -/
theorem dynamic_block_header_emit {h : Heap} {id b : Nat} {d : DeflateState} {buf : Array UInt8}
    {mb : Int32} (trees : TreesInvAt h id d b buf) (data : PreparedHeaderData d mb) (last : Bool)
    (room : 8 * d.pending.toNat + d.bi_valid.toInt.toNat + 3 +
      (dynamicHeaderBits d mb).length ≤ 8 * buf.size) :
    Emit id b (dynamicBlockHeader (Sp id) (if last then 1 else 0) mb) h d buf
      (dynamicTag last ++ dynamicHeaderBits d mb)
      (d.bi_valid.toInt.toNat + 3 + (dynamicHeaderBits d mb).length) := by
  have tag := send_bits_emit trees (if last then 5 else 4) 3 (by decide +kernel) (by decide +kernel)
    (by cases last <;> decide +kernel) (by change _ + (3 : Nat) ≤ _; omega)
  have tagBits : natBits (v16 (if last then 5 else 4)) (3 : Int32).toInt.toNat = dynamicTag last := by
    cases last <;> decide +kernel
  rw [tagBits] at tag
  obtain ⟨middleHeap, middle, middleBuf, tagRun, tagTrace⟩ := (EmitState.start trees).step tag
  have dataM := data.bitsDiff tagTrace.fields
  have bitsM := dynamicHeaderBits_bitsDiff mb tagTrace.fields
  have tagLength : (dynamicTag last).length = 3 := by simp only [dynamicTag, natBits_length]
  simp only [List.nil_append] at tagTrace
  have roomM : 8 * middle.pending.toNat + middle.bi_valid.toInt.toNat +
      (dynamicHeaderBits middle mb).length ≤ 8 * middleBuf.size := by
    rw [bitsM]
    apply tagTrace.room _ (3 + (dynamicHeaderBits d mb).length)
    · rw [tagLength]
      exact Nat.le_refl _
    · omega
  have header := atCall_emit tagTrace.inv mb _ _ _ dataM.all (by have := data.minimum; omega) roomM
  change Emit id b (atCall (Sp id) mb) middleHeap middle middleBuf (dynamicHeaderBits middle mb)
    (middle.bi_valid.toInt.toNat + (dynamicHeaderBits middle mb).length) at header
  rw [bitsM] at header
  obtain ⟨after, result, output, headerRun, headerTrace⟩ := tagTrace.step header
  have run : dynamicBlockHeader (Sp id) (if last then 1 else 0) mb h = .ok ((), after) := by
    unfold dynamicBlockHeader
    simp only [dynamic_header_arithmetic, bind_app, pure_app, tagRun]
    exact headerRun
  have emitted := headerTrace.emit run
  simpa only [List.length_append, tagLength, Nat.add_assoc] using emitted

end Zlib.Trees.Proofs
