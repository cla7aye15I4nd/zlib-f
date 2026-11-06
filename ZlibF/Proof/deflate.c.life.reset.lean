import ZlibF.Proof.«deflate.c.base»
import ZlibF.Proof.«trees.c.block»

/-!
# deflate.c: `lm_init`, `deflateResetKeep`, `deflateReset`
-/

namespace Zlib.Deflate.Spec
open C

/-- The head array after `CLEAR_HASH`: the first `hash_size` entries are 0 (`head[hash_size - 1] = NIL` and the
`memset` of the entries before it); the array has the same size. -/
def clearHead (qa : Array UInt16) (hs : Nat) : Array UInt16 := fillRange (qa.set! (hs - 1) 0) 0 (hs - 1) 0

/-- The state record after `lm_init`: `window_size = 2 * w_size`, the hash is cleared (`slid = 0`), `matches = 0`, the
tuning fields come from the table row of the level, and the position and match fields are reset. -/
def lmD (d : DeflateState) : DeflateState :=
  let c := Zlib.Deflate.configuration_table[d.level.toInt.toNat]!
  { d with window_size := 2 * d.w_size.toUInt64, slid := 0, «matches» := 0, max_lazy_match := c.max_lazy.toUInt32,
           good_match := c.good_length.toUInt32, nice_match := c.nice_length.toUInt32.toInt32,
           max_chain_length := c.max_chain.toUInt32, strstart := 0, block_start := 0, lookahead := 0, insert := 0,
           match_length := Zlib.Deflate.MIN_MATCH_u - 1, prev_length := Zlib.Deflate.MIN_MATCH_u - 1,
           match_available := 0, ins_h := 0 }


/-- `abs (wrap)`: `deflateResetKeep` makes the wrapper positive again (`wrap` is negative once the trailer was written). -/
def absWrap (w : Int32) : Int32 := if w < 0 then -w else w

/-- The state record after the first statements of `deflateResetKeep` (up to the wrapper): the pending output is dropped and
the wrapper is positive. -/
def rkMid (d : DeflateState) : DeflateState :=
  { d with pending := 0, pending_out := d.pending_buf, wrap := absWrap d.wrap }

/-- The state record after the statements of `deflateResetKeep` that follow the update of `status`, from the record `d3` that
has the new `status`: `last_flush = -2`, `gzhead = NULL`, then `_tr_init` (given the three code arrays that `init_block`
produced: their size is the C size, `Freq` is 0 except `dyn_ltree[END_BLOCK]`, which is 1): the descriptors point to the
arrays of the record, the bit buffer is empty; `matches` is kept at level 0 and cleared otherwise, `block_start = strstart`,
and the match state is reset. -/
def rkPost3 (id : Nat) (d3 : DeflateState) (a1 a2 a3 : Array CtData) : DeflateState :=
  let d4 : DeflateState := { d3 with last_flush := -2, gzhead := none }
  let dT := Zlib.Trees.Proofs.Out.ibRec (Zlib.Trees.Proofs.Out.trInitRec id d4) a1 a2 a3
  { dT with «matches» := if d3.level == 0 then d3.«matches» else 0, block_start := dT.strstart.toUInt64.toInt64,
            lookahead := 0, match_length := Zlib.Deflate.MIN_MATCH_u - 1, prev_length := Zlib.Deflate.MIN_MATCH_u - 1,
            match_available := 0 }

/-- The state record after the rest of `deflateResetKeep`, from the record `d2` after the wrapper: `status` is the gzip or
zlib header state, then `rkPost3`. -/
def rkPost (id : Nat) (d2 : DeflateState) (a1 a2 a3 : Array CtData) : DeflateState :=
  rkPost3 id { d2 with status := if d2.wrap == 2 then GZIP_STATE else INIT_STATE } a1 a2 a3

/-- The stream record after `deflateResetKeep`: the counters and `msg` are cleared, `data_type = Z_UNKNOWN`, and `adler` is the
checksum of nothing (1, or 0 for a gzip stream). -/
def rkZ (z : ZStream) (d : DeflateState) : ZStream :=
  { z with total_in := 0, total_out := 0, msg := .null, data_type := Z_UNKNOWN,
           adler := if absWrap d.wrap == 2 then 0 else 1 }

end Zlib.Deflate.Spec

namespace Zlib.Deflate.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec

theorem u32_sub_one {x : UInt32} (hx : 1 ≤ x.toNat) : (x - 1).toNat = x.toNat - 1 := by
  rw [UInt32.toNat_sub_of_le x 1 (by rw [UInt32.le_iff_toNat_le]; simp; omega)]
  simp

/-- The heap with the block of words `q` replaced. -/
def setW (h : Heap) (q : Nat) (a : Array UInt16) : Heap := { h with words := upd h.words q (some a) }

@[simp] theorem setW_dstates (h : Heap) (q : Nat) (a : Array UInt16) : (setW h q a).dstates = h.dstates := rfl
@[simp] theorem setW_words_same (h : Heap) (q : Nat) (a : Array UInt16) : (setW h q a).words q = some a := by
  simp [setW]
@[simp] theorem setW_bytes (h : Heap) (q : Nat) (a : Array UInt16) : (setW h q a).bytes = h.bytes := rfl
@[simp] theorem setW_ro (h : Heap) (q : Nat) (a : Array UInt16) : (setW h q a).ro = h.ro := rfl
theorem Space_put_words (h : Heap) (q : Nat) (a : Array UInt16) : Space.put h (WRef.blk q) a = setW h q a := rfl

/-- `CLEAR_HASH(s)` on a state whose `head` is a block of at least `hash_size` words (and `hash_size` is not 0). -/
theorem clearHash_run {h : Heap} {ds : Nat} {d : DeflateState} {q : Nat} {qa : Array UInt16}
    (hs : h.dstates ds = some d) (hq : d.head = .ref (.blk q) 0) (hqa : h.words q = some qa)
    (h1 : 1 ≤ d.hash_size.toNat) (h2 : d.hash_size.toNat ≤ qa.size) :
    CLEAR_HASH (some (.tab ds)) h =
      .ok ((), setD (setW h q (clearHead qa d.hash_size.toNat)) ds { d with slid := 0 }) := by
  have hn : (d.hash_size - 1).toNat = d.hash_size.toNat - 1 := u32_sub_one h1
  have e1 : padd (Ptr.ref (WRef.blk q) 0) (d.hash_size.toNat - 1) h = .ok (Ptr.ref (WRef.blk q) (0 + (d.hash_size.toNat - 1)), h) :=
    Ptr.add_nat_ok (h := h) (r := WRef.blk q) (a := qa) (off := 0) (n := d.hash_size.toNat - 1) hqa (by omega)
  have e2 := Ptr.store_ok (h := h) (r := WRef.blk q) (a := qa) (off := 0 + (d.hash_size.toNat - 1)) (v := (0 : UInt16))
    hqa rfl (by omega)
  have e3 := Ptr.fill_ok (h := setW h q (qa.set! (0 + (d.hash_size.toNat - 1)) 0))
    (r := WRef.blk q) (a := qa.set! (0 + (d.hash_size.toNat - 1)) 0) (off := 0) (n := d.hash_size.toNat - 1) (v := (0 : UInt16))
    (by simp [Space.get, setW]) rfl (by simp; omega)
  rw [Space_put_words] at e2 e3
  unfold CLEAR_HASH
  simp only [bind_app, ldD_eq, hs]
  rw [hq, hn, e1]
  simp only []
  rw [e2]
  simp only []
  rw [e3]
  simp only []
  rw [wrD_eq]
  simp only [setW_dstates, hs]
  simp [setW, clearHead, setD, upd_upd, hq]

theorem config_at_run (h : Heap) {level : Int32} (h0 : 0 ≤ level.toInt) (h1 : level.toInt ≤ 9) :
    config_at level h = .ok (Zlib.Deflate.configuration_table[level.toInt.toNat]!, h) := by
  unfold config_at
  simp [show 0 ≤ level.toInt ∧ level.toInt < 10 from ⟨h0, by omega⟩]

theorem lm_init_run {h : Heap} {ds : Nat} {d : DeflateState} {w p q b : Nat} {qa : Array UInt16}
    (hs : h.dstates ds = some d) (hB : DBlocks h d w p q b) (hqa : h.words q = some qa)
    (hl0 : 0 ≤ d.level.toInt) (hl1 : d.level.toInt ≤ 9)
    (h1 : 1 ≤ d.hash_size.toNat) (h2 : d.hash_size.toNat ≤ qa.size) :
    lm_init (some (.tab ds)) h = .ok ((), setD (setW h q (clearHead qa d.hash_size.toNat)) ds (lmD d)) := by
  have hs1 : (setD h ds { d with window_size := 2 * d.w_size.toUInt64 }).dstates ds = some { d with window_size := 2 * d.w_size.toUInt64 } :=
    setD_dstates_same _ _ _
  have hc := clearHash_run (h := setD h ds { d with window_size := 2 * d.w_size.toUInt64 }) (ds := ds)
    (d := { d with window_size := 2 * d.w_size.toUInt64 }) (q := q) (qa := qa) hs1 hB.head (by simpa using hqa) h1 h2
  unfold lm_init
  simp only [wrD_eq, bind_app, hs]
  rw [hc]
  simp only [wrD_eq, rdD_eq, bind_app, setD_dstates_same, setW_dstates, setD_setD]
  rw [config_at_run _ hl0 hl1]
  simp only [wrD_eq, rdD_eq, bind_app, setD_dstates_same, setW_dstates, setD_setD]
  simp [lmD, setD, setW, clearHead, hs, upd_upd]

theorem toNat_two_mul_toUInt64 (x : UInt32) : (2 * x.toUInt64).toNat = 2 * x.toNat := by
  rw [UInt64.toNat_mul]
  have := UInt32.toNat_lt x
  simp
  omega

theorem size_clearHead (qa : Array UInt16) (hs : Nat) : (clearHead qa hs).size = qa.size := by
  unfold clearHead
  rw [size_fillRange]
  simp

theorem _root_.Zlib.Deflate.Spec.DStInv.lm {h : Heap} {ds : Nat} {d : DeflateState} (hI : DStInv h ds d) :
    DStInv h ds (lmD d) := by
  have e : (lmD d).window_size.toNat = 2 * d.w_size.toNat := toNat_two_mul_toUInt64 d.w_size
  exact { hI with
    wsz := e
    hw := by rw [e]; rw [← hI.wsz]; exact hI.hw
    blocks := hI.blocks_keys rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl }

/-- **lm_init, safety and specification.** On a state of a stream with the invariant the call never faults. It clears
the hash heads (the first `hash_size` entries of the `head` block become 0, the block keeps its size), sets
`window_size = 2 * w_size`, `matches = 0`, loads `max_lazy_match`, `good_match`, `nice_match` and `max_chain_length` from the
configuration table row of `level`, and sets `strstart`, `block_start`, `lookahead` and `insert` to 0, `match_length` and
`prev_length` to `MIN_MATCH - 1`, `match_available` and `ins_h` to 0. The record is `lmD d`; the heap is the old one with
the `head` block replaced (`clearHead`) and the state record replaced. The stream is initialised again with the
invariants intact; the live blocks are the same. -/
theorem lm_init_safe {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (hG : DGood h r ds z d) :
    ∃ q qa h', C.run (lm_init (some (.tab ds))) h = .ok ((), h') ∧ d.head = .ref (.blk q) 0 ∧ h.words q = some qa ∧
      h' = setD (setW h q (clearHead qa d.hash_size.toNat)) ds (lmD d) ∧
      DGood h' r ds z (lmD d) ∧ (∀ b, h'.live b ↔ h.live b) := by
  have hI := hG.inv
  obtain ⟨w, p, q, b, hB⟩ := hI.blocks
  obtain ⟨qa, hqa, hqz⟩ := hB.qa
  have h1 : 1 ≤ d.hash_size.toNat := by
    have := hI.hsize; have : 2 ^ d.hash_bits.toNat > 0 := Nat.two_pow_pos _; omega
  refine ⟨q, qa, _, lm_init_run hG.live.hs hB hqa hI.level_lo hI.level_hi h1 (Nat.le_of_eq hqz.symm), hB.head, hqa, rfl, ?_, ?_⟩
  · have hG1 := hG.words_set q (clearHead qa d.hash_size.toNat) qa hqa (size_clearHead _ _)
    have := hG1.setD' (d' := lmD d) rfl hG.live.status (hI.lm.words_set q _ qa hqa (size_clearHead _ _)) (by trkeep)
    simpa [setD, setW] using this
  · intro x
    exact ((shape_setW hqa _).trans (shape_setD (d0 := d) (by simpa using hG.live.hs) _)).live x

open Zlib.Trees (_tr_init)

/-- The part of `deflateResetKeep` from the store of `adler` on. -/
def rkTail2 (strm : ZStreamPtr) (s : DeflateStatePtr) (adler : UInt64) : M Int32 := do
  zwr strm (fun z => { z with adler })
  wr s (fun d => { d with last_flush := -2, gzhead := none })
  let d ← ldDeflateState s
  let «matches» : UInt32 := if d.level == 0 then d.«matches» else 0
  _tr_init s
  wr s (fun d => { d with «matches» := «matches» })
  wr s (fun d => { d with block_start := d.strstart.toUInt64.toInt64, lookahead := 0,
                          match_length := MIN_MATCH_u - 1, prev_length := MIN_MATCH_u - 1, match_available := 0 })
  return Z_OK

/-- The part of `deflateResetKeep` from the status on. -/
def rkTail (strm : ZStreamPtr) (s : DeflateStatePtr) : M Int32 := do
  wr s (fun d => { d with status := if d.wrap == 2 then GZIP_STATE else INIT_STATE })
  let adler ← if (← rd s (·.wrap)) == 2 then Zlib.Crc32.crc32 0 (Ptr.null : BPtr) 0
    else Zlib.Adler32.adler32 0 (Ptr.null : BPtr) 0
  rkTail2 strm s adler

theorem deflateResetKeep_eq (strm : ZStreamPtr) : deflateResetKeep strm = (do
    if (← deflateStateCheck strm) != 0 then return Z_STREAM_ERROR
    zwr strm (fun z => { z with total_in := 0, total_out := 0, msg := .null, data_type := Z_UNKNOWN })
    let s ← castDeflateState (← zrd strm (·.state))
    wr s (fun d => { d with pending := 0, pending_out := d.pending_buf })
    let d ← ldDeflateState s
    if d.wrap < 0 then
      let w ← ineg d.wrap
      wr s (fun d => { d with wrap := w })
    rkTail strm s) := by
  rfl

theorem crc32_null : Zlib.Crc32.crc32 0 (Ptr.null : BPtr) 0 = (pure 0 : M UInt64) := by
  unfold Zlib.Crc32.crc32 Zlib.Crc32.crc32_z
  simp

theorem adler32_null : Zlib.Adler32.adler32 0 (Ptr.null : BPtr) 0 = (pure 1 : M UInt64) := by
  unfold Zlib.Adler32.adler32 Zlib.Adler32.adler32_z
  simp


theorem trSetD_eq (h : Heap) (id : Nat) (d : DeflateState) : Zlib.Trees.Proofs.Out.setD h id d = setD h id d := rfl

theorem rkTail2_run {H : Heap} {r : ZStreamRef} {ds : Nat} {z' : ZStream} {d3 : DeflateState} {b : Nat} {buf : Array UInt8}
    (hz : r.get H = some z') (hb : Zlib.Trees.Proofs.Out.TreesBase H ds d3 b buf) (v : UInt64) :
    ∃ a1 a2 a3, rkTail2 (some r) (some (.tab ds)) v H =
      .ok (Z_OK, setD (r.put H { z' with adler := v }) ds (rkPost3 ds d3 a1 a2 a3)) ∧
      a1.size = 573 ∧ a2.size = 61 ∧ a3.size = 39 := by
  have hd := hb.dstate
  have hb2 : Zlib.Trees.Proofs.Out.TreesBase (setD (r.put H { z' with adler := v }) ds { d3 with last_flush := -2, gzhead := none })
      ds { d3 with last_flush := -2, gzhead := none } b buf :=
    ⟨by simp [setD], hb.wf, by simpa using hb.static, hb.pbuf, by simpa using hb.bytes, by simpa using hb.rw, hb.size,
      hb.psize, hb.sym, hb.lit_lo, hb.lit_hi, hb.sym_end, hb.pending_le⟩
  obtain ⟨a1, a2, a3, d', e, -, hd', s1, s2, s3⟩ := Zlib.Trees.Proofs.Out.tr_init_spec hb2
  refine ⟨a1, a2, a3, ?_, s1, s2, s3⟩
  rw [trSetD_eq] at e
  unfold rkTail2
  simp only [bind_app, zwr_eq, hz, wrD_eq, rdD_eq, ldD_eq, ZStreamRef.put_dstates, hd, setD_dstates_same, ZStreamRef.get_setD, e, pure_app, setD_setD]
  subst hd'
  simp [rkPost3, setD_setD]

theorem rkTail_run {H : Heap} {r : ZStreamRef} {ds : Nat} {z' : ZStream} {d2 : DeflateState} {b : Nat} {buf : Array UInt8}
    (hz : r.get H = some z') (hb : Zlib.Trees.Proofs.Out.TreesBase H ds d2 b buf) :
    ∃ a1 a2 a3, rkTail (some r) (some (.tab ds)) H =
      .ok (Z_OK, setD (r.put H { z' with adler := if d2.wrap == 2 then 0 else 1 }) ds (rkPost ds d2 a1 a2 a3)) ∧
      a1.size = 573 ∧ a2.size = 61 ∧ a3.size = 39 := by
  have hd := hb.dstate
  have hb3 : Zlib.Trees.Proofs.Out.TreesBase (setD H ds { d2 with status := if d2.wrap == 2 then GZIP_STATE else INIT_STATE })
      ds { d2 with status := if d2.wrap == 2 then GZIP_STATE else INIT_STATE } b buf :=
    ⟨by simp [setD], hb.wf, by simpa using hb.static, hb.pbuf, by simpa using hb.bytes, by simpa using hb.rw, hb.size,
      hb.psize, hb.sym, hb.lit_lo, hb.lit_hi, hb.sym_end, hb.pending_le⟩
  have hz3 : r.get (setD H ds { d2 with status := if d2.wrap == 2 then GZIP_STATE else INIT_STATE }) = some z' := by
    simpa using hz
  obtain ⟨a1, a2, a3, e, s1, s2, s3⟩ := rkTail2_run hz3 hb3 (if d2.wrap == 2 then 0 else 1)
  refine ⟨a1, a2, a3, ?_, s1, s2, s3⟩
  unfold rkTail
  by_cases hc : (d2.wrap == 2) = true
  · simp only [hc, ↓reduceIte] at e
    simp only [bind_app, wrD_eq, rdD_eq, hd, setD_dstates_same, hc, ↓reduceIte, crc32_null, pure_app]
    rw [e]
    simp [ZStreamRef.put_setD, setD_setD, rkPost, hc]
  · have hc' : (d2.wrap == 2) = false := by simpa using hc
    simp only [hc', Bool.false_eq_true, ↓reduceIte] at e
    simp only [bind_app, wrD_eq, rdD_eq, hd, setD_dstates_same, hc', Bool.false_eq_true, ↓reduceIte, adler32_null, pure_app]
    rw [e]
    simp [ZStreamRef.put_setD, setD_setD, rkPost, hc]

theorem ineg_neg {w : Int32} (h1 : -2 ≤ w.toInt) (h2 : w.toInt < 0) : ineg w = (pure (-w) : M Int32) := by
  unfold ineg chk32
  have e : (-w).toInt = - w.toInt := by
    rw [Int32.toInt_neg]
    have := w.toInt_lt
    have := w.le_toInt
    rw [Int.bmod_eq_of_le (by omega) (by omega)]
  have : -2147483648 ≤ -w.toInt ∧ -w.toInt ≤ 2147483647 := by omega
  simp only [this, and_self, ↓reduceIte]
  congr 1
  apply Int32.toInt_inj.mp
  rw [e, Int32.toInt_ofInt]
  rw [Int.bmod_eq_of_le (by simp only [Int32.size]; omega) (by simp only [Int32.size]; omega)]

theorem resetKeep_run' {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState} {b : Nat}
    {buf : Array UInt8} (hL : DLive h r ds z d) (hB : Zlib.Trees.Proofs.Out.TreesBase h ds d b buf)
    (hw1 : -2 ≤ d.wrap.toInt) (hw2 : d.wrap.toInt ≤ 2) :
    ∃ a1 a2 a3, deflateResetKeep (some r) h =
      .ok (Z_OK, setD (r.put h (rkZ z d)) ds (rkPost ds (rkMid d) a1 a2 a3)) ∧
      a1.size = 573 ∧ a2.size = 61 ∧ a3.size = 39 := by
  have hbm : Zlib.Trees.Proofs.Out.TreesBase (setD (r.put h { z with total_in := 0, total_out := 0, msg := .null, data_type := Z_UNKNOWN }) ds (rkMid d))
      ds (rkMid d) b buf :=
    ⟨by simp [setD], hB.wf, by simpa using hB.static, hB.pbuf, by simpa using hB.bytes, by simpa using hB.rw, hB.size,
      hB.psize, hB.sym, hB.lit_lo, hB.lit_hi, hB.sym_end, by simp [rkMid]⟩
  have hzm : r.get (setD (r.put h { z with total_in := 0, total_out := 0, msg := .null, data_type := Z_UNKNOWN }) ds (rkMid d)) =
      some { z with total_in := 0, total_out := 0, msg := .null, data_type := Z_UNKNOWN } := by
    simp [ZStreamRef.get_put, hL.hz]
  obtain ⟨a1, a2, a3, e, s1, s2, s3⟩ := rkTail_run hzm hbm
  refine ⟨a1, a2, a3, ?_, s1, s2, s3⟩
  rw [deflateResetKeep_eq]
  by_cases hw : d.wrap < 0
  · have hw' : -2 ≤ d.wrap.toInt ∧ d.wrap.toInt < 0 := ⟨hw1, (Int32.lt_iff_toInt_lt.mp hw)⟩
    simp only [bind_app, stateCheck_live hL, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, zwr_eq, hL.hz, zrd_eq,
      ZStreamRef.get_put_same hL.hz, hL.zst, castD, wrD_eq, ZStreamRef.put_dstates, hL.hs, setD_dstates_same, ldD_eq, hw,
      ineg_neg hw'.1 hw'.2, pure_app, setD_setD]
    simp only [rkMid, absWrap, hw, ↓reduceIte, hL.zst] at e
    rw [e]
    simp [rkZ, rkMid, absWrap, hw, ZStreamRef.put_setD, ZStreamRef.put_put, hL.zst]
  · simp only [bind_app, stateCheck_live hL, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, zwr_eq, hL.hz, zrd_eq,
      ZStreamRef.get_put_same hL.hz, hL.zst, castD, wrD_eq, ZStreamRef.put_dstates, hL.hs, setD_dstates_same, ldD_eq, hw,
      pure_app, setD_setD]
    simp only [rkMid, absWrap, hw, ↓reduceIte, hL.zst] at e
    rw [e]
    simp [rkZ, rkMid, absWrap, hw, ZStreamRef.put_setD, ZStreamRef.put_put, hL.zst]

theorem resetKeep_run {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (hG : DGood h r ds z d) :
    ∃ a1 a2 a3, deflateResetKeep (some r) h =
      .ok (Z_OK, setD (r.put h (rkZ z d)) ds (rkPost ds (rkMid d) a1 a2 a3)) ∧
      a1.size = 573 ∧ a2.size = 61 ∧ a3.size = 39 := by
  obtain ⟨d0, b, buf, hB, hR⟩ := hG.trees
  have e0 : d0 = d := Option.some.inj (hB.dstate.symm.trans hG.live.hs)
  rw [e0] at hB
  exact resetKeep_run' hG.live hB hG.inv.wrap_lo hG.inv.wrap_hi

theorem absWrap_range {w : Int32} (h1 : -2 ≤ w.toInt) (h2 : w.toInt ≤ 2) :
    0 ≤ (absWrap w).toInt ∧ (absWrap w).toInt ≤ 2 := by
  unfold absWrap
  by_cases hw : w < 0
  · have hw' := Int32.lt_iff_toInt_lt.mp hw
    simp at hw'
    have : (-w).toInt = - w.toInt := by
      rw [Int32.toInt_neg]
      have := w.toInt_lt
      have := w.le_toInt
      rw [Int.bmod_eq_of_le (by omega) (by omega)]
    rw [if_pos hw, this]; omega
  · have hw' : ¬ w.toInt < 0 := fun h => hw (Int32.lt_iff_toInt_lt.mpr (by simpa using h))
    rw [if_neg hw]; omega

theorem _root_.Zlib.Deflate.Spec.DStInv.resetKeep {h : Heap} {ds : Nat} {d : DeflateState} (hI : DStInv h ds d) (a1 a2 a3 : Array CtData)
    (s1 : a1.size = 573) (s2 : a2.size = 61) (s3 : a3.size = 39) :
    DStInv h ds (rkPost ds (rkMid d) a1 a2 a3) := by
  obtain ⟨w, p, q, b, hB⟩ := hI.blocks
  obtain ⟨wf1, wf2, wf3, wf4, wf5, wf6⟩ := hI.wf
  have hr := absWrap_range hI.wrap_lo hI.wrap_hi
  obtain ⟨_, hsb, hsl⟩ := hI.sym
  refine ⟨⟨s1, s2, s3, wf4, wf5, wf6⟩, hI.wbits_lo, hI.wbits_hi, hI.wsize, hI.wmask, hI.wsz, hI.hbits_lo, hI.hbits_hi,
    hI.hsize, hI.hmask, hI.hshift, hI.lit, hI.level_lo, hI.level_hi, hI.strat_lo, hI.strat_hi, hI.method, ?_, ?_, hI.hw,
    ⟨w, p, q, b, ?_⟩, ?_, ?_, ?_⟩
  · simp [rkPost, rkPost3, rkMid, Zlib.Trees.Proofs.Out.ibRec, Zlib.Trees.Proofs.Out.trInitRec]; have := hr.1; omega
  · simp [rkPost, rkPost3, rkMid, Zlib.Trees.Proofs.Out.ibRec, Zlib.Trees.Proofs.Out.trInitRec]; exact hr.2
  · obtain ⟨a1', a2', a3', a4', wa, r1, pa, qa, ba, r4, ps, wb, pq, ⟨off, po, pl⟩⟩ := hB
    refine ⟨a1', a2', a3', a4', wa, r1, pa, qa, ba, r4, ps, wb, pq, ⟨0, ?_, ?_⟩⟩
    · simp [rkPost, rkPost3, rkMid, Zlib.Trees.Proofs.Out.ibRec, Zlib.Trees.Proofs.Out.trInitRec, a4']
    · simp [rkPost, rkPost3, rkMid, Zlib.Trees.Proofs.Out.ibRec, Zlib.Trees.Proofs.Out.trInitRec]
  · refine ⟨?_, ?_, ?_, ?_⟩
    · obtain ⟨b', hb1, hb2⟩ := hI.sym.1
      exact ⟨b', by simpa [rkPost, rkPost3, rkMid, Zlib.Trees.Proofs.Out.ibRec, Zlib.Trees.Proofs.Out.trInitRec] using hb1,
        by simpa [rkPost, rkPost3, rkMid, Zlib.Trees.Proofs.Out.ibRec, Zlib.Trees.Proofs.Out.trInitRec] using hb2⟩
    · simpa [rkPost, rkPost3, rkMid, Zlib.Trees.Proofs.Out.ibRec, Zlib.Trees.Proofs.Out.trInitRec] using hsb
    · simp [rkPost, rkPost3, rkMid, Zlib.Trees.Proofs.Out.ibRec, Zlib.Trees.Proofs.Out.trInitRec]
    · simp [rkPost, rkPost3, rkMid, Zlib.Trees.Proofs.Out.ibRec, Zlib.Trees.Proofs.Out.trInitRec]
  · simp [rkPost, rkPost3, rkMid, Zlib.Trees.Proofs.Out.ibRec, Zlib.Trees.Proofs.Out.trInitRec]
  · simp [rkPost, rkPost3, rkMid, Zlib.Trees.Proofs.Out.ibRec, Zlib.Trees.Proofs.Out.trInitRec, GzOk]

theorem mod_absWrap_status (d : DeflateState) : GoodStatus (if (absWrap d.wrap == 2) = true then GZIP_STATE else INIT_STATE) := by
  unfold GoodStatus
  split
  · exact Or.inr (Or.inl rfl)
  · exact Or.inl rfl

/-- **deflateResetKeep, safety and specification.** On an initialised stream with the invariant the call never faults and
returns `Z_OK`. The stream record gets `total_in = total_out = 0`, `msg = NULL`, `data_type = Z_UNKNOWN` and `adler` 1 (0 for
a gzip wrapper): `rkZ`. The state record is `rkPost`: the pending output is dropped (`pending = 0`, `pending_out =
pending_buf`), a negative wrapper becomes positive, `status` is the zlib or gzip header state, `last_flush = -2`, `gzhead =
NULL`, the trees are reset (`_tr_init`: empty bit buffer, no symbols, the code frequencies of the three arrays are 0 except
the end-of-block code, `opt_len = static_len = 0`), `matches` is kept at level 0 and cleared otherwise, `block_start =
strstart`, `lookahead = 0`, `match_length = prev_length = MIN_MATCH - 1`, `match_available = 0`. The window, the hash and
the other settings are kept. The stream is initialised again with the invariants intact, and the live blocks are the same
(no allocation, no free). -/
theorem deflateResetKeep_safe {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (hG : DGood h r ds z d) :
    ∃ a1 a2 a3 h', C.run (deflateResetKeep (some r)) h = .ok (Z_OK, h') ∧
      h' = setD (r.put h (rkZ z d)) ds (rkPost ds (rkMid d) a1 a2 a3) ∧ a1.size = 573 ∧ a2.size = 61 ∧ a3.size = 39 ∧
      DGood h' r ds (rkZ z d) (rkPost ds (rkMid d) a1 a2 a3) ∧ (∀ b, h'.live b ↔ h.live b) := by
  obtain ⟨a1, a2, a3, e, s1, s2, s3⟩ := resetKeep_run hG
  refine ⟨a1, a2, a3, _, e, rfl, s1, s2, s3, ?_, ?_⟩
  · have hI := hG.inv.resetKeep a1 a2 a3 s1 s2 s3
    obtain ⟨d0, b, buf, hB, hR⟩ := hG.trees
    have e0 : d0 = d := Option.some.inj (hB.dstate.symm.trans hG.live.hs)
    rw [e0] at hB hR
    have hS : Shape h (setD (r.put h (rkZ z d)) ds (rkPost ds (rkMid d) a1 a2 a3)) :=
      (shape_put hG.live.hz _).trans (shape_setD (by simpa using hG.live.hs) _)
    refine ⟨⟨?_, by simp, ?_, ?_, ?_, ?_, ?_⟩,
      DStInv.congr (h := h) (h' := setD (r.put h (rkZ z d)) ds (rkPost ds (rkMid d) a1 a2 a3)) (by simp) (by simp) (by simp) (by simp) hI,
      hS.uniq hG.uniq, hS.fresh (by simp) hG.fresh, ?_⟩
    · simp [ZStreamRef.get_put, hG.live.hz]
    · simpa [rkZ] using hG.live.zst
    · simpa [rkPost, rkPost3, rkMid, Zlib.Trees.Proofs.Out.ibRec, Zlib.Trees.Proofs.Out.trInitRec] using hG.live.back
    · exact mod_absWrap_status d
    · simpa [rkZ] using hG.live.zalloc
    · simpa [rkZ] using hG.live.zfree
    · refine ⟨_, b, buf, ⟨by simp, hI.wf, by simpa using hB.static, hB.pbuf, by simpa using hB.bytes, by simpa using hB.rw,
        hB.size, hB.psize, hB.sym, hB.lit_lo, hB.lit_hi, hB.sym_end,
        by simp [rkPost, rkPost3, rkMid, Zlib.Trees.Proofs.Out.ibRec, Zlib.Trees.Proofs.Out.trInitRec]⟩, ?_⟩
      refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩ <;>
        simp [rkPost, rkPost3, rkMid, Zlib.Trees.Proofs.Out.ibRec, Zlib.Trees.Proofs.Out.trInitRec]
  · intro x
    exact ((shape_put hG.live.hz _).trans (shape_setD (by simpa using hG.live.hs) _)).live x

/-- **deflateReset, safety and specification.** On an initialised stream with the invariant the call never faults and returns
`Z_OK`: it is `deflateResetKeep` (`rkZ`, `rkPost`) followed by `lm_init` (`lmD`: the hash heads are cleared, `window_size =
2 * w_size`, the tuning fields are reloaded from the table row of `level`, the position and the match state are reset). The
stream is initialised again with the invariants intact, and the live blocks are the same (no allocation, no free). -/
theorem deflateReset_safe {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (hG : DGood h r ds z d) :
    ∃ a1 a2 a3 q qa h', C.run (deflateReset (some r)) h = .ok (Z_OK, h') ∧
      a1.size = 573 ∧ a2.size = 61 ∧ a3.size = 39 ∧ d.head = .ref (.blk q) 0 ∧ h.words q = some qa ∧
      h' = setD (setW (setD (r.put h (rkZ z d)) ds (rkPost ds (rkMid d) a1 a2 a3)) q
        (clearHead qa d.hash_size.toNat)) ds (lmD (rkPost ds (rkMid d) a1 a2 a3)) ∧
      DGood h' r ds (rkZ z d) (lmD (rkPost ds (rkMid d) a1 a2 a3)) ∧ (∀ b, h'.live b ↔ h.live b) := by
  obtain ⟨a1, a2, a3, h1, e1, rfl, s1, s2, s3, hG1, hl1⟩ := deflateResetKeep_safe hG
  obtain ⟨q, qa, h2, e2, hq, hqa, rfl, hG2, hl2⟩ := lm_init_safe hG1
  have hq0 : d.head = .ref (.blk q) 0 := by
    simpa [rkPost, rkPost3, rkMid, Zlib.Trees.Proofs.Out.ibRec, Zlib.Trees.Proofs.Out.trInitRec] using hq
  have hqa0 : h.words q = some qa := by simpa using hqa
  have hhs : (rkPost ds (rkMid d) a1 a2 a3).hash_size = d.hash_size := by
    simp [rkPost, rkPost3, rkMid, Zlib.Trees.Proofs.Out.ibRec, Zlib.Trees.Proofs.Out.trInitRec]
  refine ⟨a1, a2, a3, q, qa, _, ?_, s1, s2, s3, hq0, hqa0, by rw [hhs], by simpa [hhs] using hG2, fun b => (hl2 b).trans (hl1 b)⟩
  have hz1 := hG1.live
  unfold deflateReset
  rw [C.run] at e1 ⊢
  simp only [bind_app, e1, beq_self_eq_true, ↓reduceIte, zrd_eq, hz1.hz, hz1.zst, castD, pure_app]
  rw [C.run] at e2
  rw [e2]

/-- **deflateResetKeep, refusal.** On a stream the check refuses: `Z_STREAM_ERROR`, nothing changes. -/
theorem deflateResetKeep_reject {h : Heap} {strm : ZStreamPtr} (hD : StreamDom h strm) (hN : ¬ DInitialised h strm) :
    C.run (deflateResetKeep strm) h = .ok (Z_STREAM_ERROR, h) := by
  rw [C.run, deflateResetKeep_eq]
  exact check_refuse hD hN _ _

/-- **deflateReset, refusal.** On a stream the check refuses: `Z_STREAM_ERROR`, nothing changes. -/
theorem deflateReset_reject {h : Heap} {strm : ZStreamPtr} (hD : StreamDom h strm) (hN : ¬ DInitialised h strm) :
    C.run (deflateReset strm) h = .ok (Z_STREAM_ERROR, h) := by
  have e := deflateResetKeep_reject hD hN
  unfold deflateReset
  rw [C.run] at e ⊢
  have hne : ¬ (Z_STREAM_ERROR = Z_OK) := by decide
  simp [bind_app, e, hne]

end Zlib.Deflate.Proofs
