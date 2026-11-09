import ZlibF.Proof.«compress.c.local-refill»
import ZlibF.Proof.«compress.c.local-refill-empty»
import ZlibF.Proof.«deflate.c.engine.fill-slide-call»

/-! # Real window sliding with local private representation

The source copy, signed block subtraction, insertion clamp and complete
slide_hash execution operate on the actual local private arrays. Old caller
identities may occupy several typed tables. No global Uniq is assumed.
-/
namespace ZlibF.Spec.Public.Proofs.CompressLocalSlide
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open Zlib.Deflate.Engine.Proofs ZlibF.Spec.Public
open ZlibF.Spec.Public.Proofs.CompressLocalInit
open ZlibF.Spec.Public.Proofs.CompressLocal
open ZlibF.Spec.Public.Proofs.CompressLocalHeader
open ZlibF.Spec.Public.Proofs.CompressLocalFill
open ZlibF.Spec.Public.Proofs.CompressLocalRefill
open ZlibF.Spec.Public.Proofs.CompressLocalRefillEmpty
open Zlib.Deflate.Proofs.DefaultInit
open Zlib.Trees.Proofs.Out (TreesBase)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1800000

/-- LocalState itself supplies the concrete private hash arrays. This
producer does not require caller-provided HashEnv or global uniqueness. -/
theorem local_hash_environment {h : Heap} {r : ZStreamRef} {cutoff ds : Nat}
    {z : ZStream} {d : DeflateState} (state : LocalState h cutoff r ds z d) :
    ∃ w p q wa pa qa, HashEnv h d w q p wa qa pa := by
  obtain ⟨w,p,q,b,blocks⟩ := state.inv.blocks
  obtain ⟨wa,window,windowSize⟩ := blocks.wa
  obtain ⟨pa,previous,previousSize⟩ := blocks.pa
  obtain ⟨qa,head,headSize⟩ := blocks.qa
  have positive : 1 ≤ d.w_size.toNat := by
    rw [state.inv.wsize]
    exact Nat.two_pow_pos _
  refine ⟨w,p,q,wa,pa,qa,blocks.win,window,blocks.wro,blocks.head,head,blocks.prev,previous,
    Ne.symm blocks.pq,by omega,by omega,?_,hash_parameters state.inv⟩
  rw [state.inv.wmask]
  omega

/-- Same-extent word-table replacement keeps the local private invariant. -/
theorem local_state_words_set {h : Heap} {cutoff ds : Nat} {r : ZStreamRef} {z : ZStream} {d : DeflateState}
    (state : LocalState h cutoff r ds z d) (x : Nat) (a old : Array UInt16)
    (get : h.words x = some old) (size : a.size = old.size) :
    LocalState (setW h x a) cutoff r ds z d := by
  have shape := shape_setW get a
  refine ⟨⟨?_,state.live.hs,state.live.zst,state.live.back,state.live.status,state.live.zalloc,state.live.zfree⟩,
    state.inv.words_set x a old get size,state.newUnique.shape shape,shape.fresh rfl state.fresh,
    TreesInv.words_set state.trees x a⟩
  cases r <;> simpa [ZStreamRef.get,setW] using state.live.hz
theorem local_slide_window_sizes {h : Heap} {r : ZStreamRef} {cutoff ds : Nat}
    {z : ZStream} {d : DeflateState} (state : LocalState h cutoff r ds z d) :
    512 ≤ d.w_size.toNat ∧ d.w_size.toNat ≤ 32768 := by
  constructor
  · rw [state.inv.wsize]
    exact Nat.pow_le_pow_right (n := 2) (by decide) state.inv.wbits_lo
  · rw [state.inv.wsize]
    exact Nat.pow_le_pow_right (n := 2) (by decide) state.inv.wbits_hi

theorem local_slide_threshold {h : Heap} {r : ZStreamRef} {cutoff ds : Nat}
    {z : ZStream} {d : DeflateState} (state : LocalState h cutoff r ds z d) :
    (d.w_size + (d.w_size - MIN_LOOKAHEAD_u)).toNat = 2 * d.w_size.toNat - 262 := by
  have bounds := local_slide_window_sizes state
  have sub : (d.w_size - MIN_LOOKAHEAD_u).toNat = d.w_size.toNat - 262 := by
    rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; change 262 ≤ _; omega)]
    rfl
  rw [UInt32.toNat_add, sub, Nat.mod_eq_of_lt (by omega)]
  omega

theorem local_fill_slide_counts {h : Heap} {r : ZStreamRef} {cutoff ds w : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8}
    (state : LocalState h cutoff r ds z d) (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa)
    (range : fillEnd d ≤ d.window_size.toNat)
    (taken : d.strstart ≥ d.w_size + (d.w_size - MIN_LOOKAHEAD_u)) :
    d.w_size.toNat + 1 ≤ d.strstart.toNat ∧
      (d.w_size - fillMore d).toNat = fillEnd d - d.w_size.toNat ∧
      (d.w_size - fillMore d).toNat ≤ d.w_size.toNat ∧
      d.w_size.toNat + (d.w_size - fillMore d).toNat ≤ wa.size ∧
      (slideState d).strstart.toNat = d.strstart.toNat - d.w_size.toNat ∧
      fillEnd (slideState d) = fillEnd d - d.w_size.toNat ∧
      fillEnd (slideState d) ≤ d.w_size.toNat ∧
      (fillMore d + d.w_size).toNat = d.window_size.toNat - fillEnd (slideState d) ∧
      ¬ (slideState d).strstart ≥ d.w_size + (d.w_size - MIN_LOOKAHEAD_u) := by
  have bounds := local_slide_window_sizes state
  have extent := local_window_extent state win get
  have more := local_fill_more_nat state win get range
  have threshold := local_slide_threshold state
  rw [GE.ge, UInt32.le_iff_toNat_le, threshold] at taken
  have wsz := state.inv.wsz
  have current : fillEnd d = d.strstart.toNat + d.lookahead.toNat := rfl
  have smaller : (fillMore d).toNat ≤ d.w_size.toNat := by omega
  have sub : (d.w_size - fillMore d).toNat = d.w_size.toNat - (fillMore d).toNat :=
    UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr smaller)
  have start : (slideState d).strstart.toNat = d.strstart.toNat - d.w_size.toNat := by
    change (d.strstart - d.w_size).toNat = _
    exact UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by omega))
  have endpoint : fillEnd (slideState d) = fillEnd d - d.w_size.toNat := by
    change (slideState d).strstart.toNat + d.lookahead.toNat = _
    rw [start]
    omega
  have added : (fillMore d + d.w_size).toNat = (fillMore d).toNat + d.w_size.toNat := by
    rw [UInt32.toNat_add, Nat.mod_eq_of_lt (by omega)]
  refine ⟨by omega, by omega, by omega, by omega, start, endpoint, by omega, by omega, ?_⟩
  rw [GE.ge, UInt32.le_iff_toNat_le, threshold, start]
  omega

theorem local_block_start_slide_run {h : Heap} {r : ZStreamRef} {cutoff ds b : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8} {xs : List Symbol} {credit : Int}
    (state : LocalState h cutoff r ds z d) (base : TreesBase h ds d b buf)
    (ledger : SymbolLedger buf d xs) (count : d.sym_next.toNat ≤ d.sym_end.toNat)
    (balance : BlockBalance d xs credit) (lo : 0 ≤ credit) (hi : credit ≤ 1)
    (range : d.strstart.toNat + d.lookahead.toNat ≤ d.window_size.toNat) :
    let value := d.block_start.toInt - (d.w_size.toNat : Int)
    lsub d.block_start d.w_size.toUInt64.toInt64 = pure (Int64.ofInt value) ∧
      (Int64.ofInt value).toInt = value := by
  have bounds := block_start_bounds base ledger count balance lo hi
  have ws : d.w_size.toNat ≤ 32768 := by
    rw [state.inv.wsize]
    calc 2 ^ d.w_bits.toNat ≤ 2 ^ 15 := Nat.pow_le_pow_right (by decide) state.inv.wbits_hi
         _ = 32768 := by decide
  have wsz := state.inv.wsz
  have cast : d.w_size.toUInt64.toInt64.toInt = (d.w_size.toNat : Int) := by
    rw [Int64.toInt, UInt64.toBitVec_toInt64, BitVec.toInt_eq_toNat_of_lt]
    · simp
    · simp
      omega
  dsimp only
  have valueLo : -9223372036854775808 ≤ d.block_start.toInt - (d.w_size.toNat : Int) := by omega
  have valueHi : d.block_start.toInt - (d.w_size.toNat : Int) ≤ 9223372036854775807 := by omega
  refine ⟨?_, ?_⟩
  · unfold lsub chk64
    rw [cast]
    simp only [valueLo, valueHi, and_self, ite_true]
  · rw [Int64.toInt_ofInt]
    exact Int.bmod_eq_of_le (by change -9223372036854775808 ≤ _; omega)
      (by change _ < 9223372036854775808; omega)

theorem local_fill_slide_run {h : Heap} {r : ZStreamRef} {cutoff ds w p q b : Nat}
    {z : ZStream} {d : DeflateState} {wa buf : Array UInt8} {pa qa : Array UInt16}
    {xs : List Symbol} {credit : Int}
    (state : LocalState h cutoff r ds z d) (env : HashEnv h d w q p wa qa pa)
    (base : TreesBase h ds d b buf) (ledger : SymbolLedger buf d xs)
    (count : d.sym_next.toNat ≤ d.sym_end.toNat) (balance : BlockBalance d xs credit)
    (lo : 0 ≤ credit) (hi : credit ≤ 1) (range : fillEnd d ≤ d.window_size.toNat)
    (taken : d.strstart ≥ d.w_size + (d.w_size - MIN_LOOKAHEAD_u)) :
    ∃ qa' pa', fillSlide (some (.tab ds)) d d.w_size (fillMore d) h =
      .ok ((), slideHeap h ds w p q d wa pa' qa') ∧
      qa'.size = qa.size ∧ pa'.size = pa.size ∧
      (∀ i, wfn qa' i = if i < d.hash_size.toNat then slideVal d.w_size (wfn qa i) else wfn qa i) ∧
      (∀ i, wfn pa' i = if i < d.w_size.toNat then slideVal d.w_size (wfn pa i) else wfn pa i) := by
  have geometry := local_fill_slide_counts state env.win env.wbytes range taken
  let copied := slideWindow d wa
  let hc := { h with bytes := upd h.bytes w (some copied) }
  let hp := setD hc ds (slideBeforeHash d)
  have add : padd d.window d.w_size.toNat h = .ok (.ref (.blk w) d.w_size.toNat, h) := by
    rw [env.win]
    simpa only [OkOn, padd, Nat.zero_add] using Ptr.add_nat_ok (off := 0) (n := d.w_size.toNat)
      (show Space.get h (BRef.blk w) = some wa from env.wbytes) (by omega)
  have copy : memcpyB d.window (.ref (.blk w) d.w_size.toNat) (d.w_size - fillMore d).toNat h =
      .ok ((), hc) := by
    rw [env.win]
    exact Ptr.memcpy_ok (od := 0) (os := d.w_size.toNat)
      (show Space.get h (BRef.blk w) = some wa from env.wbytes) env.wbytes env.wro
      (by omega) geometry.2.2.2.1 (Or.inr (Or.inl (by omega)))
  have signed := (local_block_start_slide_run state base ledger count balance lo hi range).1
  have getH : hp.words q = some qa := env.hwords
  have getP : hp.words p = some pa := env.pwords
  have bounds := local_slide_window_sizes state
  have hashPositive : 1 ≤ d.hash_size.toNat := by
    obtain ⟨bits, _, _, size, _, _⟩ := env.params.bits
    rw [size]
    exact Nat.two_pow_pos _
  obtain ⟨qa', pa', hash, sizeH, sizeP, viewH, viewP⟩ := slide_hash_ok (h := hp) (sr := ds)
    (d := slideBeforeHash d) (by simp [hp]) env.headp env.prevp getH getP env.hne
    env.hsize env.wsize hashPositive (by change 1 ≤ d.w_size.toNat; omega)
  refine ⟨qa', pa', ?_, sizeH, sizeP, viewH, viewP⟩
  have dsCopy : hc.dstates ds = some d := state.live.hs
  unfold fillSlide
  simp only [bind_app, add, copy, wrD_eq, rdD_eq, dsCopy, setD_dstates_same, setD_setD, signed, pure_app]
  simpa only [hp, hc, copied, slideBeforeHash, slideState, slideHeap, setD, setW, upd_upd] using hash

theorem local_slide_state {h : Heap} {r : ZStreamRef} {cutoff ds w p q : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8} {pa qa pa' qa' : Array UInt16}
    (state : LocalState h cutoff r ds z d) (env : HashEnv h d w q p wa qa pa)
    (sizeP : pa'.size = pa.size) (sizeH : qa'.size = qa.size) :
    LocalState (slideHeap h ds w p q d wa pa' qa') cutoff r ds z (slideState d) := by
  let hc := { h with bytes := upd h.bytes w (some (slideWindow d wa)) }
  have goodC : LocalState hc cutoff r ds z d := local_state_bytes_set state w (slideWindow d wa) wa env.wbytes
    (size_copyRange _ _ _ _ _)
  have goodH := local_state_words_set goodC q qa' qa env.hwords sizeH
  have getP : (setW hc q qa').words p = some pa := by
    simp only [setW, upd_ne _ _ _ _ env.hne.symm]
    exact env.pwords
  have goodP := local_state_words_set goodH p pa' pa getP sizeP
  have inv : DStInv (setW (setW hc q qa') p pa') ds (slideState d) :=
    { goodP.inv with blocks := goodP.inv.blocks_keys rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl }
  have stored := local_state_setZD (z' := z) (d' := slideState d) goodP rfl goodP.live.zalloc goodP.live.zfree rfl goodP.live.status inv (by trkeep)
  rwa [ZStreamRef.put_self goodP.live.hz] at stored

theorem local_slide_more_eq {h : Heap} {r : ZStreamRef} {cutoff ds w p q : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8} {pa qa pa' qa' : Array UInt16}
    (state : LocalState h cutoff r ds z d) (env : HashEnv h d w q p wa qa pa)
    (sizeP : pa'.size = pa.size) (sizeH : qa'.size = qa.size)
    (range : fillEnd d ≤ d.window_size.toNat)
    (taken : d.strstart ≥ d.w_size + (d.w_size - MIN_LOOKAHEAD_u)) :
    fillMore (slideState d) = fillMore d + d.w_size := by
  have counts := local_fill_slide_counts state env.win env.wbytes range taken
  have afterGood := local_slide_state state env sizeP sizeH
  have get : (slideHeap h ds w p q d wa pa' qa').bytes w = some (slideWindow d wa) := by simp [slideHeap]
  have afterRange : fillEnd (slideState d) ≤ (slideState d).window_size.toNat := by
    change fillEnd (slideState d) ≤ d.window_size.toNat
    have wsz := state.inv.wsz
    omega
  apply UInt32.toNat_inj.mp
  rw [local_fill_more_nat afterGood env.win get afterRange]
  exact counts.2.2.2.2.2.2.2.1.symm

theorem local_fill_window_slide_transfer {h : Heap} {r : ZStreamRef} {cutoff ds w p q : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8} {pa qa pa' qa' : Array UInt16}
    (state : LocalState h cutoff r ds z d) (env : HashEnv h d w q p wa qa pa)
    (sizeP : pa'.size = pa.size) (sizeH : qa'.size = qa.size)
    (range : fillEnd d ≤ d.window_size.toNat)
    (taken : d.strstart ≥ d.w_size + (d.w_size - MIN_LOOKAHEAD_u))
    (prefixRun : fillSlide (some (.tab ds)) d d.w_size (fillMore d) h =
      .ok ((), slideHeap h ds w p q d wa pa' qa')) :
    fill_window (some (.tab ds)) h = fill_window (some (.tab ds)) (slideHeap h ds w p q d wa pa' qa') := by
  let hs := slideHeap h ds w p q d wa pa' qa'
  have afterGood : LocalState hs cutoff r ds z (slideState d) := local_slide_state state env sizeP sizeH
  have counts := local_fill_slide_counts state env.win env.wbytes range taken
  have noSlide := counts.2.2.2.2.2.2.2.2
  have wsize : (slideState d).w_size = d.w_size := rfl
  have more := local_slide_more_eq state env sizeP sizeH range taken
  have first : fillBody (some (.tab ds)) d.w_size false h = fillBody (some (.tab ds)) d.w_size false hs := by
    simp only [fill_body_slide_source, bind_app, ldDeflateState_tab state.live.hs,
      ldDeflateState_tab afterGood.live.hs, wsize, taken, ite_true, prefixRun, noSlide, ite_false]
    rw [more]
  have loop := do_first_body_eq (cond := fillCond (some (.tab ds))) first
  have stateS : (slideHeap h ds w p q d wa pa' qa').dstates ds = some (slideState d) := by simp [slideHeap]
  simp only [fill_window_source, bind_app, rdD_eq, state.live.hs, stateS, wsize]
  rw [loop]


/-- Exact stores of the real sliding prefix preserve typed occupancy and
all objects outside its state/window/head/prev footprint. -/
theorem local_slide_heap_storage {h : Heap} {r : ZStreamRef} {cutoff ds w p q : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8} {pa qa pa' qa' : Array UInt16}
    (state : LocalState h cutoff r ds z d) (env : HashEnv h d w q p wa qa pa) :
    Shape h (slideHeap h ds w p q d wa pa' qa') ∧
      Frame h (slideHeap h ds w p q d wa pa' qa') (fun b => b = ds ∨ b = w ∨ b = p ∨ b = q) := by
  let copied := {h with bytes := upd h.bytes w (some (slideWindow d wa))}
  have getP : (setW copied q qa').words p = some pa := by
    simpa only [setW,upd_ne _ _ _ _ env.hne.symm] using env.pwords
  have getQ : copied.words q = some qa := env.hwords
  have stateP : (setW (setW copied q qa') p pa').dstates ds = some d := state.live.hs
  have shape := (((shape_setB env.wbytes (slideWindow d wa)).trans (shape_setW getQ qa')).trans
    (shape_setW getP pa')).trans (shape_setD stateP (slideState d))
  refine ⟨shape,rfl,rfl,rfl,Nat.le_refl _,Nat.le_refl _,?_⟩
  intro b _ outside
  have stateNe : b ≠ ds := fun same => outside (Or.inl same)
  have windowNe : b ≠ w := fun same => outside (Or.inr (Or.inl same))
  have prevNe : b ≠ p := fun same => outside (Or.inr (Or.inr (Or.inl same)))
  have headNe : b ≠ q := fun same => outside (Or.inr (Or.inr (Or.inr same)))
  simp [slideHeap,setD,setW,upd_ne _ _ _ _ stateNe,upd_ne _ _ _ _ windowNe,
    upd_ne _ _ _ _ prevNe,upd_ne _ _ _ _ headNe]

/-- Padding's exact stores preserve LocalState's typed shape and frame. -/
theorem local_slide_padding_storage {h : Heap} {r : ZStreamRef} {cutoff ds w : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8}
    (state : LocalState h cutoff r ds z d) (get : h.bytes w = some wa) :
    Shape h (paddedHeap h ds w d wa) ∧
      Frame h (paddedHeap h ds w d wa) (fun b => StreamRoot r b ∨ b = ds ∨ b = w) := by
  let output := fillRange wa (paddingStart d) (paddingCount d) 0
  have getC : r.get {h with bytes := upd h.bytes w (some output)} = some z := by
    simpa only [stream_get_bytes] using state.live.hz
  obtain ⟨shape,_,_,frame,_⟩ := local_refill_stores (nextZ := z) (nextD := paddedState d)
    (output := output) state.live get
  rw [ZStreamRef.put_self getC] at shape frame
  exact ⟨shape,frame⟩

/-- The real slide moves exactly the old valid suffix by one window. -/
theorem local_slide_window_view {h : Heap} {r : ZStreamRef} {cutoff ds w : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8}
    (state : LocalState h cutoff r ds z d) (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa)
    (range : fillEnd d ≤ d.window_size.toNat)
    (taken : d.strstart ≥ d.w_size+(d.w_size-MIN_LOOKAHEAD_u)) :
    ∀ i, i+d.w_size.toNat < fillEnd d → bfn (slideWindow d wa) i = bfn wa (i+d.w_size.toNat) := by
  have counts := local_fill_slide_counts state win get range taken
  have extent := local_window_extent state win get
  intro i bound
  have inside := copy_range_inside wa wa 0 d.w_size.toNat (d.w_size-fillMore d).toNat i
    (by omega) (by omega) (by omega)
  simpa only [slideWindow,Nat.sub_zero,Nat.add_comm] using inside

/-- Padding keeps all real valid bytes after the actual slide. -/
theorem local_slide_padded_prefix {h : Heap} {r : ZStreamRef} {cutoff ds w : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8}
    (state : LocalState h cutoff r ds z d) (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa)
    (range : fillEnd d ≤ d.window_size.toNat) (i : Nat) (before : i < fillEnd d) :
    bfn (fillRange wa (paddingStart d) (paddingCount d) 0) i = bfn wa i := by
  have extent := local_window_extent state win get
  have bounds := padding_bounds d range state.inv.hw
  have fit : paddingStart d+paddingCount d ≤ wa.size := by omega
  unfold bfn
  rw [Array.getD_eq_getD_getElem?,Array.getD_eq_getD_getElem?,getElem?_fillRange _ _ _ _ _ fit]
  simp [show ¬(paddingStart d ≤ i ∧ i < paddingStart d+paddingCount d) by omega]

/-- The taken slide executes even when caller input is empty. The complete
actual refill then exits its loop and pads the moved window. Every returned
field refers to this one run and preserves local typed-table representation. -/
theorem local_fill_window_slide_empty {h : Heap} {r : ZStreamRef} {cutoff ds w p q b : Nat}
    {z : ZStream} {d : DeflateState} {wa buf : Array UInt8} {pa qa : Array UInt16}
    {xs : List Symbol} {credit : Int}
    (state : LocalState h cutoff r ds z d) (env : HashEnv h d w q p wa qa pa)
    (base : TreesBase h ds d b buf) (ledger : SymbolLedger buf d xs)
    (balance : BlockBalance d xs credit) (lo : 0 ≤ credit) (hi : credit ≤ 1)
    (range : fillEnd d ≤ d.window_size.toNat)
    (taken : d.strstart ≥ d.w_size+(d.w_size-MIN_LOOKAHEAD_u)) (empty : z.avail_in = 0) :
    ∃ qa' pa',
      let slid := slideState d
      let moved := slideWindow d wa
      let result := paddedState slid
      let output := fillRange moved (paddingStart slid) (paddingCount slid) 0
      let after := paddedHeap (slideHeap h ds w p q d wa pa' qa') ds w slid moved
      fill_window (some (.tab ds)) h = .ok ((),after) ∧
        LocalState after cutoff r ds z result ∧ StreamAccounting z z 0 0 ∧ Shape h after ∧
        Frame h after (fun k => StreamRoot r k ∨ k = ds ∨ k = w ∨ k = p ∨ k = q) ∧
        after.bytes w = some output ∧ after.words q = some qa' ∧ after.words p = some pa' ∧
        qa'.size = qa.size ∧ pa'.size = pa.size ∧
        (∀ i, wfn qa' i = if i < d.hash_size.toNat then slideVal d.w_size (wfn qa i) else wfn qa i) ∧
        (∀ i, wfn pa' i = if i < d.w_size.toNat then slideVal d.w_size (wfn pa i) else wfn pa i) ∧
        result.strstart.toNat = d.strstart.toNat-d.w_size.toNat ∧ result.lookahead = d.lookahead ∧
        fillEnd result = fillEnd d-d.w_size.toNat ∧
        (∀ i, i < fillEnd result → bfn output i = bfn wa (i+d.w_size.toNat)) := by
  obtain ⟨qa',pa',prefixRun,sizeH,sizeP,head,prev⟩ := local_fill_slide_run state env base ledger
    state.inv.sym.2.2.1 balance lo hi range taken
  let hs := slideHeap h ds w p q d wa pa' qa'
  let slid := slideState d
  let moved := slideWindow d wa
  have localS : LocalState hs cutoff r ds z slid := local_slide_state state env sizeP sizeH
  have getS : hs.bytes w = some moved := by simp [hs,moved,slideHeap]
  have winS : slid.window = .ref (.blk w) 0 := env.win
  have geometry := local_fill_slide_counts state env.win env.wbytes range taken
  have rangeS : fillEnd slid ≤ slid.window_size.toNat := by
    change fillEnd (slideState d) ≤ d.window_size.toNat
    have wsz := state.inv.wsz
    omega
  have noSlide : ¬slid.strstart ≥ slid.w_size+(slid.w_size-MIN_LOOKAHEAD_u) := geometry.2.2.2.2.2.2.2.2
  have loop := do_once (local_fill_body_no_input localS.live empty noSlide) (fill_cond_break (some (.tab ds)) hs)
  have pad := local_fill_high_water_complete localS winS getS (local_window_writable localS winS) rangeS
  have suffix : fill_window (some (.tab ds)) hs = .ok ((),paddedHeap hs ds w slid moved) := by
    rw [fill_window_source]
    simp only [bind_app,rdD_eq,localS.live.hs,loop]
    exact pad
  obtain ⟨shapeS,frameS⟩ := local_slide_heap_storage (pa' := pa') (qa' := qa') state env
  obtain ⟨shapeA,frameA⟩ := local_slide_padding_storage localS getS
  have frameS' := full_frame_weaken frameS (large := fun k => StreamRoot r k ∨ k = ds ∨ k = w ∨ k = p ∨ k = q)
    (fun _ member => Or.inr member)
  have frameA' := full_frame_weaken frameA (large := fun k => StreamRoot r k ∨ k = ds ∨ k = w ∨ k = p ∨ k = q)
    (by intro k member;rcases member with root | state | window;exact Or.inl root;exact Or.inr (Or.inl state);exact Or.inr (Or.inr (Or.inl window)))
  refine ⟨qa',pa',(local_fill_window_slide_transfer state env sizeP sizeH range taken prefixRun).trans suffix,
    local_padded_state localS winS getS rangeS,stream_accounting_zero z,shapeS.trans shapeA,
    full_frame_trans_shape frameS' frameA' shapeS,by simp [paddedHeap],?_,by simp [paddedHeap,slideHeap],
    sizeH,sizeP,head,prev,geometry.2.2.2.2.1,rfl,geometry.2.2.2.2.2.1,?_⟩
  · simp [paddedHeap,slideHeap,setW,upd_ne _ _ _ _ env.hne]
  · intro i before
    change i < fillEnd slid at before
    rw [local_slide_padded_prefix localS winS getS rangeS i before]
    apply local_slide_window_view state env.win env.wbytes range taken i
    change i < fillEnd (slideState d) at before
    omega


/-- The slide preserves every caller input view distinct from its window.
The private depth field is unchanged even for a depth-table input view. -/
theorem local_slide_input_frame {h : Heap} {r : ZStreamRef} {cutoff ds w p q : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8} {pa' qa' : Array UInt16} {ref : BRef}
    (state : LocalState h cutoff r ds z d) (separate : BRef.blk w ≠ ref) :
    Space.get (slideHeap h ds w p q d wa pa' qa') ref = (Space.get h ref : Option (Array UInt8)) := by
  cases ref with
  | blk b =>
    have different : b ≠ w := by intro same;subst b;exact separate rfl
    simp [slideHeap,Space.get,upd_ne _ _ _ _ different]
  | dstate_depth id =>
    by_cases same : id = ds
    · subst id
      simp [slideHeap,Space.get,state.live.hs,slideState,slideBeforeHash]
    · simp [slideHeap,Space.get,setD,upd_ne _ _ _ _ same]
  | str _ | st_dist_code | st_length_code => rfl

/-- A taken slide followed by a nonempty actual read with no deferred
insertions. The actual prefix and full no-slide suffix are composed, with
precise input accounting, moved/copied/padded bytes and typed Frame. -/
theorem local_fill_window_slide_read {h : Heap} {r : ZStreamRef} {cutoff ds w p q b io : Nat}
    {z : ZStream} {d : DeflateState} {wa buf ia : Array UInt8} {pa qa : Array UInt16}
    {ref : BRef} {xs : List Symbol} {credit : Int}
    (state : LocalState h cutoff r ds z d) (env : HashEnv h d w q p wa qa pa)
    (base : TreesBase h ds d b buf) (ledger : SymbolLedger buf d xs)
    (balance : BlockBalance d xs credit) (lo : 0 ≤ credit) (hi : credit ≤ 1)
    (range : fillEnd d ≤ d.window_size.toNat) (short : d.lookahead.toNat < 262)
    (taken : d.strstart ≥ d.w_size+(d.w_size-MIN_LOOKAHEAD_u)) (insert : d.insert = 0) (wrap : d.wrap = 1)
    (pointer : z.next_in = .ref ref io) (input : Space.get h ref = some ia)
    (inputBound : io+z.avail_in.toNat ≤ ia.size) (nonempty : z.avail_in ≠ 0)
    (separate : BRef.blk w ≠ ref) :
    ∃ qa' pa',
      let hs := slideHeap h ds w p q d wa pa' qa'
      let slid := slideState d
      let moved := slideWindow d wa
      let n := rbLen z.avail_in (fillMore slid)
      let copied := copyRange moved ia (fillEnd slid) io n.toNat
      let read := resumeReadState slid n copied
      let result := resumedFillState slid n copied
      let output := fillRange copied (paddingStart read) (paddingCount read) 0
      let nextZ := readStream z n ref io (adlerValue z.adler ((ia.toList.drop io).take n.toNat))
      let after := resumedFillHeap hs r ds w z slid ref io ia moved
      fill_window (some (.tab ds)) h = .ok ((),after) ∧
        LocalState after cutoff r ds nextZ result ∧ StreamAccounting z nextZ n.toNat 0 ∧ Shape h after ∧
        Frame h after (fun k => StreamRoot r k ∨ k = ds ∨ k = w ∨ k = p ∨ k = q) ∧
        after.bytes w = some output ∧ after.words q = some qa' ∧ after.words p = some pa' ∧
        qa'.size = qa.size ∧ pa'.size = pa.size ∧
        (∀ i, wfn qa' i = if i < d.hash_size.toNat then slideVal d.w_size (wfn qa i) else wfn qa i) ∧
        (∀ i, wfn pa' i = if i < d.w_size.toNat then slideVal d.w_size (wfn pa i) else wfn pa i) ∧
        fillEnd result = fillEnd d-d.w_size.toNat+n.toNat ∧ result.strstart.toNat = d.strstart.toNat-d.w_size.toNat ∧
        result.status = d.status ∧ result.level = d.level ∧ result.strategy = d.strategy ∧
        min (fillEnd result+258) result.window_size.toNat ≤ result.high_water.toNat ∧
        (∀ i, i < fillEnd d-d.w_size.toNat → bfn output i = bfn wa (i+d.w_size.toNat)) := by
  obtain ⟨qa',pa',prefixRun,sizeH,sizeP,head,prev⟩ := local_fill_slide_run state env base ledger
    state.inv.sym.2.2.1 balance lo hi range taken
  let hs := slideHeap h ds w p q d wa pa' qa'
  let slid := slideState d
  let moved := slideWindow d wa
  have localS : LocalState hs cutoff r ds z slid := local_slide_state state env sizeP sizeH
  have getS : hs.bytes w = some moved := by simp [hs,moved,slideHeap]
  have winS : slid.window = .ref (.blk w) 0 := env.win
  have geometry := local_fill_slide_counts state env.win env.wbytes range taken
  have rangeS : fillEnd slid ≤ slid.window_size.toNat := by
    change fillEnd (slideState d) ≤ d.window_size.toNat
    have wsz := state.inv.wsz
    omega
  have noSlide : ¬slid.strstart ≥ slid.w_size+(slid.w_size-MIN_LOOKAHEAD_u) := geometry.2.2.2.2.2.2.2.2
  have insertS : slid.insert = 0 := by simp [slid,slideState,slideBeforeHash,insert]
  have inputS : Space.get hs ref = some ia := (local_slide_input_frame state separate).trans input
  obtain ⟨run,localA,account,frameA,shapeA,bytesA,_count,endpoint,start,status,level,strategy,padded,keptPrefix⟩ :=
    local_fill_window_resume localS winS getS rangeS short noSlide insertS wrap pointer inputS inputBound nonempty (Or.inl separate)
  obtain ⟨shapeS,frameS⟩ := local_slide_heap_storage (pa' := pa') (qa' := qa') state env
  have frameS' := full_frame_weaken frameS (large := fun k => StreamRoot r k ∨ k = ds ∨ k = w ∨ k = p ∨ k = q)
    (fun _ member => Or.inr member)
  have frameA' := full_frame_weaken frameA (large := fun k => StreamRoot r k ∨ k = ds ∨ k = w ∨ k = p ∨ k = q)
    (by intro k member;rcases member with root | state | window;exact Or.inl root;exact Or.inr (Or.inl state);exact Or.inr (Or.inr (Or.inl window)))
  refine ⟨qa',pa',(local_fill_window_slide_transfer state env sizeP sizeH range taken prefixRun).trans run,
    localA,account,shapeS.trans shapeA,full_frame_trans_shape frameS' frameA' shapeS,bytesA,?_,?_,
    sizeH,sizeP,head,prev,?_,?_,status,level,strategy,padded,?_⟩
  · rw [local_resumed_heap_exact]
    simp [slideHeap,setW,upd_ne _ _ _ _ env.hne]
  · rw [local_resumed_heap_exact]
    simp [slideHeap]
  · rw [endpoint]
    exact congrArg (·+(rbLen z.avail_in (fillMore slid)).toNat) geometry.2.2.2.2.2.1
  · rw [start]
    exact geometry.2.2.2.2.1
  · intro i bound
    have before : i < fillEnd slid := by change i < fillEnd (slideState d);omega
    rw [keptPrefix i before]
    apply local_slide_window_view state env.win env.wbytes range taken i
    omega

end ZlibF.Spec.Public.Proofs.CompressLocalSlide
