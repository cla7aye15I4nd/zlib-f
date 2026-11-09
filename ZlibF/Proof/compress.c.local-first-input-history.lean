import ZlibF.Proof.«compress.c.local-body-history»
import ZlibF.Proof.«compress.c.local-literal-loop»

/-! # Real first refill establishes history against the original source bytes -/
namespace ZlibF.Spec.Public.Proofs.CompressLocalFirstInputHistory
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open Zlib.Deflate.Engine.Proofs ZlibF.Spec.Public
open ZlibF.Spec.Public.Proofs.CompressLocalInit ZlibF.Spec.Public.Proofs.CompressLocalHash
open ZlibF.Spec.Public.Proofs.CompressLocalFill ZlibF.Spec.Public.Proofs.CompressLocalData
open ZlibF.Spec.Public.Proofs.CompressLocalLiteralLoop
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false
set_option maxRecDepth 100000

/-- Each copied real input byte precedes the padding interval. The view
is the original source array, not an independently chosen input function. -/
theorem first_fill_prefix_view {wa ia : Array UInt8} {io : Nat} {n : UInt32}
    (size : wa.size = 65536) (bound : n.toNat ≤ 65536) :
    ∀ i, i < n.toNat →
      bfn (fillRange (copyRange wa ia 0 io n.toNat) n.toNat (firstPadding n).toNat 0) i = bfn ia (io+i) := by
  have pad := firstPadding_nat n bound
  have fit : n.toNat+(firstPadding n).toNat ≤ (copyRange wa ia 0 io n.toNat).size := by
    rw [size_copyRange,size]
    omega
  intro i inside
  unfold bfn
  rw [Array.getD_eq_getD_getElem?,Array.getD_eq_getD_getElem?,getElem?_fillRange _ _ _ _ _ fit,
    ite_eq_right (show ¬(n.toNat ≤ i ∧ i < n.toNat+(firstPadding n).toNat) by omega),
    getElem?_copyRange wa ia 0 io n.toNat i (by rw [size];omega)]
  simp [inside,Array.getElem!_eq_getD,Array.getD_eq_getD_getElem?,show (default : UInt8) = 0 from rfl]

/-- Actual first refill with any offered uInt count at least 262. Its
logical input and window view are derived from the real source copy.
The initial match/deferred controls are internal initialization facts. -/
theorem first_fill_input_history {h : Heap} {r : ZStreamRef} {cutoff ds w io : Nat}
    {z : ZStream} {d : DeflateState} {ref : BRef} {ia wa : Array UInt8}
    (state : LocalState h cutoff r ds z d) (fields : InitialReadFields d)
    (chains : HeapChains h d 0) (symbol : SymbolBoundary h ds d [])
    (length : d.match_length = 2) (available : d.match_available = 0)
    (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa)
    (writable : h.ro w = false) (size : wa.size = 65536)
    (pointer : z.next_in = .ref ref io) (input : Space.get h ref = some ia)
    (inputBound : io+z.avail_in.toNat ≤ ia.size) (enough : 262 ≤ z.avail_in.toNat)
    (separate : BRef.blk w ≠ ref ∨ (rbLen z.avail_in 65536).toNat ≤ io ∨
      io+(rbLen z.avail_in 65536).toNat ≤ 0) :
    let n := rbLen z.avail_in 65536
    let next := readStream z n ref io (adlerValue z.adler ((ia.toList.drop io).take n.toNat))
    let result := firstFillState d n (copyRange wa ia 0 io n.toNat)
    let after := firstFillHeap h r ds w z d ref io ia wa
    let packed := fillRange (copyRange wa ia 0 io n.toNat) n.toNat (firstPadding n).toNat 0
    fill_window (some (.tab ds)) h = .ok ((),after) ∧ LocalState after cutoff r ds next result ∧
      HeapChains after result 0 ∧ SymbolBoundary after ds result [] ∧ StreamAccounting z next n.toNat 0 ∧
      LazyHistory (fun i => bfn ia (io+i)) 0 result ∧ DeferredByte result ∧
      (∀ i, i < result.strstart.toNat+result.lookahead.toNat → bfn packed i = bfn ia (io+i)) ∧
      InsHForm result.hash_shift result.hash_mask (bfn packed) result.strstart.toNat result.ins_h ∧
      result.strstart = 0 ∧ 262 ≤ result.lookahead.toNat ∧
      result.strstart.toNat+result.lookahead.toNat ≤ result.window_size.toNat ∧
      result.window = .ref (.blk w) 0 ∧ after.bytes w = some packed ∧
      (∀ flush, deflate_slow (some (.tab ds)) flush h = deflate_slow (some (.tab ds)) flush after) := by
  let n := rbLen z.avail_in 65536
  let copied := copyRange wa ia 0 io n.toNat
  let result := firstFillState d n copied
  let after := firstFillHeap h r ds w z d ref io ia wa
  let packed := fillRange copied n.toNat (firstPadding n).toNat 0
  have ncount := rbLen_nat z.avail_in 65536
  change n.toNat = min z.avail_in.toNat 65536 at ncount
  have nbound : n.toNat ≤ 65536 := by omega
  have nlarge : 262 ≤ n.toNat := by omega
  have nonzero : z.avail_in ≠ 0 := by intro zero;rw [zero] at enough;change 262 ≤ 0 at enough;omega
  obtain ⟨fill,stateF,account,_,_,lookF,startF,_statusF,_levelF,_strategyF,_lastF,getF⟩ :=
    local_fill_window_first state win get writable size fields.1 fields.2.1 fields.2.2.1 fields.2.2.2.1
      fields.2.2.2.2.1 fields.2.2.2.2.2.1 fields.2.2.2.2.2.2.1 pointer input inputBound nonzero separate
  have chainsF := first_fill_chains (r := r) (ds := ds) (z := z) (ref := ref) (io := io) (ia := ia) chains win get fields.1 fields.2.1
  have symbolsF := local_first_fill_symbols state symbol win stateF
  have keep : result.match_length = d.match_length ∧ result.match_available = d.match_available ∧
      result.hash_shift = d.hash_shift ∧ result.hash_mask = d.hash_mask ∧
      result.window_size = d.window_size ∧ result.window = d.window := by
    unfold result firstFillState primeState
    split <;> exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
  have rangeF : result.strstart.toNat+result.lookahead.toNat ≤ result.window_size.toNat := by
    rw [startF,lookF,keep.2.2.2.2.1,fields.2.2.2.2.2.1]
    simpa only [show (0 : UInt32).toNat = 0 from rfl,show (65536 : UInt64).toNat = 65536 from rfl,Nat.zero_add] using nbound
  have history := logical_history_initial (keep.1.trans length) (fun i => bfn ia (io+i)) 0
  have deferred : DeferredByte result := by intro bad;exact False.elim (bad (keep.2.1.trans available))
  have view : ∀ i, i < result.strstart.toNat+result.lookahead.toNat → bfn packed i = bfn ia (io+i) := by
    rw [startF,lookF]
    simpa only [show (0 : UInt32).toNat = 0 from rfl,Nat.zero_add] using
      (first_fill_prefix_view (ia := ia) (io := io) size nbound)
  have form : InsHForm result.hash_shift result.hash_mask (bfn packed) result.strstart.toNat result.ins_h := by
    rw [startF,keep.2.2.1,keep.2.2.2.1]
    exact first_fill_form (hash_parameters state.inv) nbound (by rw [size_copyRange];exact size)
      (by change (3 : UInt32) ≤ n;rw [UInt32.le_iff_toNat_le];change 3 ≤ n.toNat;omega)
  have ready : ¬result.lookahead < MIN_LOOKAHEAD_u := by
    rw [UInt32.lt_iff_toNat_lt]
    change ¬result.lookahead.toNat < 262
    rw [lookF]
    change ¬n.toNat < 262
    omega
  exact ⟨fill,stateF,chainsF,symbolsF,account,history,deferred,view,form,startF,
    (by rw [lookF];exact nlarge),rangeF,keep.2.2.2.2.2.trans win,getF,
    fun flush => slow_call_prepend_fill state.live.hs fields.2.1 fill stateF.live.hs ready flush⟩

end ZlibF.Spec.Public.Proofs.CompressLocalFirstInputHistory
