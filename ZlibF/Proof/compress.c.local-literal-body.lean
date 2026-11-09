import ZlibF.Proof.«compress.c.local-symbol-initial»
import ZlibF.Proof.«compress.c.local-threshold»

/-! # The first actual literal-producing slow iteration with local state -/
namespace ZlibF.Spec.Public.Proofs.CompressLocalLiteralBody
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open Zlib.Deflate.Engine.Proofs ZlibF.Spec.Public
open ZlibF.Spec.Public.Proofs.CompressLocalInit ZlibF.Spec.Public.Proofs.CompressLocalHash
open ZlibF.Spec.Public.Proofs.CompressLocalLiteral ZlibF.Spec.Public.Proofs.CompressLocalSymbols
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false
set_option maxRecDepth 100000

theorem local_nil_search_symbols {h searched : Heap} {r : ZStreamRef} {cutoff ds p q : Nat}
    {z : ZStream} {d : DeflateState} {pa qa : Array UInt16} {key : UInt32} {xs : List Symbol}
    (state : LocalState searched cutoff r ds z (lazyPrepare {d with ins_h := key}))
    (symbol : SymbolBoundary h ds d xs)
    (exactHeap : searched = setD (insertedHeap h ds p q d pa qa key) ds (lazyPrepare {d with ins_h := key})) :
    SymbolBoundary searched ds (lazyPrepare {d with ins_h := key}) xs := by
  obtain ⟨b,buf,trees,ledger,balance⟩ := symbol
  have get : searched.bytes b = some buf := by simpa [exactHeap,insertedHeap] using trees.base.bytes
  exact local_symbol_boundary_of_ledger state trees.base.pbuf get
    (ledger.keep rfl rfl rfl rfl) balance

/-- The actual first deferred-byte store keeps the original symbol list
and increases its consumption credit by exactly one. -/
theorem local_first_defer_symbols {h after : Heap} {r : ZStreamRef} {cutoff ds p q : Nat}
    {z : ZStream} {d : DeflateState} {pa qa : Array UInt16} {key : UInt32} {xs : List Symbol}
    (state : LocalState after cutoff r ds z (deferOne (lazyPrepare {d with ins_h := key})))
    (symbol : SymbolBoundary h ds d xs) (available : d.match_available = 0)
    (start : (deferOne (lazyPrepare {d with ins_h := key})).strstart.toNat = d.strstart.toNat+1)
    (exactHeap : after = setD (insertedHeap h ds p q d pa qa key) ds (deferOne (lazyPrepare {d with ins_h := key}))) :
    SymbolBoundary after ds (deferOne (lazyPrepare {d with ins_h := key})) xs := by
  obtain ⟨b,buf,trees,ledger,balance⟩ := symbol
  have get : after.bytes b = some buf := by simpa [exactHeap,insertedHeap] using trees.base.bytes
  have credit : deferredCredit d = 0 := by simp [deferredCredit,available]
  rw [credit] at balance
  have balanceA : BlockBalance (deferOne (lazyPrepare {d with ins_h := key})) xs
      (deferredCredit (deferOne (lazyPrepare {d with ins_h := key}))) := by
    change (deferOne (lazyPrepare {d with ins_h := key})).strstart.toNat-d.block_start.toInt =
      (represented xs : Int)+1
    rw [start]
    unfold BlockBalance at balance
    omega
  exact local_symbol_boundary_of_ledger state trees.base.pbuf get
    (ledger.keep rfl rfl rfl rfl) balanceA

/-- Complete source iteration at position one: actual hash insertion,
actual NIL search and actual previous-byte literal tally share one heap.
The packed symbol and deferred-byte balance are returned together. -/
theorem local_nil_literal_body {h : Heap} {r : ZStreamRef} {cutoff ds w p q top : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8} {pa qa : Array UInt16} {xs : List Symbol}
    (state : LocalState h cutoff r ds z d) (symbol : SymbolBoundary h ds d xs)
    (env : HashEnv h d w q p wa qa pa)
    (chains : HashChains (wfn qa) (wfn pa) (bfn wa) d.hash_size d.hash_shift d.hash_mask
      d.w_size.toNat top (d.strstart.toNat+d.lookahead.toNat))
    (ordered : top ≤ d.strstart.toNat) (position : d.strstart = 1)
    (enough : 262 ≤ d.lookahead.toNat)
    (window : d.strstart.toNat+d.lookahead.toNat ≤ wa.size)
    (range : d.strstart.toNat+d.lookahead.toNat ≤ d.window_size.toNat)
    (form : InsHForm d.hash_shift d.hash_mask (bfn wa) d.strstart.toNat d.ins_h)
    (length : d.match_length = 2) (available : d.match_available ≠ 0)
    (space : d.sym_next.toNat+3 < d.sym_end.toNat) (out : z.avail_out ≠ 0)
    (flush : Int32) (st : LoopS) :
    ∃ key after,
      let result := advanceOne (literalState (lazyPrepare {d with ins_h := key}) wa[0]!)
      deflate_slow_body (some (.tab ds)) flush st h =
        .ok ({st with hash_head := 0,bflush := false},after) ∧
      LocalState after cutoff r ds z result ∧ HeapChains after result 2 ∧
      SymbolBoundary after ds result (xs++[⟨0,wa[0]!.toNat⟩]) ∧
      result.strstart = 2 ∧ result.lookahead.toNat = d.lookahead.toNat-1 ∧
      after.bytes w = some wa ∧ result.sym_next.toNat < result.sym_end.toNat := by
  obtain ⟨key,searched,search,stateM,chainsM,_primed,exactHeap⟩ :=
    local_nil_search state env chains ordered (by rw [position]; decide) enough window form
  let dm := lazyPrepare {d with ins_h := key}
  have symbolM := local_nil_search_symbols stateM symbol exactHeap
  have get : searched.bytes w = some wa := by simpa [exactHeap,insertedHeap] using env.wbytes
  have previous : 1 ≤ dm.strstart.toNat := by change 1 ≤ d.strstart.toNat; rw [position]; decide
  have branch : (dm.prev_length ≥ MIN_MATCH_u && dm.match_length ≤ dm.prev_length) = false := by
    change (d.match_length ≥ MIN_MATCH_u && (2 : UInt32) ≤ d.match_length) = false
    rw [length]; decide
  obtain ⟨after,decision,stateA,chainsA,_rangeA,getA,strict,symbolA,_record,_bytes⟩ :=
    local_slow_literal_symbol_storage stateM symbolM chainsM env.win get range
      (by change 1 ≤ d.lookahead.toNat; omega) previous branch available space flush st 0
  have counts := advance_one_counts stateM.inv range (by change 1 ≤ d.lookahead.toNat; omega)
  have index : dm.strstart.toNat-1 = 0 := by change d.strstart.toNat-1 = 0; rw [position]; decide
  have noFill : ¬d.lookahead < MIN_LOOKAHEAD_u := by rw [UInt32.lt_iff_toNat_lt]; change ¬d.lookahead.toNat < 262; omega
  have full : (z.avail_out == 0) = false := beq_eq_false_iff_ne.mpr out
  have byte : wa[(lazyPrepare {d with ins_h := key}).strstart.toNat-1]! = wa[0]! := by
    change wa[d.strstart.toNat-1]! = wa[0]!
    rw [position]; rfl
  rw [byte] at stateA chainsA strict
  simp only [full,Bool.false_eq_true,ite_false] at decision
  simp only [emittedLiteral,byte] at symbolA
  have top : d.strstart.toNat+1 = 2 := by rw [position]; decide
  rw [top] at chainsA
  have startA : (advanceOne (literalState dm wa[0]!)).strstart = 2 := by
    apply UInt32.toNat_inj.mp
    change (advanceOne dm).strstart.toNat = (2 : UInt32).toNat
    rw [counts.1]
    change d.strstart.toNat+1 = (2 : UInt32).toNat
    rw [position]; decide
  refine ⟨key,after,?_,stateA,chainsA,?_,startA,counts.2.1,getA,strict⟩
  · rw [slow_body_source]
    simp only [bind_app,rdD_eq,state.live.hs,noFill,ite_false,search]
    exact decision
  · exact symbolA

end ZlibF.Spec.Public.Proofs.CompressLocalLiteralBody
