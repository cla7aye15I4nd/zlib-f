import ZlibF.Proof.«compress.c.local-search»
import ZlibF.Proof.«compress.c.local-literal-storage»

/-! # A complete actual literal iteration after general lazy matching -/
namespace ZlibF.Spec.Public.Proofs.CompressLocalSearchedLiteral
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open Zlib.Deflate.Engine.Proofs ZlibF.Spec.Public
open ZlibF.Spec.Public.Proofs.CompressLocalInit ZlibF.Spec.Public.Proofs.CompressLocalHash
open ZlibF.Spec.Public.Proofs.CompressLocalSearch ZlibF.Spec.Public.Proofs.CompressLocalLiteral
open ZlibF.Spec.Public.Proofs.CompressLocalLiteralStorage
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false
set_option maxRecDepth 100000

/-- Actual search leaves the packed symbols and consumed-byte balance
unchanged, including the active-candidate matcher branch. -/
theorem local_search_symbols {h after : Heap} {r : ZStreamRef} {cutoff ds : Nat}
    {z : ZStream} {d : DeflateState} {key pos len : UInt32} {xs : List Symbol}
    (state : LocalState after cutoff r ds z (matchState (lazyPrepare {d with ins_h := key}) pos len))
    (symbol : SymbolBoundary h ds d xs) (bytes : after.bytes = h.bytes) :
    SymbolBoundary after ds (matchState (lazyPrepare {d with ins_h := key}) pos len) xs := by
  obtain ⟨b,buf,trees,ledger,balance⟩ := symbol
  have get : after.bytes b = some buf := by rw [bytes];exact trees.base.bytes
  exact local_symbol_boundary_of_ledger state trees.base.pbuf get
    (ledger.keep rfl rfl rfl rfl) balance

/-- Complete actual insertion, general matching/filtering and literal
emission. The incoming lazy length is two, so the previous-match emission
guard is false; the current candidate may be nonzero and may improve.
This internal producer keeps the original public utility goal unchanged. -/
theorem searched_literal_body {h : Heap} {r : ZStreamRef} {cutoff ds w p q top : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8} {pa qa : Array UInt16} {xs : List Symbol}
    (state : LocalState h cutoff r ds z d) (symbol : SymbolBoundary h ds d xs)
    (env : HashEnv h d w q p wa qa pa)
    (chains : HashChains (wfn qa) (wfn pa) (bfn wa) d.hash_size d.hash_shift d.hash_mask
      d.w_size.toNat top (d.strstart.toNat+d.lookahead.toNat))
    (ordered : top ≤ d.strstart.toNat)
    (enough : 262 ≤ d.lookahead.toNat)
    (range : d.strstart.toNat+d.lookahead.toNat ≤ d.window_size.toNat)
    (room : d.strstart.toNat+262 ≤ d.window_size.toNat)
    (form : InsHForm d.hash_shift d.hash_mask (bfn wa) d.strstart.toNat d.ins_h)
    (length : d.match_length = 2) (available : d.match_available ≠ 0)
    (previous : 1 ≤ d.strstart.toNat) (space : d.sym_next.toNat+3 < d.sym_end.toNat)
    (out : z.avail_out ≠ 0) (flush : Int32) (st : LoopS) :
    ∃ key pos len after,
      let searched := matchState (lazyPrepare {d with ins_h := key}) pos len
      let result := advanceOne (literalState searched wa[d.strstart.toNat-1]!)
      deflate_slow_body (some (.tab ds)) flush st h =
        .ok ({st with hash_head := (wfn qa key.toNat).toUInt32,bflush := false},after) ∧
      LocalState after cutoff r ds z result ∧ HeapChains after result (d.strstart.toNat+1) ∧
      SymbolBoundary after ds result (xs++[emittedLiteral d wa]) ∧
      result.strstart.toNat = d.strstart.toNat+1 ∧ result.lookahead.toNat = d.lookahead.toNat-1 ∧
      len.toNat ≤ 258 ∧
      (3 ≤ len.toNat → 2 < len.toNat → GoodMatch wa d.strstart.toNat d.w_size.toNat pos.toNat len.toNat) ∧
      InsHForm d.hash_shift d.hash_mask (bfn wa) (d.strstart.toNat+1) key ∧
      after.bytes w = some wa ∧ SlowRecordFrame d result ∧ Shape h after ∧
      Frame h after (fun x => StreamRoot r x ∨ DeflateOwned ds d x) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧ after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  obtain ⟨key,hs,pos,len,search,stateM,chainsM,bound,_clip,evidence,bytes,nextForm,_byteframe,
      shapeS,frameS,_liveS,allocS,nextS⟩ := local_slow_search_room state env chains ordered range (by omega) room
    (by rw [length];decide) form
  let dm := matchState (lazyPrepare {d with ins_h := key}) pos len
  have symbolsM := local_search_symbols stateM symbol bytes
  have get : hs.bytes w = some wa := by rw [bytes];exact env.wbytes
  have branch : (dm.prev_length ≥ MIN_MATCH_u && dm.match_length ≤ dm.prev_length) = false := by
    change (d.match_length ≥ MIN_MATCH_u && len ≤ d.match_length) = false
    rw [length]
    rfl
  obtain ⟨after,decision,stateA,chainsA,_range,getA,_strict,symbolA,_record,_byte⟩ :=
    local_slow_literal_symbol_storage stateM symbolsM chainsM env.win get range
      (by change 1 ≤ d.lookahead.toNat;omega) previous branch available space flush st (wfn qa key.toNat).toUInt32
  obtain ⟨expected,storageRun,_stateE,_chainsE,_rangeE,_getE,_strictE,_recordE,_kw,_kp,_kh,_kb,
      shapeL,frameL,_liveL,allocL,nextL,_canonical⟩ :=
    local_slow_literal_full_storage stateM chainsM env.win get range
      (by change 1 ≤ d.lookahead.toNat;omega) previous branch available space flush st (wfn qa key.toNat).toUInt32
  have same : expected = after := (Prod.mk.inj (Except.ok.inj (storageRun.symm.trans decision))).2
  rw [same] at shapeL frameL allocL nextL
  have frameL' : Frame hs after (fun x => StreamRoot r x ∨ DeflateOwned ds d x) := frameL
  have shape := shapeS.trans shapeL
  have frame := full_frame_trans_shape frameS frameL' shapeS
  have counts := advance_one_counts stateM.inv range (by change 1 ≤ d.lookahead.toNat;omega)
  have noFill : ¬d.lookahead < MIN_LOOKAHEAD_u := by
    rw [UInt32.lt_iff_toNat_lt]
    change ¬d.lookahead.toNat < 262
    omega
  have full : (z.avail_out == 0) = false := beq_eq_false_iff_ne.mpr out
  simp only [full,Bool.false_eq_true,ite_false] at decision
  refine ⟨key,pos,len,after,?_,stateA,chainsA,symbolA,counts.1,counts.2.1,bound,?_,nextForm,getA,rfl,
    shape,frame,full_shape_live_change shape,allocL.trans allocS,nextL.trans nextS⟩
  · rw [slow_body_source]
    simp only [bind_app,rdD_eq,state.live.hs,noFill,ite_false,search]
    exact decision
  · intro large larger
    exact evidence large (by rw [length];exact larger)

end ZlibF.Spec.Public.Proofs.CompressLocalSearchedLiteral
