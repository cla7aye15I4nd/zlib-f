import ZlibF.Proof.«compress.c.local-content»
import ZlibF.Proof.«compress.c.local-refill»
import ZlibF.Proof.«deflate.c.engine.fill-history»

/-! # Content against the same input through an actual resumed refill -/
namespace ZlibF.Spec.Public.Proofs.CompressLocalResumeContent
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open Zlib.Deflate.Engine.Proofs ZlibF.Spec.Public
open ZlibF.Spec.Public.Proofs.CompressLocalInit ZlibF.Spec.Public.Proofs.CompressLocalHash
open ZlibF.Spec.Public.Proofs.CompressLocalContent ZlibF.Spec.Public.Proofs.CompressLocalRefill
open ZlibF.Spec.Public.Proofs.CompressLocalLiteral
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- A stream store and the concrete resumed window write retain chains.
Only the old valid prefix is used by existing hash entries. -/
theorem local_resumed_chains {h : Heap} {r : ZStreamRef} {ds w io top : Nat}
    {z : ZStream} {d : DeflateState} {ref : BRef} {wa ia output : Array UInt8}
    (chains : HeapChains h d top) (win : d.window = .ref (.blk w) 0)
    (get : h.bytes w = some wa)
    (prefixBytes : ∀ i, i < fillEnd d → bfn output i = bfn wa i)
    (count : (d.lookahead + rbLen z.avail_in (fillMore d)).toNat =
      d.lookahead.toNat + (rbLen z.avail_in (fillMore d)).toNat)
    (outputEq : output =
      let n := rbLen z.avail_in (fillMore d)
      let copied := copyRange wa ia (fillEnd d) io n.toNat
      let read := resumeReadState d n copied
      fillRange copied (paddingStart read) (paddingCount read) 0) :
    let n := rbLen z.avail_in (fillMore d)
    let copied := copyRange wa ia (fillEnd d) io n.toNat
    HeapChains (resumedFillHeap h r ds w z d ref io ia wa) (resumedFillState d n copied) top := by
  obtain ⟨wb,pb,qb,bytes,prev,head,hw,hp,hq,hbytes,hprev,hhead,H⟩ :=
    heap_chains_window_write chains win get prefixBytes
  obtain ⟨key,high,record⟩ := resumed_fill_record d (rbLen z.avail_in (fillMore d))
    (copyRange wa ia (fillEnd d) io (rbLen z.avail_in (fillMore d)).toNat)
  refine ⟨wb,pb,qb,bytes,prev,head,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [record];exact hw
  · rw [record];exact hp
  · rw [record];exact hq
  · rw [local_resumed_heap_exact]
    simpa only [setD_bytes,ZStreamRef.put_bytes,←outputEq] using hbytes
  · rw [local_resumed_heap_exact]
    simpa only [setD_words,ZStreamRef.put_words] using hprev
  · rw [local_resumed_heap_exact]
    simpa only [setD_words,ZStreamRef.put_words] using hhead
  · rw [record]
    apply chains_mono H (Nat.le_refl top)
    change fillEnd d ≤ d.strstart.toNat + (d.lookahead+rbLen z.avail_in (fillMore d)).toNat
    rw [count]
    dsimp only [fillEnd]
    omega

/-- Actual no-slide refill preserves content against one fixed logical
input. The incoming view is an internal relation to that same input, not
a replacement input defined from the destination window. -/
theorem local_resume_content {h : Heap} {r : ZStreamRef} {cutoff ds w io origin base : Nat}
    {z : ZStream} {d : DeflateState} {ref : BRef} {wa ia : Array UInt8}
    {input : Nat → UInt8} {xs : List Symbol}
    (boundary : LocalContent h cutoff r ds z d input origin base xs)
    (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa)
    (short : d.lookahead.toNat < 262)
    (noSlide : ¬d.strstart ≥ d.w_size+(d.w_size-MIN_LOOKAHEAD_u))
    (insert : d.insert = 0) (wrap : d.wrap = 1)
    (pointer : z.next_in = .ref ref io) (incoming : Space.get h ref = some ia)
    (inputBound : io+z.avail_in.toNat ≤ ia.size) (nonempty : z.avail_in ≠ 0)
    (separate : BRef.blk w ≠ ref ∨ fillEnd d+(rbLen z.avail_in (fillMore d)).toNat ≤ io ∨
      io+(rbLen z.avail_in (fillMore d)).toNat ≤ fillEnd d)
    (incomingView : ∀ j, j < z.avail_in.toNat → bfn ia (io+j) = input (origin+fillEnd d+j)) :
    let n := rbLen z.avail_in (fillMore d)
    let copied := copyRange wa ia (fillEnd d) io n.toNat
    let result := resumedFillState d n copied
    let next := readStream z n ref io (adlerValue z.adler ((ia.toList.drop io).take n.toNat))
    let after := resumedFillHeap h r ds w z d ref io ia wa
    fill_window (some (.tab ds)) h = .ok ((),after) ∧
      LocalContent after cutoff r ds next result input origin base xs ∧
      StreamAccounting z next n.toNat 0 ∧
      Frame h after (fun b => StreamRoot r b ∨ b=ds ∨ b=w) ∧ Shape h after ∧
      fillEnd result = fillEnd d+n.toNat := by
  let n := rbLen z.avail_in (fillMore d)
  let copied := copyRange wa ia (fillEnd d) io n.toNat
  let read := resumeReadState d n copied
  let result := resumedFillState d n copied
  let output := fillRange copied (paddingStart read) (paddingCount read) 0
  let after := resumedFillHeap h r ds w z d ref io ia wa
  obtain ⟨run,stateA,account,frame,shape,bytes,count,endpoint,start,status,level,strategy,padded,old⟩ :=
    local_fill_window_resume boundary.state win get boundary.range short noSlide insert wrap
      pointer incoming inputBound nonempty separate
  change LocalState after cutoff r ds
    (readStream z n ref io (adlerValue z.adler ((ia.toList.drop io).take n.toNat))) result at stateA
  have counts := local_resume_read_counts boundary.state win get boundary.range
  change n.toNat = min z.avail_in.toNat (d.window_size.toNat-fillEnd d) ∧
    (d.lookahead+n).toNat = d.lookahead.toNat+n.toNat ∧
    d.strstart.toNat+(d.lookahead+n).toNat ≤ d.window_size.toNat at counts
  have extent := CompressLocalRefill.local_window_extent boundary.state win get
  obtain ⟨key,readRecord⟩ := resume_read_record d n copied
  change read = _ at readRecord
  obtain ⟨finalKey,high,record⟩ := resumed_fill_record d n copied
  change result = _ at record
  have rangeRead : fillEnd read ≤ read.window_size.toNat := by rw [readRecord];exact counts.2.2
  have localRead := local_resume_read_state (ref := ref) (io := io) (ia := ia) boundary.state get
  have pad := padding_bounds read rangeRead localRead.inv.hw
  have copyFit : fillEnd d+n.toNat ≤ wa.size := by rw [extent.1];dsimp only [fillEnd] at counts ⊢;omega
  have padFit : paddingStart read+paddingCount read ≤ copied.size := by
    rw [size_copyRange,extent.1]
    have target := pad.2.2.2.1
    have sameSize : read.window_size = d.window_size := by rw [readRecord]
    rw [sameSize] at target
    omega
  have readEnd : fillEnd read = fillEnd d+n.toNat := by
    rw [readRecord]
    change d.strstart.toNat+(d.lookahead+n).toNat = d.strstart.toNat+d.lookahead.toNat+n.toNat
    rw [counts.2.1]
    omega
  have unpadded : ∀ i, i < fillEnd d+n.toNat → bfn output i = bfn copied i := by
    intro i hi
    unfold output bfn
    rw [Array.getD_eq_getD_getElem?,Array.getD_eq_getD_getElem?,getElem?_fillRange _ _ _ _ _ padFit]
    have noPad : ¬paddingStart read ≤ i := by have bound := pad.1;rw [readEnd] at bound;omega
    simp only [noPad,false_and,ite_false]
  obtain ⟨oldw,oldwa,oldwin,oldget,oldview,_oldform⟩ := boundary.data
  have sameW : oldw=w := BRef.blk.inj (Ptr.ref.inj (oldwin.symm.trans win)).1
  subst oldw
  have sameA : oldwa=wa := Option.some.inj (oldget.symm.trans get)
  subst oldwa
  have view : ∀ i, i < fillEnd result → bfn output i = input (origin+i) := by
    intro i hi
    rw [endpoint] at hi
    rw [unpadded i hi]
    by_cases before : i<fillEnd d
    · rw [copy_range_prefix wa ia (fillEnd d) io n.toNat copyFit i before]
      exact oldview i before
    · rw [copy_range_inside wa ia (fillEnd d) io n.toNat i copyFit (by omega) (by omega)]
      have source := incomingView (i-fillEnd d) (by omega)
      rw [source]
      congr 1
      omega
  have chainsA := local_resumed_chains (r := r) (ds := ds) (ref := ref) (ia := ia)
    boundary.chains win get old counts.2.1 (rfl : output = _)
  change HeapChains after result d.strstart.toNat at chainsA
  have frontierA := local_resumed_chains (r := r) (ds := ds) (ref := ref) (ia := ia)
    boundary.frontier win get old counts.2.1 (rfl : output = _)
  change HeapChains after result (d.strstart.toNat-d.insert.toNat) at frontierA
  have history : LazyHistory input origin result := by
    rw [record]
    refine ⟨boundary.history.1,?_⟩
    intro large
    obtain ⟨ss,available,room,distance,positive,bound,machine,earlier,meaning⟩ := boundary.history.2 large
    refine ⟨ss,available,?_,distance,positive,bound,machine,earlier,meaning⟩
    change d.match_length.toNat ≤ (d.lookahead+n).toNat+1
    rw [counts.2.1]
    omega
  have symbols : SymbolBoundary after ds result xs := by
    obtain ⟨b,buf,trees,ledger,balance⟩ := boundary.symbols
    obtain ⟨wb,pb,qb,bb,blocks⟩ := boundary.state.inv.blocks
    have wid : wb=w := BRef.blk.inj (Ptr.ref.inj (blocks.win.symm.trans win)).1
    have bid : bb=b := BRef.blk.inj (Ptr.ref.inj (blocks.pbuf.symm.trans trees.base.pbuf)).1
    subst wb bb
    have buffer : after.bytes b=some buf := by
      unfold after
      rw [local_resumed_heap_exact]
      simpa only [setD_bytes,ZStreamRef.put_bytes,upd_ne _ _ _ _ blocks.wb.symm] using trees.base.bytes
    apply local_symbol_boundary_of_ledger stateA (by rw [record];exact trees.base.pbuf) buffer
    · rw [record];exact ledger.keep rfl rfl rfl rfl
    · rw [record];exact balance
  have form : 3 ≤ result.lookahead.toNat →
      InsHForm result.hash_shift result.hash_mask (bfn output) result.strstart.toNat result.ins_h := by
    intro large
    have ready : 3 ≤ d.lookahead+n := by
      change (3 : UInt32) ≤ d.lookahead+n
      rw [UInt32.le_iff_toNat_le]
      rw [record] at large
      exact large
    have params : HashParams d.hash_size d.hash_shift d.hash_mask := hash_parameters boundary.state.inv
    have primeRange : d.strstart.toNat+(d.lookahead+n).toNat ≤ copied.size := by
      rw [size_copyRange,counts.2.1]
      dsimp only [fillEnd] at copyFit
      omega
    have primed := resume_prime_form (d := {d with lookahead := d.lookahead+n}) (wa := copied)
      params primeRange ready
    have primedRead : InsHForm read.hash_shift read.hash_mask (bfn copied) read.strstart.toNat read.ins_h := by
      change InsHForm d.hash_shift d.hash_mask (bfn copied) d.strstart.toNat read.ins_h at primed
      simpa only [readRecord] using primed
    change InsHForm read.hash_shift read.hash_mask (bfn output) read.strstart.toNat read.ins_h
    apply form_congr primedRead
    · apply unpadded
      rw [←readEnd]
      dsimp only [fillEnd]
      change 3 ≤ read.lookahead.toNat at large
      omega
    · apply unpadded
      rw [←readEnd]
      dsimp only [fillEnd]
      change 3 ≤ read.lookahead.toNat at large
      omega
  have content : LocalContent after cutoff r ds
      (readStream z n ref io (adlerValue z.adler ((ia.toList.drop io).take n.toNat))) result input origin base xs := by
    refine ⟨stateA,?_,?_,history,?_,symbols,⟨w,output,?_,bytes,view,form⟩,?_,?_,?_,boundary.trace,?_⟩
    · simpa only [record] using chainsA
    · rw [record];exact counts.2.2
    · rw [record];exact boundary.deferred
    · rw [record];exact win
    · rw [record];exact boundary.insert_le
    · simpa only [record] using frontierA
    · intro _;rw [record];exact insert
    · rw [record];exact boundary.accounted
  exact ⟨run,content,account,frame,shape,endpoint⟩

end ZlibF.Spec.Public.Proofs.CompressLocalResumeContent
