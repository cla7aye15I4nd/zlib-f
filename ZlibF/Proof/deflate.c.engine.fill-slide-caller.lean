import ZlibF.Proof.«deflate.c.engine.fill-slide-call»
import ZlibF.Spec.Functional.Checksums

/-! # A complete sliding fill call from public caller buffers -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesBase)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

theorem window_pending_separate {h : Heap} {r : ZStreamRef} {ds w b : Nat}
    {z : ZStream} {d : DeflateState} (good : DGood h r ds z d)
    (win : d.window = .ref (.blk w) 0) (pending : d.pending_buf = .ref (.blk b) 0) : w ≠ b := by
  obtain ⟨w0, p, q, b0, blocks⟩ := good.inv.blocks
  have windowId : w0 = w := by simpa only [win, Ptr.ref.injEq, BRef.blk.injEq, and_true] using blocks.win.symm
  have pendingId : b0 = b := by simpa only [pending, Ptr.ref.injEq, BRef.blk.injEq, and_true] using blocks.pbuf.symm
  subst w0 b0
  exact blocks.wb

set_option maxHeartbeats 2500000 in
/-- The whole actual fill_window call with a taken slide, nonempty new
input, wrap=1 and no deferred insertion. Public buffer storage supplies
the readable input and its separation from the private window. Actual
sliding, both hash loops, input accounting, checksum, priming, termination
and padding compose on one heap. The packed symbols and frequencies stay
unchanged; block balance and logical lazy history survive the window move.
-/
theorem fill_window_slide_caller {h : Heap} {r : ZStreamRef} {ds w p q b io top origin : Nat}
    {z : ZStream} {d : DeflateState} {ref : BRef} {wa buf : Array UInt8} {pa qa : Array UInt16}
    {input : Nat → UInt8} {xs : List Symbol} {credit : Int}
    (good : DGood h r ds z d) (env : HashEnv h d w q p wa qa pa)
    (chains : HashChains (wfn qa) (wfn pa) (bfn wa) d.hash_size d.hash_shift d.hash_mask
      d.w_size.toNat top (fillEnd d))
    (base : TreesBase h ds d b buf) (ledger : SymbolLedger buf d xs)
    (balance : BlockBalance d xs credit) (lo : 0 ≤ credit) (hi : credit ≤ 1)
    (range : fillEnd d ≤ d.window_size.toNat) (short : d.lookahead.toNat < 262)
    (taken : d.strstart ≥ d.w_size + (d.w_size - MIN_LOOKAHEAD_u))
    (insert : d.insert = 0) (wrap : d.wrap = 1) (buffers : StreamBuffers h r)
    (pointer : z.next_in = .ref ref io) (nonempty : z.avail_in ≠ 0)
    (history : LazyHistory input origin d)
    (view : ∀ i, i < fillEnd d → bfn wa i = input (origin + i)) :
    ∃ used after z' result output extended,
      fill_window (some (.tab ds)) h = .ok ((), after) ∧
      DGood after r ds z' result ∧ HeapChains after result (top - d.w_size.toNat) ∧
      StreamAccounting z z' used 0 ∧
      result.window = .ref (.blk w) 0 ∧ after.bytes w = some output ∧
      result.strstart.toNat = d.strstart.toNat - d.w_size.toNat ∧
      result.lookahead.toNat = d.lookahead.toNat + used ∧
      result.insert = 0 ∧ result.wrap = 1 ∧ result.sym_next = d.sym_next ∧
      fillEnd result ≤ result.window_size.toNat ∧
      min (fillEnd result + 258) result.window_size.toNat ≤ result.high_water.toNat ∧
      (3 ≤ result.lookahead.toNat → InsHForm result.hash_shift result.hash_mask
        (bfn output) result.strstart.toNat result.ins_h) ∧
      LazyHistory extended (origin + d.w_size.toNat) result ∧ DeferredByte result ∧
      (∀ i, i < fillEnd result → bfn output i = extended (origin + d.w_size.toNat + i)) ∧
      (∀ i, i < origin + fillEnd d → extended i = input i) ∧
      after.bytes b = some buf ∧ SymbolLedger buf result xs ∧ BlockBalance result xs credit := by
  have count := good.inv.sym.2.2.1
  obtain ⟨qa', pa', prefixRun, sizeH, sizeP, head, prev⟩ :=
    fill_slide_run good env base ledger count balance lo hi range taken
  let hs := slideHeap h ds w p q d wa pa' qa'
  let slid := slideState d
  let moved := slideWindow d wa
  have goodS : DGood hs r ds z slid := slide_good good env sizeP sizeH
  have getS : hs.bytes w = some moved := by simp [hs, moved, slideHeap]
  have winS : slid.window = .ref (.blk w) 0 := env.win
  have chainsS : HeapChains hs slid (top - d.w_size.toNat) :=
    slide_heap_chains good env chains range taken head prev
  have geometry := fill_slide_counts good env.win env.wbytes range taken
  have ws := slide_window_sizes good
  have rangeS : fillEnd slid ≤ slid.window_size.toNat := by
    change fillEnd (slideState d) ≤ d.window_size.toNat
    have wsz := good.inv.wsz
    omega
  have noSlide : ¬ slid.strstart ≥ slid.w_size + (slid.w_size - MIN_LOOKAHEAD_u) := geometry.2.2.2.2.2.2.2.2
  have insertS : slid.insert = 0 := by
    simp [slid, slideState, slideBeforeHash, insert, UInt32.lt_iff_toNat_lt]
  obtain ⟨ia, data, inputBound⟩ := caller_input_array good buffers pointer
  have separate := caller_input_window_separate good buffers env.win pointer
  have dataS : Space.get hs ref = some ia := by
    rw [slide_input_frame good separate]
    exact data
  have historyS : LazyHistory input (origin + d.w_size.toNat) slid :=
    slide_lazy_history good env.win env.wbytes range taken history
  have deferredS : DeferredByte slid := by
    intro _
    change 1 ≤ (slideState d).strstart.toNat
    omega
  have viewS : ∀ i, i < fillEnd slid → bfn moved i = input (origin + d.w_size.toNat + i) := by
    intro i bound
    have oldBound : i + d.w_size.toNat < fillEnd d := by
      change i < fillEnd (slideState d) at bound
      omega
    rw [slide_window_view good env.win env.wbytes range taken i oldBound, view _ oldBound]
    congr 1
    omega
  let n := rbLen z.avail_in (fillMore slid)
  let copied := copyRange moved ia (fillEnd slid) io n.toNat
  let read := resumeReadState slid n copied
  let result := resumedFillState slid n copied
  let output := fillRange copied (paddingStart read) (paddingCount read) 0
  let after := resumedFillHeap hs r ds w z slid ref io ia moved
  let z' := readStream z n ref io (adlerValue z.adler ((ia.toList.drop io).take n.toNat))
  let extended := extendInput input (origin + d.w_size.toNat + fillEnd slid) ia io
  obtain ⟨run, goodA, chainsA, winA, bytesA, rangeA, paddingA, formA⟩ :=
    fill_window_resume_complete goodS chainsS winS getS rangeS short noSlide insertS wrap
      pointer dataS inputBound nonempty (Or.inl separate)
  obtain ⟨historyA, deferredA, viewA⟩ := resumed_fill_history (ref := ref)
    goodS winS getS rangeS inputBound historyS deferredS viewS
  have inputCount : n.toNat ≤ z.avail_in.toNat := by
    have c := rbLen_nat z.avail_in (fillMore slid)
    change n.toNat = min z.avail_in.toNat (fillMore slid).toNat at c
    omega
  have counts := resume_read_counts goodS winS getS rangeS
  obtain ⟨key, high, fields⟩ := resumed_fill_record slid n copied
  change result = _ at fields
  have pendingS : hs.bytes b = some buf := slide_pending_frame good env.win base.pbuf base.bytes
  have distinct := window_pending_separate good env.win base.pbuf
  have balanceS : BlockBalance slid xs credit :=
    slide_balance good env.win env.wbytes base ledger count balance lo hi range taken
  refine ⟨n.toNat, after, z', result, output, extended, ?_, goodA, chainsA,
    read_stream_accounting z n ref io _ pointer inputCount, winA, bytesA, ?_, ?_, ?_, ?_, ?_,
    rangeA, paddingA, formA, historyA, deferredA, viewA, ?_, ?_, ?_, ?_⟩
  · exact (fill_window_slide_transfer good env sizeP sizeH range taken prefixRun).trans run
  · rw [fields]
    exact geometry.2.2.2.2.1
  · rw [fields]
    exact counts.2.1
  · rw [fields]
    exact insertS
  · rw [fields]
    exact wrap
  · rw [fields]
    rfl
  · intro i bound
    have before : i < origin + d.w_size.toNat + fillEnd slid := by
      change i < origin + d.w_size.toNat + fillEnd (slideState d)
      omega
    simp only [extended, extendInput, before, if_true]
  · simpa only [after, resumedFillHeap, paddedHeap, resumeReadHeap, setD_bytes, ZStreamRef.put_bytes,
      upd_ne _ _ _ _ distinct.symm] using pendingS
  · rw [fields]
    exact (slide_ledger ledger).keep rfl rfl rfl rfl
  · rw [fields]
    exact balanceS

end Zlib.Deflate.Engine.Proofs
