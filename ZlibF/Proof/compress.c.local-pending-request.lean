import ZlibF.Proof.«compress.c.local-header»
import ZlibF.Proof.«compress.c.local-pending»

/-! # Real ordinary requests that exhaust output while draining pending

This is the next complete actual public subcall after a split header. Its
entry checks, last-flush writes, pending publication and early OK return
use the locally established state. No global DGood/Rebuffer or callee
specification is assumed, and the old caller's typed slots remain separate.
-/
namespace ZlibF.Spec.Public.Proofs.CompressLocalRequest
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open Zlib.Deflate.Engine.Proofs ZlibF.Spec.Public
open ZlibF.Spec.Public.Proofs.CompressLocal ZlibF.Spec.Public.Proofs.CompressLocalInit
open ZlibF.Spec.Public.Proofs.CompressLocalHeader ZlibF.Spec.Public.Proofs.CompressLocalPending
set_option autoImplicit false
set_option maxRecDepth 100000

/-- Record the real last_flush store without global type uniqueness. -/
theorem local_last_flush {h : Heap} {r : ZStreamRef} {cutoff ds : Nat} {z : ZStream} {d : DeflateState}
    (state : LocalState h cutoff r ds z d) (flush : Int32) :
    LocalState (setD h ds {d with last_flush := flush}) cutoff r ds z {d with last_flush := flush} := by
  have inv : DStInv h ds {d with last_flush := flush} := {state.inv with blocks := state.inv.blocks_keys rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl}
  have next := local_state_setZD state (d' := {d with last_flush := flush}) rfl state.live.zalloc state.live.zfree rfl state.live.status inv (by trkeep)
  rwa [ZStreamRef.put_self state.live.hz] at next

/-- The actual BUSY entry, actual pending flush and actual early-return
write compose directly. The flush premise is an observed execution event;
its locally proved constructor is connected in the next theorem. -/
theorem pending_exhausted_entry {h after : Heap} {r : ZStreamRef} {ds : Nat}
    {z za : ZStream} {d da : DeflateState} {flush : Int32}
    (live : DLive h r ds z d) (busy : d.status = BUSY_STATE)
    (mode : flush = Z_NO_FLUSH ∨ flush = Z_FINISH)
    (out : z.next_out ≠ .null) (positive : z.avail_out ≠ 0)
    (valid : z.avail_in ≠ 0 → z.next_in ≠ .null) (pending : d.pending ≠ 0)
    (actual : flush_pending (some r) (setD h ds {d with last_flush := flush}) = .ok ((),after))
    (getZ : r.get after = some za) (getD : after.dstates ds = some da) (empty : za.avail_out = 0) :
    deflate (some r) flush h = .ok (Z_OK,setD after ds {da with last_flush := -1}) := by
  have check := stateCheck_live live
  have inputs : (z.avail_in != 0 && z.next_in == .null) = false := by
    by_cases zero : z.avail_in = 0
    · simp [zero]
    · simp [valid zero]
  have low : (flush < 0) = False := by rcases mode with eq|eq <;>rw [eq] <;>decide
  have high : (flush > Z_BLOCK) = False := by rcases mode with eq|eq <;>rw [eq] <;>decide
  have notFinished : (d.status == FINISH_STATE) = false := by rw [busy];decide
  rw [public_deflate_source]
  simp only [bind_app,pure_app,check,show ((0 : Int32) != 0) = false from rfl,low,high,
    decide_false,Bool.false_or,Bool.false_eq_true,ite_false,zrd_eq,live.hz,live.zst,castDeflateState,
    ldZStream_ok live.hz,ldDeflateState_tab live.hs,inputs,
    show (z.next_out == .null) = false from beq_eq_false_iff_ne.mpr out,notFinished,Bool.false_and,
    show (z.avail_out == 0) = false from beq_eq_false_iff_ne.mpr positive,
    wrD_eq,live.hs,show (d.pending != 0) = true from by simp [pending],ite_true,actual,getZ,empty,
    beq_self_eq_true,wrD_eq,getD,pure_app]

/-- A real ordinary request with at least its positive output offer queued
publishes exactly that offer and returns OK with zero remaining output.
It establishes its own actual flush run via the local pending producer. -/
theorem local_pending_ordinary {h : Heap} {r : ZStreamRef} {cutoff ds pb po ob oo : Nat}
    {z : ZStream} {d : DeflateState} {pending output : Array UInt8} {flush : Int32}
    (state : LocalState h cutoff r ds z d) (busy : d.status = BUSY_STATE)
    (mode : flush = Z_NO_FLUSH ∨ flush = Z_FINISH) (positive : z.avail_out ≠ 0)
    (valid : z.avail_in ≠ 0 → z.next_in ≠ .null) (enough : z.avail_out.toNat ≤ d.pending.toNat)
    (bits : d.bi_valid.toInt < 8) (buffer : d.pending_buf = .ref (.blk pb) 0)
    (cursor : d.pending_out = .ref (.blk pb) po) (pointer : z.next_out = .ref (.blk ob) oo)
    (outGet : h.bytes ob = some output) (pendingGet : h.bytes pb = some pending)
    (writable : h.ro ob = false) (separate : ob ≠ pb)
    (outBound : oo+z.avail_out.toNat ≤ output.size) (pendingBound : po+d.pending.toNat ≤ pending.size) :
    let recorded := {d with last_flush := flush}
    let copied := pendingCopyHeap (setD h ds recorded) r ds pb po ob oo z recorded pending output z.avail_out
    let nextZ := pendingStream z (.ref (.blk ob) (oo+z.avail_out.toNat)) z.avail_out
    let result := {pendingState recorded (.ref (.blk pb) (po+z.avail_out.toNat)) z.avail_out with last_flush := -1}
    let after := setD copied ds result
    deflate (some r) flush h = .ok (Z_OK,after) ∧ LocalState after cutoff r ds nextZ result ∧
      StreamAccounting z nextZ 0 z.avail_out.toNat ∧ nextZ.avail_out = 0 := by
  have selected : pendingLen d.pending z.avail_out = z.avail_out := UInt32.toNat_inj.mp (by
    rw [pendingLen_value,Nat.min_eq_right enough])
  have positiveNat : 0 < z.avail_out.toNat := by
    have nonzero : z.avail_out.toNat ≠ 0 := fun eq => positive (UInt32.toNat_inj.mp eq)
    omega
  have queued : d.pending ≠ 0 := by intro zero;rw [zero] at enough;change z.avail_out.toNat ≤ 0 at enough;omega
  have state0 := local_last_flush state flush
  obtain ⟨flushRun,stateA,account,_frame,_shape,_interval,_bytes⟩ := local_flush_pending_raw state0 bits buffer cursor pointer
    (by simpa using outGet) (by simpa using pendingGet) (by simpa using writable) separate outBound pendingBound
    (by change pendingLen d.pending z.avail_out ≠ 0;rw [selected];exact positive)
  have selected0 : pendingLen ({d with last_flush := flush} : DeflateState).pending z.avail_out = z.avail_out := selected
  rw [selected0] at flushRun stateA account
  have empty : (pendingStream z (.ref (.blk ob) (oo+z.avail_out.toNat)) z.avail_out).avail_out = 0 := by simp [pendingStream]
  have actual := pending_exhausted_entry state.live busy mode (by rw [pointer];intro bad;cases bad) positive valid queued
    flushRun stateA.live.hz stateA.live.hs empty
  exact ⟨actual,local_last_flush stateA (-1),account,empty⟩


/-- A caller's real one-byte output refill preserves the post-header
local state without using the global-Uniq Rebuffer relation. -/
theorem local_output_refill {h : Heap} {r : ZStreamRef} {cutoff ds : Nat} {z : ZStream} {d : DeflateState}
    (state : LocalState h cutoff r ds z d) :
    LocalState (r.put h {z with avail_out := 1}) cutoff r ds {z with avail_out := 1} d := by
  have next := local_state_setZD state (z' := {z with avail_out := 1}) (d' := d)
    rfl state.live.zalloc state.live.zfree rfl state.live.status state.inv (by trkeep)
  have getD : (r.put h {z with avail_out := 1}).dstates ds = some d := by simpa using state.live.hs
  rwa [setD_self getD] at next

/-- The actual one-byte first-header state feeds a second actual ordinary
call after a legal one-field refill. This second complete call drains the
remaining header byte and returns OK with no output room; it reaches no
unproved data-dispatch callee. -/
theorem local_second_header_call {h : Heap} {r : ZStreamRef} {cutoff ds pb ob oo : Nat}
    {z : ZStream} {d : DeflateState} {buf output : Array UInt8} {flush : Int32}
    (state : LocalState (oneHeaderHeap h r ds pb ob oo z d buf output) cutoff r ds
      (oneHeaderStream z ob oo) (oneHeaderState d))
    (pendingPtr : d.pending_buf = .ref (.blk pb) 0) (bits : d.bi_valid = 0)
    (one : z.avail_out = 1) (separate : ob ≠ pb) (writable : h.ro ob = false)
    (room : 2 ≤ buf.size) (outBound : oo+2 ≤ output.size)
    (valid : z.avail_in ≠ 0 → z.next_in ≠ .null) (mode : flush = Z_NO_FLUSH ∨ flush = Z_FINISH) :
    let firstHeap := oneHeaderHeap h r ds pb ob oo z d buf output
    let offered := {(oneHeaderStream z ob oo) with avail_out := 1}
    let ready := r.put firstHeap offered
    ∃ after za da,
      deflate (some r) flush ready = .ok (Z_OK,after) ∧ LocalState after cutoff r ds za da ∧
      StreamAccounting offered za 0 1 ∧ za.avail_out = 0 ∧ da.pending = 0 := by
  let firstHeap := oneHeaderHeap h r ds pb ob oo z d buf output
  let offered := {(oneHeaderStream z ob oo) with avail_out := 1}
  let ready := r.put firstHeap offered
  have next := local_output_refill state
  have outGet : ready.bytes ob = some (copyRange output (zlibHeaderBytes buf) oo 0 1) := by
    simp [ready,firstHeap,oneHeaderHeap]
  have pendingGet : ready.bytes pb = some (zlibHeaderBytes buf) := by
    simp [ready,firstHeap,oneHeaderHeap,upd_ne _ _ _ _ (Ne.symm separate)]
  have bitBound : (oneHeaderState d).bi_valid.toInt < 8 := by simp [oneHeaderState,bits]
  have cursor : (oneHeaderState d).pending_out = .ref (.blk pb) 1 := by simp [oneHeaderState,pendingPtr,advance]
  have raw : offered.next_out = .ref (.blk ob) (oo+1) := rfl
  obtain ⟨actual,stateA,account,empty⟩ := local_pending_ordinary next (by rfl) mode
    (by change (1 : UInt32) ≠ 0;decide) valid (by change (1 : Nat) ≤ 1;decide) bitBound pendingPtr cursor raw
    outGet pendingGet (by simpa [ready,firstHeap,oneHeaderHeap] using writable) separate
    (by change oo+1+1 ≤ (copyRange output (zlibHeaderBytes buf) oo 0 1).size;rw [size_copyRange];omega)
    (by change 1+1 ≤ (zlibHeaderBytes buf).size;simp only [zlibHeaderBytes,Array.size_set!];exact room)
  refine ⟨_,_,_,actual,stateA,account,empty,?_⟩
  change (1 : UInt64)-(1 : UInt32).toUInt64 = 0
  rfl

end ZlibF.Spec.Public.Proofs.CompressLocalRequest
