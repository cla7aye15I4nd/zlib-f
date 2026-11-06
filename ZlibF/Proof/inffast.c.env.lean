import ZlibF.Proof.«inffast.c.base»
import ZlibF.Proof.«inffast.c.tableok»

/-!
# inffast.c: what `inflate_fast` needs of its situation

`Zlib.Inffast.Spec` states the entry conditions and the facts about the decoding tables as predicates over the heap.
`Zlib.Inffast.Proofs.Env` bundles them with the witnesses (block numbers, offsets, arrays) that the proofs of the
loop use.

**Tables.** `TableSafe` is the shape that `inflate_table` gives (`proof/inftrees.md`, theorem T2) and that `lenfix`
and `distfix` have: the root table has `2^root` entries inside the array, an entry is a leaf (literal, base value,
end of block, invalid code) or a link to a second level inside the array whose entries are leaves; the number of
bits of a root entry plus that of a second-level entry is at most 15; the extra bits of a length base are at most 5 and
those of a distance base at most 13; a length base is between 3 and 258 and a distance base is at least 1.
-/


namespace Zlib.Inffast.Proofs
open C Zlib.Inffast Zlib.Inffast.Spec

/-! ### `ZStreamRef.put` leaves every table but the stream tables alone -/

theorem put_bytes (r : ZStreamRef) (h : Heap) (v : ZStream) : (r.put h v).bytes = h.bytes := by
  cases r <;> simp only [ZStreamRef.put] <;> split <;> rfl

theorem put_ro (r : ZStreamRef) (h : Heap) (v : ZStream) : (r.put h v).ro = h.ro := by
  cases r <;> simp only [ZStreamRef.put] <;> split <;> rfl

theorem put_istates (r : ZStreamRef) (h : Heap) (v : ZStream) : (r.put h v).istates = h.istates := by
  cases r <;> simp only [ZStreamRef.put] <;> split <;> rfl

theorem put_static (r : ZStreamRef) (h : Heap) (v : ZStream) : (r.put h v).static = h.static := by
  cases r <;> simp only [ZStreamRef.put] <;> split <;> rfl

theorem put_get (r : ZStreamRef) (h : Heap) (v0 v : ZStream) (hg : r.get h = some v0) :
    r.get (r.put h v) = some v := by
  cases r with
  | tab i =>
    simp only [ZStreamRef.get] at hg
    simp only [ZStreamRef.put, hg, ZStreamRef.get]
    exact upd_same _ _ _
  | in_gzstate_strm i =>
    simp only [ZStreamRef.get] at hg
    cases hs : h.gzstates i with
    | none => simp [hs] at hg
    | some g => simp [ZStreamRef.put, ZStreamRef.get, hs]

theorem put_put (r : ZStreamRef) (h : Heap) (v0 v v' : ZStream) (hg : r.get h = some v0) :
    r.put (r.put h v) v' = r.put h v' := by
  cases r with
  | tab i =>
    simp only [ZStreamRef.get] at hg
    simp [ZStreamRef.put, hg, upd_upd]
  | in_gzstate_strm i =>
    simp only [ZStreamRef.get] at hg
    cases hs : h.gzstates i with
    | none => simp [hs] at hg
    | some g => simp [ZStreamRef.put, hs, upd_upd]

theorem put_istates_comm (r : ZStreamRef) (h : Heap) (v : ZStream) (t : Tbl (Option InflateState)) :
    ({ r.put h v with istates := t } : Heap) = r.put { h with istates := t } v := by
  cases r <;> simp only [ZStreamRef.put] <;> split <;> rfl

theorem put_bytes_comm (r : ZStreamRef) (h : Heap) (v : ZStream) (t : Tbl (Option (Array UInt8))) :
    ({ r.put h v with bytes := t } : Heap) = r.put { h with bytes := t } v := by
  cases r <;> simp only [ZStreamRef.put] <;> split <;> rfl

/-! ### The situation -/

/-- Everything `inflate_fast` needs of the heap `h0` at entry, with the witnesses. These are the preconditions of
`inflate_fast_safe` (`Zlib.Inffast.Proofs.Env.of_pre` builds one from the hypotheses of the theorem). -/
structure Env where
  h0 : Heap
  strm : ZStreamPtr
  start : UInt32
  -- the stream record and the state
  r : ZStreamRef
  sm0 : ZStream
  stid : Nat
  s0 : InflateState
  hstrm : strm = some r
  hsm : r.get h0 = some sm0
  hrw : r.isRo = false
  hstate : sm0.state = some (StateRef.inflate stid)
  hs0 : h0.istates stid = some s0
  -- the input
  ib : Nat
  i0 : Nat
  IN : Array UInt8
  hnin : sm0.next_in = .ref (BRef.blk ib) i0
  hIN : h0.bytes ib = some IN
  hai : 6 ≤ sm0.avail_in.toNat
  hINsz : i0 + sm0.avail_in.toNat ≤ IN.size
  hINbig : IN.size < 2 ^ 63
  -- the output
  ob : Nat
  o0 : Nat
  A0 : Array UInt8
  hnout : sm0.next_out = .ref (BRef.blk ob) o0
  hA0 : h0.bytes ob = some A0
  hro : h0.ro ob = false
  hao : 258 ≤ sm0.avail_out.toNat
  hAsz : o0 + sm0.avail_out.toNat ≤ A0.size
  hAbig : A0.size < 2 ^ 63
  hstart : sm0.avail_out.toNat ≤ start.toNat
  hbeg : start.toNat - sm0.avail_out.toNat ≤ o0
  hsep : ib ≠ ob
  -- the bit buffer
  hbits : s0.bits.toNat < 8
  hhold : s0.hold.toNat < 2 ^ s0.bits.toNat
  hsane : s0.sane ≠ 0
  -- the window
  hws : s0.wsize.toNat ≤ 32768
  hwh : s0.whave.toNat ≤ s0.wsize.toNat
  hwn : s0.wnext.toNat ≤ s0.wsize.toNat
  wb : Nat
  woff : Nat
  W : Array UInt8
  hwin : s0.whave ≠ 0 →
    s0.window = .ref (BRef.blk wb) woff ∧ wb ≠ ob ∧ h0.bytes wb = some W ∧ woff + s0.wsize.toNat ≤ W.size
  -- the tables
  rl : CodeRef
  ol : Nat
  LCA : Array Code
  hlc : s0.lencode = .ref rl ol
  hLCA : Space.get h0 rl = some LCA
  hlt : LenTableSafe LCA ol s0.lenbits.toNat
  rd : CodeRef
  od : Nat
  DCA : Array Code
  hdc : s0.distcode = .ref rd od
  hDCA : Space.get h0 rd = some DCA
  hdt : DistTableSafe DCA od s0.distbits.toNat

/-- The heap while `inflate_fast` runs: the output block is `A`, the message of the stream is `msg` and the mode of
the state is `m`; nothing else differs from `h0`. -/
def Env.heap (e : Env) (A : Array UInt8) (msg : BPtr) (m : UInt32) : Heap :=
  ZStreamRef.put
    { e.h0 with bytes := upd e.h0.bytes e.ob (some A),
                istates := upd e.h0.istates e.stid (some { e.s0 with mode := m }) }
    e.r { e.sm0 with msg := msg }

/-- The heap of the loop before any `break`: the message and the mode are those of the entry. -/
def Env.hp (e : Env) (A : Array UInt8) : Heap := e.heap A e.sm0.msg e.s0.mode

variable (e : Env)

theorem Env.heap_bytes (A msg m) : (e.heap A msg m).bytes = upd e.h0.bytes e.ob (some A) := by
  unfold Env.heap; rw [put_bytes]

theorem Env.heap_ro (A msg m) : (e.heap A msg m).ro = e.h0.ro := by
  unfold Env.heap; rw [put_ro]

theorem Env.heap_istates (A msg m) :
    (e.heap A msg m).istates = upd e.h0.istates e.stid (some { e.s0 with mode := m }) := by
  unfold Env.heap; rw [put_istates]

theorem Env.heap_static (A msg m) : (e.heap A msg m).static = e.h0.static := by
  unfold Env.heap; rw [put_static]

theorem Env.heap_rget (A msg m) : e.r.get (e.heap A msg m) = some { e.sm0 with msg := msg } := by
  unfold Env.heap
  apply put_get e.r _ e.sm0
  cases hr : e.r with
  | tab i =>
    have := e.hsm; rw [hr] at this; simpa [ZStreamRef.get] using this
  | in_gzstate_strm i =>
    have := e.hsm; rw [hr] at this; simpa [ZStreamRef.get] using this

theorem Env.heap_bytes_ne (A msg m) {b : Nat} (hb : b ≠ e.ob) : (e.heap A msg m).bytes b = e.h0.bytes b := by
  rw [e.heap_bytes]; exact upd_ne _ _ _ _ hb

theorem Env.heap_bytes_ob (A msg m) : (e.heap A msg m).bytes e.ob = some A := by
  rw [e.heap_bytes]; exact upd_same _ _ _

theorem Env.heap_ro_ob (A msg m) : (e.heap A msg m).ro e.ob = false := by
  rw [e.heap_ro]; exact e.hro

end Zlib.Inffast.Proofs
