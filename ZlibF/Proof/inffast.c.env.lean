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

/-- How the window block relates to the output block. Without `alias` (every `Env`): another
block. With `alias` (`inflateBack`, whose output is the window): the output block itself is
allowed, and then `wnext = 0` and the window ends no later than the output range (`inside`). -/
@[reducible] def WinRel : Bool → Nat → Nat → UInt32 → Prop → Prop
  | false, wb, ob, _, _ => wb ≠ ob
  | true, wb, ob, wnext, inside => wb = ob → wnext = 0 ∧ inside

/-- Everything `inflate_fast` needs of the heap `h0` at entry, with the witnesses. These are the preconditions of
`inflate_fast_safe` (`Zlib.Inffast.Proofs.Env.of_pre` builds one from the hypotheses of the theorem). -/
structure EnvG (alias : Bool) where
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
  /-- Input and output are distinct blocks, or disjoint ranges of one block
  (`tests/regression/inflate-shared-block`). -/
  hsep : ib ≠ ob ∨ (ib = ob ∧
    (i0 + sm0.avail_in.toNat ≤ o0 ∨ o0 + sm0.avail_out.toNat ≤ i0))
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
    s0.window = .ref (BRef.blk wb) woff ∧
      WinRel alias wb ob s0.wnext (woff + s0.wsize.toNat ≤ o0 + sm0.avail_out.toNat) ∧ h0.bytes wb = some W ∧
      woff + s0.wsize.toNat ≤ W.size
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

/-- The situation of every caller but `inflateBack`: the window is another block than the output. -/
abbrev Env := EnvG false

/-- The heap while `inflate_fast` runs: the output block is `A`, the message of the stream is `msg` and the mode of
the state is `m`; nothing else differs from `h0`. -/
def EnvG.heap {α : Bool} (e : EnvG α) (A : Array UInt8) (msg : BPtr) (m : UInt32) : Heap :=
  ZStreamRef.put
    { e.h0 with bytes := upd e.h0.bytes e.ob (some A),
                istates := upd e.h0.istates e.stid (some { e.s0 with mode := m }) }
    e.r { e.sm0 with msg := msg }

/-- The heap of the loop before any `break`: the message and the mode are those of the entry. -/
def EnvG.hp {α : Bool} (e : EnvG α) (A : Array UInt8) : Heap := e.heap A e.sm0.msg e.s0.mode

variable {α : Bool} (e : EnvG α)

theorem EnvG.heap_bytes (A msg m) : (e.heap A msg m).bytes = upd e.h0.bytes e.ob (some A) := by
  unfold EnvG.heap; rw [put_bytes]

theorem EnvG.heap_ro (A msg m) : (e.heap A msg m).ro = e.h0.ro := by
  unfold EnvG.heap; rw [put_ro]

theorem EnvG.heap_istates (A msg m) :
    (e.heap A msg m).istates = upd e.h0.istates e.stid (some { e.s0 with mode := m }) := by
  unfold EnvG.heap; rw [put_istates]

theorem EnvG.heap_static (A msg m) : (e.heap A msg m).static = e.h0.static := by
  unfold EnvG.heap; rw [put_static]

theorem EnvG.heap_rget (A msg m) : e.r.get (e.heap A msg m) = some { e.sm0 with msg := msg } := by
  unfold EnvG.heap
  apply put_get e.r _ e.sm0
  cases hr : e.r with
  | tab i =>
    have := e.hsm; rw [hr] at this; simpa [ZStreamRef.get] using this
  | in_gzstate_strm i =>
    have := e.hsm; rw [hr] at this; simpa [ZStreamRef.get] using this

theorem EnvG.heap_bytes_ne (A msg m) {b : Nat} (hb : b ≠ e.ob) : (e.heap A msg m).bytes b = e.h0.bytes b := by
  rw [e.heap_bytes]; exact upd_ne _ _ _ _ hb

theorem EnvG.heap_bytes_ob (A msg m) : (e.heap A msg m).bytes e.ob = some A := by
  rw [e.heap_bytes]; exact upd_same _ _ _

theorem EnvG.heap_ro_ob (A msg m) : (e.heap A msg m).ro e.ob = false := by
  rw [e.heap_ro]; exact e.hro

/-! ### The input block

The input may be a range of the output block, disjoint from the output
range. The array at the input block is then the current output array; it
agrees with the input at entry on the unread input (`InputFrame`), since the
decoder writes only in the output range. -/

/-- The array at the input block while the output block holds `A`. -/
def EnvG.inArr (A : Array UInt8) : Array UInt8 := if e.ib = e.ob then A else e.IN

/-- When input and output share a block, the output array `A` has the size of
the block at entry and agrees with the input at entry from `i` to the end of
the input. -/
def EnvG.InputFrame (A : Array UInt8) (i : Nat) : Prop :=
  e.ib = e.ob → A.size = e.A0.size ∧
    ∀ k, i ≤ k → k < e.i0 + e.sm0.avail_in.toNat → A[k]? = e.IN[k]?

theorem EnvG.heap_bytes_in (A msg m) : (e.heap A msg m).bytes e.ib = some (e.inArr A) := by
  unfold EnvG.inArr
  by_cases same : e.ib = e.ob
  · rw [if_pos same, same, e.heap_bytes_ob]
  · rw [if_neg same, e.heap_bytes_ne A msg m same, e.hIN]

theorem EnvG.IN_eq_A0 (same : e.ib = e.ob) : e.IN = e.A0 := by
  have a := e.hIN
  rw [same, e.hA0] at a
  exact (Option.some.inj a).symm

theorem EnvG.inArr_size {A : Array UInt8} {i : Nat} (frame : e.InputFrame A i) :
    (e.inArr A).size = e.IN.size := by
  unfold EnvG.inArr
  by_cases same : e.ib = e.ob
  · rw [if_pos same, (frame same).1, e.IN_eq_A0 same]
  · rw [if_neg same]

theorem EnvG.InputFrame.get {α : Bool} {e : EnvG α} {A : Array UInt8} {s k : Nat} (frame : e.InputFrame A s)
    (le : s ≤ k) (lt : k < e.i0 + e.sm0.avail_in.toNat) : (e.inArr A)[k]? = e.IN[k]? := by
  unfold EnvG.inArr
  by_cases same : e.ib = e.ob
  · rw [if_pos same]
    exact (frame same).2 k le lt
  · rw [if_neg same]

theorem EnvG.InputFrame.mono {α : Bool} {e : EnvG α} {A : Array UInt8} {s s' : Nat} (frame : e.InputFrame A s)
    (le : s ≤ s') : e.InputFrame A s' :=
  fun same => ⟨(frame same).1, fun k le' lt => (frame same).2 k (Nat.le_trans le le') lt⟩

/-- At entry the output array is the block itself. -/
theorem EnvG.inputFrame_entry (i : Nat) : e.InputFrame e.A0 i :=
  fun same => ⟨rfl, fun k _ _ => by rw [e.IN_eq_A0 same]⟩

/-- Writes inside the output range keep the frame. -/
theorem EnvG.InputFrame.write {α : Bool} {e : EnvG α} {A A' : Array UInt8} {s s' o o' : Nat}
    (frame : e.InputFrame A s) (le : s ≤ s') (start : e.i0 ≤ s) (lo : e.o0 ≤ o)
    (hi : o' ≤ e.o0 + e.sm0.avail_out.toNat) (size : A'.size = A.size)
    (outside : ∀ j, (j < o ∨ o' ≤ j) → A'[j]? = A[j]?) : e.InputFrame A' s' := by
  intro same
  obtain ⟨sz, agree⟩ := frame same
  refine ⟨size.trans sz, fun k le' lt => ?_⟩
  have apart : k < o ∨ o' ≤ k := by
    rcases e.hsep with ne | ⟨_, disjoint⟩
    · exact absurd same ne
    · omega
  rw [outside k apart]
  exact agree k (Nat.le_trans le le') lt

/-- An output array that agrees with the block at entry outside the written
output holds the unread input. -/
theorem EnvG.inputFrame_of_frame {A : Array UInt8} {i o : Nat} (size : A.size = e.A0.size)
    (outside : ∀ j, (j < e.o0 ∨ o ≤ j) → A[j]? = e.A0[j]?)
    (hi : o ≤ e.o0 + e.sm0.avail_out.toNat) (start : e.i0 ≤ i) : e.InputFrame A i := by
  intro same
  refine ⟨size, fun k le lt => ?_⟩
  have apart : k < e.o0 ∨ o ≤ k := by
    rcases e.hsep with ne | ⟨_, disjoint⟩
    · exact absurd same ne
    · omega
  rw [outside k apart, e.IN_eq_A0 same]

theorem EnvG.inArr_size_of {A : Array UInt8} (size : A.size = e.A0.size) :
    (e.inArr A).size = e.IN.size := by
  unfold EnvG.inArr
  by_cases same : e.ib = e.ob
  · rw [if_pos same, size, e.IN_eq_A0 same]
  · rw [if_neg same]

end Zlib.Inffast.Proofs
