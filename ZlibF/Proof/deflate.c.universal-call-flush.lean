import ZlibF.Proof.«deflate.c.universal-call-record»
import ZlibF.Proof.«deflate.c.engine.pending-empty-cursor»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-pending-phase»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-pending-contract»

/-!
# deflate.c: a flush inside the header stages

Batch C (`deflate_header_trailer`). The extra, name and comment stages fill `pending_buf` to its
end and flush. With fewer than eight held bits (which `deflatePrime` keeps) `flush_pending` needs no
room beyond `pending_buf`. This file states that flush for either kind of output view, with what
the header stages need afterwards: the invariants, the caller buffers, the cursor after a full
drain, the checksum, and the header records.
-/

namespace Zlib.Deflate.Universal.Call
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Deflate.Engine.Proofs
open Zlib.Trees.Proofs.Out (TreesInvAt BitsDiff)
set_option autoImplicit false

theorem uniq_gzheaders_none {h : Heap} (uniq : Uniq h) {x : Nat}
    (other : h.bytes x ≠ none ∨ h.streams x ≠ none ∨ h.dstates x ≠ none ∨ h.gzstates x ≠ none) :
    h.gzheaders x = none := by
  have count := uniq x
  cases g : h.gzheaders x with
  | none => rfl
  | some _ =>
    exfalso
    rw [g] at count
    rcases other with o | o | o | o <;>
    · obtain ⟨v, e⟩ := Option.ne_none_iff_exists'.mp o
      rw [e] at count
      simp only [cnt_some] at count
      omega

theorem stream_root_gzheaders {h : Heap} (uniq : Uniq h) {r : ZStreamRef} {z : ZStream}
    (get : r.get h = some z) {x : Nat} (root : StreamRoot r x) : h.gzheaders x = none := by
  cases r with
  | tab i =>
    subst root
    exact uniq_gzheaders_none uniq (Or.inr (Or.inl (by simp only [ZStreamRef.get] at get; rw [get]; simp)))
  | in_gzstate_strm i =>
    subst root
    apply uniq_gzheaders_none uniq (Or.inr (Or.inr (Or.inr ?_)))
    simp only [ZStreamRef.get] at get
    intro none
    rw [none] at get
    cases get

/-- A frame whose changed keys hold no header record keeps every header record. -/
theorem frame_gzheaders {h g : Heap} {changed : Nat → Prop} (frame : Frame h g changed)
    (others : ∀ x, changed x → h.gzheaders x = none) {i : Nat} {gh : GzHeader}
    (get : h.gzheaders i = some gh) : g.gzheaders i = some gh := by
  have live : h.live i := Or.inr (Or.inr (Or.inr (Or.inl (by rw [get]; simp))))
  have kept : ¬ changed i := fun c => by rw [others i c] at get; cases get
  rw [((frame.2.2.2.2.2 i live kept).2.2.2.1), get]

theorem put_byte_view_keeps (current : Heap) (r : BRef) (a : Array UInt8) :
    (Space.put current r a : Heap).gzheaders = current.gzheaders ∧
      (Space.put current r a : Heap).static = current.static := by
  cases r with
  | dstate_depth id =>
    show (match current.dstates id with
      | some s => { current with dstates := upd current.dstates id (some { s with depth := a }) }
      | none => current).gzheaders = _ ∧ (match current.dstates id with
      | some s => { current with dstates := upd current.dstates id (some { s with depth := a }) }
      | none => current).static = _
    split <;> exact ⟨rfl, rfl⟩
  | _ => exact ⟨rfl, rfl⟩

theorem restore_gzheaders (before : Heap) (regions : List Region) :
    ∀ after : Heap, (restoreRegions before after regions).gzheaders = after.gzheaders ∧
      (restoreRegions before after regions).static = after.static := by
  induction regions with
  | nil => intro after; exact ⟨rfl, rfl⟩
  | cons region rest ih =>
    intro after
    simp only [restoreRegions, List.foldl_cons] at ih ⊢
    obtain ⟨a1, a2⟩ := ih (match region.pointer with
      | .null => after
      | .ref r _ => match Space.get before r with
        | none => after
        | some a => Space.put after r a)
    refine ⟨a1.trans ?_, a2.trans ?_⟩ <;>
    split
    all_goals first | rfl | (split <;> first | rfl | exact (put_byte_view_keeps _ _ _).1 | exact (put_byte_view_keeps _ _ _).2)

/-- **A flush with fewer than eight held bits**, for either kind of output view. -/
theorem header_flush {h : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream} {d : DeflateState}
    {buf : Array UInt8} (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) (low : d.bi_valid.toInt < 8) (cursor : d.pending_out = d.pending_buf)
    (out : z.next_out ≠ .null) :
    ∃ (produced : Nat) (after : Heap) (z' : ZStream) (d' : DeflateState),
      flush_pending (some r) h = .ok ((), after) ∧ DGood after r ds z' d' ∧
      (∃ buf', TreesInvAt after ds d' pb buf' ∧ buf'.size = buf.size) ∧ StreamBuffers after r ∧
      StreamAccounting z z' 0 produced ∧ produced = min d.pending.toNat z.avail_out.toNat ∧
      d'.pending.toNat + produced = d.pending.toNat ∧
      d' = { d with pending := d'.pending, pending_out := d'.pending_out } ∧
      (d'.pending = 0 → d'.pending_out = d'.pending_buf) ∧ z'.adler = z.adler ∧
      (∀ i g, h.gzheaders i = some g → after.gzheaders i = some g) ∧ after.static = h.static ∧
      ByteSizes h after := by
  obtain ⟨ob, pointer⟩ := Block.output_pointer_cases good buffers out
  have cursor0 : d.pending = 0 → d.pending_out = d.pending_buf := fun _ => cursor
  have common : ∀ {produced : Nat} {after : Heap} {z' : ZStream} {d' : DeflateState},
      flush_pending (some r) h = .ok ((), after) → DGood after r ds z' d' → ByteSizes h after →
      StreamAccounting z z' 0 produced → d' = { d with pending := d'.pending, pending_out := d'.pending_out } →
      (∃ buf', TreesInvAt after ds d' pb buf' ∧ buf'.size = buf.size) ∧ StreamBuffers after r := by
    intro produced after z' d' _run goodA sizes account fields
    obtain ⟨d0, b0, buf0, treesA⟩ := goodA.trees
    have state : d0 = d' := Option.some.inj (treesA.base.dstate.symm.trans goodA.live.hs)
    subst d0
    have block : b0 = pb := by
      have p1 := treesA.base.pbuf
      have p2 := trees.base.pbuf
      rw [fields] at p1
      have := p1.symm.trans p2
      simpa using this
    subst b0
    obtain ⟨next, getN, sizeN⟩ := sizes.get (.blk pb) buf trees.base.bytes
    have same : buf0 = next := Option.some.inj (treesA.base.bytes.symm.trans getN)
    subst same
    have owned := stream_owned_keys good goodA (by rw [fields]) (by rw [fields]) (by rw [fields]) (by rw [fields])
    exact ⟨⟨buf0, ⟨treesA.base, treesA.run⟩, sizeN⟩,
      stream_buffers_sizes good.live.hz goodA.live.hz buffers sizes owned account⟩
  rcases pointer with ⟨oo, ptr⟩ | ⟨oo, ptr⟩
  · obtain ⟨output, outGet, writable, outBound, outside⟩ := caller_raw_output good buffers ptr
    have separate : ob ≠ pb := by
      intro same
      subst ob
      exact outside (Or.inr (Or.inr (Or.inr (Or.inr trees.base.pbuf))))
    obtain ⟨produced, after, z', d', _w, _rem, run, goodA, account, sizes, copied, left, fields,
      _b, _p, _o, storage⟩ :=
      flush_pending_low_raw_bits_storage good trees low cursor ptr outGet writable separate outBound
    obtain ⟨treesA, buffersA⟩ := common run goodA sizes account fields
    have empty := low_pending_run_empty_cursor good buffers ptr low cursor0 run goodA.live.hs
    have adler := flush_pending_low_run_adler good buffers ptr low run goodA.live.hz account
    refine ⟨produced, after, z', d', run, goodA, treesA, buffersA, account, copied, left, fields, empty,
      adler, fun i g get => frame_gzheaders storage.frame ?_ get, storage.frame.1.symm, sizes⟩
    intro x changed
    rcases changed with root | e | e | e
    · exact stream_root_gzheaders good.uniq good.live.hz root
    · subst e; exact uniq_gzheaders_none good.uniq (Or.inr (Or.inr (Or.inl (by rw [good.live.hs]; simp))))
    · subst e; exact uniq_gzheaders_none good.uniq (Or.inl (by rw [trees.base.bytes]; simp))
    · subst e; exact uniq_gzheaders_none good.uniq (Or.inl (by rw [outGet]; simp))
  · obtain ⟨foreign, outGet, outBound, different, _lt, _notRoot⟩ := caller_foreign_output good buffers ptr
    obtain ⟨produced, after, z', d', _w, _rem, run, goodA, account, sizes, copied, left, fields,
      _b, _p, _o, frame⟩ :=
      flush_pending_low_foreign_bits_frame good trees low cursor ptr outGet different outBound
    obtain ⟨treesA, buffersA⟩ := common run goodA sizes account fields
    have empty := low_foreign_pending_run_empty_cursor good buffers ptr low cursor0 run goodA.live.hs
    have adler := (flush_pending_low_foreign_run_scalar_effects good buffers ptr low run goodA.live.hz account).1
    have restored := restore_gzheaders h [⟨z.next_out, produced⟩] after
    refine ⟨produced, after, z', d', run, goodA, treesA, buffersA, account, copied, left, fields, empty,
      adler, fun i g get => ?_, ?_, sizes⟩
    · have kept := frame_gzheaders frame.1 (fun x changed => ?_) get
      · rw [restored.1] at kept; exact kept
      · rcases changed with root | e
        · exact stream_root_gzheaders good.uniq good.live.hz root
        · subst e; exact uniq_gzheaders_none good.uniq (Or.inr (Or.inr (Or.inl (by rw [good.live.hs]; simp))))
    · rw [← restored.2]; exact frame.1.1.symm

/-- **A copy into `pending_buf` at `pending`** from a byte view other than `pending_buf`, then
`pending` set to the new count. Keeps the engine invariants, the caller buffers and every other
byte view. -/
theorem pending_copy {h : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream} {d : DeflateState}
    {buf : Array UInt8} (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) (cursor : d.pending_out = d.pending_buf)
    {rs : BRef} {os : Nat} {sa : Array UInt8} (src : Space.get h rs = some sa) (other : rs ≠ .blk pb)
    (n : Nat) (fits : d.pending.toNat + n ≤ buf.size) (inside : os + n ≤ sa.size)
    (newp : UInt64) (count : newp.toNat = d.pending.toNat + n) :
    let next := copyRange buf sa d.pending.toNat os n
    let after := setD (Zlib.Trees.Proofs.Out.setB h pb next) ds { d with pending := newp }
    memcpyB (.ref (.blk pb) d.pending.toNat) (.ref rs os) n h =
        .ok ((), Zlib.Trees.Proofs.Out.setB h pb next) ∧
      DGood after r ds z { d with pending := newp } ∧ TreesInvAt after ds { d with pending := newp } pb next ∧
      StreamBuffers after r ∧ HeaderFrame h after pb ∧ next.size = buf.size := by
  intro next after
  have size : next.size = buf.size := size_copyRange _ _ _ _ _
  have run : memcpyB (.ref (.blk pb) d.pending.toNat) (.ref rs os) n h =
      .ok ((), Zlib.Trees.Proofs.Out.setB h pb next) :=
    Ptr.memcpy_ok (rd := BRef.blk pb) trees.base.bytes src trees.base.rw fits inside (Or.inl (Ne.symm other))
  let result : DeflateState := { d with pending := newp }
  have treesA : TreesInvAt after ds result pb next :=
    ⟨trees.base.step next size result trees.base.wf rfl rfl rfl rfl rfl
      (by change newp.toNat ≤ d.pending_buf_size.toNat; rw [count, trees.base.psize]; exact fits),
      trees.run.ldyn, trees.run.lstat, trees.run.ddyn, trees.run.dstat, trees.run.bldyn, trees.run.blstat,
      trees.run.bi_lo, trees.run.bi_hi, trees.run.bi_buf, trees.run.sym_next_le, trees.run.sym_next_mod⟩
  have diff : BitsDiff d result := ⟨newp, d.bi_buf, d.bi_valid, d.bi_used, rfl⟩
  have stateB : (Zlib.Trees.Proofs.Out.setB h pb next).dstates ds = some d := good.live.hs
  refine ⟨run, output_bits_good good cursor trees.base.bytes size diff treesA, treesA,
    output_bits_buffers good buffers cursor trees.base.bytes size diff treesA,
    ⟨rfl, rfl, fun ref ne => ?_⟩, size⟩
  rw [byte_view_setD_depth stateB (show result.depth = d.depth from rfl) ref]
  exact setB_view h pb next ref ne

/-- Writing `gzindex` keeps the engine invariants and the caller buffers. -/
theorem gzindex_engine {h : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream} {d : DeflateState}
    {buf : Array UInt8} (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) (v : UInt64) :
    DGood (setD h ds { d with gzindex := v }) r ds z { d with gzindex := v } ∧
      TreesInvAt (setD h ds { d with gzindex := v }) ds { d with gzindex := v } pb buf ∧
      StreamBuffers (setD h ds { d with gzindex := v }) r ∧
      HeaderFrame h (setD h ds { d with gzindex := v }) pb := by
  obtain ⟨goodA, treesA, buffersA⟩ := gzindex_status_engine good trees buffers v d.status good.live.status
  exact ⟨goodA, treesA, buffersA, HeaderFrame.state pb good.live.hs _ rfl⟩

/-- Writing `last_flush` keeps the engine invariants and the caller buffers. -/
theorem last_flush_frame {h : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream} {d : DeflateState}
    {buf : Array UInt8} (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) (v : Int32) :
    DGood (setD h ds { d with last_flush := v }) r ds z { d with last_flush := v } ∧
      StreamBuffers (setD h ds { d with last_flush := v }) r ∧
      HeaderFrame h (setD h ds { d with last_flush := v }) pb := by
  obtain ⟨goodA, _, buffersA⟩ := last_flush_engine (pb := pb) (buf := buf) v good trees buffers
  exact ⟨goodA, buffersA, HeaderFrame.state pb good.live.hs _ rfl⟩

end Zlib.Deflate.Universal.Call
