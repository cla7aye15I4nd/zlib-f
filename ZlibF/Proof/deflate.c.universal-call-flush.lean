import ZlibF.Proof.«deflate.c.universal-call-record»
import ZlibF.Proof.«deflate.c.engine.pending-empty-cursor»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-pending-phase»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-pending-contract»
import ZlibF.Proof.«deflate.c.engine.raw-output-frame»
import ZlibF.Proof.«deflate.c.borrow-stable-publish»

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


theorem slice_of_pointwise {a a' : Array UInt8} {i n : Nat}
    (same : ∀ j, i ≤ j → j < i + n → a'[j]? = a[j]?) :
    (a'.toList.drop i).take n = (a.toList.drop i).take n := by
  apply List.ext_getElem?
  intro k
  simp only [List.getElem?_take, List.getElem?_drop, Array.getElem?_toList]
  split
  · exact same (i + k) (by omega) (by omega)
  · rfl

/-- The output owner and the private keys of a flush hold no caller range outside the stream. -/
theorem owned_pending {h : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream} {d : DeflateState}
    {buf : Array UInt8} (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) :
    StreamOwned h r pb ∧ StreamOwned h r ds := by
  refine ⟨⟨z, good.live.hz, Or.inr ⟨ds, d, good.live.zst, good.live.hs, ?_⟩⟩,
    ⟨z, good.live.hz, Or.inr ⟨ds, d, good.live.zst, good.live.hs, Or.inl rfl⟩⟩⟩
  exact Or.inr (Or.inr (Or.inr (Or.inr trees.base.pbuf)))

theorem uniq_two {h : Heap} (uniq : Uniq h) {x : Nat} (bytes : h.bytes x ≠ none) :
    h.streams x = none ∧ h.dstates x = none ∧ h.gzstates x = none := by
  have count := uniq x
  obtain ⟨v, e⟩ := Option.ne_none_iff_exists'.mp bytes
  rw [e] at count
  simp only [cnt_some] at count
  refine ⟨?_, ?_, ?_⟩
  · cases hx : h.streams x with
    | none => rfl
    | some w => rw [hx] at count; simp only [cnt_some] at count; omega
  · cases hx : h.dstates x with
    | none => rfl
    | some w => rw [hx] at count; simp only [cnt_some] at count; omega
  · cases hx : h.gzstates x with
    | none => rfl
    | some w => rw [hx] at count; simp only [cnt_some] at count; omega


theorem uniq_dstates {h : Heap} (uniq : Uniq h) {x : Nat} (state : h.dstates x ≠ none) :
    h.bytes x = none ∧ h.streams x = none ∧ h.gzstates x = none := by
  have count := uniq x
  obtain ⟨v, e⟩ := Option.ne_none_iff_exists'.mp state
  rw [e] at count
  simp only [cnt_some] at count
  refine ⟨?_, ?_, ?_⟩
  · cases hx : h.bytes x with
    | none => rfl
    | some w => rw [hx] at count; simp only [cnt_some] at count; omega
  · cases hx : h.streams x with
    | none => rfl
    | some w => rw [hx] at count; simp only [cnt_some] at count; omega
  · cases hx : h.gzstates x with
    | none => rfl
    | some w => rw [hx] at count; simp only [cnt_some] at count; omega

theorem stream_root_tables {h : Heap} {r : ZStreamRef} {z : ZStream} (get : r.get h = some z) {x : Nat}
    (root : StreamRoot r x) : h.streams x ≠ none ∨ h.gzstates x ≠ none := by
  cases r with
  | tab i => subst root; left; simp only [ZStreamRef.get] at get; rw [get]; simp
  | in_gzstate_strm i =>
    subst root; right; simp only [ZStreamRef.get] at get; intro e; rw [e] at get; cases get

/-- A frame keeps every byte view whose key it does not change, given the borrowed strings. -/
theorem frame_view_same {h g : Heap} {changed : Nat → Prop} (frame : Frame h g changed)
    (borrow : g.libcErrorBorrow = h.libcErrorBorrow) {ref : BRef} {a : Array UInt8}
    (get : Space.get h ref = some a) (keep : ∀ x, (ref = .blk x ∨ ref = .dstate_depth x) → ¬ changed x) :
    Space.get g ref = some a := by
  cases ref with
  | blk b =>
    have live : h.live b := Or.inl (by change h.bytes b = some a at get; rw [get]; simp)
    have same := (frame.2.2.2.2.2 b live (keep b (Or.inl rfl))).1
    change g.bytes b = some a
    rw [same]; exact get
  | dstate_depth x =>
    change (h.dstates x).map (·.depth) = some a at get
    have live : h.live x := by
      refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
      intro e; rw [e] at get; cases get
    have same := (frame.2.2.2.2.2 x live (keep x (Or.inr rfl))).2.2.2.2.1
    change (g.dstates x).map (·.depth) = some a
    rw [same]; exact get
  | str i =>
    change staticStringBytes g i = some a
    change staticStringBytes h i = some a at get
    unfold staticStringBytes at get ⊢
    rw [borrow]; exact get
  | st_dist_code =>
    change some g.static.dist_code = some a
    rw [← frame.1]; exact get
  | st_length_code =>
    change some g.static.length_code = some a
    rw [← frame.1]; exact get


/-- Positions a flush may write: inside `[oo, oo + produced)`, hence outside a separate range. -/
theorem separate_outside {ip n oo m produced j : Nat} (sep : n = 0 ∨ m = 0 ∨ ip + n ≤ oo ∨ oo + m ≤ ip)
    (le : produced ≤ m) (lo : ip ≤ j) (hi : j < ip + n) : ¬ (oo ≤ j ∧ j < oo + produced) := by
  omega


/-- Restoring a foreign output view leaves every other view as the flush left it. -/
theorem restore_depth_view (before after : Heap) (owner oo len : Nat) {rp : BRef}
    (ne : rp ≠ .dstate_depth owner) :
    (Space.get (restoreRegions before after [⟨.ref (.dstate_depth owner) oo, len⟩]) rp :
        Option (Array UInt8)) = Space.get after rp ∧
      (restoreRegions before after [⟨.ref (.dstate_depth owner) oo, len⟩]).libcErrorBorrow =
        after.libcErrorBorrow := by
  simp only [restoreRegions, List.foldl_cons, List.foldl_nil]
  cases hb : (Space.get before (BRef.dstate_depth owner) : Option (Array UInt8)) with
  | none => exact ⟨rfl, rfl⟩
  | some a0 =>
    simp only []
    show (Space.get (Space.put after (BRef.dstate_depth owner) a0) rp : Option (Array UInt8)) = _ ∧
      (Space.put after (BRef.dstate_depth owner) a0 : Heap).libcErrorBorrow = _
    cases hd : after.dstates owner with
    | none =>
      have e : (Space.put after (BRef.dstate_depth owner) a0 : Heap) = after := by
        show (match after.dstates owner with
          | some s => { after with dstates := upd after.dstates owner (some { s with depth := a0 }) }
          | none => after) = after
        rw [hd]
      rw [e]; exact ⟨rfl, rfl⟩
    | some s =>
      have e : (Space.put after (BRef.dstate_depth owner) a0 : Heap) =
          { after with dstates := upd after.dstates owner (some { s with depth := a0 }) } := by
        show (match after.dstates owner with
          | some s => { after with dstates := upd after.dstates owner (some { s with depth := a0 }) }
          | none => after) = _
        rw [hd]
      rw [e]
      refine ⟨?_, rfl⟩
      cases rp with
      | dstate_depth x =>
        have other : x ≠ owner := fun same => ne (by rw [same])
        show ((upd after.dstates owner (some { s with depth := a0 })) x).map (·.depth) = (after.dstates x).map (·.depth)
        rw [upd_ne _ _ _ _ other]
      | _ => rfl

/-- **A flush keeps the caller's bytes** in a range that is separate from the output range and
lies outside the storage the stream owns. -/
theorem flush_keeps_bytes {h after : Heap} {r : ZStreamRef} {ds pb produced : Nat} {z z' : ZStream}
    {d : DeflateState} {buf : Array UInt8}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (low : d.bi_valid.toInt < 8) (cursor : d.pending_out = d.pending_buf) (out : z.next_out ≠ .null)
    (run : flush_pending (some r) h = .ok ((), after)) (live : r.get after = some z')
    (account : StreamAccounting z z' 0 produced)
    {p : BPtr} {n : Nat} {xs : List UInt8} (bytes : Bytes h p n xs)
    (apart : Separate p n z.next_out z.avail_out.toNat) (keys : ∀ b, ByteRoot p b → b ≠ pb ∧ b ≠ ds) :
    Bytes after p n xs := by
  rcases bytes with ⟨rfl, rfl, rfl⟩ | ⟨rp, ip, a, rfl, get, fits, rfl⟩
  · exact Or.inl ⟨rfl, rfl, rfl⟩
  right
  have le : produced ≤ z.avail_out.toNat := account.2.1
  have borrow : after.libcErrorBorrow = h.libcErrorBorrow :=
    Zlib.Deflate.BorrowProofs.stable_flush_pending (some r) h () after run
  have notPb : ∀ x, (rp = .blk x ∨ rp = .dstate_depth x) → x ≠ pb ∧ x ≠ ds := by
    intro x e
    have root : ByteRoot (.ref rp ip) x := by rcases e with rfl | rfl <;> rfl
    exact keys x root
  obtain ⟨ob, pointer⟩ := Block.output_pointer_cases good buffers out
  rcases pointer with ⟨oo, ptr⟩ | ⟨oo, ptr⟩
  · obtain ⟨output, outGet, writable, outBound, outside⟩ := caller_raw_output good buffers ptr
    have separate : ob ≠ pb := by
      intro same; subst ob; exact outside (Or.inr (Or.inr (Or.inr (Or.inr trees.base.pbuf))))
    obtain ⟨_, after', _, _, _, _, run', _, _, _, _, _, _, _, _, _, storage⟩ :=
      flush_pending_low_raw_bits_storage good trees low cursor ptr outGet writable separate outBound
    have same : after' = after := (Prod.mk.inj (Except.ok.inj (run'.symm.trans run))).2
    subst same
    by_cases onOut : rp = .blk ob
    · subst onOut
      obtain ⟨next, getN, sizeN, keep⟩ :=
        flush_pending_low_run_output_interval good buffers ptr low run live account outGet
      have eqA : a = output := Option.some.inj (get.symm.trans outGet)
      subst eqA
      rw [ptr] at apart
      have sep : n = 0 ∨ z.avail_out.toNat = 0 ∨ ip + n ≤ oo ∨ oo + z.avail_out.toNat ≤ ip := by
        rcases apart with e | e | e
        · exact Or.inl e
        · exact Or.inr (Or.inl e)
        · rcases e with e | e
          · exact absurd rfl e
          · exact Or.inr (Or.inr e)
      refine ⟨.blk ob, ip, next, rfl, getN, by omega, (slice_of_pointwise ?_).symm⟩
      intro j lo hi
      exact keep j (by omega) (separate_outside sep le lo hi)
    · refine ⟨rp, ip, a, rfl, frame_view_same storage.frame borrow get ?_, fits, rfl⟩
      intro x e changed
      obtain ⟨xPb, xDs⟩ := notPb x e
      rcases changed with root | e2 | e2 | e2
      · rcases e with rfl | rfl
        · have b : h.bytes x ≠ none := by change h.bytes x = some a at get; rw [get]; simp
          obtain ⟨s1, _, s3⟩ := uniq_two good.uniq b
          rcases stream_root_tables good.live.hz root with t | t
          · exact t s1
          · exact t s3
        · have st : h.dstates x ≠ none := by
            change (h.dstates x).map (·.depth) = some a at get; intro e; rw [e] at get; cases get
          obtain ⟨_, s2, s3⟩ := uniq_dstates good.uniq st
          rcases stream_root_tables good.live.hz root with t | t
          · exact t s2
          · exact t s3
      · exact xDs e2
      · exact xPb e2
      · subst e2
        rcases e with rfl | rfl
        · exact onOut rfl
        · have st : h.dstates x ≠ none := by
            change (h.dstates x).map (·.depth) = some a at get; intro e; rw [e] at get; cases get
          have := (uniq_dstates good.uniq st).1
          rw [outGet] at this; cases this
  · obtain ⟨foreign, outGet, outBound, different, _lt, _notRoot⟩ := caller_foreign_output good buffers ptr
    obtain ⟨produced2, after', z2, _, _, _, run', good2, account2, _, _, _, _, _, _, _, frame⟩ :=
      flush_pending_low_foreign_bits_frame good trees low cursor ptr outGet different outBound
    have same : after = after' := (Prod.mk.inj (Except.ok.inj (run.symm.trans run'))).2
    subst same
    have sameZ : z2 = z' := Option.some.inj (good2.live.hz.symm.trans live)
    subst sameZ
    have sameP : produced = produced2 := by
      have a1 := account.2.2.2.1; have a2 := account2.2.2.2.1; omega
    subst sameP
    by_cases onOut : rp = .dstate_depth ob
    · subst onOut
      obtain ⟨a', getA, sizeA, keep⟩ := frame.2 ⟨z.next_out, produced⟩ (by simp) (.dstate_depth ob) oo a ptr get
      rw [ptr] at apart
      have sep : n = 0 ∨ z.avail_out.toNat = 0 ∨ ip + n ≤ oo ∨ oo + z.avail_out.toNat ≤ ip := by
        rcases apart with e | e | e
        · exact Or.inl e
        · exact Or.inr (Or.inl e)
        · rcases e with e | e
          · exact absurd rfl e
          · exact Or.inr (Or.inr e)
      refine ⟨.dstate_depth ob, ip, a', rfl, getA, by omega, (slice_of_pointwise ?_).symm⟩
      intro j lo hi
      apply keep j (by omega)
      rintro ⟨region, member, off, pointer, lo2, hi2⟩
      simp only [List.mem_singleton] at member
      subst member
      rw [ptr] at pointer
      simp only [Ptr.ref.injEq] at pointer
      obtain ⟨_, rfl⟩ := pointer
      exact separate_outside sep le lo hi ⟨lo2, hi2⟩
    · obtain ⟨view, borrowR⟩ := restore_depth_view h after ob oo produced onOut
      rw [ptr] at frame
      have kept := frame_view_same frame.1 (borrowR.trans borrow) get (fun x e changed => by
        obtain ⟨xPb, xDs⟩ := notPb x e
        rcases changed with root | e2
        · rcases e with rfl | rfl
          · have b : h.bytes x ≠ none := by change h.bytes x = some a at get; rw [get]; simp
            obtain ⟨s1, _, s3⟩ := uniq_two good.uniq b
            rcases stream_root_tables good.live.hz root with t | t
            · exact t s1
            · exact t s3
          · have st : h.dstates x ≠ none := by
              change (h.dstates x).map (·.depth) = some a at get; intro e; rw [e] at get; cases get
            obtain ⟨_, s2, s3⟩ := uniq_dstates good.uniq st
            rcases stream_root_tables good.live.hz root with t | t
            · exact t s2
            · exact t s3
        · exact xDs e2)
      rw [view] at kept
      exact ⟨rp, ip, a, rfl, kept, fits, rfl⟩

/-- A range separate from the output stays separate from what is left of the output. -/
theorem separate_advance {p q : BPtr} {n m produced m' : Nat} (sep : Separate p n q m)
    (left : m' + produced = m) : Separate p n (advance q produced) m' := by
  cases p with
  | null => simp [Separate]
  | ref r i =>
    cases q with
    | null => simp [Separate, advance]
    | ref s j =>
      simp only [Separate, advance] at sep ⊢
      rcases sep with e | e | e | e | e
      · exact Or.inl e
      · exact Or.inr (Or.inl (by omega))
      · exact Or.inr (Or.inr (Or.inl e))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (by omega))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (by omega))))

/-- The caller bytes a header step keeps: every caller range that is separate from the current
output range and whose root block is neither `pending_buf` nor the state record. -/
def CallerKeep (h after : Heap) (z : ZStream) (ds pb : Nat) : Prop :=
  ∀ (p : BPtr) (n : Nat) (xs : List UInt8), Bytes h p n xs → Separate p n z.next_out z.avail_out.toNat →
    (∀ b, ByteRoot p b → b ≠ pb ∧ b ≠ ds) → Bytes after p n xs

theorem CallerKeep.refl (h : Heap) (z : ZStream) (ds pb : Nat) : CallerKeep h h z ds pb :=
  fun _ _ _ bytes _ _ => bytes

/-- A step that changes no byte view other than `pending_buf` keeps the caller bytes. -/
theorem CallerKeep.of_frame {h after : Heap} {z : ZStream} {ds pb : Nat} (frame : HeaderFrame h after pb) :
    CallerKeep h after z ds pb := by
  intro p n xs bytes _ keys
  rcases bytes with ⟨e1, e2, e3⟩ | ⟨rp, ip, a, ptr, get, fits, slice⟩
  · exact Or.inl ⟨e1, e2, e3⟩
  · refine Or.inr ⟨rp, ip, a, ptr, ?_, fits, slice⟩
    have ne : rp ≠ .blk pb := by
      intro same
      subst ptr; subst same
      exact (keys pb rfl).1 rfl
    rw [frame.views rp ne]; exact get

theorem CallerKeep.trans {h1 h2 h3 : Heap} {z z2 : ZStream} {ds pb produced : Nat}
    (first : CallerKeep h1 h2 z ds pb) (second : CallerKeep h2 h3 z2 ds pb)
    (account : StreamAccounting z z2 0 produced) : CallerKeep h1 h3 z ds pb := by
  intro p n xs bytes apart keys
  apply second p n xs (first p n xs bytes apart keys) _ keys
  rw [account.2.2.2.2.2.1]; exact separate_advance apart account.2.2.2.1

/-- A flush with fewer than eight held bits keeps the caller bytes. -/
theorem CallerKeep.of_flush {h after : Heap} {r : ZStreamRef} {ds pb produced : Nat} {z z' : ZStream}
    {d : DeflateState} {buf : Array UInt8}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (low : d.bi_valid.toInt < 8) (cursor : d.pending_out = d.pending_buf) (out : z.next_out ≠ .null)
    (run : flush_pending (some r) h = .ok ((), after)) (live : r.get after = some z')
    (account : StreamAccounting z z' 0 produced) : CallerKeep h after z ds pb :=
  fun _ _ _ bytes apart keys => flush_keeps_bytes good trees buffers low cursor out run live account bytes apart keys

end Zlib.Deflate.Universal.Call
