import ZlibF.Proof.«deflate.c.universal-window»
import ZlibF.Proof.«trees.c.universal-flush»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-private-arrays»
import ZlibF.Proof.«deflate.c.universal-acc»
import ZlibF.Proof.«deflate.c.engine.raw-output-interval»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-buffer-frame-adjacent»

/-!
# deflate.c: the output frame of a strategy run (batch B)

`deflate_call` needs, from each strategy, the input and output counts with the totals, and a heap
frame in which only the stream record, the stream's own blocks and the written part
`[next_out, next_out + produced)` of the caller's output change (`OutFrame`). The owned blocks are
named by four pointer fields of the state, which a strategy never writes (`Keys`). This file
composes such frames: adjacent output intervals, and steps that write no output.
-/

namespace Zlib.Deflate.Universal
open C ZlibF.Spec ZlibF.Spec.Public Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Engine.Proofs
open Zlib.Deflate.Proofs Zlib.Deflate.Proofs.DefaultInit
set_option autoImplicit false

/-- A one-region frame on a raw output block gives the coarse frame with that block changed. -/
theorem raw_buffer_frame_facts {h g : Heap} {ob offset produced : Nat} {arr : Array UInt8}
    {changed : Nat → Prop} (frame : BufferFrame h g changed [⟨.ref (.blk ob) offset, produced⟩])
    (get : h.bytes ob = some arr) (outside : ¬ changed ob) :
    Frame h g (fun b => changed b ∨ b = ob) ∧ g.ro ob = h.ro ob := by
  have restored : restoreRegions h g [⟨.ref (.blk ob) offset, produced⟩] = Zlib.Trees.Proofs.Out.setB g ob arr := by
    simp only [restoreRegions, List.foldl_cons, List.foldl_nil]
    change (match h.bytes ob with | none => g | some a => Zlib.Trees.Proofs.Out.setB g ob a) = _
    rw [get]
  have kept := frame.1
  rw [restored] at kept
  obtain ⟨static, alloc, garbage, nextBlk, nalloc, slots⟩ := kept
  have live : h.live ob := by simp [Heap.live, get]
  have ro : g.ro ob = h.ro ob := by
    have := (slots ob live outside).2.2.2.2.2.2.2
    simpa [Zlib.Trees.Proofs.Out.setB] using this
  refine ⟨⟨static, alloc, garbage, nextBlk, nalloc, ?_⟩, ro⟩
  intro b liveB out
  have different : b ≠ ob := fun e => out (Or.inr e)
  have s := slots b liveB (fun yes => out (Or.inl yes))
  simpa [SlotSame, Zlib.Trees.Proofs.Out.setB, upd_ne _ _ _ _ different] using s

/-- Adjacent frames on one raw output block compose. -/
theorem raw_buffer_frame_adjacent {h m k : Heap} {ob offset first second : Nat} {arr : Array UInt8}
    {changed : Nat → Prop}
    (one : BufferFrame h m changed [⟨.ref (.blk ob) offset, first⟩])
    (two : BufferFrame m k changed [⟨.ref (.blk ob) (offset + first), second⟩])
    (shapeOne : Zlib.Deflate.Proofs.Shape h m) (shapeTwo : Zlib.Deflate.Proofs.Shape m k) (unique : Uniq h)
    (get : h.bytes ob = some arr) (outside : ¬ changed ob) :
    BufferFrame h k changed [⟨.ref (.blk ob) offset, first + second⟩] := by
  obtain ⟨frameOne, roOne⟩ := raw_buffer_frame_facts one get outside
  have intervalOne := ByteOutputInterval.of_buffer_frame one
  obtain ⟨mid, getMid, sizeMid, _⟩ := intervalOne arr (by simpa using get)
  have getMid' : m.bytes ob = some mid := by simpa using getMid
  obtain ⟨frameTwo, roTwo⟩ := raw_buffer_frame_facts two getMid' outside
  have interval := intervalOne.trans (ByteOutputInterval.of_buffer_frame two)
  obtain ⟨fin, getFin, sizeFin, same⟩ := interval arr (by simpa using get)
  exact raw_buffer_frame_of_interval (full_frame_trans_shape frameOne frameTwo shapeOne) (shapeOne.trans shapeTwo)
    unique get (by simpa using getFin) (roTwo.trans roOne) sizeFin same

/-- A block that holds bytes, or a state record, is not the stream root. -/
theorem not_root_of_unique {h : Heap} {r : ZStreamRef} {z : ZStream} {b : Nat} (unique : Uniq h)
    (get : r.get h = some z) (other : h.streams b = none ∧ h.gzstates b = none) : ¬ StreamRoot r b := by
  intro root
  cases r with
  | tab i =>
    change b = i at root; subst root
    change h.streams b = some z at get
    rw [other.1] at get; cases get
  | in_gzstate_strm i =>
    change b = i at root; subst root
    change (h.gzstates b).map (·.strm) = some z at get
    rw [other.2] at get; cases get

/-- The caller's output: `NULL`, a raw byte block, or the depth array of another state, never
the stream root or the stream's own blocks. -/
theorem output_target {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (good : DGood h r ds z d) (buffers : StreamBuffers h r) :
    z.next_out = .null ∨
    (∃ ob oo arr, z.next_out = .ref (.blk ob) oo ∧ h.bytes ob = some arr ∧
      ¬ (StreamRoot r ob ∨ DeflateOwned ds d ob)) ∨
    (∃ owner oo foreign, z.next_out = .ref (.dstate_depth owner) oo ∧ h.dstates owner = some foreign ∧
      ¬ (StreamRoot r owner ∨ DeflateOwned ds d owner)) := by
  have writable : ∀ ref oo, z.next_out = .ref ref oo → Space.ro h ref = false := by
    intro ref oo e
    obtain ⟨z0, get0, _, output, _⟩ := buffers
    have same : z0 = z := Option.some.inj (get0.symm.trans good.live.hz)
    subst z0
    rw [e] at output
    rcases output with null | ⟨_, w, _⟩
    · cases null
    · rcases w rfl with ⟨null, _⟩ | ⟨ref', i, a, eq, _, ro, _⟩
      · cases null
      · cases eq; exact ro
  rcases e : z.next_out with _ | ⟨ref, oo⟩
  · exact Or.inl rfl
  · cases ref with
    | str i => have := writable _ _ e; cases this
    | st_dist_code => have := writable _ _ e; cases this
    | st_length_code => have := writable _ _ e; cases this
    | blk ob =>
      obtain ⟨arr, get, _, _, notOwned⟩ := caller_raw_output good buffers e
      have only := good.uniq.bytes_only get
      refine Or.inr (Or.inl ⟨ob, oo, arr, rfl, get, ?_⟩)
      rintro (root | owned)
      · exact not_root_of_unique good.uniq good.live.hz ⟨only.2.1, only.2.2.2.2.2⟩ root
      · exact notOwned owned
    | dstate_depth owner =>
      obtain ⟨foreign, get, _, ne, _, notRoot⟩ := caller_foreign_output good buffers e
      have only := good.uniq.dstates_only get
      refine Or.inr (Or.inr ⟨owner, oo, foreign, rfl, get, ?_⟩)
      rintro (root | owned)
      · exact notRoot root
      · rcases owned with eq | win | prev | head | pbuf
        · exact ne eq
        · obtain ⟨w, p, q, b, blocks⟩ := good.inv.blocks
          rw [blocks.win] at win; cases win
          obtain ⟨a, ga, _⟩ := blocks.wa
          rw [only.1] at ga; cases ga
        · obtain ⟨w, p, q, b, blocks⟩ := good.inv.blocks
          rw [blocks.prev] at prev; cases prev
          obtain ⟨a, ga, _⟩ := blocks.pa
          rw [only.2.1] at ga; cases ga
        · obtain ⟨w, p, q, b, blocks⟩ := good.inv.blocks
          rw [blocks.head] at head; cases head
          obtain ⟨a, ga, _⟩ := blocks.qa
          rw [only.2.1] at ga; cases ga
        · obtain ⟨w, p, q, b, blocks⟩ := good.inv.blocks
          rw [blocks.pbuf] at pbuf; cases pbuf
          obtain ⟨a, ga, _⟩ := blocks.ba
          rw [only.1] at ga; cases ga


/-- Where the caller's output is: `NULL`, a raw byte block, or the depth array of another state,
outside the stream root and the stream's own blocks. -/
def OutTarget (h : Heap) (r : ZStreamRef) (ds : Nat) (d : DeflateState) (z : ZStream) : Prop :=
  z.next_out = .null ∨
    (∃ ob oo arr, z.next_out = .ref (.blk ob) oo ∧ h.bytes ob = some arr ∧
      ¬ (StreamRoot r ob ∨ DeflateOwned ds d ob)) ∨
    (∃ owner oo foreign, z.next_out = .ref (.dstate_depth owner) oo ∧ h.dstates owner = some foreign ∧
      ¬ (StreamRoot r owner ∨ DeflateOwned ds d owner))

/-- The four pointer fields that name the stream's own blocks. -/
def Keys (d d' : DeflateState) : Prop :=
  d'.window = d.window ∧ d'.prev = d.prev ∧ d'.head = d.head ∧ d'.pending_buf = d.pending_buf

theorem Keys.refl (d : DeflateState) : Keys d d := ⟨rfl, rfl, rfl, rfl⟩

theorem Keys.trans {a b c : DeflateState} (one : Keys a b) (two : Keys b c) : Keys a c :=
  ⟨two.1.trans one.1, two.2.1.trans one.2.1, two.2.2.1.trans one.2.2.1, two.2.2.2.trans one.2.2.2⟩

theorem Keys.owned {d d' : DeflateState} (keys : Keys d d') (ds b : Nat) :
    DeflateOwned ds d' b ↔ DeflateOwned ds d b := by
  unfold DeflateOwned
  rw [keys.1, keys.2.1, keys.2.2.1, keys.2.2.2]

/-- The output frame of a part of a strategy run: counts with totals, the heap frame over the
written output interval, and the heap shape. -/
def OutFrame (h after : Heap) (r : ZStreamRef) (ds : Nat) (d : DeflateState) (z z' : ZStream)
    (used produced : Nat) : Prop :=
  StreamAccounting z z' used produced ∧ Totals z z' used produced ∧
  BufferFrame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) [⟨z.next_out, produced⟩] ∧
  Zlib.Deflate.Proofs.Shape h after

theorem OutFrame.acc {h after : Heap} {r : ZStreamRef} {ds : Nat} {d : DeflateState} {z z' : ZStream}
    {used produced : Nat} (frame : OutFrame h after r ds d z z' used produced) : Acc z z' :=
  ⟨used, produced, frame.1, frame.2.1⟩

/-- Two adjacent parts compose; the second may start from a state with the same keys. -/
theorem OutFrame.trans {h m k : Heap} {r : ZStreamRef} {ds : Nat} {d d1 : DeflateState}
    {z z1 z2 : ZStream} {u1 p1 u2 p2 : Nat}
    (one : OutFrame h m r ds d z z1 u1 p1) (two : OutFrame m k r ds d1 z1 z2 u2 p2)
    (keys : Keys d d1) (unique : Uniq h) (target : OutTarget h r ds d z) :
    OutFrame h k r ds d z z2 (u1 + u2) (p1 + p2) := by
  obtain ⟨acc1, tot1, buf1, shape1⟩ := one
  obtain ⟨acc2, tot2, buf2, shape2⟩ := two
  have same : (fun b => StreamRoot r b ∨ DeflateOwned ds d1 b) = (fun b => StreamRoot r b ∨ DeflateOwned ds d b) := by
    funext b; rw [keys.owned ds b]
  rw [same] at buf2
  have next1 : z1.next_out = advance z.next_out p1 := acc1.2.2.2.2.2.1
  rw [next1] at buf2
  refine ⟨stream_accounting_trans acc1 acc2, Totals.trans tot1 tot2, ?_, shape1.trans shape2⟩
  rcases target with null | ⟨ob, oo, arr, ptr, get, outside⟩ | ⟨owner, oo, foreign, ptr, get, outside⟩
  · rw [null] at buf1 buf2 ⊢
    have f1 : Frame h m (fun b => StreamRoot r b ∨ DeflateOwned ds d b) := by
      simpa only [restoreRegions, List.foldl_cons, List.foldl_nil] using buf1.1
    have f2 : Frame m k (fun b => StreamRoot r b ∨ DeflateOwned ds d b) := by
      simpa only [restoreRegions, List.foldl_cons, List.foldl_nil, advance] using buf2.1
    exact null_output_buffer_frame (full_frame_trans_shape f1 f2 shape1)
  · rw [ptr] at buf1 buf2 ⊢
    exact raw_buffer_frame_adjacent buf1 buf2 shape1 shape2 unique get outside
  · rw [ptr] at buf1 buf2 ⊢
    exact foreign_buffer_frame_adjacent buf1 buf2 shape1 shape2 unique get outside

/-- A part that writes no output and changes only the stream record and the stream's own blocks. -/
theorem out_frame_private {h after : Heap} {r : ZStreamRef} {ds : Nat} {d : DeflateState} {z z' : ZStream}
    {used : Nat} (account : StreamAccounting z z' used 0) (totals : Totals z z' used 0)
    (frame : Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b))
    (shape : Zlib.Deflate.Proofs.Shape h after) (unique : Uniq h) (target : OutTarget h r ds d z) :
    OutFrame h after r ds d z z' used 0 := by
  refine ⟨account, totals, ?_, shape⟩
  have slots := frame.2.2.2.2.2
  rcases target with null | ⟨ob, oo, arr, ptr, get, outside⟩ | ⟨owner, oo, foreign, ptr, get, outside⟩
  · rw [null]; exact null_output_buffer_frame frame
  · rw [ptr]
    have liveOb : h.live ob := by simp [Heap.live, get]
    obtain ⟨b1, _, _, _, _, _, _, ro1⟩ := slots ob liveOb outside
    exact raw_buffer_frame_of_interval (full_frame_weaken frame (fun _ c => Or.inl c)) shape unique get
      (by rw [b1]; exact get) ro1 rfl (fun _ _ _ => rfl)
  · rw [ptr]
    have liveO : h.live owner := by simp [Heap.live, get]
    obtain ⟨_, _, _, _, ds1, _, _, ro1⟩ := slots owner liveO outside
    refine foreign_buffer_frame_of_fields (full_frame_weaken frame (fun _ c => Or.inl c)) shape unique get
      (fun f g => ⟨f, by rw [ds1]; exact g, rfl⟩) ro1 ?_
    intro before g
    refine ⟨before, ?_, rfl, fun _ _ _ => rfl⟩
    change (after.dstates owner).map (·.depth) = some before
    rw [ds1]; exact g

theorem frame_refl (h : Heap) (changed : Nat → Prop) : Frame h h changed :=
  ⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _, fun _ _ _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

theorem OutFrame.refl {h : Heap} {r : ZStreamRef} {ds : Nat} {d : DeflateState} {z : ZStream}
    (unique : Uniq h) (target : OutTarget h r ds d z) : OutFrame h h r ds d z z 0 0 :=
  out_frame_private (stream_accounting_self z) (Totals.refl z) (frame_refl h _)
    (Zlib.Deflate.Proofs.Shape.refl h) unique target

/-- **`fill_window` in the output frame**: it reads input and writes no output. -/
theorem fill_out_frame {roll : Prop} {h after : Heap} {r : ZStreamRef} {ds : Nat} {z z' : ZStream}
    {d result : DeflateState} (good : DGood h r ds z d) (post : FillPost roll h after r ds z z' d result)
    (buffers : StreamBuffers h r) :
    ∃ used, OutFrame h after r ds d z z' used 0 := by
  obtain ⟨used, account, _⟩ := post.account
  have totals : Totals z z' used 0 := by
    rcases post.stream with same | ⟨n, ref, io, ia, pointer, data, bound, count, value⟩
    · subst same
      have : used = 0 := by have := account.2.2.1; omega
      subst this
      exact Totals.refl _
    · have a2 := read_stream_accounting z n ref io
        (checksumValue d.wrap z.adler ((ia.toList.drop io).take n.toNat)) pointer count
      rw [← value] at a2
      have : used = n.toNat := by have := account.2.2.1; have := a2.2.2.1; omega
      subst this
      rw [value]
      exact ⟨by simp [readStream], by simp [readStream]⟩
  exact ⟨used, out_frame_private account totals post.frame post.shape good.uniq (output_target good buffers)⟩

/-- `fill_window` keeps the keys. -/
theorem FillPost.keys {roll : Prop} {h after : Heap} {r : ZStreamRef} {ds : Nat} {z z' : ZStream}
    {d result : DeflateState} (post : FillPost roll h after r ds z z' d result) : Keys d result := by
  obtain ⟨base, choice, eq⟩ := post.fields
  rcases choice with same | ⟨_, slid⟩
  · subst same; rw [eq]; exact ⟨rfl, rfl, rfl, rfl⟩
  · subst slid; rw [eq]; exact ⟨rfl, rfl, rfl, rfl⟩

/-! ## Private steps -/

/-- A step that changes only the stream root and the stream's own blocks, keeping the heap shape. -/
def PrivStep (h after : Heap) (r : ZStreamRef) (ds : Nat) (d : DeflateState) : Prop :=
  Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) ∧ Zlib.Deflate.Proofs.Shape h after

theorem PrivStep.refl (h : Heap) (r : ZStreamRef) (ds : Nat) (d : DeflateState) : PrivStep h h r ds d :=
  ⟨frame_refl h _, Zlib.Deflate.Proofs.Shape.refl h⟩

theorem PrivStep.trans {h m k : Heap} {r : ZStreamRef} {ds : Nat} {d : DeflateState}
    (one : PrivStep h m r ds d) (two : PrivStep m k r ds d) : PrivStep h k r ds d :=
  ⟨full_frame_trans_shape one.1 two.1 one.2, one.2.trans two.2⟩

theorem PrivStep.keys {h after : Heap} {r : ZStreamRef} {ds : Nat} {d d' : DeflateState}
    (step : PrivStep h after r ds d') (keys : Keys d d') : PrivStep h after r ds d := by
  have same : (fun b => StreamRoot r b ∨ DeflateOwned ds d' b) = (fun b => StreamRoot r b ∨ DeflateOwned ds d b) := by
    funext b; rw [keys.owned ds b]
  unfold PrivStep at step ⊢
  rw [same] at step
  exact step

/-- A private step in the output frame. -/
theorem PrivStep.out {h after : Heap} {r : ZStreamRef} {ds : Nat} {d : DeflateState} {z : ZStream}
    (step : PrivStep h after r ds d) (good : DGood h r ds z d) (buffers : StreamBuffers h r) :
    OutFrame h after r ds d z z 0 0 :=
  out_frame_private (stream_accounting_self z) (Totals.refl z) step.1 step.2 good.uniq (output_target good buffers)

theorem priv_setD (h : Heap) (r : ZStreamRef) (ds : Nat) (d d' : DeflateState) {e : DeflateState}
    (get : h.dstates ds = some e) :
    PrivStep h (setD h ds d') r ds d := by
  refine ⟨⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _, fun b _ outside => ?_⟩, fun b => ?_⟩
  · have ne : b ≠ ds := fun e => outside (Or.inr (Or.inl e))
    simp [setD, upd_ne _ _ _ _ ne]
  · by_cases e : b = ds
    · subst e; simp [setD, get]
    · simp [setD, upd_ne _ _ _ _ e]

theorem priv_setB (h : Heap) (r : ZStreamRef) (ds b : Nat) (d : DeflateState) (a : Array UInt8)
    (owned : DeflateOwned ds d b) (get : (h.bytes b).isSome) :
    PrivStep h (Zlib.Trees.Proofs.Out.setB h b a) r ds d := by
  refine ⟨⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _, fun x _ outside => ?_⟩, fun x => ?_⟩
  · have ne : x ≠ b := fun e => outside (Or.inr (by rw [e]; exact owned))
    simp [Zlib.Trees.Proofs.Out.setB, upd_ne _ _ _ _ ne]
  · by_cases e : x = b
    · subst e; simp [Zlib.Trees.Proofs.Out.setB, get]
    · simp [Zlib.Trees.Proofs.Out.setB, upd_ne _ _ _ _ e]

theorem priv_setW (h : Heap) (r : ZStreamRef) (ds q : Nat) (d : DeflateState) (a : Array UInt16)
    (owned : DeflateOwned ds d q) (get : (h.words q).isSome) :
    PrivStep h (setW h q a) r ds d := by
  refine ⟨⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _, fun x _ outside => ?_⟩, fun x => ?_⟩
  · have ne : x ≠ q := fun e => outside (Or.inr (by rw [e]; exact owned))
    simp [setW, upd_ne _ _ _ _ ne]
  · by_cases e : x = q
    · subst e; simp [setW, get]
    · simp [setW, upd_ne _ _ _ _ e]

/-- A write of the stream record. -/
theorem priv_put (h : Heap) (r : ZStreamRef) (ds : Nat) (d : DeflateState) (z : ZStream) :
    PrivStep h (r.put h z) r ds d := by
  cases r with
  | tab i =>
    cases g : h.streams i with
    | none =>
      have e : (ZStreamRef.tab i).put h z = h := by simp [ZStreamRef.put, g]
      rw [e]; exact PrivStep.refl h _ ds d
    | some v =>
      have e : (ZStreamRef.tab i).put h z = { h with streams := upd h.streams i (some z) } := by
        simp [ZStreamRef.put, g]
      rw [e]
      refine ⟨⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _, fun b _ outside => ?_⟩, fun b => ?_⟩
      · have ne : b ≠ i := fun same => outside (Or.inl same)
        simp [upd_ne _ _ _ _ ne]
      · by_cases same : b = i
        · subst same; simp [g]
        · simp [upd_ne _ _ _ _ same]
  | in_gzstate_strm i =>
    cases g : h.gzstates i with
    | none =>
      have e : (ZStreamRef.in_gzstate_strm i).put h z = h := by simp [ZStreamRef.put, g]
      rw [e]; exact PrivStep.refl h _ ds d
    | some v =>
      have e : (ZStreamRef.in_gzstate_strm i).put h z =
          { h with gzstates := upd h.gzstates i (some { v with strm := z }) } := by
        simp [ZStreamRef.put, g]
      rw [e]
      refine ⟨⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _, fun b _ outside => ?_⟩, fun b => ?_⟩
      · have ne : b ≠ i := fun same => outside (Or.inl same)
        simp [upd_ne _ _ _ _ ne]
      · by_cases same : b = i
        · subst same; simp [g]
        · simp [upd_ne _ _ _ _ same]

theorem buffer_frame_weaken {h g : Heap} {small large : Nat → Prop} {regions : List Region}
    (frame : BufferFrame h g small regions) (includes : ∀ b, small b → large b) : BufferFrame h g large regions :=
  ⟨full_frame_weaken frame.1 includes, frame.2⟩

/-! ## The frame of a strategy run -/

/-- The frame of a strategy run so far, from the heap `h0`, stream `z0` and state `d0` at the call:
the output frame (counts, totals, the written output interval, the heap shape) and the keys. -/
def Fr (h0 : Heap) (r : ZStreamRef) (ds : Nat) (d0 : DeflateState) (z0 : ZStream) (h : Heap) (z : ZStream)
    (d : DeflateState) : Prop :=
  (∃ used produced, OutFrame h0 h r ds d0 z0 z used produced) ∧ Keys d0 d

theorem Fr.refl {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (good : DGood h r ds z d) (buffers : StreamBuffers h r) : Fr h r ds d z h z d :=
  ⟨⟨0, 0, OutFrame.refl good.uniq (output_target good buffers)⟩, Keys.refl d⟩

theorem Fr.acc {h0 h : Heap} {r : ZStreamRef} {ds : Nat} {d0 d : DeflateState} {z0 z : ZStream}
    (fr : Fr h0 r ds d0 z0 h z d) : Acc z0 z := by
  obtain ⟨⟨_, _, f⟩, _⟩ := fr
  exact f.acc

theorem Fr.trans {h0 h1 h2 : Heap} {r : ZStreamRef} {ds : Nat} {d0 d1 d2 : DeflateState} {z0 z1 z2 : ZStream}
    (good0 : DGood h0 r ds z0 d0) (buffers0 : StreamBuffers h0 r)
    (one : Fr h0 r ds d0 z0 h1 z1 d1) (two : Fr h1 r ds d1 z1 h2 z2 d2) : Fr h0 r ds d0 z0 h2 z2 d2 := by
  obtain ⟨⟨_, _, f1⟩, k1⟩ := one
  obtain ⟨⟨_, _, f2⟩, k2⟩ := two
  exact ⟨⟨_, _, f1.trans f2 k1 good0.uniq (output_target good0 buffers0)⟩, k1.trans k2⟩

theorem Fr.priv {h h' : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d d' : DeflateState}
    (good : DGood h r ds z d) (buffers : StreamBuffers h r) (step : PrivStep h h' r ds d) (keys : Keys d d') :
    Fr h r ds d z h' z d' :=
  ⟨⟨0, 0, step.out good buffers⟩, keys⟩

theorem Fr.fill {roll : Prop} {h after : Heap} {r : ZStreamRef} {ds : Nat} {z z' : ZStream}
    {d d' : DeflateState} (good : DGood h r ds z d) (buffers : StreamBuffers h r)
    (post : FillPost roll h after r ds z z' d d') : Fr h r ds d z after z' d' := by
  obtain ⟨used, f⟩ := fill_out_frame good post buffers
  exact ⟨⟨used, 0, f⟩, post.keys⟩

theorem Fr.flush {h after : Heap} {r : ZStreamRef} {ds : Nat} {z z' : ZStream} {d d' : DeflateState}
    {produced : Nat} (account : StreamAccounting z z' 0 produced) (totalIn : z'.total_in = z.total_in)
    (totalOut : z'.total_out = z.total_out + UInt64.ofNat produced)
    (buffer : BufferFrame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) [⟨z.next_out, produced⟩])
    (shape : Zlib.Deflate.Proofs.Shape h after) (keys : Keys d d') : Fr h r ds d z after z' d' :=
  ⟨⟨0, produced, account, ⟨by rw [totalIn]; simp, totalOut⟩, buffer, shape⟩, keys⟩


theorem Fr.out {h after : Heap} {r : ZStreamRef} {ds : Nat} {z z' : ZStream} {d d' : DeflateState}
    {used produced : Nat} (frame : OutFrame h after r ds d z z' used produced) (keys : Keys d d') :
    Fr h r ds d z after z' d' :=
  ⟨⟨used, produced, frame⟩, keys⟩

/-- A private step that also reads input. -/
theorem Fr.read {h h' : Heap} {r : ZStreamRef} {ds : Nat} {z z' : ZStream} {d d' : DeflateState} {used : Nat}
    (good : DGood h r ds z d) (buffers : StreamBuffers h r) (step : PrivStep h h' r ds d)
    (account : StreamAccounting z z' used 0) (totals : Totals z z' used 0) (keys : Keys d d') :
    Fr h r ds d z h' z' d' :=
  ⟨⟨used, 0, out_frame_private account totals step.1 step.2 good.uniq (output_target good buffers)⟩, keys⟩

end Zlib.Deflate.Universal
