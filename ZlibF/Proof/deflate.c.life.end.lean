import ZlibF.Proof.«deflate.c.base»

/-!
# deflate.c: `deflateEnd`

`deflateEnd` frees the four buffers (`pending_buf`, `head`, `prev`, `window`, in this order) and the state, clears
`strm->state`, and returns `Z_DATA_ERROR` if the stream was in the middle of a block (`BUSY_STATE`) and `Z_OK` otherwise.
-/

namespace Zlib.Deflate.Spec
open C

/-- The heap after `free(p)` of a byte pointer that is `NULL` or the start of a block. -/
def freeBytes (h : Heap) (p : BPtr) : Heap :=
  match p with
  | .ref (.blk w) 0 => { h with bytes := upd h.bytes w none }
  | _ => h

/-- The heap after `free(p)` of a pointer to words that is `NULL` or the start of a block. -/
def freeWords (h : Heap) (p : WPtr) : Heap :=
  match p with
  | .ref (.blk w) 0 => { h with words := upd h.words w none }
  | _ => h

/-- The heap after `deflateEnd` of the stream `r` (record `z`) whose state is the record `d` at block `ds`: the four
buffers and the state record are gone, and the stream record has `state = NULL`. -/
def endHeap (h : Heap) (r : ZStreamRef) (ds : Nat) (z : ZStream) (d : DeflateState) : Heap :=
  { r.put (freeBytes (freeWords (freeWords (freeBytes h d.pending_buf) d.head) d.prev) d.window) { z with state := none }
    with dstates := upd h.dstates ds none }

end Zlib.Deflate.Spec

namespace Zlib.Deflate.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec

@[simp] theorem freeBytes_dstates (h : Heap) (p : BPtr) : (freeBytes h p).dstates = h.dstates := by
  unfold freeBytes; split <;> rfl
@[simp] theorem freeBytes_streams (h : Heap) (p : BPtr) : (freeBytes h p).streams = h.streams := by
  unfold freeBytes; split <;> rfl
@[simp] theorem freeBytes_gzstates (h : Heap) (p : BPtr) : (freeBytes h p).gzstates = h.gzstates := by
  unfold freeBytes; split <;> rfl
@[simp] theorem freeBytes_words (h : Heap) (p : BPtr) : (freeBytes h p).words = h.words := by
  unfold freeBytes; split <;> rfl
@[simp] theorem freeBytes_nextBlk (h : Heap) (p : BPtr) : (freeBytes h p).nextBlk = h.nextBlk := by
  unfold freeBytes; split <;> rfl
@[simp] theorem freeWords_dstates (h : Heap) (p : WPtr) : (freeWords h p).dstates = h.dstates := by
  unfold freeWords; split <;> rfl
@[simp] theorem freeWords_streams (h : Heap) (p : WPtr) : (freeWords h p).streams = h.streams := by
  unfold freeWords; split <;> rfl
@[simp] theorem freeWords_gzstates (h : Heap) (p : WPtr) : (freeWords h p).gzstates = h.gzstates := by
  unfold freeWords; split <;> rfl
@[simp] theorem freeWords_bytes (h : Heap) (p : WPtr) : (freeWords h p).bytes = h.bytes := by
  unfold freeWords; split <;> rfl
@[simp] theorem freeWords_nextBlk (h : Heap) (p : WPtr) : (freeWords h p).nextBlk = h.nextBlk := by
  unfold freeWords; split <;> rfl
@[simp] theorem freeWords_ro (h : Heap) (p : WPtr) : (freeWords h p).ro = h.ro := by
  unfold freeWords; split <;> rfl
@[simp] theorem freeBytes_ro (h : Heap) (p : BPtr) : (freeBytes h p).ro = h.ro := by
  unfold freeBytes; split <;> rfl
@[simp] theorem freeWords_gzheaders (h : Heap) (p : WPtr) : (freeWords h p).gzheaders = h.gzheaders := by
  unfold freeWords; split <;> rfl
@[simp] theorem freeBytes_gzheaders (h : Heap) (p : BPtr) : (freeBytes h p).gzheaders = h.gzheaders := by
  unfold freeBytes; split <;> rfl
@[simp] theorem freeWords_istates (h : Heap) (p : WPtr) : (freeWords h p).istates = h.istates := by
  unfold freeWords; split <;> rfl
@[simp] theorem freeBytes_istates (h : Heap) (p : BPtr) : (freeBytes h p).istates = h.istates := by
  unfold freeBytes; split <;> rfl

@[simp] theorem ZStreamRef.get_freeBytes (h : Heap) (p : BPtr) (r : ZStreamRef) : r.get (freeBytes h p) = r.get h := by
  cases r <;> simp [ZStreamRef.get]
@[simp] theorem ZStreamRef.get_freeWords (h : Heap) (p : WPtr) (r : ZStreamRef) : r.get (freeWords h p) = r.get h := by
  cases r <;> simp [ZStreamRef.get]

theorem zfreeB_run {h : Heap} {r : ZStreamRef} {z : ZStream} (hz : r.get h = some z) (hf : z.zfree = .fn "zcfree")
    {p : BPtr} (hp : p = .null ∨ ∃ b a, p = .ref (.blk b) 0 ∧ h.bytes b = some a ∧ h.ro b = false) :
    ZFREE_bytes (some r) p h = .ok ((), freeBytes h p) := by
  rcases hp with rfl | ⟨b, a, rfl, hb, hro⟩
  · simp [ZFREE_bytes, zfree_default, ldZ_eq, hz, hf, freeBytes, freeB_null, bind_app]
  · simp [ZFREE_bytes, zfree_default, ldZ_eq, hz, hf, freeBytes, freeB_ok hb hro, bind_app]

theorem zfreeW_run {h : Heap} {r : ZStreamRef} {z : ZStream} (hz : r.get h = some z) (hf : z.zfree = .fn "zcfree")
    {p : WPtr} (hp : p = .null ∨ ∃ b a, p = .ref (.blk b) 0 ∧ h.words b = some a) :
    ZFREE_words (some r) p h = .ok ((), freeWords h p) := by
  rcases hp with rfl | ⟨b, a, rfl, hb⟩
  · simp [ZFREE_words, zfree_default, ldZ_eq, hz, hf, freeWords, bind_app]; rfl
  · simp [ZFREE_words, zfree_default, ldZ_eq, hz, hf, freeWords, freeW_ok hb, bind_app]


@[simp] theorem ZStreamRef.get_dstates (g : Heap) (r : ZStreamRef) (t : Tbl (Option DeflateState)) :
    r.get { g with dstates := t } = r.get g := by cases r <;> rfl

theorem ZStreamRef.put_with_dstates (g : Heap) (r : ZStreamRef) (t : Tbl (Option DeflateState)) (v : ZStream) :
    r.put { g with dstates := t } v = { r.put g v with dstates := t } := by
  cases r with
  | tab i => simp only [ZStreamRef.put]; cases g.streams i <;> rfl
  | in_gzstate_strm i => simp only [ZStreamRef.put]; cases g.gzstates i <;> rfl

theorem zfree_default_run {h : Heap} {r : ZStreamRef} {z : ZStream} (hz : r.get h = some z)
    (hf : z.zfree = .fn "zcfree") : zfree_default (some r) h = .ok ((), h) := by
  simp [zfree_default, ldZ_eq, hz, hf, bind_app]

theorem freeDeflateState_free_ok {h' : Heap} {ds : Nat} {d : DeflateState} (hd : h'.dstates ds = some d) :
    freeDeflateState (some (.tab ds)) h' = .ok ((), { h' with dstates := upd h'.dstates ds none }) :=
  freeDeflateState_tab hd

theorem deflateEnd_run {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState} {w p q b : Nat}
    (hL : DLive h r ds z d) (hf : z.zfree = .fn "zcfree") (hB : DBlocks h d w p q b) :
    deflateEnd (some r) h =
      .ok ((if d.status == BUSY_STATE then Z_DATA_ERROR else Z_OK), endHeap h r ds z d) := by
  obtain ⟨wa, hwa, -⟩ := hB.wa
  obtain ⟨pa, hpa, -⟩ := hB.pa
  obtain ⟨qa, hqa, -⟩ := hB.qa
  obtain ⟨ba, hba, -⟩ := hB.ba
  have hbw : b ≠ w := fun e => hB.wb e.symm
  have f1 := zfreeB_run (h := h) hL.hz hf (p := d.pending_buf) (Or.inr ⟨b, ba, hB.pbuf, hba, hB.bro⟩)
  have f2 := zfreeW_run (h := freeBytes h d.pending_buf) (r := r) (z := z) (by simpa using hL.hz) hf (p := d.head)
    (Or.inr ⟨q, qa, hB.head, by simpa using hqa⟩)
  have f3 := zfreeW_run (h := freeWords (freeBytes h d.pending_buf) d.head) (r := r) (z := z) (by simpa using hL.hz) hf
    (p := d.prev) (Or.inr ⟨p, pa, hB.prev, by
      have : (freeWords (freeBytes h d.pending_buf) d.head).words p = h.words p := by
        rw [hB.head]; simp [freeWords, upd_ne _ _ _ _ hB.pq]
      rw [this]; exact hpa⟩)
  have f4 := zfreeB_run (h := freeWords (freeWords (freeBytes h d.pending_buf) d.head) d.prev) (r := r) (z := z)
    (by simpa using hL.hz) hf (p := d.window) (Or.inr ⟨w, wa, hB.win, by
      simp only [freeWords_bytes, freeBytes, hB.pbuf, hB.win]
      simp [upd_ne _ _ _ _ hbw.symm, hwa], by simpa using hB.wro⟩)
  simp only [hB.pbuf, hB.head, hB.prev, hB.win] at f1 f2 f3 f4
  unfold deflateEnd
  dsimp' [stateCheck_live hL, hL.zst, hL.hz, hL.hs, hB.pbuf, hB.head, hB.prev, hB.win, f1, f2, f3, f4]
  have hz' : ∀ h' : Heap, r.get h' = r.get h → zfree_default (some r) h' = .ok ((), h') := fun h' e =>
    zfree_default_run (by rw [e]; exact hL.hz) hf
  rw [hz']
  · simp only [bind_app, pure_app]
    rw [freeDeflateState_free_ok (d := d)]
    · simp only [ZStreamRef.get_dstates, ZStreamRef.get_freeBytes, ZStreamRef.get_freeWords, hL.hz,
        ZStreamRef.put_with_dstates, endHeap, hB.win, hB.prev, hB.head, hB.pbuf, freeBytes_dstates, freeWords_dstates]
    · simp [hL.hs]
  · simp


theorem endHeap_eq {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState} {w p q b : Nat}
    (hB : DBlocks h d w p q b) :
    endHeap h r ds z d = { r.put { h with bytes := upd (upd h.bytes b none) w none,
                                          words := upd (upd h.words q none) p none } { z with state := none }
                           with dstates := upd h.dstates ds none } := by
  unfold endHeap
  rw [hB.win, hB.prev, hB.head, hB.pbuf]
  simp only [freeBytes, freeWords]

theorem DOwned_iff {d : DeflateState} {ds w p q b : Nat} {h : Heap} (hB : DBlocks h d w p q b) (x : Nat) :
    DOwned d ds x ↔ x = ds ∨ x = w ∨ x = p ∨ x = q ∨ x = b := by
  unfold DOwned
  rw [hB.win, hB.prev, hB.head, hB.pbuf]
  constructor
  · rintro (h1 | ⟨w', h2, h3⟩ | ⟨p', h2, h3⟩ | ⟨q', h2, h3⟩ | ⟨b', h2, h3⟩)
    · exact Or.inl h1
    · cases h2; exact Or.inr (Or.inl h3)
    · cases h2; exact Or.inr (Or.inr (Or.inl h3))
    · cases h2; exact Or.inr (Or.inr (Or.inr (Or.inl h3)))
    · cases h2; exact Or.inr (Or.inr (Or.inr (Or.inr h3)))
  · rintro (h1 | h1 | h1 | h1 | h1)
    · exact Or.inl h1
    · exact Or.inr (Or.inl ⟨w, by simp, h1⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨p, by simp, h1⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨q, by simp, h1⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨b, by simp, h1⟩)))

theorem ZStreamRef.get_bw (g : Heap) (r : ZStreamRef) (bs : Tbl (Option (Array UInt8))) (ws : Tbl (Option (Array UInt16))) :
    r.get { g with bytes := bs, words := ws } = r.get g := by cases r <;> rfl

theorem ZStreamRef.put_streams (r : ZStreamRef) (g : Heap) (v : ZStream) (x : Nat)
    (hx : ∀ i, r = .tab i → x ≠ i) : (r.put g v).streams x = g.streams x := by
  cases r with
  | tab i => 
    have := hx i rfl
    simp only [ZStreamRef.put]; split <;> simp [upd_apply, this]
  | in_gzstate_strm i => simp only [ZStreamRef.put]; split <;> rfl

theorem ZStreamRef.put_gzstates (r : ZStreamRef) (g : Heap) (v : ZStream) (x : Nat)
    (hx : ∀ i, r = .in_gzstate_strm i → x ≠ i) : (r.put g v).gzstates x = g.gzstates x := by
  cases r with
  | tab i => simp only [ZStreamRef.put]; split <;> rfl
  | in_gzstate_strm i =>
    have := hx i rfl
    simp only [ZStreamRef.put]; split <;> simp [upd_apply, this]

theorem endHeap_tables {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState} {w p q b : Nat}
    (hB : DBlocks h d w p q b) (hz : r.get h = some z) (x : Nat) :
    (endHeap h r ds z d).bytes x = (if x = w ∨ x = b then none else h.bytes x) ∧
    (endHeap h r ds z d).words x = (if x = p ∨ x = q then none else h.words x) ∧
    (endHeap h r ds z d).dstates x = (if x = ds then none else h.dstates x) ∧
    ((endHeap h r ds z d).streams x).isSome = (h.streams x).isSome ∧
    ((endHeap h r ds z d).gzstates x).isSome = (h.gzstates x).isSome ∧
    (endHeap h r ds z d).gzheaders x = h.gzheaders x ∧ (endHeap h r ds z d).istates x = h.istates x := by
  have hS : Shape { h with bytes := upd (upd h.bytes b none) w none, words := upd (upd h.words q none) p none }
      (r.put { h with bytes := upd (upd h.bytes b none) w none, words := upd (upd h.words q none) p none }
        { z with state := none }) := shape_put (by rw [ZStreamRef.get_bw]; exact hz) _
  obtain ⟨-, -, e4, -, -, -, e5⟩ := hS x
  rw [endHeap_eq hB]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [ZStreamRef.put_bytes]; simp only [upd_apply]
    by_cases h1 : x = w <;> by_cases h2 : x = b <;> simp [h1, h2]
  · simp only [ZStreamRef.put_words]; simp only [upd_apply]
    by_cases h1 : x = p <;> by_cases h2 : x = q <;> simp [h1, h2]
  · simp only [ZStreamRef.put_dstates]; simp only [upd_apply]
  · exact e4
  · exact e5
  · simp
  · simp

theorem endHeap_live {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState} {w p q b : Nat}
    (hB : DBlocks h d w p q b) (hU : Uniq h) (hz : r.get h = some z) (hs : h.dstates ds = some d) (x : Nat) :
    (endHeap h r ds z d).live x ↔ h.live x ∧ ¬ (x = ds ∨ x = w ∨ x = p ∨ x = q ∨ x = b) := by
  obtain ⟨wa, hwa, -⟩ := hB.wa
  obtain ⟨pa, hpa, -⟩ := hB.pa
  obtain ⟨qa, hqa, -⟩ := hB.qa
  obtain ⟨ba, hba, -⟩ := hB.ba
  obtain ⟨t1, t2, t3, t4, t5, t6, t7⟩ := endHeap_tables (ds := ds) hB hz x
  have key : (endHeap h r ds z d).live x ↔
      ((endHeap h r ds z d).bytes x ≠ none ∨ (endHeap h r ds z d).words x ≠ none ∨ (h.streams x).isSome ∨
        h.gzheaders x ≠ none ∨ (endHeap h r ds z d).dstates x ≠ none ∨ h.istates x ≠ none ∨ (h.gzstates x).isSome) := by
    unfold Heap.live
    rw [t6, t7, ← Option.isSome_iff_ne_none (o := (endHeap h r ds z d).streams x), t4,
      ← Option.isSome_iff_ne_none (o := (endHeap h r ds z d).gzstates x), t5]
  rw [key]
  unfold Heap.live
  rw [t1, t2, t3]
  by_cases hx : x = ds ∨ x = w ∨ x = p ∨ x = q ∨ x = b
  · simp only [hx, not_true_eq_false, and_false, iff_false]
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · obtain ⟨e1, e2, e3, e4, e5, e6⟩ := hU.dstates_only hs
      simp [e1, e2, e3, e4, e5, e6]
    · obtain ⟨e1, e2, e3, e4, e5, e6⟩ := hU.bytes_only hwa
      simp [e1, e2, e3, e4, e5, e6, Option.isSome_none]
    · obtain ⟨e1, e2, e3, e4, e5, e6⟩ := hU.words_only hpa
      simp [e1, e2, e3, e4, e5, e6, Option.isSome_none]
    · obtain ⟨e1, e2, e3, e4, e5, e6⟩ := hU.words_only hqa
      simp [e1, e2, e3, e4, e5, e6, Option.isSome_none]
    · obtain ⟨e1, e2, e3, e4, e5, e6⟩ := hU.bytes_only hba
      simp [e1, e2, e3, e4, e5, e6, Option.isSome_none]
  · have hx1 : ¬ (x = w ∨ x = b) := fun e => hx (by rcases e with e | e <;> simp [e])
    have hx2 : ¬ (x = p ∨ x = q) := fun e => hx (by rcases e with e | e <;> simp [e])
    have hx3 : ¬ x = ds := fun e => hx (Or.inl e)
    have hn : ¬ (x = w ∨ x = p ∨ x = q ∨ x = b) := fun e => hx (Or.inr e)
    simp only [hx1, hx2, hx3, ite_false]
    simp [hn, Option.isSome_iff_ne_none]

theorem endHeap_uniq {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState} {w p q b : Nat}
    (hB : DBlocks h d w p q b) (hU : Uniq h) (hz : r.get h = some z) : Uniq (endHeap h r ds z d) := by
  intro x
  obtain ⟨t1, t2, t3, t4, t5, t6, t7⟩ := endHeap_tables (ds := ds) hB hz x
  have := hU x
  have c1 : cnt ((endHeap h r ds z d).bytes x) ≤ cnt (h.bytes x) := by
    rw [t1]; split <;> simp [cnt]
  have c2 : cnt ((endHeap h r ds z d).words x) ≤ cnt (h.words x) := by
    rw [t2]; split <;> simp [cnt]
  have c3 : cnt ((endHeap h r ds z d).dstates x) ≤ cnt (h.dstates x) := by
    rw [t3]; split <;> simp [cnt]
  have c4 : cnt ((endHeap h r ds z d).streams x) = cnt (h.streams x) := by simp only [cnt, t4]
  have c5 : cnt ((endHeap h r ds z d).gzstates x) = cnt (h.gzstates x) := by simp only [cnt, t5]
  rw [t6, t7]
  omega

/-- **deflateEnd, safety and specification.** On an initialised stream with the invariant and the default `zfree`, the
call never faults. It returns `Z_DATA_ERROR` if the status was `BUSY_STATE` (the stream ended in the middle of a block)
and `Z_OK` otherwise. It frees exactly the state record and its four buffers (`window`, `prev`, `head`, `pending_buf`) and
sets `strm->state` to `NULL`: the live blocks afterwards are the old ones minus those five (no leak, no double
free), every other block of every table is as before, and the heap is again `Uniq` and `Fresh`. (The blocks are named by
`DBlocks`.) -/
theorem deflateEnd_safe {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (hG : DGood h r ds z d) (hf : z.zfree = .fn "zcfree") :
    ∃ w p q b, DBlocks h d w p q b ∧ ∃ h',
      C.run (deflateEnd (some r)) h = .ok ((if d.status = BUSY_STATE then Z_DATA_ERROR else Z_OK), h') ∧
      h' = endHeap h r ds z d ∧ r.get h' = some { z with state := none } ∧
      h'.dstates ds = none ∧ h'.bytes w = none ∧ h'.bytes b = none ∧ h'.words p = none ∧ h'.words q = none ∧
      (∀ x, x ≠ ds → h'.dstates x = h.dstates x) ∧ (∀ x, x ≠ w → x ≠ b → h'.bytes x = h.bytes x) ∧
      (∀ x, x ≠ p → x ≠ q → h'.words x = h.words x) ∧ h'.ro = h.ro ∧ h'.gzheaders = h.gzheaders ∧
      h'.istates = h.istates ∧ h'.nextBlk = h.nextBlk ∧ h'.nalloc = h.nalloc ∧
      (∀ x, (∀ i, r = .tab i → x ≠ i) → h'.streams x = h.streams x) ∧
      (∀ x, (∀ i, r = .in_gzstate_strm i → x ≠ i) → h'.gzstates x = h.gzstates x) ∧
      Uniq h' ∧ Fresh h' ∧ (∀ S, h.Owns S → h'.Owns (fun x => S x ∧ ¬ DOwned d ds x)) := by
  obtain ⟨w, p, q, b, hB⟩ := hG.inv.blocks
  refine ⟨w, p, q, b, hB, _, ?_, rfl, ?_⟩
  · have := deflateEnd_run hG.live hf hB
    rw [C.run, this]
    simp [BEq.beq]
  have hU := hG.uniq
  have hF := hG.fresh
  obtain ⟨wa, hwa, -⟩ := hB.wa
  obtain ⟨pa, hpa, -⟩ := hB.pa
  obtain ⟨qa, hqa, -⟩ := hB.qa
  obtain ⟨ba, hba, -⟩ := hB.ba
  have hbw : b ≠ w := fun e => hB.wb e.symm
  have hz := hG.live.hz
  have hs := hG.live.hs
  have hUni := endHeap_uniq (ds := ds) hB hU hz
  have hLive := endHeap_live hB hU hz hs
  have hnb : (endHeap h r ds z d).nextBlk = h.nextBlk := by rw [endHeap_eq hB]; simp
  rw [endHeap_eq hB]
  refine ⟨?_, by simp, by simp, by simp [hbw], by simp, by simp [hB.pq.symm], ?_, ?_, ?_, by simp, by simp, by simp, by simp,
    by simp, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ZStreamRef.get_dstates, ZStreamRef.get_put, ZStreamRef.get_bw, hz]; rfl
  · intro x hx; simp [upd_apply, hx]
  · intro x h1 h2; simp [upd_apply, h1, h2]
  · intro x h1 h2; simp [upd_apply, h1, h2]
  · intro x hx; simp [ZStreamRef.put_streams r _ _ x hx]
  · intro x hx; simp [ZStreamRef.put_gzstates r _ _ x hx]
  · rw [← endHeap_eq hB]; exact hUni
  · intro x hx hl
    rw [← endHeap_eq hB] at hl
    rw [← endHeap_eq hB] at hx
    rw [hnb] at hx
    exact hF x hx ((hLive x).1 hl).1
  · intro S hO x
    rw [← endHeap_eq hB, hLive x, hO x]
    show _ ↔ S x ∧ ¬ DOwned d ds x
    rw [DOwned_iff hB x]

/-- **deflateEnd, refusal.** On a stream the check refuses (including `NULL`) the call returns `Z_STREAM_ERROR` and changes
nothing (in particular nothing is freed). -/
theorem deflateEnd_reject {h : Heap} {strm : ZStreamPtr} (hD : StreamDom h strm) (hN : ¬ DInitialised h strm) :
    C.run (deflateEnd strm) h = .ok (Z_STREAM_ERROR, h) := by
  unfold deflateEnd
  exact check_refuse hD hN _ _

end Zlib.Deflate.Proofs
