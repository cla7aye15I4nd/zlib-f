import ZlibF.Proof.«gz.inv-queries»
import ZlibF.Proof.«public-gz-error»
import ZlibF.Proof.«inflate.c.match-invariant»
import ZlibF.Proof.«inflate.c.byte-views»
import ZlibF.Proof.PlatformMemory

/-!
# gz safety: a write outside the handle keeps `GzInv`, and `gzerror`

`GzInv.frame_shape`: when every block the handle owns is unchanged, the same blocks exist in the same tables
(`Shape`), and the global facts hold of the new heap, the invariant holds of the new heap with the same record,
and the handle owns the same blocks. `GzInv.byte_put` instantiates it for one store into a byte view the handle
does not own. `gzerror_step` (skeleton statement, unchanged) follows: `gzerror` stores the code into the
caller's 4-byte cell and changes nothing else.
-/

namespace ZlibF.Spec.Public
open C Zlib.GzFs
set_option autoImplicit false

theorem live_of_shape {h after : Heap} (sh : Zlib.Gzlib.Spec.Shape h after) (b : Nat) :
    after.live b ↔ h.live b := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := sh b
  simp only [Heap.live, Option.ne_none_iff_isSome, e1, e2, e3, e4, e5, e6, e7]

theorem uniq_of_shape {h after : Heap} (sh : Zlib.Gzlib.Spec.Shape h after) (u : Zlib.Gzlib.Spec.Uniq h) :
    Zlib.Gzlib.Spec.Uniq after := by
  intro b
  obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := sh b
  have hb := u b
  simp only [Zlib.Gzlib.Spec.cnt, e1, e2, e3, e4, e5, e6, e7] at hb ⊢
  exact hb

theorem bytes_blk_congr {h after : Heap} {c o n : Nat} {xs : List UInt8} (e : after.bytes c = h.bytes c) :
    Bytes after (.ref (.blk c) o) n xs ↔ Bytes h (.ref (.blk c) o) n xs := by
  have eg : Space.get after (BRef.blk c) = Space.get h (BRef.blk c) := e
  unfold Bytes
  constructor
  · rintro (⟨hp, _, _⟩ | ⟨r, j, a, hp, hg, hle, hx⟩)
    · cases hp
    · cases hp
      exact Or.inr ⟨_, _, a, rfl, by rw [← eg]; exact hg, hle, hx⟩
  · rintro (⟨hp, _, _⟩ | ⟨r, j, a, hp, hg, hle, hx⟩)
    · cases hp
    · cases hp
      exact Or.inr ⟨_, _, a, rfl, by rw [eg]; exact hg, hle, hx⟩

theorem cstring_blk_congr {h after : Heap} {c o : Nat} {xs : List UInt8} (e : after.bytes c = h.bytes c) :
    CString after (.ref (.blk c) o) xs ↔ CString h (.ref (.blk c) o) xs := by
  unfold CString
  rw [bytes_blk_congr e]

section frame
variable {h after : Heap} {i : Nat} {s : GzState}

/-- A block the codec of the handle owns is owned by the handle. -/
theorem GzInv.streamOwned_owned (inv : GzInv h i s) {b : Nat} (hb : StreamOwned h (gzStrm i) b) :
    GzOwned h i s b := by
  have hs := inv.common.record
  by_cases hz : s.size = 0
  · exfalso
    rcases inv.common.mode with hm | hm
    · exact noCodec_owned hs ((inv.reader hm).unalloc hz).2.2.2 b hb
    · exact noCodec_owned hs ((inv.writer hm).unalloc hz) b hb
  · rcases inv.common.mode with hm | hm
    · exact Or.inr (Or.inr (Or.inr ⟨hz, Or.inr ⟨Or.inl hm, Or.inr hb⟩⟩))
    · by_cases hd : s.direct = 0
      · exact Or.inr (Or.inr (Or.inr ⟨hz, Or.inr ⟨Or.inr hd, Or.inr hb⟩⟩))
      · exact absurd hb (noCodec_owned hs ((inv.writer hm).transparent hd) b)

/-- The inflate state named by the embedded stream is live. -/
theorem GzInv.inflate_live (inv : GzInv h i s) {k : Nat} (hk : s.strm.state = some (.inflate k)) :
    ∃ st, h.istates k = some st := by
  have hs := inv.common.record
  rcases inv.common.mode with hm | hm
  · have r := inv.reader hm
    by_cases hz : s.size = 0
    · rw [(r.unalloc hz).2.2.2] at hk
      cases hk
    · obtain ⟨_, z, k', st, hzget, hzst, hk', _⟩ := r.codec hz
      have hzs : s.strm = z := by simpa [ZStreamRef.get, gzStrm, hs] using hzget
      subst hzs
      rw [hk] at hzst
      cases hzst
      exact ⟨st, hk'⟩
  · have w := inv.writer hm
    by_cases hz : s.size = 0
    · rw [w.unalloc hz] at hk
      cases hk
    · by_cases hd : s.direct = 0
      · obtain ⟨_, z, k', d, hzget, hzst, _, _⟩ := w.codec hd hz
        have hzs : s.strm = z := by simpa [ZStreamRef.get, gzStrm, hs] using hzget
        subst hzs
        rw [hk] at hzst
        cases hzst
      · rw [w.transparent hd] at hk
        cases hk

/-- The deflate state named by the embedded stream is live. -/
theorem GzInv.deflate_live (inv : GzInv h i s) {k : Nat} (hk : s.strm.state = some (.deflate k)) :
    ∃ d, h.dstates k = some d := by
  have hs := inv.common.record
  rcases inv.common.mode with hm | hm
  · have r := inv.reader hm
    by_cases hz : s.size = 0
    · rw [(r.unalloc hz).2.2.2] at hk
      cases hk
    · obtain ⟨_, z, k', st, hzget, hzst, _, _⟩ := r.codec hz
      have hzs : s.strm = z := by simpa [ZStreamRef.get, gzStrm, hs] using hzget
      subst hzs
      rw [hk] at hzst
      cases hzst
  · have w := inv.writer hm
    by_cases hz : s.size = 0
    · rw [w.unalloc hz] at hk
      cases hk
    · by_cases hd : s.direct = 0
      · obtain ⟨_, z, k', d, hzget, hzst, hk', _⟩ := w.codec hd hz
        have hzs : s.strm = z := by simpa [ZStreamRef.get, gzStrm, hs] using hzget
        subst hzs
        rw [hk] at hzst
        cases hzst
        exact ⟨d, hk'⟩
      · rw [w.transparent hd] at hk
        cases hk

/-- An owned block is unchanged by a frame over the blocks the handle does not own. -/
theorem GzInv.kept (inv : GzInv h i s) (fr : Frame h after (fun b => ¬ GzOwned h i s b)) {b : Nat}
    (hb : GzOwned h i s b) :
    after.bytes b = h.bytes b ∧ after.words b = h.words b ∧ after.streams b = h.streams b ∧
    after.gzheaders b = h.gzheaders b ∧ after.dstates b = h.dstates b ∧ after.istates b = h.istates b ∧
    after.gzstates b = h.gzstates b ∧ after.ro b = h.ro b :=
  fr.2.2.2.2.2 b (inv.common.live b hb) (fun hn => hn hb)

theorem GzInv.frame_get (inv : GzInv h i s) (fr : Frame h after (fun b => ¬ GzOwned h i s b)) :
    ZStreamRef.get after (.in_gzstate_strm i) = ZStreamRef.get h (.in_gzstate_strm i) := by
  show (after.gzstates i).map (·.strm) = (h.gzstates i).map (·.strm)
  rw [(inv.kept fr (Or.inl rfl)).2.2.2.2.2.2.1]

/-- The codec owns the same blocks after a frame that keeps the owned blocks and the shape. -/
theorem GzInv.frame_streamOwned (inv : GzInv h i s) (fr : Frame h after (fun b => ¬ GzOwned h i s b))
    (b : Nat) :
    StreamOwned after (.in_gzstate_strm i) b ↔ StreamOwned h (.in_gzstate_strm i) b := by
  have hget := inv.frame_get fr
  constructor
  · rintro ⟨z, hz, ⟨k, st, hk, hst, ho⟩ | ⟨k, d, hk, hd, ho⟩⟩
    · rw [hget] at hz
      have hzs : s.strm = z := by simpa [ZStreamRef.get, gzStrm, inv.common.record] using hz
      obtain ⟨st0, hst0⟩ := inv.inflate_live (by rw [hzs]; exact hk)
      have hown : StreamOwned h (gzStrm i) k := ⟨z, hz, Or.inl ⟨k, st0, hk, hst0, Or.inl rfl⟩⟩
      have he := (inv.kept fr (inv.streamOwned_owned hown)).2.2.2.2.2.1
      rw [he, hst0] at hst
      cases hst
      exact ⟨z, hz, Or.inl ⟨k, _, hk, hst0, ho⟩⟩
    · rw [hget] at hz
      have hzs : s.strm = z := by simpa [ZStreamRef.get, gzStrm, inv.common.record] using hz
      obtain ⟨d0, hd0⟩ := inv.deflate_live (by rw [hzs]; exact hk)
      have hown : StreamOwned h (gzStrm i) k := ⟨z, hz, Or.inr ⟨k, d0, hk, hd0, Or.inl rfl⟩⟩
      have he := (inv.kept fr (inv.streamOwned_owned hown)).2.2.2.2.1
      rw [he, hd0] at hd
      cases hd
      exact ⟨z, hz, Or.inr ⟨k, _, hk, hd0, ho⟩⟩
  · rintro ⟨z, hz, ⟨k, st, hk, hst, ho⟩ | ⟨k, d, hk, hd, ho⟩⟩
    · have hown : StreamOwned h (gzStrm i) k := ⟨z, hz, Or.inl ⟨k, st, hk, hst, Or.inl rfl⟩⟩
      have he := (inv.kept fr (inv.streamOwned_owned hown)).2.2.2.2.2.1
      exact ⟨z, by rw [hget]; exact hz, Or.inl ⟨k, st, hk, by rw [he]; exact hst, ho⟩⟩
    · have hown : StreamOwned h (gzStrm i) k := ⟨z, hz, Or.inr ⟨k, d, hk, hd, Or.inl rfl⟩⟩
      have he := (inv.kept fr (inv.streamOwned_owned hown)).2.2.2.2.1
      exact ⟨z, by rw [hget]; exact hz, Or.inr ⟨k, d, hk, by rw [he]; exact hd, ho⟩⟩

theorem GzInv.frame_owned (inv : GzInv h i s) (fr : Frame h after (fun b => ¬ GzOwned h i s b))
    (b : Nat) : GzOwned after i s b ↔ GzOwned h i s b := by
  unfold GzOwned
  rw [inv.frame_streamOwned fr]

/-- The frame over the blocks the handle does not own, seen as the frame of a rebuffer of its codec. -/
theorem GzInv.frame_rebuffer (inv : GzInv h i s) (fr : Frame h after (fun b => ¬ GzOwned h i s b))
    (fresh : Fresh after) (uniq : Zlib.Gzlib.Spec.Uniq after) (globals : LibraryGlobals after) :
    Rebuffer h after (gzStrm i) := by
  have hs := inv.common.record
  have hs' : after.gzstates i = some s := by rw [(inv.kept fr (Or.inl rfl)).2.2.2.2.2.2.1]; exact hs
  refine ⟨fresh, uniq, globals, ⟨fr.1, fr.2.1, fr.2.2.1, fr.2.2.2.1, fr.2.2.2.2.1, ?_⟩, s.strm, s.strm,
    ?_, ?_, rfl⟩
  · intro b hl hn
    exact fr.2.2.2.2.2 b hl (fun hg => hg (inv.streamOwned_owned (Classical.byContradiction hn)))
  · simp [ZStreamRef.get, gzStrm, hs]
  · simp [ZStreamRef.get, gzStrm, hs']

/-- **`GzInv` survives a change of the heap that keeps every block the handle owns.** -/
theorem GzInv.frame_core (inv : GzInv h i s) (fr : Frame h after (fun b => ¬ GzOwned h i s b))
    (fresh : Fresh after) (uniq : Zlib.Gzlib.Spec.Uniq after)
    (globals : LibraryGlobals after) (fit : ZlibF.PlatformMemory.ByteObjectsFit after) :
    GzInv after i s ∧ (∀ b, GzOwned after i s b ↔ GzOwned h i s b) := by
  have c := inv.common
  have hs' : after.gzstates i = some s := by rw [(inv.kept fr (Or.inl rfl)).2.2.2.2.2.2.1]; exact c.record
  have hso : ∀ b, StreamOwned after (gzStrm i) b ↔ StreamOwned h (gzStrm i) b := inv.frame_streamOwned fr
  have hown := inv.frame_owned fr
  have hlive : ∀ b, GzOwned h i s b → after.live b := by
    intro b ho
    have hl := c.live b ho
    obtain ⟨e1, e2, e3, e4, e5, e6, e7, _⟩ := inv.kept fr ho
    simp only [Heap.live, e1, e2, e3, e4, e5, e6, e7]
    exact hl
  have hbytes : ∀ b, GzOwned h i s b → after.bytes b = h.bytes b := fun b hb => (inv.kept fr hb).1
  have hro : ∀ b, GzOwned h i s b → after.ro b = h.ro b := fun b hb => (inv.kept fr hb).2.2.2.2.2.2.2
  have hexact : ∀ p n, (∀ b, p = .ref (.blk b) 0 → GzOwned h i s b) → ExactBuffer h p n → ExactBuffer after p n := by
    intro p n own hx
    obtain ⟨b, a, hp, hb, hr, hsz⟩ := hx
    exact ⟨b, a, hp, by rw [hbytes b (own b hp)]; exact hb, by rw [hro b (own b hp)]; exact hr, hsz⟩
  have hmalloc : ∀ p n, (∀ b, p = .ref (.blk b) 0 → GzOwned h i s b) → MallocBuffer h p n →
      MallocBuffer after p n := by
    intro p n own hx
    obtain ⟨b, a, hp, hb, hr, hsz⟩ := hx
    exact ⟨b, a, hp, by rw [hbytes b (own b hp)]; exact hb, by rw [hro b (own b hp)]; exact hr, hsz⟩
  have hreb := inv.frame_rebuffer fr fresh uniq globals
  have hget : ZStreamRef.get after (gzStrm i) = ZStreamRef.get h (gzStrm i) := inv.frame_get fr
  refine ⟨⟨?_, ?_, ?_⟩, hown⟩
  · exact {
      record := hs'
      mode := c.mode
      fresh := fresh
      uniq := uniq
      globals := globals
      fit := fit
      path := by
        obtain ⟨p, hc, hm⟩ := c.path
        obtain ⟨pb, a, hp, hb, hr, hn⟩ := hm
        have own : GzOwned h i s pb := Or.inr (Or.inl hp)
        refine ⟨p, ?_, hmalloc _ _ (fun b e => by rw [hp] at e; cases e; exact own) ⟨pb, a, hp, hb, hr, hn⟩⟩
        rw [hp] at hc ⊢
        exact (cstring_blk_congr (hbytes pb own)).2 hc
      msg := by
        rcases c.msg with hn | ⟨m, hc, hm⟩
        · exact Or.inl hn
        · obtain ⟨mb, a, hp, hb, hr, hn⟩ := hm
          have own : GzOwned h i s mb := Or.inr (Or.inr (Or.inl hp))
          refine Or.inr ⟨m, ?_, hmalloc _ _ (fun b e => by rw [hp] at e; cases e; exact own) ⟨mb, a, hp, hb, hr, hn⟩⟩
          rw [hp] at hc ⊢
          exact (cstring_blk_congr (hbytes mb own)).2 hc
      memerr := c.memerr
      want := c.want
      size := c.size
      distinct := ⟨c.distinct.1, fun p hp b hb =>
        ⟨(c.distinct.2 p hp b hb).1, by rw [hso]; exact (c.distinct.2 p hp b hb).2⟩⟩
      live := fun b hb => hlive b ((hown b).1 hb)
      pos := c.pos
      next := by
        rcases c.next with hn | ⟨b, off, a, hx, hbi, ho, hmb, hb, hle⟩
        · exact Or.inl hn
        · exact Or.inr ⟨b, off, a, hx, hbi, (hown b).2 ho, hmb, by rw [hbytes b ho]; exact hb, hle⟩
      nullHave := c.nullHave
      recordFree := fun hn => c.recordFree ((hso i).1 hn) }
  · intro hm
    have r := inv.reader hm
    exact {
      how := r.how
      copyDirect := r.copyDirect
      gzipDirect := r.gzipDirect
      direct := r.direct
      junk := r.junk
      flags := r.flags
      unalloc := r.unalloc
      bufs := fun hz =>
        ⟨hexact _ _ (fun b hp => Or.inr (Or.inr (Or.inr ⟨hz, Or.inl hp⟩))) (r.bufs hz).1,
         hexact _ _ (fun b hp => Or.inr (Or.inr (Or.inr ⟨hz, Or.inr ⟨Or.inl hm, Or.inl hp⟩⟩))) (r.bufs hz).2⟩
      input := r.input
      output := r.output
      codec := fun hz => by
        obtain ⟨reach, z, k, st, hzget, hzst, hk, hhead⟩ := r.codec hz
        have hown_k : StreamOwned h (gzStrm i) k := ⟨z, hzget, Or.inl ⟨k, st, hzst, hk, Or.inl rfl⟩⟩
        have he := (inv.kept fr (inv.streamOwned_owned hown_k)).2.2.2.2.2.1
        exact ⟨StreamReachable.rebuffer reach hreb (fun _ => fit),
          z, k, st, by rw [hget]; exact hzget, hzst, by rw [he]; exact hk, hhead⟩
      posHave := r.posHave
      againSize := r.againSize
      haveSkip := r.haveSkip }
  · intro hm
    have w := inv.writer hm
    exact {
      have0 := w.have0
      direct := w.direct
      reset := w.reset
      unalloc := w.unalloc
      bufs := fun hz =>
        ⟨hexact _ _ (fun b hp => Or.inr (Or.inr (Or.inr ⟨hz, Or.inl hp⟩))) (w.bufs hz).1,
         fun hd => hexact _ _ (fun b hp => Or.inr (Or.inr (Or.inr ⟨hz, Or.inr ⟨Or.inr hd, Or.inl hp⟩⟩)))
          ((w.bufs hz).2 hd)⟩
      input := w.input
      output := w.output
      codec := fun hd hz => by
        obtain ⟨reach, z, k, d, hzget, hzst, hk, hhead⟩ := w.codec hd hz
        have hown_k : StreamOwned h (gzStrm i) k := ⟨z, hzget, Or.inr ⟨k, d, hzst, hk, Or.inl rfl⟩⟩
        have he := (inv.kept fr (inv.streamOwned_owned hown_k)).2.2.2.2.1
        exact ⟨StreamReachable.rebuffer reach hreb (fun e => nomatch e),
          z, k, d, by rw [hget]; exact hzget, hzst, by rw [he]; exact hk, hhead⟩
      transparent := w.transparent }

/-- `GzInv` survives a change that keeps every block the handle owns and the shape of the heap. -/
theorem GzInv.frame_shape (inv : GzInv h i s) (fr : Frame h after (fun b => ¬ GzOwned h i s b))
    (sh : Zlib.Gzlib.Spec.Shape h after) (fresh : Fresh after) (uniq : Zlib.Gzlib.Spec.Uniq after)
    (globals : LibraryGlobals after) (fit : ZlibF.PlatformMemory.ByteObjectsFit after) :
    GzInv after i s ∧ (∀ b, after.live b ↔ h.live b) ∧ (∀ b, GzOwned after i s b ↔ GzOwned h i s b) :=
  let r := inv.frame_core fr fresh uniq globals fit
  ⟨r.1, live_of_shape sh, r.2⟩

/-- Interface: an edit of the caller's memory (anything the handle does not own) keeps the invariant. Uses
`StreamReachable.rebuffer` for the codec (the record is not edited, so the stream fields are unchanged) and,
for `next`, the local patch for R-4 (`x.next` never points into caller memory). -/
theorem GzInv.caller (inv : GzInv h i s)
    (hf : GzCallerFrame h after i s) (fit : ZlibF.PlatformMemory.ByteObjectsFit after) : GzInv after i s :=
  (inv.frame_core hf.2.2.2 hf.1 hf.2.1 hf.2.2.1 fit).1

end frame

/-- One store into a byte view whose root is not in `P` is a frame over the blocks outside `P`. -/
theorem byte_put_frame {h : Heap} {r : BRef} {off : Nat} {a arr : Array UInt8} {P : Nat → Prop}
    (hg : Space.get h r = some a) (hro : Space.ro h r = false) (hnot : ∀ b, ByteRoot (.ref r off) b → ¬ P b) :
    Frame h (Space.put h r arr) (fun b => ¬ P b) := by
  cases r with
  | blk c =>
    refine ⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _, ?_⟩
    intro b _ hb
    have hbc : b ≠ c := by
      rintro rfl
      exact hb (hnot b rfl)
    exact ⟨by show upd h.bytes c (some arr) b = h.bytes b; exact upd_ne _ _ _ _ hbc,
      rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | str j => simp [Space.ro] at hro
  | dstate_depth k =>
    cases hd : h.dstates k with
    | none => simp [Space.get, hd] at hg
    | some d =>
      have e : Space.put h (BRef.dstate_depth k) arr =
          { h with dstates := upd h.dstates k (some { d with depth := arr }) } := by
        simp [Space.put, hd]
      rw [e]
      refine ⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _, ?_⟩
      intro b _ hb
      have hbk : b ≠ k := by
        rintro rfl
        exact hb (hnot b rfl)
      exact ⟨rfl, rfl, rfl, rfl, by show upd h.dstates k _ b = h.dstates b; exact upd_ne _ _ _ _ hbk,
        rfl, rfl, rfl⟩
  | st_dist_code => simp [Space.ro] at hro
  | st_length_code => simp [Space.ro] at hro

/-- **One store into a byte view the handle does not own keeps `GzInv`.** -/
theorem GzInv.byte_put {h : Heap} {i : Nat} {s : GzState} (inv : GzInv h i s) {r : BRef} {off : Nat}
    {a arr : Array UInt8} (hg : Space.get h r = some a) (hro : Space.ro h r = false) (hsz : arr.size = a.size)
    (hnot : ∀ b, ByteRoot (.ref r off) b → ¬ GzOwned h i s b) :
    GzInv (Space.put h r arr) i s ∧ (∀ b, (Space.put h r arr).live b ↔ h.live b) ∧
    (∀ b, GzOwned (Space.put h r arr) i s b ↔ GzOwned h i s b) := by
  have sh : Zlib.Gzlib.Spec.Shape h (Space.put h r arr) := Zlib.Inflate.Proofs.byte_view_put_shape hg hro arr
  have hnext : (Space.put h r arr).nextBlk = h.nextBlk := Zlib.Inflate.Proofs.byte_view_put_nextBlk h r arr
  have hstatic : (Space.put h r arr).static = h.static := by
    cases r <;> simp only [Space.put]
    split <;> rfl
  refine inv.frame_shape (byte_put_frame hg hro hnot) sh ?_ (uniq_of_shape sh inv.common.uniq) ?_ ?_
  · intro b hb hl
    exact inv.common.fresh b (by rw [← hnext]; exact hb) ((live_of_shape sh b).1 hl)
  · show (Space.put h r arr).static = _
    rw [hstatic]
    exact inv.common.globals
  · apply ZlibF.PlatformMemory.ByteObjectsFit.of_sizes_le inv.common.fit
    intro r' a' e'
    by_cases hr : r' = r
    · subst hr
      rw [Zlib.Inflate.Proofs.byte_view_get_put hg hro arr] at e'
      cases e'
      exact ⟨a, hg, by rw [hsz]; exact Nat.le_refl _⟩
    · rw [Zlib.Inflate.Proofs.byte_view_get_put_ne h hr arr] at e'
      exact ⟨a', e', Nat.le_refl _⟩

end ZlibF.Spec.Public

namespace ZlibF.Spec.Public.GzSkeleton
open C Zlib.GzFs Zlib.Gzguts ZlibF.Spec.Public
set_option autoImplicit false

/-- The post-condition of a call that keeps the record, the world, the live blocks and the owned blocks. -/
theorem post_of_same {h after : Heap} {i : Nat} {s : GzState} {fs : Fs} {call : Call} (inv : GzInv h i s)
    (hfs : FileSystem fs) (inv' : GzInv after i s) (hlive : ∀ b, after.live b ↔ h.live b)
    (hown : ∀ b, GzOwned after i s b ↔ GzOwned h i s b)
    (bf : BufferFrame h after (GzOwned h i s) (GzWriteRegions call)) :
    FdsKept fs fs ∧ GzStepPost h i s call fs after := by
  refine ⟨fun _ => Iff.rfl, hfs, s, inv', rfl, rfl, bf, ?_⟩
  unfold LiveChange
  intro b
  dsimp only
  rw [hlive b, hown b]
  constructor
  · intro hl
    exact Or.inl ⟨hl, fun hn => hn.2 hn.1⟩
  · rintro (⟨hl, _⟩ | ⟨ho, hn⟩)
    · exact hl
    · exact absurd (inv.common.live b ho) hn

/-- A call with one result, whose post-condition holds, is safe. -/
theorem safe_of_run {i : Nat} {call : Call} {h after : Heap} {fs : Fs} {s : GzState} {v : call.Result}
    (e : call.execute fs h = .ok ((v, fs), after)) (post : FdsKept fs fs ∧ GzStepPost h i s call fs after) :
    (∀ err, call.execute fs h = .error err → err = .outOfFuel) ∧
    ((NeedsReadBound call → ReadsFinite fs s.fd) →
      ∃ value fs' after, call.execute fs h = .ok ((value, fs'), after)) ∧
    (∀ value fs' after', call.execute fs h = .ok ((value, fs'), after') →
      FdsKept fs fs' ∧ GzStepPost h i s call fs' after') := by
  refine ⟨?_, fun _ => ⟨v, fs, after, e⟩, ?_⟩
  · intro err he
    rw [e] at he
    cases he
  · intro value fs' after' he
    rw [e] at he
    cases he
    exact post

/-- `gzerror`, from the registered `gzerror` goal: stores the code in `[errnum, errnum + 4)`. -/
theorem gzerror_step (i : Nat) (errnum : BPtr) : GzCallSafe i (.gzerror (some (.in_gzstate_x i)) errnum) := by
  intro h fs s inv hfs ha
  have hs := inv.common.record
  have hm := inv.common.mode
  have split := ZlibF.Spec.Public.GzErrorProof.gzerror_split hs hm errnum
  rcases ha with hn | hrange
  · subst hn
    obtain ⟨q, hq, _⟩ := ZlibF.Spec.Public.GzErrorProof.errorMessage_run h s
    have r : Zlib.Gzlib.gzerror (some (.in_gzstate_x i)) .null h = .ok (q, h) := by
      change Zlib.Gzlib.gzerror (Zlib.Gzlib.Spec.hnd i) .null h = .ok (q, h)
      rw [split]
      simpa using hq
    have e : Call.execute (.gzerror (some (.in_gzstate_x i)) .null) fs h = .ok ((q, fs), h) := by
      show heapCall _ fs h = _
      simp only [heapCall, r]
    refine safe_of_run e (post_of_same inv hfs inv (fun _ => Iff.rfl) (fun _ => Iff.rfl) ?_)
    refine ⟨?_, ?_⟩
    · show Frame h h _
      exact ⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _, fun _ _ _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
    · intro region hmem r off a hp _
      have hreg : region = ⟨.null, 4⟩ := by simpa [GzWriteRegions] using hmem
      subst hreg
      cases hp
  · rcases hrange with h0 | ⟨_, hw, hnot⟩
    · exact absurd h0 (by decide)
    rcases hw rfl with ⟨_, h0⟩ | ⟨r, off, a, rfl, hg, hro, hfit⟩
    · exact absurd h0 (by decide)
    let arr : Array UInt8 := a.extract 0 off ++ #[s.err.toUInt32.toUInt8, (s.err.toUInt32 >>> 8).toUInt8,
      (s.err.toUInt32 >>> 16).toUInt8, (s.err.toUInt32 >>> 24).toUInt8] ++ a.extract (off + 4) a.size
    have hstore : store32 (.ref r off) s.err h = .ok ((), Space.put h r arr) :=
      ZlibF.Spec.Public.GzErrorProof.store32_slice_run hg hro hfit s.err
    obtain ⟨q, hq, _⟩ := ZlibF.Spec.Public.GzErrorProof.errorMessage_run (Space.put h r arr) s
    have run : Zlib.Gzlib.gzerror (some (.in_gzstate_x i)) (.ref r off) h = .ok (q, Space.put h r arr) := by
      change Zlib.Gzlib.gzerror (Zlib.Gzlib.Spec.hnd i) (.ref r off) h = _
      rw [split]
      simp [bind_app, hstore, hq]
    have e : Call.execute (.gzerror (some (.in_gzstate_x i)) (.ref r off)) fs h =
        .ok ((q, fs), Space.put h r arr) := by
      show heapCall _ fs h = _
      simp only [heapCall, run]
    have hmin : min off a.size = off := Nat.min_eq_left (by omega)
    have hsz : arr.size = a.size := by
      simp [arr, hmin] <;> omega
    obtain ⟨inv', hlive, hown⟩ := inv.byte_put hg hro hsz hnot
    refine safe_of_run e (post_of_same inv hfs inv' hlive hown ?_)
    refine ⟨?_, ?_⟩
    · have hrest : restoreRegions h (Space.put h r arr) (GzWriteRegions (.gzerror (some (.in_gzstate_x i)) (.ref r off)))
          = h := by
        simp only [GzWriteRegions, restoreRegions, List.foldl_cons, List.foldl_nil, hg]
        rw [Zlib.Inflate.Proofs.byte_view_put_put hg hro, Zlib.Inflate.Proofs.byte_view_put_self hg hro]
      rw [hrest]
      exact ⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _, fun _ _ _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
    · intro region hmem r' off' a' hp hg'
      have hreg : region = ⟨.ref r off, 4⟩ := by simpa [GzWriteRegions] using hmem
      subst hreg
      cases hp
      rw [hg] at hg'
      cases hg'
      refine ⟨arr, Zlib.Inflate.Proofs.byte_view_get_put hg hro arr, hsz, ?_⟩
      intro j _ hout
      have hj : j < off ∨ off + 4 ≤ j := by
        by_cases h1 : off ≤ j
        · by_cases h2 : j < off + 4
          · exact absurd ⟨⟨.ref r off, 4⟩, List.mem_singleton_self _, off, rfl, h1, h2⟩ hout
          · exact Or.inr (by omega)
        · exact Or.inl (by omega)
      have h0 : off ≠ j := by omega
      have h1 : off + 1 ≠ j := by omega
      have h2 : off + 2 ≠ j := by omega
      have h3 : off + 3 ≠ j := by omega
      show arr[j]? = a[j]?
      simp only [arr]
      rw [← ZlibF.Spec.Public.GzErrorProof.set_four_slice a off hfit]
      simp [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, h0, h1, h2, h3]

end ZlibF.Spec.Public.GzSkeleton
