import ZlibF.Proof.«gzfs.read-contract»
import ZlibF.Proof.«gz.inv-frame»
import ZlibF.Proof.«gz.inv-put-scalars»
import ZlibF.Proof.«gz.inv-clearerr»
import ZlibF.Zlib.«gzread.c»
import ZlibF.Proof.«deflate.c.engine.macros»

/-!
# gz read side: one `storeBytes` into a writable byte view

`storeBytes p bs` (the model of copying the bytes a `read` returned into `p`) allocates a temporary block, copies
it to `p` and frees it. Into a writable byte view (a byte block or a `deflate_state` `depth` array) with room it
returns, and its heap is the view's array updated (`copyRange`), with the temporary's number used up
(`nextBlk + 1`) and nothing else changed.
-/

namespace ZlibF.Spec.Public.GzRead
open C Zlib.GzFs Zlib.Gzguts Zlib.Gzlib.Spec Zlib.Gzlib.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- What `storeBytes` into view `r` with new array `x` leaves: the view holds `x`, every other byte view and every
other table is unchanged, the temporary's number is used up (`nextBlk + 1`, its read-only flag cleared, still not
live), and no block appears or disappears. -/
structure Stored (h H : Heap) (r : BRef) (x : Array UInt8) : Prop where
  view : Space.get H r = some x
  bytes : ∀ b, r ≠ .blk b → H.bytes b = h.bytes b
  dstates : ∀ k, r ≠ .dstate_depth k → H.dstates k = h.dstates k
  depthRec : ∀ k, r = .dstate_depth k → H.dstates k = (h.dstates k).map (fun st => { st with depth := x })
  shape : Shape h H
  words : H.words = h.words
  streams : H.streams = h.streams
  gzheaders : H.gzheaders = h.gzheaders
  istates : H.istates = h.istates
  gzstates : H.gzstates = h.gzstates
  ro : ∀ b, b ≠ h.nextBlk → H.ro b = h.ro b
  static : H.static = h.static
  nextBlk : H.nextBlk = h.nextBlk + 1
  nalloc : H.nalloc = h.nalloc
  allocOk : H.allocOk = h.allocOk
  garbage : H.garbage = h.garbage
  borrow : H.libcErrorBorrow = h.libcErrorBorrow

theorem storeBytes_view (h : Heap) (r : BRef) (off : Nat) (a bs : Array UInt8)
    (hg : Space.get h r = some a) (hro : Space.ro h r = false) (hfit : off + bs.size ≤ a.size)
    (hslot : h.slotUsed h.nextBlk = false) (hne : bs.isEmpty = false) :
    ∃ H, storeBytes (.ref r off) bs h = .ok ((), H) ∧ Stored h H r (copyRange a bs off 0 bs.size) := by
  have hfree : ¬ h.live h.nextBlk := Heap.slotUsed_eq_false.mp hslot
  have hbn : h.bytes h.nextBlk = none := by
    cases e : h.bytes h.nextBlk with
    | none => rfl
    | some _ => exact absurd (Or.inl (by rw [e]; simp)) hfree
  let n := h.nextBlk
  let T : Heap := { h with bytes := upd h.bytes n (some bs), ro := upd h.ro n false, nextBlk := n + 1 }
  have ha : allocBytes bs h = .ok (.ref (.blk n) 0, T) := by
    simp [allocBytes, hslot, T, n]
  have hrn : r ≠ .blk n := by
    rintro rfl
    have hb : h.bytes h.nextBlk = some a := hg
    rw [hbn] at hb; cases hb
  have hgT : Space.get T r = some a := by
    cases r with
    | blk b =>
      have hb : b ≠ n := fun e => hrn (by rw [e])
      simpa [Space.get, T, upd_ne _ _ _ _ hb] using hg
    | dstate_depth k => simpa [Space.get, T] using hg
    | _ => simp [Space.ro] at hro
  have hsT : Space.get T (BRef.blk n) = some bs := by simp [Space.get, T]
  have hroT : Space.ro T r = false := by
    cases r with
    | blk b =>
      have hb : b ≠ n := fun e => hrn (by rw [e])
      simpa [Space.ro, T, upd_ne _ _ _ _ hb] using hro
    | dstate_depth k => rfl
    | _ => simp [Space.ro] at hro
  have hc := Ptr.memcpy_ok (rd := r) (rs := BRef.blk n) (od := off) (os := 0) (n := bs.size) hgT hsT hroT hfit
    (by omega) (Or.inl hrn)
  unfold storeBytes
  simp only [hne, Bool.false_eq_true, ite_false, bind_app]
  rw [ha]
  dsimp only
  simp only [memcpyB, hc]
  cases r with
  | blk b =>
    have hb : b ≠ n := fun e => hrn (by rw [e])
    refine ⟨_, by simp [freeB, Space.put, T, upd_ne _ _ _ _ (Ne.symm hb)]; rfl, ?_⟩
    refine ⟨?_, ?_, fun _ _ => rfl, (fun _ e => by cases e), ?_, rfl, rfl, rfl, rfl, rfl, ?_, rfl, rfl, rfl, rfl, rfl,
      rfl⟩
    · show (upd (upd (upd h.bytes n (some bs)) b _) n none) b = _
      rw [upd_ne _ _ _ _ hb, upd_same]
    · intro c hc'
      have hcb : c ≠ b := fun e => hc' (by rw [e])
      show (upd (upd (upd h.bytes n (some bs)) b _) n none) c = _
      rw [upd_apply, upd_ne _ _ _ _ hcb, upd_apply]
      split
      · rename_i e; rw [e, hbn]
      · rfl
    · intro c
      have hu : ((upd (upd (upd h.bytes n (some bs)) b (some (copyRange a bs off 0 bs.size))) n none) c).isSome =
          (h.bytes c).isSome := by
        rw [upd_apply, upd_apply, upd_apply]
        by_cases e1 : c = n
        · simp [e1]; exact hbn
        · by_cases e2 : c = b
          · subst e2; simp [e1]; have : h.bytes c = some a := hg; simp [this]
          · simp [e1, e2]
      exact ⟨hu, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · intro c hcn
      show (upd h.ro n false) c = h.ro c
      exact upd_ne _ _ _ _ hcn
  | dstate_depth k =>
    have hg' : (h.dstates k).map (·.depth) = some a := hg
    cases hst : h.dstates k with
    | none => rw [hst] at hg'; cases hg'
    | some st =>
      refine ⟨_, by simp [freeB, Space.put, T, hst]; rfl, ?_⟩
      refine ⟨?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
      · show ((upd h.dstates k _) k).map (·.depth) = _
        rw [upd_same]; rfl
      · intro c _
        show (upd (upd h.bytes n (some bs)) n none) c = _
        rw [upd_upd, upd_apply]
        split
        · rename_i e; rw [e, hbn]
        · rfl
      · intro c hc'
        have hck : c ≠ k := fun e => hc' (by rw [e])
        exact upd_ne _ _ _ _ hck
      · intro c e
        cases e
        show (upd h.dstates k _) k = _
        rw [upd_same, hst]; rfl
      · intro c
        have hu : ((upd (upd h.bytes n (some bs)) n none) c).isSome = (h.bytes c).isSome := by
          rw [upd_upd, upd_apply]
          by_cases e1 : c = n
          · simp [e1]; exact hbn
          · simp [e1]
        have hd : ((upd h.dstates k (some { st with depth := copyRange a bs off 0 bs.size })) c).isSome =
            (h.dstates c).isSome := by
          rw [upd_apply]
          by_cases e2 : c = k
          · subst e2; simp [hst]
          · simp [e2]
        exact ⟨hu, rfl, rfl, rfl, hd, rfl, rfl⟩
      · intro c hcn
        show (upd h.ro n false) c = h.ro c
        exact upd_ne _ _ _ _ hcn
  | _ => simp [Space.ro] at hro

/-! ## Data buffers: their bytes are not part of the invariant -/

/-- `b` is the block of a data buffer of the handle (`in`, or `out` when the handle owns one). -/
def DataBuf (s : GzState) (b : Nat) : Prop :=
  s.size ≠ 0 ∧ (s.«in» = .ref (.blk b) 0 ∨ ((s.mode = GZ_READ ∨ s.direct = 0) ∧ s.out = .ref (.blk b) 0))

section data
variable {h after : Heap} {i : Nat} {s : GzState}

theorem DataBuf.owned {b : Nat} (hb : DataBuf s b) : GzOwned h i s b := by
  obtain ⟨hz, hin | ⟨hm, hout⟩⟩ := hb
  · exact Or.inr (Or.inr (Or.inr ⟨hz, Or.inl hin⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hz, Or.inr ⟨hm, Or.inl hout⟩⟩))

/-- A data buffer is not the record, the path, the message or a block of the codec. -/
theorem GzInv.data_separate (inv : GzInv h i s) {b : Nat} (hb : DataBuf s b) :
    b ≠ i ∧ ¬ StreamOwned h (gzStrm i) b ∧ s.path ≠ .ref (.blk b) 0 ∧ s.msg ≠ .ref (.blk b) 0 := by
  have c := inv.common
  obtain ⟨hz, hio⟩ := hb
  have hp : ∃ p, p ∈ ownedPtrs s ∧ p = .ref (.blk b) 0 := by
    rcases hio with hin | ⟨hm, hout⟩
    · exact ⟨s.«in», by simp [ownedPtrs, hz], hin⟩
    · exact ⟨s.out, by simp [ownedPtrs, hz, hm], hout⟩
  obtain ⟨p, hpm, hpe⟩ := hp
  obtain ⟨hi, hso⟩ := c.distinct.2 p hpm b (by rw [hpe]; rfl)
  refine ⟨hi, hso, ?_, ?_⟩
  · intro e
    have nd := c.distinct.1
    simp only [ownedPtrs, if_pos hz, List.cons_append, List.nil_append] at nd
    rcases hio with hin | ⟨hm, hout⟩
    · exact absurd (nd.sublist (List.Sublist.filterMap blkOf
        (List.Sublist.cons₂ _ (List.Sublist.cons _ (List.Sublist.cons₂ _ (List.nil_sublist _))))))
        (by simp [e, hin, blkOf])
    · rw [if_pos hm] at nd
      exact absurd (nd.sublist (List.Sublist.filterMap blkOf
        (List.Sublist.cons₂ _ (List.Sublist.cons _ (List.Sublist.cons _ (List.Sublist.cons₂ _
          (List.nil_sublist _)))))))
        (by simp [e, hout, blkOf])
  · intro e
    obtain ⟨-, -, -, hsep⟩ := inv.msg_separate (mb := b) (by rw [e]; rfl)
    rcases hio with hin | ⟨hm, hout⟩
    · exact (hsep hz).1 hin
    · exact (hsep hz).2 hm hout

/-- **`GzInv` survives a change of the bytes of the data buffers (`in`, `out`) that keeps their sizes, and of
nothing else the handle owns.** The bytes of the data buffers are not part of the invariant. -/
theorem GzInv.frame_data (inv : GzInv h i s) (fr : Frame h after (fun b => ¬ GzOwned h i s b ∨ DataBuf s b))
    (hdata : ∀ b, DataBuf s b → (∃ a a', h.bytes b = some a ∧ after.bytes b = some a' ∧ a'.size = a.size) ∧
      after.ro b = h.ro b ∧ after.words b = h.words b ∧ after.streams b = h.streams b ∧
      after.gzheaders b = h.gzheaders b ∧ after.dstates b = h.dstates b ∧ after.istates b = h.istates b ∧
      after.gzstates b = h.gzstates b)
    (fresh : Fresh after) (uniq : Zlib.Gzlib.Spec.Uniq after)
    (globals : LibraryGlobals after) (fit : ZlibF.PlatformMemory.ByteObjectsFit after) :
    GzInv after i s ∧ (∀ b, GzOwned after i s b ↔ GzOwned h i s b) := by
  have c := inv.common
  have kept : ∀ b, GzOwned h i s b → ¬ DataBuf s b →
      after.bytes b = h.bytes b ∧ after.words b = h.words b ∧ after.streams b = h.streams b ∧
      after.gzheaders b = h.gzheaders b ∧ after.dstates b = h.dstates b ∧ after.istates b = h.istates b ∧
      after.gzstates b = h.gzstates b ∧ after.ro b = h.ro b :=
    fun b ho hd => fr.2.2.2.2.2 b (c.live b ho) (fun hn => hn.elim (fun x => x ho) hd)
  have notData_i : ¬ DataBuf s i := fun hd => (GzInv.data_separate inv hd).1 rfl
  have notData_codec : ∀ b, StreamOwned h (gzStrm i) b → ¬ DataBuf s b :=
    fun b hb hd => (GzInv.data_separate inv hd).2.1 hb
  have hs' : after.gzstates i = some s := by rw [(kept i (Or.inl rfl) notData_i).2.2.2.2.2.2.1]; exact c.record
  have hget : ZStreamRef.get after (gzStrm i) = ZStreamRef.get h (gzStrm i) := by
    show (after.gzstates i).map (·.strm) = (h.gzstates i).map (·.strm)
    rw [(kept i (Or.inl rfl) notData_i).2.2.2.2.2.2.1]
  have keptC : ∀ b, StreamOwned h (gzStrm i) b → _ := fun b hb =>
    kept b (inv.streamOwned_owned hb) (notData_codec b hb)
  have hso : ∀ b, StreamOwned after (gzStrm i) b ↔ StreamOwned h (gzStrm i) b := by
    intro b
    constructor
    · rintro ⟨z, hz, ⟨k, st, hk, hst, ho⟩ | ⟨k, d, hk, hd, ho⟩⟩
      · rw [hget] at hz
        have hzs : s.strm = z := by simpa [ZStreamRef.get, gzStrm, c.record] using hz
        obtain ⟨st0, hst0⟩ := inv.inflate_live (by rw [hzs]; exact hk)
        have hown : StreamOwned h (gzStrm i) k := ⟨z, hz, Or.inl ⟨k, st0, hk, hst0, Or.inl rfl⟩⟩
        have he := (keptC k hown).2.2.2.2.2.1
        rw [he, hst0] at hst
        cases hst
        exact ⟨z, hz, Or.inl ⟨k, _, hk, hst0, ho⟩⟩
      · rw [hget] at hz
        have hzs : s.strm = z := by simpa [ZStreamRef.get, gzStrm, c.record] using hz
        obtain ⟨d0, hd0⟩ := inv.deflate_live (by rw [hzs]; exact hk)
        have hown : StreamOwned h (gzStrm i) k := ⟨z, hz, Or.inr ⟨k, d0, hk, hd0, Or.inl rfl⟩⟩
        have he := (keptC k hown).2.2.2.2.1
        rw [he, hd0] at hd
        cases hd
        exact ⟨z, hz, Or.inr ⟨k, _, hk, hd0, ho⟩⟩
    · rintro ⟨z, hz, ⟨k, st, hk, hst, ho⟩ | ⟨k, d, hk, hd, ho⟩⟩
      · have hown : StreamOwned h (gzStrm i) k := ⟨z, hz, Or.inl ⟨k, st, hk, hst, Or.inl rfl⟩⟩
        have he := (keptC k hown).2.2.2.2.2.1
        exact ⟨z, by rw [hget]; exact hz, Or.inl ⟨k, st, hk, by rw [he]; exact hst, ho⟩⟩
      · have hown : StreamOwned h (gzStrm i) k := ⟨z, hz, Or.inr ⟨k, d, hk, hd, Or.inl rfl⟩⟩
        have he := (keptC k hown).2.2.2.2.1
        exact ⟨z, by rw [hget]; exact hz, Or.inr ⟨k, d, hk, by rw [he]; exact hd, ho⟩⟩
  have hown : ∀ b, GzOwned after i s b ↔ GzOwned h i s b := by
    intro b; unfold GzOwned; rw [show StreamOwned after (.in_gzstate_strm i) b ↔ StreamOwned h (.in_gzstate_strm i) b
      from hso b]
  have hlive : ∀ b, GzOwned h i s b → after.live b := by
    intro b ho
    by_cases hd : DataBuf s b
    · obtain ⟨⟨a, a', -, ha', -⟩, -⟩ := hdata b hd
      exact Or.inl (by rw [ha']; simp)
    · have hl := c.live b ho
      obtain ⟨e1, e2, e3, e4, e5, e6, e7, _⟩ := kept b ho hd
      simp only [Heap.live, e1, e2, e3, e4, e5, e6, e7]
      exact hl
  have hsize : ∀ b a, GzOwned h i s b → h.bytes b = some a → ∃ a', after.bytes b = some a' ∧ a'.size = a.size := by
    intro b a ho hb
    by_cases hd : DataBuf s b
    · obtain ⟨⟨a0, a', h0, ha', hsz⟩, -⟩ := hdata b hd
      rw [h0] at hb; cases hb
      exact ⟨a', ha', hsz⟩
    · exact ⟨a, by rw [(kept b ho hd).1]; exact hb, rfl⟩
  have hro : ∀ b, GzOwned h i s b → after.ro b = h.ro b := by
    intro b ho
    by_cases hd : DataBuf s b
    · exact (hdata b hd).2.1
    · exact (kept b ho hd).2.2.2.2.2.2.2
  have hexact : ∀ p n, (∀ b, p = .ref (.blk b) 0 → GzOwned h i s b) → ExactBuffer h p n → ExactBuffer after p n := by
    intro p n own hx
    obtain ⟨b, a, hp, hb, hr, hsz⟩ := hx
    obtain ⟨a', ha', hs'⟩ := hsize b a (own b hp) hb
    exact ⟨b, a', hp, ha', by rw [hro b (own b hp)]; exact hr, by rw [hs']; exact hsz⟩
  have hstr : ∀ (p : BPtr) b, p = .ref (.blk b) 0 → GzOwned h i s b → ¬ DataBuf s b → after.bytes b = h.bytes b :=
    fun p b _ ho hd => (kept b ho hd).1
  have hmalloc : ∀ p n, (∀ b, p = .ref (.blk b) 0 → GzOwned h i s b) → MallocBuffer h p n →
      MallocBuffer after p n := by
    intro p n own hx
    obtain ⟨b, a, hp, hb, hr, hsz⟩ := hx
    obtain ⟨a', ha', hs'⟩ := hsize b a (own b hp) hb
    exact ⟨b, a', hp, ha', by rw [hro b (own b hp)]; exact hr, by rw [hs']; exact hsz⟩
  have hreb : Rebuffer h after (gzStrm i) := by
    refine ⟨fresh, uniq, globals, ⟨fr.1, fr.2.1, fr.2.2.1, fr.2.2.2.1, fr.2.2.2.2.1, ?_⟩, s.strm, s.strm, ?_, ?_, rfl⟩
    · intro b hl hn
      have hb : StreamOwned h (gzStrm i) b := Classical.byContradiction hn
      exact fr.2.2.2.2.2 b hl (fun hc => hc.elim (fun x => x (inv.streamOwned_owned hb)) (notData_codec b hb))
    · simp [ZStreamRef.get, gzStrm, c.record]
    · simp [ZStreamRef.get, gzStrm, hs']
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
        exact (cstring_blk_congr (hstr _ pb hp own (fun hd => (GzInv.data_separate inv hd).2.2.1 hp))).2 hc
      msg := by
        rcases c.msg with hn | ⟨m, hc, hm⟩
        · exact Or.inl hn
        · obtain ⟨mb, a, hp, hb, hr, hn⟩ := hm
          have own : GzOwned h i s mb := Or.inr (Or.inr (Or.inl hp))
          refine Or.inr ⟨m, ?_, hmalloc _ _ (fun b e => by rw [hp] at e; cases e; exact own) ⟨mb, a, hp, hb, hr, hn⟩⟩
          rw [hp] at hc ⊢
          exact (cstring_blk_congr (hstr _ mb hp own (fun hd => (GzInv.data_separate inv hd).2.2.2 hp))).2 hc
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
        · obtain ⟨a', ha', hs'⟩ := hsize b a ho hb
          exact Or.inr ⟨b, off, a', hx, hbi, (hown b).2 ho, hmb, ha', by rw [hs']; exact hle⟩
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
        have he := (keptC k hown_k).2.2.2.2.2.1
        exact ⟨StreamReachable.rebuffer reach hreb (fun _ => fit),
          z, k, st, by rw [hget]; exact hzget, hzst, by rw [he]; exact hk, hhead⟩
      posHave := r.posHave
      againSize := r.againSize }
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
        have he := (keptC k hown_k).2.2.2.2.1
        exact ⟨StreamReachable.rebuffer reach hreb (fun e => nomatch e),
          z, k, d, by rw [hget]; exact hzget, hzst, by rw [he]; exact hk, hhead⟩
      transparent := w.transparent }


theorem Stored.get_other {r : BRef} {x : Array UInt8} (st : Stored h after r x) (r' : BRef) (hne : r' ≠ r) :
    Space.get after r' = Space.get h r' := by
  cases r' with
  | blk b => exact st.bytes b (fun e => hne e.symm)
  | dstate_depth k =>
    show (after.dstates k).map (·.depth) = (h.dstates k).map (·.depth)
    rw [st.dstates k (fun e => hne e.symm)]
  | str j =>
    show staticStringBytes after j = staticStringBytes h j
    simp only [staticStringBytes, st.borrow]
  | st_dist_code => show some after.static.dist_code = some h.static.dist_code; rw [st.static]
  | st_length_code => show some after.static.length_code = some h.static.length_code; rw [st.static]

/-- **One `storeBytes` into a data buffer of the handle, or into a byte view it does not own, keeps `GzInv`**
(the view keeps its size). -/
theorem GzInv.stored (inv : GzInv h i s) {r : BRef} {a x : Array UInt8} (st : Stored h after r x)
    (hg : Space.get h r = some a) (hsz : x.size = a.size)
    (hroot : (∃ b, r = .blk b ∧ DataBuf s b) ∨ (∀ b, ByteRoot (.ref r 0) b → ¬ GzOwned h i s b)) :
    GzInv after i s ∧ (∀ b, after.live b ↔ h.live b) ∧ (∀ b, GzOwned after i s b ↔ GzOwned h i s b) := by
  have c := inv.common
  have hlive := live_of_shape st.shape
  have hnfree : ¬ h.live h.nextBlk := fun hl => c.fresh h.nextBlk (Nat.le_refl _) hl
  have hbne : ∀ b, h.live b → b ≠ h.nextBlk := fun b hl e => hnfree (e ▸ hl)
  have fr : Frame h after (fun b => ¬ GzOwned h i s b ∨ DataBuf s b) := by
    refine ⟨st.static.symm, st.allocOk.symm, st.garbage.symm, by rw [st.nextBlk]; omega,
      by rw [st.nalloc]; exact Nat.le_refl _, fun b hl hnc => ?_⟩
    have ho : GzOwned h i s b := Classical.byContradiction (fun hn => hnc (Or.inl hn))
    have hnd : ¬ DataBuf s b := fun hd => hnc (Or.inr hd)
    refine ⟨st.bytes b ?_, by rw [st.words], by rw [st.streams], by rw [st.gzheaders], st.dstates b ?_,
      by rw [st.istates], by rw [st.gzstates], st.ro b (hbne b hl)⟩
    · rintro rfl
      rcases hroot with ⟨b', e, hd⟩ | hn
      · cases e; exact hnd hd
      · exact hn b rfl ho
    · rintro rfl
      rcases hroot with ⟨b', e, _⟩ | hn
      · cases e
      · exact hn b rfl ho
  have hdata : ∀ b, DataBuf s b → (∃ a a', h.bytes b = some a ∧ after.bytes b = some a' ∧ a'.size = a.size) ∧
      after.ro b = h.ro b ∧ after.words b = h.words b ∧ after.streams b = h.streams b ∧
      after.gzheaders b = h.gzheaders b ∧ after.dstates b = h.dstates b ∧ after.istates b = h.istates b ∧
      after.gzstates b = h.gzstates b := by
    intro b hd
    have ho : GzOwned h i s b := hd.owned
    have hl := c.live b ho
    have hbb : ∃ a0, h.bytes b = some a0 := by
      obtain ⟨hz, hin | ⟨hm, hout⟩⟩ := hd
      · rcases c.mode with hm | hm
        · obtain ⟨⟨b1, a1, e1, h1, -⟩, -⟩ := (inv.reader hm).bufs hz
          rw [hin] at e1; cases e1; exact ⟨a1, h1⟩
        · obtain ⟨⟨b1, a1, e1, h1, -⟩, -⟩ := (inv.writer hm).bufs hz
          rw [hin] at e1; cases e1; exact ⟨a1, h1⟩
      · rcases c.mode with hm' | hm'
        · obtain ⟨-, ⟨b1, a1, e1, h1, -⟩⟩ := (inv.reader hm').bufs hz
          rw [hout] at e1; cases e1; exact ⟨a1, h1⟩
        · have hd0 : s.direct = 0 := by
            rcases hm with hm | hm
            · rw [hm'] at hm; exact absurd hm (by decide)
            · exact hm
          obtain ⟨-, hw⟩ := (inv.writer hm').bufs hz
          obtain ⟨b1, a1, e1, h1, -⟩ := hw hd0
          rw [hout] at e1; cases e1; exact ⟨a1, h1⟩
    obtain ⟨a0, ha0⟩ := hbb
    refine ⟨?_, st.ro b (hbne b hl), by rw [st.words], by rw [st.streams], by rw [st.gzheaders], ?_,
      by rw [st.istates], by rw [st.gzstates]⟩
    · by_cases e : r = .blk b
      · subst e
        have ha : a = a0 := by
          have : h.bytes b = some a := hg
          rw [ha0] at this; cases this; rfl
        subst ha
        exact ⟨a, x, ha0, st.view, hsz⟩
      · exact ⟨a0, a0, ha0, by rw [st.bytes b (fun e' => e e')]; exact ha0, rfl⟩
    · apply st.dstates b
      rintro rfl
      rcases hroot with ⟨b', e, _⟩ | hn
      · cases e
      · exact hn b rfl ho
  have fresh : Fresh after := by
    intro b hb hl
    rw [st.nextBlk] at hb
    exact c.fresh b (by omega) ((hlive b).1 hl)
  have uniq := uniq_of_shape st.shape c.uniq
  have globals : LibraryGlobals after := by
    unfold LibraryGlobals; rw [st.static]; exact c.globals
  have fit : ZlibF.PlatformMemory.ByteObjectsFit after := by
    apply ZlibF.PlatformMemory.ByteObjectsFit.of_sizes_le c.fit
    intro r' a' e'
    by_cases e : r' = r
    · subst e
      rw [st.view] at e'; cases e'
      exact ⟨a, hg, by rw [hsz]; exact Nat.le_refl _⟩
    · rw [st.get_other r' e] at e'
      exact ⟨a', e', Nat.le_refl _⟩
  obtain ⟨inv', hown⟩ := GzInv.frame_data inv fr hdata fresh uniq globals fit
  exact ⟨inv', hlive, hown⟩

end data

/-! ## A `do … while` loop over the gz world, with an invariant and a measure -/

theorem g_bind_app {α β : Type} (m : G α) (f : α → G β) (fs : Fs) (h : Heap) :
    (m >>= f) fs h = match m fs h with
      | .ok ((a, fs1), h1) => f a fs1 h1 | .error e => .error e := by
  simp only [bind, StateT.bind]
  cases he : m fs h with
  | error e => rfl
  | ok result => obtain ⟨⟨a, fs1⟩, h1⟩ := result; rfl

/-- A `gdoWhile` loop whose body keeps an invariant and whose measure drops on each continuing trip returns,
within any fuel above the measure, a state satisfying the exit condition. -/
theorem gdoWhile_go_spec {σ : Type} (body : σ → G σ) (cond : σ → G (Bool × σ))
    (J Post : σ → Fs → Heap → Prop) (μ : σ → Nat)
    (step : ∀ x fs h, J x fs h → ∃ y fs1 h1, body x fs h = .ok ((y, fs1), h1) ∧
      ∃ c z fs2 h2, cond y fs1 h1 = .ok (((c, z), fs2), h2) ∧
        (c = true → J z fs2 h2 ∧ μ z < μ x) ∧ (c = false → Post z fs2 h2)) :
    ∀ n x fs h, J x fs h → μ x < n →
      ∃ z fs' h', Zlib.GzFs.gdoWhile.go body cond n x fs h = .ok ((z, fs'), h') ∧ Post z fs' h' := by
  intro n
  induction n with
  | zero => intro x fs h _ hm; omega
  | succ n ih =>
    intro x fs h hJ hm
    obtain ⟨y, fs1, h1, hb, c, z, fs2, h2, hc, hcont, hstop⟩ := step x fs h hJ
    rw [Zlib.GzFs.gdoWhile.go, g_bind_app, hb]
    dsimp only
    rw [g_bind_app, hc]
    dsimp only
    cases c with
    | true =>
      obtain ⟨hJ', hlt⟩ := hcont rfl
      simp only [ite_true]
      exact ih z fs2 h2 hJ' (by omega)
    | false =>
      simp only [Bool.false_eq_true, ite_false]
      exact ⟨z, fs2, h2, rfl, hstop rfl⟩

/-! ## `gz_load`: the source split -/

/-- The body of `gz_load`'s loop (source order). -/
def loadBody (i : Nat) (buf : BPtr) (len : UInt32) (l : Zlib.Gzread.LoadLoop) : G Zlib.Gzread.LoadLoop := do
  let max : UInt32 := (((0 : UInt32) - 1) >>> 2) + 1
  let mut get := len - l.«have»
  if get > max then get := max
  let s ← ldS (some (.tab i))
  let p ← buf.add l.«have».toNat
  let (r, bs) ← fsRead s.fd get.toUInt64
  storeBytes p bs
  let ret := r.toInt32
  if ret ≤ 0 then return { l with ret, brk := true }
  return { l with ret, «have» := l.«have» + ret.toUInt32 }

/-- The condition of `gz_load`'s loop. -/
def loadCond (len : UInt32) (l : Zlib.Gzread.LoadLoop) : G (Bool × Zlib.Gzread.LoadLoop) :=
  pure (!l.brk && l.«have» < len, l)

/-- What `gz_load` does after its loop. -/
def loadTail (i : Nat) (l : Zlib.Gzread.LoadLoop) : G (Int32 × UInt32) := do
  if l.ret < 0 then
    let e ← getErrno
    if BLOCKED e then
      updS (some (.tab i)) fun s => { s with again := 1 }
      if l.«have» != 0 then return (0, l.«have»)
    Zlib.Gzlib.gz_error (some (.tab i)) Z_ERRNO (← zstrerror)
    return (-1, l.«have»)
  if l.ret == 0 then updS (some (.tab i)) fun s => { s with eof := 1 }
  return (0, l.«have»)

theorem gz_load_source (i : Nat) (buf : BPtr) (len : UInt32) :
    Zlib.Gzread.gz_load (gzSt i) buf len = (do
      updS (some (.tab i)) fun s => { s with again := 0 }
      setErrno 0
      let l ← gdoWhile (loadBody i buf len) (loadCond len) { «have» := 0, ret := 0, brk := false }
      loadTail i l) := rfl

/-! ## The heap of `gz_load`'s loop: only the buffer's view changes -/

/-- `hk` differs from `h1` only in the array of the view `r` (same size, the same bytes outside
`[off, off + len)`, for a `depth` view the rest of the state record unchanged) and in used-up block numbers of
temporaries. -/
structure LoadHeap (h1 hk : Heap) (r : BRef) (off len : Nat) : Prop where
  gzstates : hk.gzstates = h1.gzstates
  words : hk.words = h1.words
  streams : hk.streams = h1.streams
  gzheaders : hk.gzheaders = h1.gzheaders
  istates : hk.istates = h1.istates
  static : hk.static = h1.static
  allocOk : hk.allocOk = h1.allocOk
  garbage : hk.garbage = h1.garbage
  nalloc : hk.nalloc = h1.nalloc
  borrow : hk.libcErrorBorrow = h1.libcErrorBorrow
  nextBlk : h1.nextBlk ≤ hk.nextBlk
  shape : Shape h1 hk
  ro : ∀ b, h1.live b → hk.ro b = h1.ro b
  bytes : ∀ b, r ≠ .blk b → hk.bytes b = h1.bytes b
  dstates : ∀ k, r ≠ .dstate_depth k → hk.dstates k = h1.dstates k
  depth : ∀ k st, r = .dstate_depth k → h1.dstates k = some st →
    ∃ d, hk.dstates k = some { st with depth := d }
  view : ∀ a, Space.get h1 r = some a → ∃ a', Space.get hk r = some a' ∧ a'.size = a.size ∧
    ∀ j, j < a.size → ¬ (off ≤ j ∧ j < off + len) → a'[j]? = a[j]?

theorem LoadHeap.refl (h1 : Heap) (r : BRef) (off len : Nat) : LoadHeap h1 h1 r off len := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, Nat.le_refl _, ?_, fun _ _ => rfl, fun _ _ => rfl,
    fun _ _ => rfl, fun k st _ hst => ⟨st.depth, by rw [hst]⟩, fun a ha => ⟨a, ha, rfl, fun _ _ _ => rfl⟩⟩
  intro b; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem Shape.trans' {a b c : Heap} (one : Shape a b) (two : Shape b c) : Shape a c := by
  intro x
  obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := one x
  obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := two x
  exact ⟨f1.trans e1, f2.trans e2, f3.trans e3, f4.trans e4, f5.trans e5, f6.trans e6, f7.trans e7⟩

/-- A store into the view `r` at `[off + k, off + k + m)` inside the region extends the loop's heap relation. -/
theorem LoadHeap.store {h1 hk H : Heap} {r : BRef} {off len k : Nat} {ak x bs : Array UInt8}
    (lh : LoadHeap h1 hk r off len) (st : Stored hk H r x) (hg : Space.get hk r = some ak)
    (hx : x = copyRange ak bs (off + k) 0 bs.size) (hfit : off + k + bs.size ≤ off + len)
    (hroom : off + k + bs.size ≤ ak.size) (hfresh : ¬ h1.live hk.nextBlk) : LoadHeap h1 H r off len := by
  have hsh := Shape.trans' lh.shape st.shape
  refine ⟨st.gzstates.trans lh.gzstates, st.words.trans lh.words, st.streams.trans lh.streams,
    st.gzheaders.trans lh.gzheaders, st.istates.trans lh.istates, st.static.trans lh.static,
    st.allocOk.trans lh.allocOk, st.garbage.trans lh.garbage, st.nalloc.trans lh.nalloc,
    st.borrow.trans lh.borrow, by rw [st.nextBlk]; have := lh.nextBlk; omega, hsh, ?_,
    fun b hb => (st.bytes b hb).trans (lh.bytes b hb), fun c hc => (st.dstates c hc).trans (lh.dstates c hc),
    ?_, ?_⟩
  · intro b hl
    have hne : b ≠ hk.nextBlk := fun e => hfresh (e ▸ hl)
    rw [st.ro b hne, lh.ro b hl]
  · intro c st0 hr hst0
    subst hr
    obtain ⟨d, hd⟩ := lh.depth c st0 rfl hst0
    refine ⟨x, ?_⟩
    rw [st.depthRec c rfl, hd]
    rfl
  · intro a ha
    obtain ⟨a1, ha1, hs1, hk1⟩ := lh.view a ha
    rw [hg] at ha1; cases ha1
    refine ⟨x, st.view, by rw [hx, size_copyRange, hs1], fun j hj hout => ?_⟩
    rw [hx, Zlib.Deflate.Engine.Proofs.getElem?_copyRange _ _ _ _ _ _ hroom, if_neg (by omega)]
    exact hk1 j hj hout

/-! ## `gz_load`: one trip of the loop -/

theorem ret_count (r : Int64) (k : Nat) (hr : r.toInt = k) (hk : k ≤ 2 ^ 30) :
    r.toInt32.toInt = k ∧ (r.toInt32 ≤ 0 ↔ k = 0) ∧ r.toInt32.toUInt32.toNat = k := by
  have e : r.toInt32.toInt = k := by
    rw [Int64.toInt_toInt32, hr]
    exact Int.bmod_eq_of_le (by omega) (by omega)
  refine ⟨e, ?_, ?_⟩
  · rw [Int32.le_iff_toInt_le, e]; simp
  · have h0 : (0 : Int32) ≤ r.toInt32 := by rw [Int32.le_iff_toInt_le, e]; simp
    rw [Int32.toNat_toUInt32_of_le h0]
    show r.toInt32.toInt.toNat = k
    rw [e]; simp

theorem ret_fail : (-1 : Int64).toInt32 ≤ 0 ∧ (-1 : Int64).toInt32 < 0 := by decide

/-- One trip of `gz_load`'s loop with request size `g`. -/
def loadTrip (i : Nat) (buf : BPtr) (g : UInt32) (l : Zlib.Gzread.LoadLoop) : G Zlib.Gzread.LoadLoop := do
  let s ← liftM (ldS (some (.tab i)))
  let p ← liftM (Ptr.add buf ↑l.«have».toNat)
  let x ← fsRead s.fd g.toUInt64
  liftM (storeBytes p x.snd)
  if x.fst.toInt32 ≤ 0 then pure { «have» := l.«have», ret := x.fst.toInt32, brk := true }
    else pure { «have» := l.«have» + x.fst.toInt32.toUInt32, ret := x.fst.toInt32, brk := l.brk }

theorem loadBody_eq (i : Nat) (buf : BPtr) (len : UInt32) (l : Zlib.Gzread.LoadLoop) :
    loadBody i buf len l = loadTrip i buf
      (if len - l.«have» > ((0 : UInt32) - 1) >>> 2 + 1 then ((0 : UInt32) - 1) >>> 2 + 1 else len - l.«have») l := by
  unfold loadBody loadTrip
  dsimp only
  split <;> rfl

theorem g_lift_app {α : Type} (m : M α) (fs : Fs) (h : Heap) :
    (StateT.lift m : G α) fs h = match m h with
      | .ok (a, h1) => .ok ((a, fs), h1) | .error e => .error e := rfl

theorem g_pure_app {α : Type} (a : α) (fs : Fs) (h : Heap) :
    (pure a : G α) fs h = .ok ((a, fs), h) := rfl

theorem Stored.putGz {h H : Heap} {r : BRef} {x : Array UInt8} (st : Stored h H r x) (i : Nat) (t : GzState) :
    Stored (putGz h i t) (putGz H i t) r x := by
  refine ⟨by rw [putGz_space]; exact st.view, st.bytes, st.dstates, st.depthRec, ?_, st.words, st.streams,
    st.gzheaders, st.istates, by show upd H.gzstates i (some t) = upd h.gzstates i (some t); rw [st.gzstates], st.ro, st.static, st.nextBlk, st.nalloc, st.allocOk,
    st.garbage, st.borrow⟩
  intro b
  obtain ⟨e1, e2, e3, e4, e5, e6, _⟩ := st.shape b
  refine ⟨e1, e2, e3, e4, e5, e6, ?_⟩
  show ((upd H.gzstates i (some t)) b).isSome = ((upd h.gzstates i (some t)) b).isSome
  rw [st.gzstates]

/-- The loop's invariant apart from the exit flag: the record is `s1`, the handle (with no buffered output) is in
`GzInv` and owns the same blocks, the live blocks are those of `h1`, the world is well formed with the same open
descriptors, and only the buffer's view changed. -/
def LoadInv (i : Nat) (buf : BPtr) (len : UInt32) (s1 : GzState) (h1 : Heap) (fs0 : Fs)
    (l : Zlib.Gzread.LoadLoop) (fsk : Fs) (hk : Heap) : Prop :=
  l.«have».toNat ≤ len.toNat ∧ hk.gzstates i = some s1 ∧ GzInv (putGz hk i (clearOut s1)) i (clearOut s1) ∧
  (∀ b, GzOwned (putGz hk i (clearOut s1)) i (clearOut s1) b ↔ GzOwned (putGz h1 i (clearOut s1)) i (clearOut s1) b) ∧
  (∀ b, hk.live b ↔ h1.live b) ∧ FileSystem fsk ∧ FdsKept fs0 fsk ∧
  (∀ r off, buf = .ref r off → LoadHeap h1 hk r off len.toNat) ∧ (buf = .null → hk = h1)

/-- **One trip of `gz_load`'s loop** with a request `g` that fits the rest of the buffer: it returns, keeps the loop
invariant, and either stops (`brk`, nothing counted) or counts `k ≥ 1` more bytes. -/
theorem loadTrip_step (i : Nat) (buf : BPtr) (len : UInt32) (s1 : GzState) (h1 : Heap) (fs0 : Fs)
    (hw : Writable h1 buf len.toNat)
    (hroot : (∃ b off, buf = .ref (.blk b) off ∧ DataBuf (clearOut s1) b) ∨
      (∀ b, ByteRoot buf b → ¬ GzOwned (putGz h1 i (clearOut s1)) i (clearOut s1) b))
    (g : UInt32) (l : Zlib.Gzread.LoadLoop) (fsk : Fs) (hk : Heap)
    (hg : g.toNat + l.«have».toNat ≤ len.toNat) (hg2 : g.toNat ≤ 2 ^ 30)
    (hJ : LoadInv i buf len s1 h1 fs0 l fsk hk) :
    ∃ y fs1 H, loadTrip i buf g l fsk hk = .ok ((y, fs1), H) ∧ LoadInv i buf len s1 h1 fs0 y fs1 H ∧
      ((y.brk = true ∧ y.«have» = l.«have») ∨ (y.brk = l.brk ∧ l.«have».toNat < y.«have».toNat)) := by
  obtain ⟨hle, hrec, ginv, gown, glive, gfs, gkept, glh, gnull⟩ := hJ
  have c1 := ginv.common
  have hfresh : ¬ hk.live hk.nextBlk := by
    intro hl
    exact c1.fresh hk.nextBlk (by simp [putGz]) ((putGz_live hrec hk.nextBlk).2 hl)
  -- the pointer `buf + have`
  obtain ⟨p, hp, hpnull, hpref⟩ : ∃ p, Ptr.add buf (l.«have».toNat : Int) hk = .ok (p, hk) ∧
      (buf = .null → p = .null) ∧ (∀ r off, buf = .ref r off → p = .ref r (off + l.«have».toNat)) := by
    rcases hw with ⟨hn, hz⟩ | ⟨r, off, a, hb, ha, hro, hfit⟩
    · subst hn
      have h0 : l.«have».toNat = 0 := by omega
      refine ⟨.null, by simp [Ptr.add, h0], fun _ => rfl, fun _ _ e => by cases e⟩
    · subst hb
      obtain ⟨ak, hak, hsz, -⟩ := (glh r off rfl).view a ha
      refine ⟨.ref r (off + l.«have».toNat), ?_, ?_, ?_⟩
      · simp only [Ptr.add, hak]
        rw [if_pos (by constructor <;> omega)]
        simp only [Except.ok.injEq, Prod.mk.injEq, Ptr.ref.injEq, true_and, and_true]
        omega
      · intro e; cases e
      · intro r' off' e
        injection e with e1 e2
        subst e1; subst e2; rfl
  -- the read
  obtain ⟨rr, bs, fs', hread, hres, hfs', hkept'⟩ :=
    fsRead_contract s1.fd g.toUInt64 fsk gfs (by have : g.toUInt64.toNat = g.toNat := rfl; omega)
  have hgn : g.toUInt64.toNat = g.toNat := rfl
  unfold loadTrip
  simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, g_bind_app, g_lift_app, g_pure_app,
    ldS_run hrec, hp]
  rw [show fsRead s1.fd g.toUInt64 fsk hk = .ok (((rr, bs), fs'), hk) from by rw [hread]; rfl]
  dsimp only
  have hkept2 : FdsKept fs0 fs' := fun j => (hkept' j).trans (gkept j)
  by_cases hbe : bs.isEmpty = true
  · have hs : storeBytes p bs hk = .ok ((), hk) := by unfold storeBytes; simp [hbe, pure_app]
    have hz : bs.size = 0 := by simpa using hbe
    have hret : rr.toInt32 ≤ 0 := by
      rcases hres with ⟨e, -⟩ | ⟨e, -⟩
      · rw [e]; exact ret_fail.1
      · exact ((ret_count rr 0 (by rw [e, hz]) (by omega)).2.1).2 rfl
    simp only [hs]
    rw [if_pos hret]
    exact ⟨_, _, _, rfl, ⟨hle, hrec, ginv, gown, glive, hfs', hkept2, glh, gnull⟩, Or.inl ⟨rfl, rfl⟩⟩
  · have hne : bs.isEmpty = false := by simpa using hbe
    have hpos : 0 < bs.size := by
      cases bs with | mk lst => cases lst with
        | nil => simp at hbe
        | cons _ _ => simp
    obtain ⟨hcnt, hbg⟩ : rr.toInt = bs.size ∧ bs.size ≤ g.toNat := by
      rcases hres with ⟨-, e⟩ | ⟨e1, e2⟩
      · omega
      · exact ⟨e1, by rw [hgn] at e2; exact e2⟩
    rcases hw with ⟨hn, hz⟩ | ⟨r0, off, a, hb, ha, hro, hfit⟩
    · omega
    subst hb
    have hpe := hpref r0 off rfl
    subst hpe
    have lh := glh r0 off rfl
    obtain ⟨ak, hak, hsz, -⟩ := lh.view a ha
    have hrok : Space.ro hk r0 = false := by
      cases r0 with
      | blk b =>
        have hl : h1.live b := Or.inl (by have : h1.bytes b = some a := ha; rw [this]; simp)
        show hk.ro b = false
        rw [lh.ro b hl]; exact hro
      | dstate_depth k => rfl
      | _ => simp [Space.ro] at hro
    have hslot : hk.slotUsed hk.nextBlk = false := Heap.slotUsed_eq_false.mpr hfresh
    obtain ⟨H, hst, st⟩ := storeBytes_view hk r0 (off + l.«have».toNat) ak bs hak hrok (by omega) hslot hne
    have hroot' : (∃ b, r0 = .blk b ∧ DataBuf (clearOut s1) b) ∨
        (∀ b, ByteRoot (.ref r0 0) b → ¬ GzOwned (putGz hk i (clearOut s1)) i (clearOut s1) b) := by
      rcases hroot with ⟨b, off', e, hd⟩ | hn
      · injection e with e1 e2
        exact Or.inl ⟨b, e1, hd⟩
      · right
        intro b hb ho
        have hb' : ByteRoot (.ref r0 off) b := by cases r0 <;> exact hb
        exact hn b hb' ((gown b).1 ho)
    obtain ⟨ginv', glive', gown'⟩ := GzInv.stored ginv (st.putGz i (clearOut s1))
      (by rw [putGz_space]; exact hak) (size_copyRange _ _ _ _ _) hroot'
    have hrecH : H.gzstates i = some s1 := by rw [st.gzstates]; exact hrec
    obtain ⟨hr1, hr2, hr3⟩ := ret_count rr bs.size hcnt (by omega)
    have hnot : ¬ rr.toInt32 ≤ 0 := fun x => by have := hr2.1 x; omega
    simp only [hst]
    rw [if_neg hnot]
    have hlen := len.toNat_lt
    have hsum : (l.«have» + rr.toInt32.toUInt32).toNat = l.«have».toNat + bs.size := by
      rw [UInt32.toNat_add, hr3]; omega
    refine ⟨_, _, _, rfl, ⟨by show (l.«have» + rr.toInt32.toUInt32).toNat ≤ len.toNat; omega, hrecH, ginv',
      fun b => (gown' b).trans (gown b), fun b => ?_, hfs', hkept2, ?_, fun e => by cases e⟩,
      Or.inr ⟨rfl, by show l.«have».toNat < (l.«have» + rr.toInt32.toUInt32).toNat; omega⟩⟩
    · have e1 := putGz_live (s' := clearOut s1) hrecH b
      have e2 := putGz_live (s' := clearOut s1) hrec b
      rw [← e1, glive' b, e2]; exact glive b
    · intro r' off' e
      injection e with e1 e2
      subst e1; subst e2
      exact lh.store st hak rfl (by omega) (by omega) (fun hl => hfresh ((glive _).2 hl))

/-- **`gz_load`'s loop**: from the heap after its prefix it returns, keeping the loop invariant, and stops with
`brk` or a full buffer. The fuel is `2^64`, above `len`. -/
theorem gz_load_loop (i : Nat) (buf : BPtr) (len : UInt32) (s1 : GzState) (h1 : Heap) (fs1 : Fs)
    (hw : Writable h1 buf len.toNat)
    (hroot : (∃ b off, buf = .ref (.blk b) off ∧ DataBuf (clearOut s1) b) ∨
      (∀ b, ByteRoot buf b → ¬ GzOwned (putGz h1 i (clearOut s1)) i (clearOut s1) b))
    (hrec : h1.gzstates i = some s1) (ginv : GzInv (putGz h1 i (clearOut s1)) i (clearOut s1))
    (hfs : FileSystem fs1) :
    ∃ l fs' H, gdoWhile (loadBody i buf len) (loadCond len) { «have» := 0, ret := 0, brk := false } fs1 h1 =
        .ok ((l, fs'), H) ∧ LoadInv i buf len s1 h1 fs1 l fs' H ∧ (l.brk = true ∨ l.«have» = len) := by
  let J : Zlib.Gzread.LoadLoop → Fs → Heap → Prop := fun l fs h => l.brk = false ∧ LoadInv i buf len s1 h1 fs1 l fs h
  let Post : Zlib.Gzread.LoadLoop → Fs → Heap → Prop := fun l fs h =>
    LoadInv i buf len s1 h1 fs1 l fs h ∧ (l.brk = true ∨ l.«have» = len)
  have hstep : ∀ x fs h, J x fs h → ∃ y fs1' h1', loadBody i buf len x fs h = .ok ((y, fs1'), h1') ∧
      ∃ c z fs2 h2, loadCond len y fs1' h1' = .ok (((c, z), fs2), h2) ∧
        (c = true → J z fs2 h2 ∧ len.toNat - z.«have».toNat < len.toNat - x.«have».toNat) ∧
        (c = false → Post z fs2 h2) := by
    intro x fs h ⟨hbrk, hinv⟩
    have hle := hinv.1
    have hmax : ((0 : UInt32) - 1) >>> 2 + 1 = 1073741824 := by decide
    let g : UInt32 := if len - x.«have» > ((0 : UInt32) - 1) >>> 2 + 1 then ((0 : UInt32) - 1) >>> 2 + 1
      else len - x.«have»
    have hsub : (len - x.«have»).toNat = len.toNat - x.«have».toNat :=
      UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr hle)
    have hg : g.toNat + x.«have».toNat ≤ len.toNat ∧ g.toNat ≤ 2 ^ 30 := by
      show (if len - x.«have» > ((0 : UInt32) - 1) >>> 2 + 1 then ((0 : UInt32) - 1) >>> 2 + 1
        else len - x.«have»).toNat + _ ≤ _ ∧ (if len - x.«have» > ((0 : UInt32) - 1) >>> 2 + 1 then
          ((0 : UInt32) - 1) >>> 2 + 1 else len - x.«have»).toNat ≤ 2 ^ 30
      rw [hmax]
      split
      · rename_i hc
        have := UInt32.lt_iff_toNat_lt.mp hc
        have h30 : (1073741824 : UInt32).toNat = 1073741824 := rfl
        rw [h30] at this ⊢
        constructor <;> omega
      · rename_i hc
        have := (UInt32.not_lt).mp hc
        have := UInt32.le_iff_toNat_le.mp this
        have h30 : (1073741824 : UInt32).toNat = 1073741824 := rfl
        rw [h30] at this
        constructor <;> omega
    obtain ⟨y, fs', H, hrun, hinv', hcase⟩ :=
      loadTrip_step i buf len s1 h1 fs1 hw hroot g x fs h hg.1 hg.2 hinv
    refine ⟨y, fs', H, by rw [loadBody_eq]; exact hrun, _, _, _, _, rfl, ?_, ?_⟩
    · intro hc
      simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hc
      obtain ⟨hb, hlt⟩ := hc
      refine ⟨⟨hb, hinv'⟩, ?_⟩
      rcases hcase with ⟨e, -⟩ | ⟨-, e⟩
      · rw [e] at hb; cases hb
      · have := UInt32.lt_iff_toNat_lt.mp hlt
        omega
    · intro hc
      refine ⟨hinv', ?_⟩
      simp only [Bool.and_eq_false_iff, Bool.not_eq_eq_eq_not, Bool.not_false, decide_eq_false_iff_not] at hc
      rcases hc with hb | hn
      · exact Or.inl hb
      · right
        have h1' := hinv'.1
        have := UInt32.not_lt.mp hn
        exact UInt32.le_antisymm (UInt32.le_iff_toNat_le.mpr h1') this
  have hJ0 : J { «have» := 0, ret := 0, brk := false } fs1 h1 :=
    ⟨rfl, Nat.zero_le _, hrec, ginv, fun _ => Iff.rfl, fun _ => Iff.rfl, hfs, fun _ => Iff.rfl,
      fun r off _ => LoadHeap.refl h1 r off len.toNat, fun _ => rfl⟩
  have hlen := len.toNat_lt
  obtain ⟨z, fs', h', hrun, hpost⟩ := gdoWhile_go_spec (loadBody i buf len) (loadCond len) J Post
    (fun l => len.toNat - l.«have».toNat) hstep C.fuel _ fs1 h1 hJ0 (by show _ < 18446744073709551616; omega)
  exact ⟨z, fs', h', hrun, hpost⟩

end ZlibF.Spec.Public.GzRead
