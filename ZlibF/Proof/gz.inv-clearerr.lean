import ZlibF.Proof.«gz.inv-frame»
import ZlibF.Proof.«gzlib.c.error»
import ZlibF.Proof.«gzlib.c.simple»

/-!
# gz safety: dropping the message keeps `GzInv`, and `gzclearerr`

`GzInv.clear_message`: freeing the owned message, clearing the pointer and setting the error code (and, for a
reader, `eof` and `past`) keeps the invariant; the handle then owns exactly its old blocks but the message.
This is the `msg == NULL` path of `gz_error`. `gzclearerr_step` (skeleton statement, unchanged) follows.
-/

namespace ZlibF.Spec.Public
open C Zlib.GzFs
open Zlib.Gzlib.Proofs (freeStr)
set_option autoImplicit false

section clear
variable {h : Heap} {i : Nat} {s : GzState}

/-- The message block, if any, is a block of its own: the record, the path, the buffers and the codec do not use
it. -/
theorem GzInv.msg_separate (inv : GzInv h i s) {mb : Nat} (hm : blkOf s.msg = some mb) :
    mb ≠ i ∧ s.path ≠ .ref (.blk mb) 0 ∧ ¬ StreamOwned h (gzStrm i) mb ∧
    (s.size ≠ 0 → s.«in» ≠ .ref (.blk mb) 0 ∧ ((s.mode = GZ_READ ∨ s.direct = 0) → s.out ≠ .ref (.blk mb) 0)) := by
  have c := inv.common
  have hp : s.msg = .ref (.blk mb) 0 := by
    rcases c.msg with hn | ⟨_, _, mb', a, hp, _⟩
    · rw [hn] at hm; cases hm
    · rw [hp] at hm; cases hm; exact hp
  have hmem : s.msg ∈ ownedPtrs s := by simp [ownedPtrs]
  obtain ⟨hi, hso⟩ := c.distinct.2 s.msg hmem mb hm
  have nd := c.distinct.1
  simp only [ownedPtrs, hp] at nd
  have hpath : s.path ≠ .ref (.blk mb) 0 := by
    intro e
    simp [e, blkOf] at nd
  refine ⟨hi, hpath, hso, fun hz => ⟨?_, fun hmo => ?_⟩⟩
  · intro e
    simp only [e, List.cons_append, List.nil_append] at nd
    rw [if_pos hz] at nd
    exact absurd (nd.sublist (List.Sublist.filterMap blkOf
      (List.Sublist.cons _ (List.Sublist.cons₂ _ (List.Sublist.cons₂ _ (List.nil_sublist _)))))) (by simp [blkOf])
  · intro e
    simp only [hmo, e, ite_true, List.cons_append, List.nil_append] at nd
    rw [if_pos hz] at nd
    exact absurd (nd.sublist (List.Sublist.filterMap blkOf
      (List.Sublist.cons _ (List.Sublist.cons₂ _ (List.Sublist.cons _ (List.Sublist.cons₂ _
        (List.nil_sublist _))))))) (by simp [blkOf])

end clear

/-- The heap with the message freed. -/
theorem freeStr_facts {h : Heap} {s : GzState} (u : Zlib.Gzlib.Spec.Uniq h)
    (hmsg : s.msg = .null ∨ ∃ mb a, s.msg = .ref (.blk mb) 0 ∧ h.bytes mb = some a) :
    (freeStr h s.msg).gzstates = h.gzstates ∧ (freeStr h s.msg).istates = h.istates ∧
    (freeStr h s.msg).dstates = h.dstates ∧ (freeStr h s.msg).ro = h.ro ∧
    (freeStr h s.msg).static = h.static ∧ (freeStr h s.msg).nextBlk = h.nextBlk ∧
    (freeStr h s.msg).words = h.words ∧ (freeStr h s.msg).streams = h.streams ∧
    (freeStr h s.msg).gzheaders = h.gzheaders ∧ (freeStr h s.msg).allocOk = h.allocOk ∧
    (freeStr h s.msg).garbage = h.garbage ∧ (freeStr h s.msg).nalloc = h.nalloc ∧
    (∀ b, blkOf s.msg ≠ some b → (freeStr h s.msg).bytes b = h.bytes b) ∧
    (∀ b, (freeStr h s.msg).live b ↔ h.live b ∧ blkOf s.msg ≠ some b) ∧
    (∀ (r : BRef) (a : Array UInt8), Space.get (freeStr h s.msg) r = some a → Space.get h r = some a) := by
  rcases hmsg with hn | ⟨mb, a, hp, hb⟩
  · rw [hn]
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, ?_, fun _ _ e => e⟩
    intro b
    simp [blkOf, freeStr]
  · rw [hp]
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
    · intro b hb'
      have hne : b ≠ mb := fun e => hb' (by rw [e]; rfl)
      show upd h.bytes mb none b = h.bytes b
      exact upd_ne _ _ _ _ hne
    · intro b
      have := Zlib.Gzlib.Proofs.live_freeBytes u hb b
      show ({ h with bytes := upd h.bytes mb none } : Heap).live b ↔ _
      rw [this]
      simp [blkOf, eq_comm]
    · intro r a' e
      cases r with
      | blk c =>
        show h.bytes c = some a'
        have e' : upd h.bytes mb none c = some a' := e
        by_cases hc : c = mb
        · rw [hc, upd_same] at e'
          cases e'
        · rw [upd_ne _ _ _ _ hc] at e'
          exact e'
      | str j => exact e
      | dstate_depth k => exact e
      | st_dist_code => exact e
      | st_length_code => exact e

/-- **Dropping the message keeps `GzInv`.** The owned message is freed, the pointer cleared, the code set to `e`,
and (for a reader) `eof` and `past` set to `e1` and `p1`. -/
theorem GzInv.clear_message {h : Heap} {i : Nat} {s : GzState} (inv : GzInv h i s) (e1 p1 e : Int32)
    (rd : s.mode = GZ_READ → (e1 = 0 ∨ e1 = 1) ∧ (p1 = 0 ∨ p1 = 1) ∧ (s.again ≠ 0 → e1 ≠ 0 → s.strm.avail_in = 0)) :
    GzInv (putGz (freeStr h s.msg) i { s with eof := e1, past := p1, msg := .null, err := e }) i
        { s with eof := e1, past := p1, msg := .null, err := e } ∧
    (∀ b, GzOwned (putGz (freeStr h s.msg) i { s with eof := e1, past := p1, msg := .null, err := e }) i
        { s with eof := e1, past := p1, msg := .null, err := e } b ↔ GzOwned h i s b ∧ blkOf s.msg ≠ some b) ∧
    (∀ b, (putGz (freeStr h s.msg) i { s with eof := e1, past := p1, msg := .null, err := e }).live b ↔
        h.live b ∧ blkOf s.msg ≠ some b) ∧
    Frame h (putGz (freeStr h s.msg) i { s with eof := e1, past := p1, msg := .null, err := e })
      (fun b => b = i ∨ blkOf s.msg = some b) := by
  have c := inv.common
  have hs := c.record
  have hmsg : s.msg = .null ∨ ∃ mb a, s.msg = .ref (.blk mb) 0 ∧ h.bytes mb = some a := by
    rcases c.msg with hn | ⟨_, _, mb, a, hp, hb, _, _⟩
    · exact Or.inl hn
    · exact Or.inr ⟨mb, a, hp, hb⟩
  obtain ⟨dgz, dist, dds, dro, dst, dnext, dwords, dstreams, dhead, dok, dgarb, dnal, dbytes, dlive, dget⟩ :=
    freeStr_facts c.uniq hmsg
  have hsD : (freeStr h s.msg).gzstates i = some s := by rw [dgz]; exact hs
  have freshD : Fresh (freeStr h s.msg) := by
    intro b hb hl
    exact c.fresh b (by rw [← dnext]; exact hb) ((dlive b).1 hl).1
  have uniqD : Zlib.Gzlib.Spec.Uniq (freeStr h s.msg) := by
    rcases hmsg with hn | ⟨mb, a, hp, _⟩
    · rw [hn]; exact c.uniq
    · rw [hp]; exact Zlib.Gzlib.Proofs.Uniq.freeBytes c.uniq mb
  have fitD : ZlibF.PlatformMemory.ByteObjectsFit (freeStr h s.msg) := fun r a g => c.fit r a (dget r a g)
  have hget : ZStreamRef.get (putGz (freeStr h s.msg) i { s with eof := e1, past := p1, msg := .null, err := e })
      (gzStrm i) = ZStreamRef.get h (gzStrm i) := by
    simp [ZStreamRef.get, gzStrm, putGz, hs]
  have hist : (putGz (freeStr h s.msg) i { s with eof := e1, past := p1, msg := .null, err := e }).istates =
      h.istates := dist
  have hdst : (putGz (freeStr h s.msg) i { s with eof := e1, past := p1, msg := .null, err := e }).dstates =
      h.dstates := dds
  have hso : ∀ b, StreamOwned (putGz (freeStr h s.msg) i { s with eof := e1, past := p1, msg := .null, err := e })
      (gzStrm i) b ↔ StreamOwned h (gzStrm i) b := by
    intro b
    unfold StreamOwned
    rw [hget, hist, hdst]
  have hso' : ∀ b, StreamOwned (putGz (freeStr h s.msg) i { s with eof := e1, past := p1, msg := .null, err := e })
      (.in_gzstate_strm i) b ↔ StreamOwned h (.in_gzstate_strm i) b := hso
  have hliveH : ∀ b, (putGz (freeStr h s.msg) i { s with eof := e1, past := p1, msg := .null, err := e }).live b ↔
      h.live b ∧ blkOf s.msg ≠ some b := fun b => (putGz_live hsD b).trans (dlive b)
  have hown : ∀ b, GzOwned (putGz (freeStr h s.msg) i { s with eof := e1, past := p1, msg := .null, err := e }) i
      { s with eof := e1, past := p1, msg := .null, err := e } b ↔ GzOwned h i s b ∧ blkOf s.msg ≠ some b := by
    intro b
    unfold GzOwned
    dsimp only
    rw [hso']
    constructor
    · intro ho
      have ho' : GzOwned h i s b := by
        rcases ho with hb | hb | hb | hb
        · exact Or.inl hb
        · exact Or.inr (Or.inl hb)
        · cases hb
        · exact Or.inr (Or.inr (Or.inr hb))
      refine ⟨ho', fun hm => ?_⟩
      obtain ⟨hi, hpath, hnso, hbuf⟩ := inv.msg_separate hm
      rcases ho with hb | hb | hb | ⟨hz, hb | ⟨hmo, hb | hb⟩⟩
      · exact hi hb
      · exact hpath hb
      · cases hb
      · exact (hbuf hz).1 hb
      · exact (hbuf hz).2 hmo hb
      · exact hnso hb
    · rintro ⟨ho, hne⟩
      rcases ho with hb | hb | hb | hb
      · exact Or.inl hb
      · exact Or.inr (Or.inl hb)
      · exact absurd (by rw [hb]; rfl) hne
      · exact Or.inr (Or.inr (Or.inr hb))
  have hframe : Frame h (putGz (freeStr h s.msg) i { s with eof := e1, past := p1, msg := .null, err := e })
      (fun b => b = i ∨ blkOf s.msg = some b) := by
    refine ⟨dst.symm, dok.symm, dgarb.symm, Nat.le_of_eq dnext.symm, Nat.le_of_eq dnal.symm, ?_⟩
    intro b _ hb
    have hbi : b ≠ i := fun e => hb (Or.inl e)
    have hbm : blkOf s.msg ≠ some b := fun e => hb (Or.inr e)
    refine ⟨dbytes b hbm, by rw [← dwords]; rfl, by rw [← dstreams]; rfl, by rw [← dhead]; rfl,
      by rw [← dds]; rfl, by rw [← dist]; rfl, ?_, by rw [← dro]; rfl⟩
    show upd _ i _ b = h.gzstates b
    rw [upd_ne _ _ _ _ hbi, dgz]
  have hreb : Rebuffer h (putGz (freeStr h s.msg) i { s with eof := e1, past := p1, msg := .null, err := e })
      (gzStrm i) := by
    refine ⟨putGz_fresh hsD freshD, putGz_uniq hsD uniqD, by show (freeStr h s.msg).static = _; rw [dst]; exact c.globals,
      ⟨hframe.1, hframe.2.1, hframe.2.2.1, hframe.2.2.2.1, hframe.2.2.2.2.1, ?_⟩, s.strm, s.strm, ?_, ?_, rfl⟩
    · intro b hl hn
      have hb : StreamOwned h (gzStrm i) b := Classical.byContradiction hn
      refine hframe.2.2.2.2.2 b hl ?_
      rintro (e | e)
      · subst e; exact c.recordFree hb
      · exact (inv.msg_separate e).2.2.1 hb
    · simp [ZStreamRef.get, gzStrm, hs]
    · simp [ZStreamRef.get, gzStrm, putGz]
  have fitH : ZlibF.PlatformMemory.ByteObjectsFit
      (putGz (freeStr h s.msg) i { s with eof := e1, past := p1, msg := .null, err := e }) := putGz_fit fitD
  have hexact : ∀ p n, (∀ b, p = .ref (.blk b) 0 → blkOf s.msg ≠ some b) →
      ExactBuffer h p n →
      ExactBuffer (putGz (freeStr h s.msg) i { s with eof := e1, past := p1, msg := .null, err := e }) p n := by
    intro p n own hx
    obtain ⟨b, a, hp, hb, hr, hsz⟩ := hx
    refine ⟨b, a, hp, ?_, ?_, hsz⟩
    · show (freeStr h s.msg).bytes b = some a
      rw [dbytes b (own b hp)]; exact hb
    · show (freeStr h s.msg).ro b = false
      rw [dro]; exact hr
  have hpl : ∃ L, ownedPtrs { s with eof := e1, past := p1, msg := .null, err := e } = [s.path, .null] ++ L ∧
      ownedPtrs s = [s.path, s.msg] ++ L := ⟨_, rfl, rfl⟩
  obtain ⟨L, eL1, eL2⟩ := hpl
  refine ⟨⟨?_, ?_, ?_⟩, hown, hliveH, hframe⟩
  · exact {
      record := by simp [putGz]
      mode := c.mode
      fresh := putGz_fresh hsD freshD
      uniq := putGz_uniq hsD uniqD
      globals := by show (freeStr h s.msg).static = _; rw [dst]; exact c.globals
      fit := fitH
      path := by
        obtain ⟨p, hc, pb, a, hp, hb, hr, hn⟩ := c.path
        have hpm : blkOf s.msg ≠ some pb := by
          intro hm
          exact (inv.msg_separate hm).2.1 hp
        have eb : (putGz (freeStr h s.msg) i { s with eof := e1, past := p1, msg := .null, err := e }).bytes pb =
            h.bytes pb := dbytes pb hpm
        refine ⟨p, ?_, pb, a, hp, by rw [eb]; exact hb, by show (freeStr h s.msg).ro pb = _; rw [dro]; exact hr, hn⟩
        show CString _ s.path p
        rw [hp] at hc ⊢
        exact (cstring_blk_congr eb).2 hc
      msg := Or.inl rfl
      memerr := fun _ => rfl
      want := c.want
      size := c.size
      distinct := by
        refine ⟨?_, fun p hp b hb => ?_⟩
        · have nd := c.distinct.1
          rw [eL2] at nd
          rw [eL1]
          have hn : blkOf (.null : BPtr) = none := rfl
          have h1 : ([s.path, (Ptr.null : BPtr)] ++ L).filterMap blkOf = (s.path :: L).filterMap blkOf := by
            show (s.path :: (Ptr.null : BPtr) :: L).filterMap blkOf = _
            simp only [List.filterMap_cons, hn]
          rw [h1]
          exact List.Nodup.sublist (List.Sublist.filterMap blkOf ((List.sublist_cons_self s.msg L).cons₂ s.path)) nd
        · have hp' : p ∈ ownedPtrs s := by
            rw [eL1] at hp
            rw [eL2]
            simp only [List.cons_append, List.mem_cons] at hp ⊢
            rcases hp with e' | e' | e'
            · exact Or.inl e'
            · subst e'; cases hb
            · exact Or.inr (Or.inr e')
          obtain ⟨hi, hn⟩ := c.distinct.2 p hp' b hb
          exact ⟨hi, by rw [hso]; exact hn⟩
      live := fun b hb => (hliveH b).2 (by
        obtain ⟨ho, hm⟩ := (hown b).1 hb
        exact ⟨c.live b ho, hm⟩)
      pos := c.pos
      next := fun hh => by
        obtain ⟨b, off, a, hx, hbi, ho, hmb, hb, hle⟩ := c.next hh
        refine ⟨b, off, a, hx, hbi, (hown b).2 ⟨ho, hmb⟩, by simp [blkOf], ?_, hle⟩
        show (freeStr h s.msg).bytes b = some a
        rw [dbytes b hmb]; exact hb
      nullHave := c.nullHave
      recordFree := by rw [hso]; exact c.recordFree }
  · intro hm
    have r := inv.reader hm
    obtain ⟨he1, hp1, hae⟩ := rd hm
    exact {
      how := r.how
      copyDirect := r.copyDirect
      gzipDirect := r.gzipDirect
      direct := r.direct
      junk := r.junk
      flags := ⟨he1, hp1, r.flags.2.2⟩
      unalloc := r.unalloc
      bufs := fun hz =>
        ⟨hexact _ _ (fun b hp hmb => ((inv.msg_separate hmb).2.2.2 hz).1 hp) (r.bufs hz).1,
         hexact _ _ (fun b hp hmb => ((inv.msg_separate hmb).2.2.2 hz).2 (Or.inl hm) hp) (r.bufs hz).2⟩
      input := r.input
      output := r.output
      codec := fun hz => by
        obtain ⟨reach, z, k, st, hzget, hzst, hk, hhead⟩ := r.codec hz
        exact ⟨StreamReachable.rebuffer reach hreb (fun _ => fitH),
          z, k, st, by rw [hget]; exact hzget, hzst, by rw [hist]; exact hk, hhead⟩
      posHave := r.posHave
      againSize := r.againSize
      haveSkip := r.haveSkip
      againEof := hae }
  · intro hm
    have w := inv.writer hm
    exact {
      have0 := w.have0
      direct := w.direct
      reset := w.reset
      unalloc := w.unalloc
      bufs := fun hz =>
        ⟨hexact _ _ (fun b hp hmb => ((inv.msg_separate hmb).2.2.2 hz).1 hp) (w.bufs hz).1,
         fun hd => hexact _ _ (fun b hp hmb => ((inv.msg_separate hmb).2.2.2 hz).2 (Or.inr hd) hp)
          ((w.bufs hz).2 hd)⟩
      input := w.input
      output := w.output
      codec := fun hd hz => by
        obtain ⟨reach, z, k, d, hzget, hzst, hk, hhead⟩ := w.codec hd hz
        exact ⟨StreamReachable.rebuffer reach hreb (fun e => nomatch e),
          z, k, d, by rw [hget]; exact hzget, hzst, by rw [hdst]; exact hk, hhead⟩
      transparent := w.transparent }

end ZlibF.Spec.Public

namespace ZlibF.Spec.Public.GzSkeleton
open C Zlib.GzFs Zlib.Gzguts ZlibF.Spec.Public Zlib.Gzlib.Proofs
set_option autoImplicit false

/-- The run of `gzclearerr` on a handle in `GzInv` (as the registered `gzclearerr` proof). -/
theorem gzclearerr_inv_run {h : Heap} {i : Nat} {s : GzState} (inv : GzInv h i s) :
    Zlib.Gzlib.gzclearerr (some (.in_gzstate_x i)) h =
      .ok ((), Zlib.Gzlib.Spec.setS (Zlib.Gzlib.Proofs.freeStr h s.msg) i
        (Zlib.Gzlib.Spec.errNull (Zlib.Gzlib.Spec.clearRec s) Z_OK)) := by
  have hs := inv.common.record
  have hm := inv.common.mode
  have hmem := inv.common.memerr
  show Zlib.Gzlib.gzclearerr (Zlib.Gzlib.Spec.hnd i) h = _
  unfold Zlib.Gzlib.gzclearerr
  rcases inv.common.msg with hn | ⟨_, _, mb, a, hp, ha, hro, _⟩
  · rcases hm with hmode | hmode <;>
      gsimp [hs, hn, hmode, Zlib.Gzlib.gz_error, Zlib.Gzlib.Spec.clearRec, Zlib.Gzlib.Spec.errNull, GZ_READ, GZ_WRITE]
  · have hne : s.err ≠ Z_MEM_ERROR := fun he => by
      have hnull := hmem he
      rw [hp] at hnull
      cases hnull
    rcases hm with hmode | hmode <;>
      gsimp [hs, hp, hne, hmode, Zlib.Gzlib.Proofs.freeB_blk_setS ha hro, Zlib.Gzlib.Proofs.freeB_blk_run ha hro,
        Zlib.Gzlib.gz_error, Zlib.Gzlib.Spec.clearRec, Zlib.Gzlib.Spec.errNull, GZ_READ, GZ_WRITE]

/-- `gzclearerr`, from the registered `gzclearerr` goal and `GzInv.gz_error`. Proved here from the run (as the registered proof) and
`GzInv.clear_message`, the `msg == NULL` path of `gz_error`. -/
theorem gzclearerr_step (i : Nat) : GzCallSafe i (.gzclearerr (some (.in_gzstate_x i))) := by
  intro h fs s inv hfs _
  have hrun := gzclearerr_inv_run inv
  have key : ∃ e1 p1 : Int32, (s.mode = GZ_READ → (e1 = 0 ∨ e1 = 1) ∧ (p1 = 0 ∨ p1 = 1) ∧
        (s.again ≠ 0 → e1 ≠ 0 → s.strm.avail_in = 0)) ∧
      Zlib.Gzlib.Spec.errNull (Zlib.Gzlib.Spec.clearRec s) Z_OK =
        { s with eof := e1, past := p1, msg := .null, err := Z_OK } := by
    by_cases hm : s.mode = GZ_READ
    · refine ⟨0, 0, fun _ => ⟨Or.inl rfl, Or.inl rfl, fun _ he => absurd rfl he⟩, ?_⟩
      simp [Zlib.Gzlib.Spec.errNull, Zlib.Gzlib.Spec.clearRec, hm]
    · refine ⟨s.eof, s.past, fun h' => absurd h' hm, ?_⟩
      have hm' : (s.mode == GZ_READ) = false := by simpa using hm
      simp [Zlib.Gzlib.Spec.errNull, Zlib.Gzlib.Spec.clearRec, hm']
  obtain ⟨e1, p1, rd, es⟩ := key
  rw [es] at hrun
  obtain ⟨inv', hown, hlive, hframe⟩ := inv.clear_message e1 p1 Z_OK rd
  have e : Call.execute (.gzclearerr (some (.in_gzstate_x i))) fs h =
      .ok (((), fs), putGz (Zlib.Gzlib.Proofs.freeStr h s.msg) i
        { s with eof := e1, past := p1, msg := .null, err := Z_OK }) := by
    show heapCall _ fs h = _
    simp only [heapCall, hrun]
    try rfl
  refine safe_of_run e ⟨fun _ => Iff.rfl, hfs, _, inv', rfl, rfl, ?_, ?_⟩
  · refine ⟨?_, fun region hm => by cases hm⟩
    show Frame h _ (GzOwned h i s)
    refine ⟨hframe.1, hframe.2.1, hframe.2.2.1, hframe.2.2.2.1, hframe.2.2.2.2.1, ?_⟩
    intro b hl ho
    refine hframe.2.2.2.2.2 b hl ?_
    rintro (hb | hb)
    · exact ho (Or.inl hb)
    · rcases inv.common.msg with hn | ⟨_, _, mb, _, hp, _⟩
      · rw [hn] at hb; cases hb
      · rw [hp] at hb
        cases hb
        exact ho (Or.inr (Or.inr (Or.inl hp)))
  · unfold LiveChange
    intro b
    dsimp only
    rw [hlive b, hown b]
    constructor
    · rintro ⟨hl, hm⟩
      exact Or.inl ⟨hl, fun hn => hn.2 ⟨hn.1, hm⟩⟩
    · rintro (⟨hl, hn⟩ | ⟨⟨ho, hm⟩, hnl⟩)
      · refine ⟨hl, fun hm => hn ⟨?_, fun hx => hx.2 hm⟩⟩
        rcases inv.common.msg with hnul | ⟨_, _, mb, _, hp, _⟩
        · rw [hnul] at hm; cases hm
        · rw [hp] at hm; cases hm; exact Or.inr (Or.inr (Or.inl hp))
      · exact absurd (inv.common.live b ho) hnl

end ZlibF.Spec.Public.GzSkeleton
