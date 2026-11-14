import ZlibF.Proof.«gz.read-store»
import ZlibF.Proof.«gzlib.c.error-inv-rec»
import ZlibF.Proof.«libc-errno-cstring»
import ZlibF.Proof.«inflate.c.gzip-header-frame»

/-!
# gz read side: the failure report of `gz_load`, and `gz_load_safe`

When a `read` fails and it is not a stall after some bytes, `gz_load` sets `again` on a stall, borrows
`strerror(errno)` and reports `gz_error(state, Z_ERRNO, ...)`, then returns `-1`. `gz_load_error_tail` shows that this
path returns with the post-condition `GzPost` over the caller's buffer region. With `gz_load_paths`
(`gz.read-store`) it gives `gz_load_safe`, the skeleton statement with the two premises found on the way
(`size ≠ 0`, and the buffer is a data buffer of the handle or memory it does not own).

`bufferFrame_extend` adds to a buffer frame over one region a later heap change that touches only blocks the frame
may change and keeps the region's view.
-/

namespace ZlibF.Spec.Public.GzRead
open C Zlib.GzFs Zlib.Gzguts Zlib.Gzlib.Spec Zlib.Gzlib.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-! ## A buffer frame over one region, extended by a frame -/

/-- The eight tables of a block agree. -/
def AgreeAt (X Y : Heap) (b : Nat) : Prop :=
  Y.bytes b = X.bytes b ∧ Y.words b = X.words b ∧ Y.streams b = X.streams b ∧ Y.gzheaders b = X.gzheaders b ∧
    Y.dstates b = X.dstates b ∧ Y.istates b = X.istates b ∧ Y.gzstates b = X.gzstates b ∧ Y.ro b = X.ro b

theorem agree_put {X Y : Heap} {b : Nat} (hag : AgreeAt X Y b) (r : BRef) (a : Array UInt8) :
    AgreeAt (Space.put X r a) (Space.put Y r a) b := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ := hag
  cases r with
  | blk c =>
    refine ⟨?_, e2, e3, e4, e5, e6, e7, e8⟩
    show upd Y.bytes c (some a) b = upd X.bytes c (some a) b
    rw [upd_apply, upd_apply, e1]
  | str j => exact ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩
  | dstate_depth k =>
    have pdd : ∀ Z : Heap, Space.put Z (BRef.dstate_depth k) a = (match Z.dstates k with
        | some st => { Z with dstates := upd Z.dstates k (some { st with depth := a }) }
        | none => Z) := fun _ => rfl
    have hd : ∀ Z : Heap, (Space.put Z (BRef.dstate_depth k) a).dstates b =
        if b = k then (Z.dstates k).map (fun st => { st with depth := a }) else Z.dstates b := by
      intro Z
      rw [pdd]
      cases hz : Z.dstates k with
      | none =>
        by_cases e : b = k
        · subst e; simp [hz]
        · simp [e]
      | some st =>
        simp only [upd_apply]
        by_cases e : b = k
        · subst e; simp
        · simp [e]
    have ho : ∀ Z : Heap, (Space.put Z (BRef.dstate_depth k) a).bytes = Z.bytes ∧
        (Space.put Z (BRef.dstate_depth k) a).words = Z.words ∧
        (Space.put Z (BRef.dstate_depth k) a).streams = Z.streams ∧
        (Space.put Z (BRef.dstate_depth k) a).gzheaders = Z.gzheaders ∧
        (Space.put Z (BRef.dstate_depth k) a).istates = Z.istates ∧
        (Space.put Z (BRef.dstate_depth k) a).gzstates = Z.gzstates ∧
        (Space.put Z (BRef.dstate_depth k) a).ro = Z.ro := by
      intro Z
      rw [pdd]
      cases Z.dstates k <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    obtain ⟨x1, x2, x3, x4, x5, x6, x7⟩ := ho X
    obtain ⟨y1, y2, y3, y4, y5, y6, y7⟩ := ho Y
    refine ⟨by rw [x1, y1, e1], by rw [x2, y2, e2], by rw [x3, y3, e3], by rw [x4, y4, e4], ?_,
      by rw [x5, y5, e6], by rw [x6, y6, e7], by rw [x7, y7, e8]⟩
    rw [hd, hd]
    by_cases e : b = k
    · subst e; rw [if_pos rfl, if_pos rfl, e5]
    · rw [if_neg e, if_neg e, e5]
  | st_dist_code => exact ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩
  | st_length_code => exact ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩

/-- A put into a view makes a block live only at the view's own byte block. -/
theorem live_of_put {Z : Heap} {r : BRef} {a : Array UInt8} {b : Nat} (hl : (Space.put Z r a).live b) :
    r = .blk b ∨ Z.live b := by
  cases r with
  | blk c =>
    by_cases e : c = b
    · exact Or.inl (by rw [e])
    · right
      unfold Heap.live at hl ⊢
      have : (Space.put Z (BRef.blk c) a).bytes b = Z.bytes b := by
        show upd Z.bytes c (some a) b = Z.bytes b
        exact upd_ne _ _ _ _ (Ne.symm e)
      rw [this] at hl
      exact hl
  | str j => exact Or.inr hl
  | dstate_depth k =>
    right
    have pdd : Space.put Z (BRef.dstate_depth k) a = (match Z.dstates k with
        | some st => { Z with dstates := upd Z.dstates k (some { st with depth := a }) }
        | none => Z) := rfl
    rw [pdd] at hl
    split at hl
    · rename_i st hz
      unfold Heap.live at hl ⊢
      simp only [upd_apply] at hl
      by_cases e : b = k
      · subst e
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by rw [hz]; intro x; cases x)))))
      · simpa [e] using hl
    · exact hl
  | st_dist_code => exact Or.inr hl
  | st_length_code => exact Or.inr hl

/-- The restore of one region. -/
def restoreOne (h Z : Heap) (p : BPtr) : Heap :=
  match p with
  | .null => Z
  | .ref r _ => match Space.get h r with | none => Z | some a => Space.put Z r a

theorem restore_single (h Z : Heap) (p : BPtr) (n : Nat) :
    restoreRegions h Z [⟨p, n⟩] = restoreOne h Z p := rfl

/-- **A buffer frame over one region, extended by a frame** whose changed blocks the buffer frame may change (or
were not live), and that keeps the region's view. -/
theorem bufferFrame_extend {h X Y : Heap} {C D : Nat → Prop} {p : BPtr} {n : Nat}
    (bf : BufferFrame h X C [⟨p, n⟩]) (fr : Frame X Y D) (hD : ∀ b, D b → C b ∨ ¬ h.live b)
    (hget : ∀ r off, p = .ref r off → Space.get Y r = Space.get X r) :
    BufferFrame h Y C [⟨p, n⟩] := by
  obtain ⟨⟨s1, a1, g1, n1, c1, slots1⟩, cells1⟩ := bf
  obtain ⟨s2, a2, g2, n2, c2, slots2⟩ := fr
  have oX := Zlib.Inflate.Proofs.restoreRegions_other h X [⟨p, n⟩]
  have oY := Zlib.Inflate.Proofs.restoreRegions_other h Y [⟨p, n⟩]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [oY.1, ← s2, ← oX.1]; exact s1
  · rw [oY.2.1, ← a2, ← oX.2.1]; exact a1
  · rw [oY.2.2.1, ← g2, ← oX.2.2.1]; exact g1
  · rw [oY.2.2.2.1]; have := oX.2.2.2.1; omega
  · rw [oY.2.2.2.2.1]; have := oX.2.2.2.2.1; omega
  · intro b hl hc
    have hnD : ¬ D b := fun hd => (hD b hd).elim hc (fun hn => hn hl)
    obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8⟩ := slots1 b hl hc
    have hRX : (restoreRegions h X [⟨p, n⟩]).live b := by
      unfold Heap.live; rw [r1, r2, r3, r4, r5, r6, r7]; exact hl
    have agreeRestore : AgreeAt X Y b → AgreeAt (restoreRegions h X [⟨p, n⟩]) (restoreRegions h Y [⟨p, n⟩]) b := by
      intro ag
      rw [restore_single, restore_single]
      unfold restoreOne
      cases p with
      | null => exact ag
      | ref r off =>
        dsimp only
        cases Space.get h r with
        | none => exact ag
        | some a => exact agree_put ag r a
    have hXl : X.live b := by
      rw [restore_single] at hRX
      unfold restoreOne at hRX
      cases hp : p with
      | null => rw [hp] at hRX; exact hRX
      | ref r off =>
        rw [hp] at hRX
        dsimp only at hRX
        cases ha : Space.get h r with
        | none => rw [ha] at hRX; exact hRX
        | some a =>
          rw [ha] at hRX
          rcases live_of_put hRX with e | e
          · subst e
            obtain ⟨a', ha', _⟩ := cells1 ⟨p, n⟩ (List.mem_singleton.mpr rfl) _ off a hp ha
            exact Or.inl (by
              have : X.bytes b = some a' := ha'
              rw [this]; intro x; cases x)
          · exact e
    obtain ⟨q1, q2, q3, q4, q5, q6, q7, q8⟩ := slots2 b hXl hnD
    obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8⟩ := agreeRestore ⟨q1, q2, q3, q4, q5, q6, q7, q8⟩
    exact ⟨t1.trans r1, t2.trans r2, t3.trans r3, t4.trans r4, t5.trans r5, t6.trans r6, t7.trans r7, t8.trans r8⟩
  · intro region mem r off a hp ha
    obtain ⟨a', ha', hsz, hout⟩ := cells1 region mem r off a hp ha
    have hp' : p = .ref r off := by
      rcases List.mem_singleton.1 mem with rfl
      exact hp
    exact ⟨a', by rw [hget r off hp']; exact ha', hsz, hout⟩

#print axioms bufferFrame_extend

/-! ## `gz_error` leaves the decoder records alone -/

theorem istates_none_of_gz {h : Heap} (u : Zlib.Gzlib.Spec.Uniq h) {b : Nat} {g : GzState}
    (e : h.gzstates b = some g) : h.istates b = none := by
  have hb := u b
  rw [e] at hb
  cases hi : h.istates b with
  | none => rfl
  | some x => rw [hi] at hb; simp only [Zlib.Gzlib.Spec.cnt_some] at hb; omega

theorem istates_none_of_bytes {h : Heap} (u : Zlib.Gzlib.Spec.Uniq h) {b : Nat} {a : Array UInt8}
    (e : h.bytes b = some a) : h.istates b = none := by
  have hb := u b
  rw [e] at hb
  cases hi : h.istates b with
  | none => rfl
  | some x => rw [hi] at hb; simp only [Zlib.Gzlib.Spec.cnt_some] at hb; omega

/-- The message block of a handle in `GzInv` holds bytes. -/
theorem GzInv.msg_bytes {h : Heap} {i : Nat} {s : GzState} (inv : GzInv h i s) {b : Nat}
    (hb : blkOf s.msg = some b) : ∃ a, h.bytes b = some a := by
  rcases inv.common.msg with hn | ⟨_, _, mb, a, hp, ha, _, _⟩
  · rw [hn] at hb; cases hb
  · rw [hp] at hb; cases hb; exact ⟨a, ha⟩

/-- **`gz_error` writes no decoder record**, read from its post-condition. -/
theorem errPost_istates {h after : Heap} {i : Nat} {s s' : GzState} {err : Int32} (inv : GzInv h i s)
    (post : ErrPost h i s err after s') : ∀ b, after.istates b = h.istates b := by
  obtain ⟨inv', -, -, fr, lc, -, -, -, -⟩ := post
  intro b
  have u := inv.common.uniq
  have u' := inv'.common.uniq
  have afterNone : ¬ (h.live b ∧ ¬ blkOf s.msg = some b) → after.istates b = none := by
    intro hn
    cases ha : after.istates b with
    | none => rfl
    | some x =>
      exfalso
      have hl : after.live b := Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by rw [ha]; intro e; cases e))))))
      rcases (lc b).1 hl with h1 | ⟨hm, _⟩
      · exact hn h1
      · obtain ⟨a, hab⟩ := GzInv.msg_bytes inv' hm
        rw [istates_none_of_bytes u' hab] at ha
        cases ha
  by_cases hl : h.live b
  · by_cases hc : b = i ∨ blkOf s.msg = some b
    · rcases hc with e | hm
      · subst e
        rw [istates_none_of_gz u inv.common.record, istates_none_of_gz u' inv'.common.record]
      · obtain ⟨a, hab⟩ := GzInv.msg_bytes inv hm
        rw [istates_none_of_bytes u hab]
        exact afterNone (fun h1 => h1.2 hm)
    · exact (fr.2.2.2.2.2 b hl hc).2.2.2.2.2.1
  · have h0 : h.istates b = none := by
      cases hh : h.istates b with
      | none => rfl
      | some x => exact absurd (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by rw [hh]; intro e; cases e))))))) hl
    rw [h0]
    exact afterNone (fun h1 => hl h1.1)

/-! ## The failure report -/

/-- **`gz_load`'s failure report.** After the loop (`LoadInv`), when the last `read` failed and it was not a stall
after some bytes, the tail sets `again` on a stall, borrows `strerror(errno)`, reports `gz_error(Z_ERRNO, ...)` and
returns `(-1, have)`, with the open descriptors kept and `GzPost` over the buffer region. The recorded error is
not `Z_OK`. -/
theorem gz_load_error_tail (i : Nat) (buf : BPtr) (len : UInt32) (h : Heap) (fs : Fs) (s : GzState)
    (hu : GzInvUpToOutput h i s) (hm : s.mode = GZ_READ) (hsz : s.size ≠ 0)
    (hw : Writable h buf len.toNat)
    (hroot : (∃ b off, buf = .ref (.blk b) off ∧ DataBuf (clearOut s) b) ∨
      (∀ b, ByteRoot buf b → ¬ GzOwned h i s b))
    (l : Zlib.Gzread.LoadLoop) (fs' : Fs) (H : Heap)
    (linv : LoadInv i buf len { s with again := 0 } (putGz h i { s with again := 0 }) { fs with errno := 0 } l fs' H)
    (herr : l.ret < 0 ∧ ¬ (BLOCKED fs'.errno = true ∧ l.«have» ≠ 0))
    (heofin : s.eof ≠ 0 → s.strm.avail_in = 0) :
    ∃ fs'' after, loadTail i l fs' H = .ok (((-1, l.«have»), fs''), after) ∧ fs'' = fs' ∧ FdsKept fs fs'' ∧
      (∀ k, after.istates k = h.istates k) ∧ GzPost h i s [⟨buf, len.toNat⟩] fs'' after GzInvUpToOutput ∧
      ∃ ag ef e m, after.gzstates i = some { s with again := ag, eof := ef, err := e, msg := m } ∧
        (e = s.err ∨ e = Z_ERRNO ∨ e = Z_MEM_ERROR) ∧ e ≠ Z_OK ∧ (ag ≠ 0 → ef = s.eof) := by
  have hs : h.gzstates i = some s := hu.1
  have inv : GzInv (putGz h i (clearOut s)) i (clearOut s) := hu.2
  have linv0 := linv
  have histH : ∀ k, H.istates k = h.istates k := fun k => by rw [linv.istates]; rfl
  obtain ⟨hle, hrecH, ginvH, -, -, hfsH, hkeptH, -, -, -⟩ := linv
  let s1 : GzState := { s with again := 0 }
  have hm1 : s1.mode = GZ_READ := hm
  -- the flag `again`
  let ag : Int32 := if BLOCKED fs'.errno = true then 1 else 0
  have hag : ag = 0 ∨ ag = 1 := by
    by_cases hb : BLOCKED fs'.errno = true
    · right; simp [ag, hb]
    · left; simp [ag, hb]
  let S2 : GzState := { s1 with again := ag, eof := s.eof }
  have hu2 : GzInvUpToOutput (putGz H i S2) i S2 :=
    upToOutput_flags ⟨hrecH, ginvH⟩ hm1 ag s.eof hag (inv.reader hm).flags.1 (fun hz => absurd hz hsz)
      (fun _ he => heofin he)
  have hs2 : (putGz H i S2).gzstates i = some S2 := hu2.1
  -- the borrow of `strerror`
  let H3 : Heap := { putGz H i S2 with libcErrorBorrow := some (Zlib.GzFs.Proofs.nextErrorEpoch (putGz H i S2), fs'.errno) }
  have hz3 : zstrerror fs' (putGz H i S2) = .ok ((.ref (.str (libcErrnoIndex
      (Zlib.GzFs.Proofs.nextErrorEpoch (putGz H i S2)) fs'.errno)) 0, fs'), H3) := Zlib.GzFs.Proofs.zstrerror_run _ _
  have hu3 : GzInvUpToOutput H3 i S2 := by
    refine ⟨hs2, ?_⟩
    have fr3 : Frame (putGz (putGz H i S2) i (clearOut S2)) (putGz H3 i (clearOut S2))
        (fun b => ¬ GzOwned (putGz (putGz H i S2) i (clearOut S2)) i (clearOut S2) b) :=
      ⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _, fun _ _ _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
    exact (hu2.2.frame_core fr3 hu2.2.common.fresh hu2.2.common.uniq hu2.2.common.globals
      (ZlibF.PlatformMemory.ByteObjectsFit.of_storage_eq hu2.2.common.fit rfl rfl rfl)).1
  have hcs := Zlib.GzFs.Proofs.zstrerror_cstring hz3
  obtain ⟨after, s4, run4, hs4, shape4, post4⟩ := gz_error_upToOutput hu3 Z_ERRNO _
    (Or.inr ⟨_, hcs, fun b hb => by cases hb⟩)
  have hist4 : ∀ k, after.istates k = h.istates k := fun k => by
    have := errPost_istates hu3.2 post4 k
    exact this.trans (histH k)
  obtain ⟨inv4, -, herr4, fr4, lc4, nolive4, -, ng4, keep4⟩ := post4
  -- the run of the tail
  have hrun : loadTail i l fs' H = .ok (((-1, l.«have»), fs'), after) := by
    unfold loadTail
    rw [if_pos herr.1]
    have hge : getErrno fs' H = .ok ((fs'.errno, fs'), H) := rfl
    by_cases hb : BLOCKED fs'.errno = true
    · have h0 : l.«have» = 0 := Classical.byContradiction fun hn => herr.2 ⟨hb, hn⟩
      have hne : (l.«have» != 0) = false := by simp [h0]
      have hS2 : putGz H i S2 = setS H i { s1 with again := 1 } := by
        show putGz H i { s1 with again := ag, eof := s.eof } = _
        simp only [ag, hb, ite_true]; rfl
      have run4' : Zlib.Gzlib.gz_error (gzSt i) Z_ERRNO _ H3 = .ok ((), after) := run4
      simp only [g_bind_app, g_lift_app, liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, hge, hb,
        ite_true, updS_run hrecH, hne, Bool.false_eq_true, ite_false, g_pure_app]
      rw [← hS2, hz3]
      simp only [gzSt] at run4'
      simp only [run4', g_pure_app]
    · have hS2 : putGz H i S2 = H := by
        show putGz H i { s1 with again := ag, eof := s.eof } = H
        simp only [ag, hb, Bool.false_eq_true, ite_false]
        exact upd_self_heap hrecH
      have run4' : Zlib.Gzlib.gz_error (gzSt i) Z_ERRNO _ H3 = .ok ((), after) := run4
      simp only [g_bind_app, g_lift_app, liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, hge, hb,
        Bool.false_eq_true, ite_false]
      rw [← hS2, hz3]
      simp only [gzSt] at run4'
      simp only [run4', g_pure_app]
  -- the post-condition
  obtain ⟨bfX, hliveX, hownX⟩ := load_frame i buf len h s { fs with errno := 0 } fs' l H S2 hs hw linv0
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hsame4 : s4.path = S2.path ∧ s4.msg = s4.msg ∧ s4.«in» = S2.«in» ∧ s4.out = S2.out ∧ s4.size = S2.size ∧
      s4.mode = S2.mode ∧ s4.direct = S2.direct ∧ s4.strm = S2.strm := by
    rw [shape4]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have liveX3 : ∀ b, (putGz H3 i (clearOut S2)).live b ↔ (putGz H i S2).live b := fun b => putGz_live hs2 b
  have liveA : ∀ b, (putGz after i (clearOut s4)).live b ↔ after.live b := fun b => putGz_live hs4 b
  have ownA : ∀ b, GzOwned (putGz after i (clearOut s4)) i (clearOut s4) b ↔ GzOwned after i s4 b :=
    putGz_owned (s' := clearOut s4) hs4 ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have ownX3 : ∀ b, GzOwned (putGz H3 i (clearOut S2)) i (clearOut S2) b ↔ GzOwned (putGz H i S2) i S2 b :=
    putGz_owned (s' := clearOut S2) hs2 ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hsmsg : S2.msg = s.msg := rfl
  have msgOwned : ∀ b, blkOf s.msg = some b → GzOwned h i s b := by
    intro b hb
    rcases inv.common.msg with hn | ⟨_, _, mb, _, hp, _⟩
    · have : s.msg = .null := hn
      rw [this] at hb; cases hb
    · have hp' : s.msg = .ref (.blk mb) 0 := hp
      rw [hp'] at hb; cases hb; exact Or.inr (Or.inr (Or.inl hp'))
  have ownedLive : ∀ b, GzOwned h i s b → h.live b := fun b ho =>
    (putGz_live hs b).1 (inv.common.live b
      ((putGz_owned (s' := clearOut s) hs ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ b).2 ho))
  -- the heap change of the report, seen on the actual heaps
  have frXY : Frame (putGz H i S2) after (fun b => b = i ∨ blkOf s.msg = some b) := by
    obtain ⟨f1, f2, f3, f4, f5, f6⟩ := fr4
    refine ⟨f1, f2, f3, f4, f5, fun b hl hc => ?_⟩
    have hbi : b ≠ i := fun e => hc (Or.inl e)
    have hl3 : (putGz H3 i (clearOut S2)).live b := (liveX3 b).2 hl
    obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ := f6 b hl3 hc
    refine ⟨e1, e2, e3, e4, e5, e6, ?_, e8⟩
    have e7' : upd after.gzstates i (some (clearOut s4)) b = upd H3.gzstates i (some (clearOut S2)) b := e7
    rw [upd_ne _ _ _ _ hbi, upd_ne _ _ _ _ hbi] at e7'
    exact e7'
  have hD : ∀ b, (b = i ∨ blkOf s.msg = some b) → GzOwned h i s b ∨ ¬ h.live b := by
    rintro b (rfl | hb)
    · exact Or.inl (Or.inl rfl)
    · exact Or.inl (msgOwned b hb)
  -- the buffer's block is neither the record nor the message
  have notD : ∀ r off c, buf = .ref r off → (r = .blk c ∨ r = .dstate_depth c) → ¬ (c = i ∨ blkOf s.msg = some c) := by
    intro r off c hp hrc hc
    rcases hroot with ⟨b0, off0, hb0, hdb⟩ | hno
    · rw [hp] at hb0
      cases hb0
      rcases hrc with e | e
      · cases e
        obtain ⟨hne, -, -, hnm⟩ := GzInv.data_separate inv hdb
        rcases hc with e | hmc
        · exact hne e
        · rcases inv.common.msg with hn | ⟨_, _, mb, _, hpm, _⟩
          · have : s.msg = .null := hn
            rw [this] at hmc; cases hmc
          · have hpm' : s.msg = .ref (.blk mb) 0 := hpm
            rw [hpm'] at hmc; cases hmc
            exact hnm hpm
      · cases e
    · have hroot' : ByteRoot buf c := by
        rw [hp]; rcases hrc with rfl | rfl <;> exact rfl
      rcases hc with rfl | hmc
      · exact hno _ hroot' (Or.inl rfl)
      · exact hno c hroot' (msgOwned c hmc)
  have hget : ∀ r off, buf = .ref r off → Space.get after r = Space.get (putGz H i S2) r := by
    intro r off hp
    obtain ⟨_, _, _, _, _, frs⟩ := frXY
    rcases hw with ⟨hn, _⟩ | ⟨r', off', a, hp', ha, hro, _⟩
    · rw [hn] at hp; cases hp
    rw [hp] at hp'
    cases hp'
    obtain ⟨a', ha', _⟩ := bfX.2 ⟨buf, len.toNat⟩ (List.mem_singleton.mpr rfl) r off a hp ha
    cases r with
    | blk c =>
      have hbx : (putGz H i S2).bytes c = some a' := ha'
      have hl : (putGz H i S2).live c := Or.inl (by rw [hbx]; intro x; cases x)
      exact (frs c hl (notD _ _ c hp (Or.inl rfl))).1
    | dstate_depth c =>
      have hdx : ((putGz H i S2).dstates c).map (·.depth) = some a' := ha'
      have hl : (putGz H i S2).live c := by
        refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
        intro e; rw [e] at hdx; cases hdx
      have e5 := (frs c hl (notD _ _ c hp (Or.inr rfl))).2.2.2.2.1
      show (after.dstates c).map (·.depth) = ((putGz H i S2).dstates c).map (·.depth)
      rw [e5]
    | str j => simp [Space.ro] at hro
    | st_dist_code => simp [Space.ro] at hro
    | st_length_code => simp [Space.ro] at hro
  have bf := bufferFrame_extend bfX frXY hD hget
  -- liveness and ownership
  have ownLive4 : ∀ b, GzOwned after i s4 b → after.live b := fun b ho =>
    (liveA b).1 (inv4.common.live b ((ownA b).2 ho))
  have msg4 : ∀ b, blkOf s4.msg = some b → GzOwned after i s4 b := by
    intro b hb
    rcases inv4.common.msg with hn | ⟨_, _, mb, _, hpm, _⟩
    · have : s4.msg = .null := hn
      rw [this] at hb; cases hb
    · have hpm' : s4.msg = .ref (.blk mb) 0 := hpm
      rw [hpm'] at hb; cases hb; exact Or.inr (Or.inr (Or.inl hpm'))
  refine ⟨fs', after, hrun, rfl, hkeptH, hist4, ⟨hfsH, s4, ⟨hs4, inv4⟩, by rw [hsame4.2.2.2.2.2.1],
    by rw [shape4], bf, ?_, ?_⟩, ag, s.eof, s4.err, s4.msg, by rw [hs4, shape4],
    herr4.elim (fun e => Or.inr (Or.inl e)) (fun e => Or.inr (Or.inr e.1)),
    herr4.elim (fun e => by show (clearOut s4).err ≠ Z_OK; rw [e]; decide)
      (fun e => by show (clearOut s4).err ≠ Z_OK; rw [e.1]; decide), fun _ => rfl⟩
  · intro b
    have L2 := lc4 b
    simp only [liveA, liveX3, hliveX] at L2
    rw [L2]
    constructor
    · rintro (⟨hl, hnm⟩ | ⟨hnew, hnl⟩)
      · refine Or.inl ⟨hl, fun ⟨ho, hno⟩ => hno ?_⟩
        exact (ownA b).1 (keep4 b ((ownX3 b).2 ((hownX b).2 ho)) hnm)
      · exact Or.inr ⟨msg4 b hnew, hnl⟩
    · rintro (⟨hl, hk⟩ | ⟨ho, hnl⟩)
      · by_cases hmb : blkOf s.msg = some b
        · have ho : GzOwned after i s4 b := Classical.byContradiction fun hn => hk ⟨msgOwned b hmb, hn⟩
          have := (L2.1) (ownLive4 b ho)
          exact this
        · exact Or.inl ⟨hl, hmb⟩
      · have hal := ownLive4 b ho
        rw [L2] at hal
        exact hal
  · intro b ho
    rcases ng4 b ((ownA b).2 ho) with h1 | h1
    · exact Or.inl ((hownX b).1 ((ownX3 b).1 h1))
    · exact Or.inr (fun hl => h1 ((liveX3 b).2 ((hliveX b).2 hl)))


/-- The run of `gz_load` and everything known of it. -/
theorem gz_load_key (i : Nat) (buf : BPtr) (len : UInt32) (h : Heap) (fs : Fs) (s : GzState)
    (hu : GzInvUpToOutput h i s) (hm : s.mode = GZ_READ) (hsz : s.size ≠ 0) (hfs : FileSystem fs)
    (hw : Writable h buf len.toNat)
    (hroot : (∃ b off, buf = .ref (.blk b) off ∧ DataBuf (clearOut s) b) ∨
      (∀ b, ByteRoot buf b → ¬ GzOwned h i s b))
    (heofin : s.eof ≠ 0 → s.strm.avail_in = 0) :
    ∃ r fs'' after, Zlib.Gzread.gz_load (gzSt i) buf len fs h = .ok ((r, fs''), after) ∧ (∀ k, after.istates k = h.istates k) ∧
      ((r.1 = 0 ∨ r.1 = -1) ∧ r.2.toNat ≤ len.toNat ∧ FdsKept fs fs'' ∧
      GzPost h i s [⟨buf, len.toNat⟩] fs'' after GzInvUpToOutput ∧
      (∃ ag ef e m, after.gzstates i = some { s with again := ag, eof := ef, err := e, msg := m } ∧
        (e = s.err ∨ e = Z_ERRNO ∨ e = Z_MEM_ERROR) ∧
        (r.1 = 0 → e = s.err) ∧ (r.1 = -1 → e ≠ Z_OK) ∧ (r.1 = 0 → r.2 = 0 → ef = 1) ∧
        (ag ≠ 0 → ef = s.eof)) ∧
      BudgetAcc s.fd fs fs'' r.2.toNat) := by
  obtain ⟨l, fs', H, hrun, linv, hle, hok⟩ := gz_load_paths i buf len h fs s hu hm hsz hfs hw hroot heofin
  have key : ∃ r fs'' after, Zlib.Gzread.gz_load (gzSt i) buf len fs h = .ok ((r, fs''), after) ∧ (∀ k, after.istates k = h.istates k) ∧
      (r.1 = 0 ∨ r.1 = -1) ∧ r.2.toNat ≤ len.toNat ∧ FdsKept fs fs'' ∧
      GzPost h i s [⟨buf, len.toNat⟩] fs'' after GzInvUpToOutput ∧
      (∃ ag ef e m, after.gzstates i = some { s with again := ag, eof := ef, err := e, msg := m } ∧
        (e = s.err ∨ e = Z_ERRNO ∨ e = Z_MEM_ERROR) ∧
        (r.1 = 0 → e = s.err) ∧ (r.1 = -1 → e ≠ Z_OK) ∧ (r.1 = 0 → r.2 = 0 → ef = 1) ∧
        (ag ≠ 0 → ef = s.eof)) ∧
      BudgetAcc s.fd fs fs'' r.2.toNat := by
    have hbud : BudgetAcc s.fd fs fs' l.«have».toNat := linv.2.2.2.2.2.2.2.2.2
    by_cases herr : l.ret < 0 ∧ ¬ (BLOCKED fs'.errno = true ∧ l.«have» ≠ 0)
    · obtain ⟨fs'', after, ht, hfe, hk, hist, hp, ag, ef, e, m, hr, hdis, hok', hae⟩ :=
        gz_load_error_tail i buf len h fs s hu hm hsz hw hroot l fs' H linv herr heofin
      subst hfe
      exact ⟨_, fs'', after, hrun.trans ht, hist, Or.inr rfl, hle, hk, hp,
        ⟨ag, ef, e, m, hr, hdis, (fun h0 => absurd (show (-1 : Int32) = 0 from h0) (by decide)), (fun _ => hok'),
          (fun h0 => absurd (show (-1 : Int32) = 0 from h0) (by decide)), hae⟩, hbud⟩
    · obtain ⟨fs'', after, ht, hfe, hk, hist, hp, ag, ef, hr, hef, hae⟩ := hok herr
      subst hfe
      exact ⟨_, fs'', after, hrun.trans ht, hist, Or.inl rfl, hle, hk, hp,
        ⟨ag, ef, s.err, s.msg, hr, Or.inl rfl, (fun _ => rfl), (fun h0 => absurd (show (0 : Int32) = -1 from h0) (by decide)),
          (fun _ h0 => hef h0), hae⟩, hbud⟩
  exact key

/-- **`gz_load(state, buf, len, &have)` is safe** (the skeleton statement `gz_load_safe`, with three premises found
in the proof: the reader has its buffers, `size ≠ 0`, since only then can a stall set `again` within the invariant;
the buffer is a data buffer of the handle or memory the handle does not own; and at the end of the input there is no
pending input, `eof ≠ 0 → avail_in = 0`, since a stall then sets `again` with `eof` kept (`GzReadInv.againEof`):
`gz_avail` calls it with `eof = 0`, the COPY load of `gz_fetch` with `avail_in = 0`). It does not fault, returns, and every
result is `0` or `-1` with `have ≤ len`, the open descriptors kept and `GzPost` over `[buf, buf + len)`. A `0` keeps
the error, a `-1` records one that is not `Z_OK`, a `0` with nothing read sets `eof`, and a stall keeps `eof`. -/
theorem gz_load_safe (i : Nat) (buf : BPtr) (len : UInt32) (h : Heap) (fs : Fs) (s : GzState)
    (hu : GzInvUpToOutput h i s) (hm : s.mode = GZ_READ) (hsz : s.size ≠ 0) (hfs : FileSystem fs)
    (hw : Writable h buf len.toNat)
    (hroot : (∃ b off, buf = .ref (.blk b) off ∧ DataBuf (clearOut s) b) ∨
      (∀ b, ByteRoot buf b → ¬ GzOwned h i s b))
    (heofin : s.eof ≠ 0 → s.strm.avail_in = 0) :
    RunSafe (Zlib.Gzread.gz_load (gzSt i) buf len) fs h True fun r fs' after =>
      (r.1 = 0 ∨ r.1 = -1) ∧ r.2.toNat ≤ len.toNat ∧ FdsKept fs fs' ∧
      GzPost h i s [⟨buf, len.toNat⟩] fs' after GzInvUpToOutput ∧
      (∃ ag ef e m, after.gzstates i = some { s with again := ag, eof := ef, err := e, msg := m } ∧
        (e = s.err ∨ e = Z_ERRNO ∨ e = Z_MEM_ERROR) ∧
        (r.1 = 0 → e = s.err) ∧ (r.1 = -1 → e ≠ Z_OK) ∧ (r.1 = 0 → r.2 = 0 → ef = 1) ∧
        (ag ≠ 0 → ef = s.eof)) ∧
      BudgetAcc s.fd fs fs' r.2.toNat := by
  obtain ⟨r, fs'', after, run, -, post⟩ := gz_load_key i buf len h fs s hu hm hsz hfs hw hroot heofin
  refine ⟨fun e he => ?_, fun _ => ⟨r, fs'', after, run⟩, fun r' fs3 after' he => ?_⟩
  · rw [run] at he; cases he
  · rw [run] at he
    cases he
    exact post

/-- `gz_load` writes no decoder record. -/
theorem gz_load_istates (i : Nat) (buf : BPtr) (len : UInt32) (h : Heap) (fs : Fs) (s : GzState)
    (hu : GzInvUpToOutput h i s) (hm : s.mode = GZ_READ) (hsz : s.size ≠ 0) (hfs : FileSystem fs)
    (hw : Writable h buf len.toNat)
    (hroot : (∃ b off, buf = .ref (.blk b) off ∧ DataBuf (clearOut s) b) ∨
      (∀ b, ByteRoot buf b → ¬ GzOwned h i s b))
    (heofin : s.eof ≠ 0 → s.strm.avail_in = 0)
    {r : Int32 × UInt32} {fs' : Fs} {after : Heap}
    (run : Zlib.Gzread.gz_load (gzSt i) buf len fs h = .ok ((r, fs'), after)) : ∀ k, after.istates k = h.istates k := by
  obtain ⟨r2, fs2, after2, run2, hist, -⟩ := gz_load_key i buf len h fs s hu hm hsz hfs hw hroot heofin
  rw [run2] at run
  cases run
  exact hist

#print axioms gz_load_error_tail
#print axioms gz_load_safe

end ZlibF.Spec.Public.GzRead
