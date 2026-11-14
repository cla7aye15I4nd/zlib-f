import ZlibF.Proof.«gzlib.c.error-inv»

/-!
# gz safety: `gz_error` inside a call, where the invariant holds of a changed record

Inside a reading or writing call the invariant holds of the record with some fields put aside: the buffered
output (`GzInvUpToOutput`, `clearOut`), the pending skip, or the pending input (`clearIn`). `gz_error` reads only
`path`, `msg` and `err` and writes only `msg` and `err`. So its run on the actual heap is its run on the heap with
the changed record, with the fields put back.

`gz_error_rec` states this for a map `T` of records that keeps `path`, `msg` and `err` and commutes with writing
`err` and `msg` (`RecMap`). The run on the actual heap is computed by the same source steps as in
`gzlib.c.error-inv` (`gz_error_prefix'` and the tails). The post-condition is that of `GzInv.gz_error_full` in the
world of `T`.
-/

namespace ZlibF.Spec.Public
open C Zlib.GzFs Zlib.GzFs.MessageStore
open Zlib.Gzlib.Proofs (freeStr)
set_option autoImplicit false

/-- A map of records that keeps what `gz_error` reads and commutes with what it writes. -/
structure RecMap (T : GzState → GzState) : Prop where
  path : ∀ v, (T v).path = v.path
  msg : ∀ v, (T v).msg = v.msg
  err : ∀ v, (T v).err = v.err
  upd : ∀ v e m, T { v with err := e, msg := m } = { T v with err := e, msg := m }

theorem recMap_clearOut : RecMap clearOut :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ _ _ => rfl⟩

namespace GzErrorRun
open Zlib.Gzlib.Spec (setS)

/-- **Prefix**, from the record's message fields alone. -/
theorem gz_error_prefix' {h : Heap} {i : Nat} {s : GzState} (hs : h.gzstates i = some s)
    (hmsg : s.msg = .null ∨ ∃ mb a, s.msg = .ref (.blk mb) 0 ∧ h.bytes mb = some a ∧ h.ro mb = false ∧
      s.err ≠ Z_MEM_ERROR) (err : Int32) (msg : BPtr) :
    Zlib.Gzlib.gz_error (gzSt i) err msg h =
      Zlib.Gzlib.gz_error (gzSt i) err msg
        (putGz (freeStr h s.msg) i { s with eof := s.eof, past := s.past, msg := .null, err := err }) := by
  unfold Zlib.Gzlib.gz_error
  rcases hmsg with hn | ⟨mb, a, hp, ha, hro, hne⟩
  · gsimp [gzSt, hs, hn, putGz, freeStr, setS, upd_upd]
  · gsimp [gzSt, hs, hp, hne, Zlib.Gzlib.Proofs.freeB_blk_run ha hro, putGz, freeStr, setS, upd_upd]

end GzErrorRun

theorem freeStr_putGz (h : Heap) (i : Nat) (v : GzState) (p : BPtr) :
    freeStr (putGz h i v) p = putGz (freeStr h p) i v := by
  unfold freeStr; split <;> rfl

theorem putGz_putGz' (h : Heap) (i : Nat) (v w : GzState) : putGz (putGz h i v) i w = putGz h i w := by
  simp [putGz, upd_upd]

theorem cstring_putGz' (h : Heap) (i : Nat) (v : GzState) (p : BPtr) (xs : List UInt8) :
    CString (putGz h i v) p xs ↔ CString h p xs := putGz_cstring p xs

namespace GzErrorRun

theorem finalH_rec (X : Heap) (i : Nat) (u v v' : GzState) (e : Int32) (xs t : List UInt8) :
    finalH (putGz X i u) i v' e xs t = putGz (finalH X i v e xs t) i (copiedS X v' e) := by
  simp only [finalH_eq, putGz, upd_upd, copiedS, garb]

theorem refused_rec (X : Heap) (i : Nat) (u v v' : GzState) :
    Zlib.Gzlib.MessageRefusal.refusedMessageHeap (putGz X i u) i v' =
      putGz (Zlib.Gzlib.MessageRefusal.refusedMessageHeap X i v) i
        (Zlib.Gzlib.MessageRefusal.refusedMessageState v') := by
  simp only [Zlib.Gzlib.MessageRefusal.refusedMessageHeap, putGz, Zlib.Gzlib.Spec.setS, upd_upd]

end GzErrorRun

open GzErrorRun in
/-- **`gz_error` on a heap whose record is in the invariant after a map `T`.** The run on the actual heap returns;
the record after it is the old one with `err` and `msg` changed, and the post-condition of
`GzInv.gz_error_full` holds in the world of `T`. -/
theorem gz_error_rec {T : GzState → GzState} (hT : RecMap T) {H : Heap} {i : Nat} {s : GzState}
    (hs : H.gzstates i = some s) (inv : GzInv (putGz H i (T s)) i (T s)) (err : Int32) (msg : BPtr)
    (hmsg : msg = .null ∨ ∃ t, CString H msg t ∧ ∀ b, ByteRoot msg b → ¬ GzOwned (putGz H i (T s)) i (T s) b)
    (he : err ≠ Z_STREAM_END) :
    ∃ after s', C.run (Zlib.Gzlib.gz_error (gzSt i) err msg) H = .ok ((), after) ∧ after.gzstates i = some s' ∧
      s' = { s with err := s'.err, msg := s'.msg } ∧
      ErrPost (putGz H i (T s)) i (T s) err (putGz after i (T s')) (T s') := by
  have hTm := hT.msg s
  have hTe := hT.err s
  -- the prefix on the actual heap
  have hpre : s.msg = .null ∨ ∃ mb a, s.msg = .ref (.blk mb) 0 ∧ H.bytes mb = some a ∧ H.ro mb = false ∧
      s.err ≠ Z_MEM_ERROR := by
    rcases inv.common.msg with hn | ⟨_, _, mb, a, hp, ha, hro, _⟩
    · exact Or.inl (hTm ▸ hn)
    · refine Or.inr ⟨mb, a, hTm ▸ hp, ha, hro, fun he => ?_⟩
      have hnull := inv.common.memerr (hTe.trans he)
      rw [hp] at hnull
      cases hnull
  have hrun0 := gz_error_prefix' hs hpre err msg
  have c := cleared_of inv err he
  rw [hTm] at c
  -- the two worlds after the prefix
  have eS : ({ T s with eof := (T s).eof, past := (T s).past, msg := .null, err := err } : GzState) =
      T { s with eof := s.eof, past := s.past, msg := .null, err := err } := (hT.upd s err .null).symm
  rw [eS, freeStr_putGz, putGz_putGz'] at c
  generalize hS1 : ({ s with eof := s.eof, past := s.past, msg := .null, err := err } : GzState) = S1 at c hrun0
  generalize hH1 : putGz (freeStr H s.msg) i S1 = H1 at hrun0
  have eH : putGz (freeStr H s.msg) i (T S1) = putGz H1 i (T S1) := by rw [← hH1, putGz_putGz']
  rw [eH] at c
  have hs1 : H1.gzstates i = some S1 := by rw [← hH1]; simp [putGz]
  have hm1 : S1.msg = .null := by rw [← hS1]
  have he1 : S1.err = err := by rw [← hS1]
  have hshape : ∀ e m, ({ S1 with err := e, msg := m } : GzState) = { s with err := e, msg := m } := by
    intro e m; rw [← hS1]
  have hsame : Zlib.Gzlib.Spec.setS H1 i S1 = H1 := by
    have e := upd_self H1.gzstates i S1 hs1
    simp only [Zlib.Gzlib.Spec.setS, e]
  have run : ∀ after, Zlib.Gzlib.gz_error (gzSt i) err msg H1 = .ok ((), after) →
      C.run (Zlib.Gzlib.gz_error (gzSt i) err msg) H = .ok ((), after) := by
    intro after e
    show Zlib.Gzlib.gz_error _ _ _ H = _
    rw [hrun0, e]
  have hlive1 : ∀ b, (putGz H1 i (T S1)).live b ↔ H1.live b := putGz_live hs1
  have shape1 : S1 = { s with err := S1.err, msg := S1.msg } :=
    (show S1 = { S1 with err := S1.err, msg := S1.msg } from rfl).trans (hshape _ _)
  rcases hmsg with hnull | ⟨t, ct, hno⟩
  · subst hnull
    exact ⟨H1, S1, run _ (by rw [tail_null hs1 hm1 he1, hsame]), hs1, shape1, post_stop c⟩
  by_cases hmem : err = Z_MEM_ERROR
  · subst hmem
    exact ⟨H1, S1, run _ (by rw [tail_memerr hs1 hm1 he1, hsame]), hs1, shape1, post_stop c⟩
  obtain ⟨xs, hpxc, _⟩ := c.inv1.common.path
  have hpx : CString H1 S1.path xs := by
    rw [← hT.path S1]; exact (cstring_putGz' _ _ _ _ _).1 hpxc
  have ctc : CString (putGz H1 i (T S1)) msg t := c.keep msg t ((cstring_putGz' H i (T s) msg t).2 ct) hno
  have ct1 : CString H1 msg t := (cstring_putGz' _ _ _ _ _).1 ctc
  have hxs := cstring_len_fit c.inv1.common.fit hpxc
  have hts := cstring_len_fit c.inv1.common.fit ctc
  have fresh1 : Fresh H1 := fun b hb hl => c.inv1.common.fresh b hb ((hlive1 b).2 hl)
  by_cases hok : H1.allocOk H1.nalloc = true ∧ xs.length + t.length + 3 < C.mallocLimit
  · have pc := post_copied c hmem hpxc ctc hok.2
    rw [finalH_rec H1 i (T S1) S1 (T S1)] at pc
    have e2 : copiedS H1 (T S1) err = { T S1 with msg := .ref (.blk H1.nextBlk) 0 } := by
      show ({ T S1 with err := err, msg := .ref (.blk H1.nextBlk) 0 } : GzState) = _
      rw [← he1, ← hT.err S1]
    rw [e2] at pc
    have e1 : T (copiedS H1 S1 err) = { T S1 with msg := .ref (.blk H1.nextBlk) 0 } :=
      (hT.upd S1 err (.ref (.blk H1.nextBlk) 0)).trans e2
    refine ⟨_, copiedS H1 S1 err, run _ (tail_copied hs1 hm1 hmem hpx ct1 fresh1 hxs hts hok.1 hok.2),
      by rw [finalH_put]; simp [putGz], hshape err (.ref (.blk H1.nextBlk) 0), ?_⟩
    rw [e1]
    exact pc
  · have pr := post_refused c
    rw [refused_rec H1 i (T S1) S1 (T S1)] at pr
    refine ⟨_, Zlib.Gzlib.MessageRefusal.refusedMessageState S1,
      run _ (tail_refused hs1 hm1 hmem hpx ct1 hxs hts hok),
      by simp [Zlib.Gzlib.MessageRefusal.refusedMessageHeap, Zlib.Gzlib.Spec.setS], hshape Z_MEM_ERROR .null, ?_⟩
    have e1 : T (Zlib.Gzlib.MessageRefusal.refusedMessageState S1) =
        Zlib.Gzlib.MessageRefusal.refusedMessageState (T S1) := hT.upd S1 Z_MEM_ERROR .null
    rw [e1]
    exact pr

/-- `gz_error` inside a reading call: the invariant up to the buffered output is kept. -/
theorem gz_error_upToOutput {H : Heap} {i : Nat} {s : GzState} (hu : GzInvUpToOutput H i s) (err : Int32)
    (msg : BPtr)
    (hmsg : msg = .null ∨ ∃ t, CString H msg t ∧
      ∀ b, ByteRoot msg b → ¬ GzOwned (putGz H i (clearOut s)) i (clearOut s) b)
    (he : err ≠ Z_STREAM_END) :
    ∃ after s', C.run (Zlib.Gzlib.gz_error (gzSt i) err msg) H = .ok ((), after) ∧ after.gzstates i = some s' ∧
      s' = { s with err := s'.err, msg := s'.msg } ∧
      ErrPost (putGz H i (clearOut s)) i (clearOut s) err (putGz after i (clearOut s')) (clearOut s') :=
  gz_error_rec recMap_clearOut hu.1 hu.2 err msg hmsg he

#print axioms gz_error_rec
#print axioms gz_error_upToOutput

end ZlibF.Spec.Public
