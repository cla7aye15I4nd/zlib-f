import ZlibF.Proof.«gz.inv-clearerr»
import ZlibF.Proof.«gz.inv-put-scalars»
import ZlibF.Proof.«gzfs.error-message-store»
import ZlibF.Proof.«gzlib.c.error-message-refusal»

/-!
# gz safety: `gz_error` keeps `GzInv` (the skeleton's interface lemma `GzInv.gz_error`)

`gz_error(state, err, msg)` frees the old message (unless the code was `Z_MEM_ERROR`), clears the pointer and
stores `err`. With a message and a code other than `Z_MEM_ERROR` it then allocates
`strlen(path) + strlen(msg) + 3` bytes and formats `"%s%s%s"` of the path, `": "` and the message into them; a
refused allocation records `Z_MEM_ERROR` and no message.

The proof follows the source:

1. **Prefix.** The run on the handle's heap equals the run on the heap where the old message is already freed
   and the code stored (`gz_error_prefix`). `GzInv.clear_message` gives the invariant there.
2. **Tails**, from a record with no message:
   - no message, or `Z_MEM_ERROR`: nothing more happens (`tail_null`, `tail_memerr`);
   - refusal: the allocator returns NULL. That is an oracle failure or, since the runtime follows glibc, a
     request of `2^63` bytes or more (`tail_refused`). The code becomes `Z_MEM_ERROR`;
   - success: a fresh block receives the path, `": "`, the message and a NUL (`tail_copied`). The formatter's
     result is ignored by `gz_error`, so no `INT_MAX` bound on the message is needed (`snprintf_error_any`).
3. **The invariant after the copy.** The new block is outside everything the handle owned, so the heap change is
   a frame over blocks the handle does not own (`GzInv.frame_core`); then the record takes the new message
   (`GzInv.put_message`).

Each string lies in one byte object below `2^63` bytes (`ByteObjectsFit`, carried by `GzInv`), so the `size_t`
sum `strlen(path) + strlen(msg) + 3` does not wrap.

The results: `GzInv.gz_error` (the skeleton statement) and `GzInv.gz_error_own` (no grab: a block the handle owns
after the call that was live before was owned before).
-/

namespace ZlibF.Spec.Public
open C Zlib.GzFs Zlib.GzFs.MessageStore
open Zlib.Gzlib.Proofs (freeStr)
set_option autoImplicit false

/-! ## Strings and the formatter -/

/-- A C string in a heap whose byte objects fit holds fewer than `2^63 - 1` characters. -/
theorem cstring_len_fit {h : Heap} {p : BPtr} {xs : List UInt8} (fit : ZlibF.PlatformMemory.ByteObjectsFit h)
    (hc : CString h p xs) : xs.length + 1 < 2 ^ 63 := by
  rcases hc.1 with ⟨_, hn, _⟩ | ⟨r, off, a, _, ha, hle, _⟩
  · omega
  · have := fit r a ha
    unfold ZlibF.PlatformMemory.byteObjectLimit at this
    omega

theorem cstring_nonnull' {h : Heap} {p : BPtr} {xs : List UInt8} (hc : CString h p xs) : p ≠ .null := by
  intro hp
  rcases hc.1 with hn | ⟨r, off, a, he, _⟩
  · have := hn.2.1; omega
  · rw [hp] at he; cases he

/-- A C string keeps its bytes when the block of every view it reads keeps its bytes. -/
theorem cstring_views {h after : Heap} {p : BPtr} {xs : List UInt8} (hc : CString h p xs)
    (views : ∀ (r : BRef) (a : Array UInt8), Space.get h r = some a → Space.get after r = some a) :
    CString after p xs := by
  refine ⟨?_, hc.2⟩
  rcases hc.1 with hn | ⟨r, off, a, hp, ha, hf, he⟩
  · exact Or.inl hn
  · exact Or.inr ⟨r, off, a, hp, views r a ha, hf, he⟩

private theorem m_bind_assoc {α β γ : Type} (m : M α) (f : α → M β) (g : β → M γ) :
    (m >>= f) >>= g = m >>= (fun a => f a >>= g) := by
  funext h
  cases he : m h <;> simp [bind_app, he]

private theorem m_pure_bind {α β : Type} (a : α) (f : α → M β) :
    (pure a >>= f) = f a := rfl

/-- The formatter call of `gz_error` for every message length: the bytes stored are the same as in
`snprintf_error_copy_run`; only the returned count, which `gz_error` ignores, depends on `INT_MAX`. -/
theorem snprintf_error_any {h : Heap} {b : Nat} {a : Array UInt8}
    {path msg : BPtr} {xs es : List UInt8}
    (hp : CString h path xs) (he : CString h msg es)
    (hb : h.bytes b = some a) (hro : h.ro b = false)
    (hlen : a.size = xs.length + es.length + 3)
    (hsmall : xs.length + es.length + 3 < 2 ^ 64)
    (hslot : h.slotUsed h.nextBlk = false) :
    ∃ r, snprintf (.ref (.blk b) 0) (UInt64.ofNat (xs.length + es.length + 3)) errorFormatPointer
      [.str path, .str errorSeparatorPointer, .str msg] h =
        .ok (r, storedMessageHeap h b a (xs ++ [58,32] ++ es).toArray) := by
  let out := (xs ++ [58,32] ++ es).toArray
  have hsize : out.size = xs.length + es.length + 2 := by simp [out]; omega
  have hbytes : a.size = out.size + 1 := by omega
  have hread := Zlib.GzFs.Proofs.format_error_message
    (Zlib.GzFs.Proofs.cstring_of_CString hp) (error_separator_read h)
    (Zlib.GzFs.Proofs.cstring_of_CString he)
  have hformat : formatBytes #[37,115,37,115,37,115]
      [.str path, .str errorSeparatorPointer, .str msg] h = .ok (out, h) := by
    simpa [out] using hread.1
  have hnum : (UInt64.ofNat (xs.length + es.length + 3)).toNat = out.size + 1 := by
    rw [UInt64.toNat_ofNat_of_lt' (by omega)]
    omega
  have hne : UInt64.ofNat (xs.length + es.length + 3) ≠ 0 := by
    intro heq
    have ht := congrArg UInt64.toNat heq
    rw [hnum] at ht
    change out.size + 1 = 0 at ht
    omega
  have hnonempty : out.isEmpty = false := by simp [Array.isEmpty, hsize]
  have hstored := store_message_nul_run hb hro hbytes hnonempty hslot
  refine ⟨if out.size > 2147483647 then -1 else Int32.ofNat out.size, ?_⟩
  have result : (do
      let _ ← (do storeBytes (.ref (.blk b) 0) out
                  let p ← (Ptr.ref (BRef.blk b) 0).add out.size
                  store8 p 0)
      pure (if out.size > 2147483647 then -1 else Int32.ofNat out.size)) h =
        .ok (if out.size > 2147483647 then -1 else Int32.ofNat out.size, storedMessageHeap h b a out) := by
    rw [bind_app, hstored]
    rfl
  change snprintf _ _ _ _ h = _
  unfold snprintf
  simp only [bind_app, error_format_read, hformat]
  simp only [show (UInt64.ofNat (xs.length + es.length + 3) != 0) = true by simpa only [bne_iff_ne] using hne,
    ite_true, hnum, Nat.add_sub_cancel, Nat.min_self, Array.extract_size]
  simpa only [m_bind_assoc, m_pure_bind] using result

/-- `storedMessageHeap` as one record update (its parts are private to the store module). -/
theorem stored_eq (h : Heap) (b : Nat) (a out : Array UInt8) :
    storedMessageHeap h b a out =
      { h with bytes := upd (upd (upd (upd h.bytes h.nextBlk (some out)) b (some (copyRange a out 0 0 out.size)))
                          h.nextBlk none) b (some (out.push 0)),
               ro := upd h.ro h.nextBlk false, nextBlk := h.nextBlk + 1 } := rfl

/-! ## The blocks of the owned pointers -/

section owned
variable {h : Heap} {i : Nat} {s : GzState}

/-- Every block an owned pointer names is live. -/
theorem GzInv.ptr_live (inv : GzInv h i s) {p : BPtr} (hp : p ∈ ownedPtrs s) {b : Nat} (hb : blkOf p = some b) :
    h.live b := by
  have c := inv.common
  have ofbytes : ∀ a, h.bytes b = some a → h.live b := fun a e => Or.inl (by rw [e]; intro x; cases x)
  unfold ownedPtrs at hp
  rcases List.mem_append.1 hp with hp | hp
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · obtain ⟨_, _, pb, a, hpp, hpb, _, _⟩ := c.path
      rw [hpp] at hb; cases hb; exact ofbytes a hpb
    · rcases c.msg with hn | ⟨_, _, mb, a, hpp, hpb, _, _⟩
      · rw [hn] at hb; cases hb
      · rw [hpp] at hb; cases hb; exact ofbytes a hpb
  · split at hp
    · rename_i hz
      rcases List.mem_cons.1 hp with rfl | hp
      · rcases c.mode with hm | hm
        · obtain ⟨bb, a, hpp, hpb, _, _⟩ := ((inv.reader hm).bufs hz).1
          rw [hpp] at hb; cases hb; exact ofbytes a hpb
        · obtain ⟨bb, a, hpp, hpb, _, _⟩ := ((inv.writer hm).bufs hz).1
          rw [hpp] at hb; cases hb; exact ofbytes a hpb
      · split at hp
        · rename_i hmd
          rcases List.mem_singleton.1 hp with rfl
          rcases c.mode with hm | hm
          · obtain ⟨bb, a, hpp, hpb, _, _⟩ := ((inv.reader hm).bufs hz).2
            rw [hpp] at hb; cases hb; exact ofbytes a hpb
          · have hd : s.direct = 0 := by
              rcases hmd with e | e
              · exact absurd (hm.symm.trans e) (by decide)
              · exact e
            obtain ⟨bb, a, hpp, hpb, _, _⟩ := ((inv.writer hm).bufs hz).2 hd
            rw [hpp] at hb; cases hb; exact ofbytes a hpb
        · cases hp
    · cases hp

end owned

/-! ## Setting a message on a record without one -/

/-- **A record with no message takes a new message block** that the handle did not own and no owned pointer
names: the invariant holds, and the handle owns its old blocks and the new one. -/
theorem GzInv.put_message {h : Heap} {i : Nat} {s : GzState} (inv : GzInv h i s) (hm0 : s.msg = .null)
    (herr : s.err ≠ Z_MEM_ERROR) {nb : Nat} {m : List UInt8} (hb : h.bytes nb = some (m ++ [0]).toArray)
    (hro : h.ro nb = false) (h0 : 0 ∉ m) (hlen : m.length < 2 ^ 64) (hnb : ¬ GzOwned h i s nb)
    (hptr : ∀ p, p ∈ ownedPtrs s → blkOf p ≠ some nb) :
    GzInv (putGz h i { s with msg := .ref (.blk nb) 0 }) i { s with msg := .ref (.blk nb) 0 } ∧
    (∀ b, GzOwned (putGz h i { s with msg := .ref (.blk nb) 0 }) i { s with msg := .ref (.blk nb) 0 } b ↔
      GzOwned h i s b ∨ b = nb) := by
  have c := inv.common
  have hs := c.record
  have hnbi : nb ≠ i := fun e => hnb (Or.inl e)
  have hnbso : ¬ StreamOwned h (gzStrm i) nb := fun e => hnb (inv.streamOwned_owned e)
  have hso : ∀ b, StreamOwned (putGz h i { s with msg := .ref (.blk nb) 0 }) (gzStrm i) b =
      StreamOwned h (gzStrm i) b := putGz_streamOwned hs rfl
  have hown : ∀ b, GzOwned (putGz h i { s with msg := .ref (.blk nb) 0 }) i { s with msg := .ref (.blk nb) 0 } b ↔
      GzOwned h i s b ∨ b = nb := by
    intro b
    unfold GzOwned
    dsimp only
    rw [putGz_streamOwned (s' := { s with msg := .ref (.blk nb) 0 }) hs rfl]
    constructor
    · rintro (hb | hb | hb | hb)
      · exact Or.inl (Or.inl hb)
      · exact Or.inl (Or.inr (Or.inl hb))
      · cases hb; exact Or.inr rfl
      · exact Or.inl (Or.inr (Or.inr (Or.inr hb)))
    · rintro (hb | rfl)
      · rcases hb with hb | hb | hb | hb
        · exact Or.inl hb
        · exact Or.inr (Or.inl hb)
        · rw [hm0] at hb; cases hb
        · exact Or.inr (Or.inr (Or.inr hb))
      · exact Or.inr (Or.inr (Or.inl rfl))
  have hget := putGz_get (s' := { s with msg := .ref (.blk nb) 0 }) hs rfl
  have hreb := putGz_rebuffer (s' := { s with msg := .ref (.blk nb) 0 }) inv rfl c.recordFree
  have hlive : h.live nb := Or.inl (by rw [hb]; intro x; cases x)
  have hpl : ∃ L, ownedPtrs { s with msg := .ref (.blk nb) 0 } = [s.path, .ref (.blk nb) 0] ++ L ∧
      ownedPtrs s = [s.path, s.msg] ++ L := ⟨_, rfl, rfl⟩
  obtain ⟨L, eL1, eL2⟩ := hpl
  refine ⟨⟨?_, ?_, ?_⟩, hown⟩
  · exact {
      record := by simp [putGz]
      mode := c.mode
      fresh := putGz_fresh hs c.fresh
      uniq := putGz_uniq hs c.uniq
      globals := c.globals
      fit := putGz_fit c.fit
      path := by
        obtain ⟨p, hp, hmb⟩ := c.path
        exact ⟨p, (putGz_cstring _ _).2 hp, hmb⟩
      msg := by
        refine Or.inr ⟨m, (putGz_cstring _ _).2 ?_, nb, _, rfl, hb, hro, by simp⟩
        refine ⟨Or.inr ⟨.blk nb, 0, _, rfl, hb, by simp, ?_⟩, h0, hlen⟩
        simp only [List.toList_toArray, List.drop_zero]
        exact (List.take_of_length_le (by simp)).symm
      memerr := fun e => absurd e herr
      want := c.want
      size := c.size
      distinct := by
        refine ⟨?_, fun p hp b hb' => ?_⟩
        · have nd := c.distinct.1
          rw [eL2, hm0] at nd
          rw [eL1]
          have hnull : blkOf (.null : BPtr) = none := rfl
          have h1 : ([s.path, (Ptr.null : BPtr)] ++ L).filterMap blkOf = (s.path :: L).filterMap blkOf := by
            show (s.path :: (Ptr.null : BPtr) :: L).filterMap blkOf = _
            simp only [List.filterMap_cons, hnull]
          rw [h1] at nd
          have hperm : ([s.path, Ptr.ref (BRef.blk nb) 0] ++ L).filterMap blkOf =
              (s.path :: Ptr.ref (BRef.blk nb) 0 :: L).filterMap blkOf := rfl
          rw [hperm]
          have hsw : List.Perm ((s.path :: Ptr.ref (BRef.blk nb) 0 :: L).filterMap blkOf)
              ((Ptr.ref (BRef.blk nb) 0 :: s.path :: L).filterMap blkOf) :=
            (List.Perm.swap _ _ _).filterMap _
          rw [hsw.nodup_iff]
          show (nb :: (s.path :: L).filterMap blkOf).Nodup
          refine List.nodup_cons.2 ⟨?_, nd⟩
          intro hmem
          obtain ⟨p, hp, hpb⟩ := List.mem_filterMap.1 hmem
          refine hptr p ?_ hpb
          rw [eL2]
          rcases List.mem_cons.1 hp with e | e
          · exact List.mem_cons.2 (Or.inl e)
          · exact List.mem_cons.2 (Or.inr (List.mem_cons.2 (Or.inr e)))
        · rw [hso]
          rw [eL1] at hp
          rcases List.mem_cons.1 hp with e | e
          · subst e
            exact c.distinct.2 s.path (by rw [eL2]; exact List.mem_cons_self) b hb'
          rcases List.mem_cons.1 e with e | e
          · subst e
            cases hb'
            exact ⟨hnbi, hnbso⟩
          · exact c.distinct.2 p (by rw [eL2]; exact List.mem_cons.2 (Or.inr (List.mem_cons.2 (Or.inr e)))) b hb'
      live := fun b hb' => by
        rw [putGz_live hs]
        rcases (hown b).1 hb' with ho | rfl
        · exact c.live b ho
        · exact hlive
      pos := c.pos
      next := by
        rcases c.next with hn | ⟨b, off, a, hx, hbi, ho, _, hb', hle⟩
        · exact Or.inl hn
        · refine Or.inr ⟨b, off, a, hx, hbi, (hown b).2 (Or.inl ho), ?_, hb', hle⟩
          intro e
          cases e
          exact hnb ho
      nullHave := c.nullHave
      recordFree := by rw [hso]; exact c.recordFree }
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
      bufs := r.bufs
      input := r.input
      output := r.output
      codec := fun hz => by
        obtain ⟨reach, z, k, st, hzget, hzst, hk, hhead⟩ := r.codec hz
        exact ⟨StreamReachable.rebuffer reach hreb (fun _ => putGz_fit c.fit),
          z, k, st, by rw [hget]; exact hzget, hzst, hk, hhead⟩
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
      bufs := w.bufs
      input := w.input
      output := w.output
      codec := fun hd hz => by
        obtain ⟨reach, z, k, d, hzget, hzst, hk, hhead⟩ := w.codec hd hz
        exact ⟨StreamReachable.rebuffer reach hreb (fun e => nomatch e),
          z, k, d, by rw [hget]; exact hzget, hzst, hk, hhead⟩
      transparent := w.transparent }

/-! ## The run of `gz_error` -/

namespace GzErrorRun
open Zlib.Gzlib.Spec (setS)
open Zlib.Gzlib.Proofs (ldS_eq updS_eq)

private theorem view_setS (h : Heap) (i : Nat) (s : GzState) (r : BRef) :
    Space.get (setS h i s) r = Space.get h r := by
  cases r <;> rfl

private theorem strlenB_setS (h : Heap) (i : Nat) (s : GzState) (p : BPtr) :
    strlenB p (setS h i s) = match strlenB p h with
      | .error e => .error e
      | .ok (n, _) => .ok (n, setS h i s) := by
  cases p with
  | null => rfl
  | ref r off =>
    simp only [strlenB, view_setS]
    cases he : Space.get h r with
    | none => rfl
    | some a =>
      dsimp only
      cases hl : strlenFrom a off <;> simp only [hl]

/-- **Prefix**: the run equals the run from the heap with the old message freed and the code stored. -/
theorem gz_error_prefix {h : Heap} {i : Nat} {s : GzState} (inv : GzInv h i s) (err : Int32) (msg : BPtr) :
    Zlib.Gzlib.gz_error (gzSt i) err msg h =
      Zlib.Gzlib.gz_error (gzSt i) err msg
        (putGz (freeStr h s.msg) i { s with eof := s.eof, past := s.past, msg := .null, err := err }) := by
  have hs := inv.common.record
  have hmem := inv.common.memerr
  unfold Zlib.Gzlib.gz_error
  rcases inv.common.msg with hn | ⟨_, _, mb, a, hp, ha, hro, _⟩
  · gsimp [gzSt, hs, hn, putGz, freeStr, setS, upd_upd]
  · have hne : s.err ≠ Z_MEM_ERROR := fun he => by
      have hnull := hmem he
      rw [hp] at hnull
      cases hnull
    gsimp [gzSt, hs, hp, hne, Zlib.Gzlib.Proofs.freeB_blk_run ha hro, putGz, freeStr, setS, upd_upd]

/-- **Tail, no message**: nothing more happens. -/
theorem tail_null {h : Heap} {i : Nat} {s : GzState} {err : Int32} (hs : h.gzstates i = some s)
    (hm : s.msg = .null) (herr0 : s.err = err) :
    Zlib.Gzlib.gz_error (gzSt i) err .null h = .ok ((), setS h i s) := by
  subst herr0
  unfold Zlib.Gzlib.gz_error
  gsimp [gzSt, hs, hm]
  rw [← hm]

/-- **Tail, `Z_MEM_ERROR`**: nothing more happens. -/
theorem tail_memerr {h : Heap} {i : Nat} {s : GzState} {msg : BPtr} (hs : h.gzstates i = some s)
    (hm : s.msg = .null) (herr0 : s.err = Z_MEM_ERROR) :
    Zlib.Gzlib.gz_error (gzSt i) Z_MEM_ERROR msg h = .ok ((), setS h i s) := by
  unfold Zlib.Gzlib.gz_error
  gsimp [gzSt, hs, hm]
  rw [← herr0, ← hm]

/-- **Tail, refusal**: an oracle failure or a request of `2^63` bytes or more. -/
theorem tail_refused {h : Heap} {i : Nat} {s : GzState} {err : Int32} {msg : BPtr} {xs es : List UInt8}
    (hs : h.gzstates i = some s) (hm : s.msg = .null) (herr : err ≠ Z_MEM_ERROR)
    (hp : CString h s.path xs) (he : CString h msg es)
    (hxs : xs.length + 1 < 2 ^ 63) (hes : es.length + 1 < 2 ^ 63)
    (hrefuse : ¬ (h.allocOk h.nalloc = true ∧ xs.length + es.length + 3 < C.mallocLimit)) :
    Zlib.Gzlib.gz_error (gzSt i) err msg h =
      .ok ((), Zlib.Gzlib.MessageRefusal.refusedMessageHeap h i s) := by
  have hp0 := Zlib.GzFs.Proofs.strlenB_of_CString hp
  have he0 := Zlib.GzFs.Proofs.strlenB_of_CString he
  have hp1 : strlenB s.path (setS h i { s with err := err }) =
      .ok (UInt64.ofNat xs.length, setS h i { s with err := err }) := by
    rw [strlenB_setS, hp0]
  have he1 : strlenB msg (setS h i { s with err := err }) =
      .ok (UInt64.ofNat es.length, setS h i { s with err := err }) := by
    rw [strlenB_setS, he0]
  simp only [setS, hm] at hp1 he1
  have hn := cstring_nonnull' he
  have herr' : (err == Z_MEM_ERROR) = false := by simpa using herr
  have hxm : xs.length % 18446744073709551616 = xs.length := Nat.mod_eq_of_lt (by omega)
  have hem : es.length % 18446744073709551616 = es.length := Nat.mod_eq_of_lt (by omega)
  have hsm : (xs.length + es.length + 3) % 18446744073709551616 = xs.length + es.length + 3 :=
    Nat.mod_eq_of_lt (by omega)
  by_cases hok : h.allocOk h.nalloc = true
  · have hbig : ¬ (xs.length + es.length + 3 < C.mallocLimit) := fun e => hrefuse ⟨hok, e⟩
    unfold Zlib.Gzlib.gz_error
    simp [gzSt, bind_app, ldS_eq, updS_eq, hs, hm, hn, hp1, he1, herr', hxm, hem, hsm, hbig,
      allocB, Zlib.Gzlib.MessageRefusal.refusedMessageHeap, Zlib.Gzlib.MessageRefusal.refusedMessageState,
      setS, upd_upd]
  · have ha : h.allocOk h.nalloc = false := by simpa using hok
    unfold Zlib.Gzlib.gz_error
    simp [gzSt, bind_app, ldS_eq, updS_eq, hs, hm, hn, hp1, he1, herr', hxm, hem, hsm, ha,
      allocB, Zlib.Gzlib.MessageRefusal.refusedMessageHeap, Zlib.Gzlib.MessageRefusal.refusedMessageState,
      setS, upd_upd]

/-- The size of the message request (opaque to `simp`, so that the `size_t` sum is not split again). -/
def msgLen (xs es : List UInt8) : Nat := xs.length + es.length + 3

/-- The bytes `malloc` leaves in the message block. -/
def garb (h : Heap) (n : Nat) : Array UInt8 := Array.ofFn (n := n) fun k => Junk.of (h.garbage h.nalloc k.val)

/-- The message characters: the path, `": "`, the message. -/
def chars (xs es : List UInt8) : Array UInt8 := (xs ++ [58,32] ++ es).toArray

/-- The record with the new message. -/
def copiedS (h : Heap) (s : GzState) (err : Int32) : GzState :=
  { s with err := err, msg := .ref (.blk h.nextBlk) 0 }

/-- The heap after `malloc` and the store of the pointer. -/
def readyH (h : Heap) (i : Nat) (s : GzState) (err : Int32) (n : Nat) : Heap :=
  setS { setS h i { s with err := err } with
    bytes := upd h.bytes h.nextBlk (some (garb h n)), ro := upd h.ro h.nextBlk false,
    nextBlk := h.nextBlk + 1, nalloc := h.nalloc + 1 } i (copiedS h s err)

/-- The heap after the formatter. -/
def finalH (h : Heap) (i : Nat) (s : GzState) (err : Int32) (xs es : List UInt8) : Heap :=
  storedMessageHeap (readyH h i s err (msgLen xs es)) h.nextBlk
    (garb h (msgLen xs es)) (chars xs es)

/-- `finalH` as one record update. -/
theorem finalH_eq (h : Heap) (i : Nat) (s : GzState) (err : Int32) (xs es : List UInt8) :
    finalH h i s err xs es =
      { h with
        bytes := upd (upd (upd (upd (upd h.bytes h.nextBlk (some (garb h (msgLen xs es))))
          (h.nextBlk + 1) (some (chars xs es))) h.nextBlk
          (some (copyRange (garb h (msgLen xs es)) (chars xs es) 0 0 (chars xs es).size)))
          (h.nextBlk + 1) none) h.nextBlk (some ((chars xs es).push 0)),
        ro := upd (upd h.ro h.nextBlk false) (h.nextBlk + 1) false,
        nextBlk := h.nextBlk + 1 + 1, nalloc := h.nalloc + 1,
        gzstates := upd (upd h.gzstates i (some { s with err := err })) i (some (copiedS h s err)) } := rfl

/-- The heap after the copy, with the record of the handle as before it. -/
def addH (h : Heap) (i : Nat) (s : GzState) (err : Int32) (xs es : List UInt8) : Heap :=
  { finalH h i s err xs es with gzstates := h.gzstates }

theorem finalH_put (h : Heap) (i : Nat) (s : GzState) (err : Int32) (xs es : List UInt8) :
    finalH h i s err xs es = putGz (addH h i s err xs es) i (copiedS h s err) := by
  unfold addH putGz
  rw [finalH_eq]
  simp only [upd_upd]

theorem addH_bytes (h : Heap) (i : Nat) (s : GzState) (err : Int32) (xs es : List UInt8) (b : Nat) :
    (addH h i s err xs es).bytes b =
      if b = h.nextBlk then some ((chars xs es).push 0) else if b = h.nextBlk + 1 then none else h.bytes b := by
  unfold addH
  rw [finalH_eq]
  simp only [upd_apply]
  by_cases e1 : b = h.nextBlk
  · simp [e1]
  · by_cases e2 : b = h.nextBlk + 1
    · simp [e2]
    · simp [e1, e2]

theorem addH_ro (h : Heap) (i : Nat) (s : GzState) (err : Int32) (xs es : List UInt8) (b : Nat) :
    (addH h i s err xs es).ro b = if b = h.nextBlk ∨ b = h.nextBlk + 1 then false else h.ro b := by
  unfold addH
  rw [finalH_eq]
  simp only [upd_apply]
  by_cases e1 : b = h.nextBlk
  · simp [e1]
  · by_cases e2 : b = h.nextBlk + 1
    · simp [e2]
    · simp [e1, e2]

theorem addH_get (h : Heap) (i : Nat) (s : GzState) (err : Int32) (xs es : List UInt8) (r : BRef)
    (hr : ∀ b, r ≠ .blk b) : Space.get (addH h i s err xs es) r = Space.get h r := by
  unfold addH
  rw [finalH_eq]
  cases r with
  | blk b => exact absurd rfl (hr b)
  | _ => rfl

theorem addH_fields (h : Heap) (i : Nat) (s : GzState) (err : Int32) (xs es : List UInt8) :
    (addH h i s err xs es).words = h.words ∧ (addH h i s err xs es).streams = h.streams ∧
    (addH h i s err xs es).gzheaders = h.gzheaders ∧ (addH h i s err xs es).dstates = h.dstates ∧
    (addH h i s err xs es).istates = h.istates ∧ (addH h i s err xs es).gzstates = h.gzstates ∧
    (addH h i s err xs es).static = h.static ∧ (addH h i s err xs es).allocOk = h.allocOk ∧
    (addH h i s err xs es).garbage = h.garbage ∧ (addH h i s err xs es).nextBlk = h.nextBlk + 2 ∧
    (addH h i s err xs es).nalloc = h.nalloc + 1 := by
  unfold addH
  rw [finalH_eq]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem ready_view {h : Heap} {i : Nat} {s : GzState} {err : Int32} {n : Nat}
    (hf : Fresh h) (r : BRef) (a : Array UInt8) (ha : Space.get h r = some a) :
    Space.get (readyH h i s err n) r = some a := by
  cases r with
  | blk b =>
    have hne : b ≠ h.nextBlk := by
      intro he
      subst b
      have hl : h.live h.nextBlk := Or.inl (by rw [show h.bytes h.nextBlk = some a from ha]; intro hn; cases hn)
      exact hf h.nextBlk (Nat.le_refl _) hl
    simpa [readyH, setS, hne] using ha
  | str j => exact ha
  | dstate_depth j => exact ha
  | st_dist_code => exact ha
  | st_length_code => exact ha

private theorem ready_fresh {h : Heap} {i : Nat} {s : GzState} {err : Int32} {n : Nat}
    (hs : h.gzstates i = some s) (hf : Fresh h) : Fresh (readyH h i s err n) := by
  have hi : i < h.nextBlk := by
    by_cases ht : i < h.nextBlk
    · exact ht
    · exact False.elim (hf i (by omega) (by simp [Heap.live, hs]))
  intro j hj hl
  have hj' : h.nextBlk + 1 ≤ j := hj
  have hjn : j ≠ h.nextBlk := by omega
  have hji : j ≠ i := by omega
  apply hf j (by omega)
  simpa [Heap.live, readyH, setS, hjn, hji] using hl

/-- **Tail, copy**: the message block is allocated and receives the formatted message. -/
theorem tail_copied {h : Heap} {i : Nat} {s : GzState} {err : Int32} {msg : BPtr} {xs es : List UInt8}
    (hs : h.gzstates i = some s) (hm : s.msg = .null) (herr : err ≠ Z_MEM_ERROR)
    (hp : CString h s.path xs) (he : CString h msg es) (hf : Fresh h)
    (hxs : xs.length + 1 < 2 ^ 63) (hes : es.length + 1 < 2 ^ 63)
    (ha : h.allocOk h.nalloc = true) (hlim : xs.length + es.length + 3 < C.mallocLimit) :
    Zlib.Gzlib.gz_error (gzSt i) err msg h = .ok ((), finalH h i s err xs es) := by
  have hpPre : CString (setS h i { s with err := err }) s.path xs := cstring_views hp (fun r a hv => by
    rw [view_setS]; exact hv)
  have hePre : CString (setS h i { s with err := err }) msg es := cstring_views he (fun r a hv => by
    rw [view_setS]; exact hv)
  have hpLen := Zlib.GzFs.Proofs.strlenB_of_CString hpPre
  have heLen := Zlib.GzFs.Proofs.strlenB_of_CString hePre
  have hpReady : CString (readyH h i s err (msgLen xs es)) s.path xs :=
    cstring_views hp (ready_view hf)
  have heReady : CString (readyH h i s err (msgLen xs es)) msg es :=
    cstring_views he (ready_view hf)
  have hpLenReady := Zlib.GzFs.Proofs.strlenB_of_CString hpReady
  have heLenReady := Zlib.GzFs.Proofs.strlenB_of_CString heReady
  have hsum : UInt64.ofNat xs.length + UInt64.ofNat es.length + 3 = UInt64.ofNat (msgLen xs es) := by
    apply UInt64.toNat_inj.1
    simp only [UInt64.toNat_add, UInt64.toNat_ofNat']
    unfold msgLen
    rw [show (3 : UInt64).toNat = 3 by decide]
    omega
  have hnum : (UInt64.ofNat (msgLen xs es)).toNat = msgLen xs es :=
    UInt64.toNat_ofNat_of_lt' (by unfold msgLen UInt64.size; omega)
  have hfPre : Fresh (setS h i { s with err := err }) :=
    Zlib.Gzlib.Proofs.Shape.fresh (Zlib.Gzlib.Proofs.shape_setS hs _) rfl hf
  have hmalloc : allocB (msgLen xs es) (setS h i { s with err := err }) =
      .ok (.ref (.blk h.nextBlk) 0, { setS h i { s with err := err } with
        bytes := upd h.bytes h.nextBlk (some (garb h (msgLen xs es))),
        ro := upd h.ro h.nextBlk false, nextBlk := h.nextBlk + 1, nalloc := h.nalloc + 1 }) := by
    exact allocB_some _ ha (by unfold msgLen; exact hlim) (Fresh.slotUsed_next hfPre)
  have hready : (readyH h i s err (msgLen xs es)).gzstates i = some (copiedS h s err) := by
    simp [readyH, setS]
  obtain ⟨r0, hprint⟩ := snprintf_error_any hpReady heReady
    (show (readyH h i s err (msgLen xs es)).bytes h.nextBlk = some (garb h (msgLen xs es)) by
      simp [readyH, setS])
    (show (readyH h i s err (msgLen xs es)).ro h.nextBlk = false by simp [readyH, setS])
    (show (garb h (msgLen xs es)).size = xs.length + es.length + 3 by simp [garb, msgLen])
    (by omega) (Fresh.slotUsed_next (ready_fresh hs hf))
  have hxm : xs.length % 2^64 = xs.length := Nat.mod_eq_of_lt (by omega)
  have hem : es.length % 2^64 = es.length := Nat.mod_eq_of_lt (by omega)
  have hlenmod : (xs.length + es.length + 3) % 2^64 = msgLen xs es := by
    rw [Nat.mod_eq_of_lt (by omega)]
    rfl
  simp only [readyH, copiedS, setS, upd_upd, hm] at hpLen heLen hpLenReady heLenReady hmalloc hprint
  have hn := cstring_nonnull' he
  have herr' : (err == Z_MEM_ERROR) = false := by simpa using herr
  unfold Zlib.Gzlib.gz_error
  simp [gzSt, bind_app, ldS_eq, updS_eq, hs, hm, hn, hpLen, heLen, hpLenReady, heLenReady,
    hsum, hnum, hxm, hem, hlenmod, hmalloc, hready, error_format_literal, error_separator_literal,
    finalH, chars, copiedS, readyH, herr', setS, upd_upd]
  dsimp only [msgLen] at hprint ⊢
  rw [hprint]
  try simp only [List.append_assoc, List.cons_append, List.nil_append]

end GzErrorRun

/-! ## The invariant after `gz_error` -/

/-- Two frames with the same changed set compose. -/
theorem frame_comp {a b c : Heap} {C : Nat → Prop} (f : Frame a b C) (g : Frame b c C) : Frame a c C := by
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ := f
  obtain ⟨g1, g2, g3, g4, g5, g6⟩ := g
  refine ⟨f1.trans g1, f2.trans g2, f3.trans g3, Nat.le_trans f4 g4, Nat.le_trans f5 g5, ?_⟩
  intro x hx hc
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ := f6 x hx hc
  have hbx : b.live x := by
    unfold Heap.live at hx ⊢
    rw [e1, e2, e3, e4, e5, e6, e7]
    exact hx
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8⟩ := g6 x hbx hc
  exact ⟨d1.trans e1, d2.trans e2, d3.trans e3, d4.trans e4, d5.trans e5, d6.trans e6, d7.trans e7, d8.trans e8⟩

theorem frame_mono' {a b : Heap} {C D : Nat → Prop} (f : Frame a b C) (hCD : ∀ x, C x → D x) : Frame a b D := by
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ := f
  exact ⟨f1, f2, f3, f4, f5, fun x hx hn => f6 x hx (fun c => hn (hCD x c))⟩

/-- The heap with the old message freed keeps every view whose block is not the old message. -/
theorem freeStr_get {h : Heap} {p : BPtr} {r : BRef} (hr : ∀ b, r = .blk b → blkOf p ≠ some b) :
    Space.get (freeStr h p) r = Space.get h r := by
  unfold freeStr
  split
  · rename_i b0 _
    cases r with
    | blk c =>
      have hc : c ≠ b0 := fun e => hr c rfl (by rw [e]; rfl)
      show upd h.bytes b0 none c = h.bytes c
      exact upd_ne _ _ _ _ hc
    | str j => rfl
    | dstate_depth k => rfl
    | st_dist_code => rfl
    | st_length_code => rfl
  · rfl

theorem freeStr_nextBlk (h : Heap) (p : BPtr) : (freeStr h p).nextBlk = h.nextBlk := by
  unfold freeStr; split <;> rfl

/-- The post-condition of `gz_error` on a handle in `GzInv`: the skeleton's clauses, the record of the result,
and no grab. -/
def ErrPost (h : Heap) (i : Nat) (s : GzState) (err : Int32) (after : Heap) (s' : GzState) : Prop :=
  GzInv after i s' ∧ s' = { s with err := s'.err, msg := s'.msg } ∧
    (s'.err = err ∨ (s'.err = Z_MEM_ERROR ∧ s'.msg = .null)) ∧
    Frame h after (fun b => b = i ∨ blkOf s.msg = some b) ∧
    LiveChange h after (fun b => blkOf s'.msg = some b ∧ ¬ h.live b) (fun b => blkOf s.msg = some b) ∧
    (∀ b, blkOf s'.msg = some b → ¬ h.live b) ∧
    after.gzstates i = some s' ∧
    (∀ b, GzOwned after i s' b → GzOwned h i s b ∨ ¬ h.live b)

/-- What the prefix of `gz_error` leaves: the old message freed, the code stored. -/
structure Cleared (h : Heap) (i : Nat) (s : GzState) (err : Int32) (h1 : Heap) (s1 : GzState) : Prop where
  inv1 : GzInv h1 i s1
  own1 : ∀ b, GzOwned h1 i s1 b ↔ GzOwned h i s b ∧ blkOf s.msg ≠ some b
  live1 : ∀ b, h1.live b ↔ h.live b ∧ blkOf s.msg ≠ some b
  frame1 : Frame h h1 (fun b => b = i ∨ blkOf s.msg = some b)
  msg1 : s1.msg = .null
  err1 : s1.err = err
  shape1 : ∀ e m, ({ s1 with err := e, msg := m } : GzState) = { s with err := e, msg := m }
  next1 : h1.nextBlk = h.nextBlk
  fresh0 : ¬ h.live h.nextBlk
  /-- the caller's message keeps its bytes -/
  keep : ∀ msg t, CString h msg t → (∀ b, ByteRoot msg b → ¬ GzOwned h i s b) → CString h1 msg t

theorem cleared_of {h : Heap} {i : Nat} {s : GzState} (inv : GzInv h i s) (err : Int32) :
    Cleared h i s err (putGz (freeStr h s.msg) i { s with eof := s.eof, past := s.past, msg := .null, err := err })
      { s with eof := s.eof, past := s.past, msg := .null, err := err } := by
  obtain ⟨inv1, own1, live1, frame1⟩ := inv.clear_message s.eof s.past err
    (fun hm => ⟨(inv.reader hm).flags.1, (inv.reader hm).flags.2.1⟩)
  refine ⟨inv1, own1, live1, frame1, rfl, rfl, fun _ _ => rfl, freeStr_nextBlk h s.msg,
    inv.common.fresh _ (Nat.le_refl _), ?_⟩
  intro msg t ct hno
  rcases ct.1 with hn | ⟨r, off, a, hpm, ha, hle, hxs⟩
  · exact ⟨Or.inl hn, ct.2⟩
  · refine ⟨Or.inr ⟨r, off, a, hpm, ?_, hle, hxs⟩, ct.2⟩
    rw [putGz_space, freeStr_get]
    · exact ha
    · intro b hrb hmb
      subst hrb
      apply hno b (by rw [hpm]; exact rfl)
      rcases inv.common.msg with hn | ⟨_, _, mb, _, hp, _⟩
      · rw [hn] at hmb; cases hmb
      · rw [hp] at hmb; cases hmb; exact Or.inr (Or.inr (Or.inl hp))

/-- The paths that end after the prefix. -/
theorem post_stop {h h1 : Heap} {i : Nat} {s s1 : GzState} {err : Int32} (c : Cleared h i s err h1 s1) :
    ErrPost h i s err h1 s1 := by
  refine ⟨c.inv1, ?_, Or.inl c.err1, c.frame1, ?_, ?_, c.inv1.common.record, ?_⟩
  · exact (show s1 = { s1 with err := s1.err, msg := s1.msg } from rfl).trans (c.shape1 _ _)
  · intro b
    rw [c.live1 b, c.msg1]
    simp [blkOf]
  · intro b hb; rw [c.msg1] at hb; cases hb
  · intro b hb; exact Or.inl ((c.own1 b).1 hb).1


open GzErrorRun in
/-- The refusal path: an oracle failure or a request of `2^63` bytes or more. -/
theorem post_refused {h h1 : Heap} {i : Nat} {s s1 : GzState} {err : Int32} (c : Cleared h i s err h1 s1) :
    ErrPost h i s err (Zlib.Gzlib.MessageRefusal.refusedMessageHeap h1 i s1)
      { s1 with err := Z_MEM_ERROR, msg := .null } := by
  obtain ⟨inv2, own2, live2, frame2⟩ := c.inv1.clear_message s1.eof s1.past Z_MEM_ERROR
    (fun hm => ⟨(c.inv1.reader hm).flags.1, (c.inv1.reader hm).flags.2.1⟩)
  have hX : freeStr h1 s1.msg = h1 := by rw [c.msg1]; rfl
  rw [hX] at inv2 own2 live2 frame2
  have hafter : Zlib.Gzlib.MessageRefusal.refusedMessageHeap h1 i s1 =
      { putGz h1 i { s1 with err := Z_MEM_ERROR, msg := .null } with nalloc := h1.nalloc + 1 } := rfl
  rw [hafter]
  have frX : ∀ C : Nat → Prop, Frame (putGz h1 i { s1 with err := Z_MEM_ERROR, msg := .null })
      { putGz h1 i { s1 with err := Z_MEM_ERROR, msg := .null } with nalloc := h1.nalloc + 1 } C :=
    fun C => ⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_succ _,
      fun _ _ _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
  obtain ⟨inv3, own3⟩ := inv2.frame_core (frX _) inv2.common.fresh inv2.common.uniq inv2.common.globals
    inv2.common.fit
  have hm2 : ({ s1 with err := Z_MEM_ERROR, msg := .null } : GzState).msg = .null := rfl
  refine ⟨inv3, c.shape1 _ _, Or.inr ⟨rfl, rfl⟩, ?_, ?_, ?_, inv3.common.record, ?_⟩
  · refine frame_comp c.frame1 (frame_comp (frame_mono' frame2 ?_) (frX _))
    rintro x (e | e)
    · exact Or.inl e
    · rw [c.msg1] at e; cases e
  · intro b
    show (putGz h1 i { s1 with err := Z_MEM_ERROR, msg := .null }).live b ↔ _
    rw [live2 b, c.live1 b, c.msg1, hm2]
    simp [blkOf]
  · intro b e; rw [hm2] at e; cases e
  · intro b hb
    exact Or.inl ((c.own1 b).1 ((own2 b).1 ((own3 b).1 hb)).1).1

open GzErrorRun in
/-- The copy path: a fresh block receives the message. -/
theorem post_copied {h h1 : Heap} {i : Nat} {s s1 : GzState} {err : Int32} {msg : BPtr} {xs t : List UInt8}
    (c : Cleared h i s err h1 s1) (herr : err ≠ Z_MEM_ERROR) (hpx : CString h1 s1.path xs) (ct : CString h1 msg t)
    (hlim : xs.length + t.length + 3 < C.mallocLimit) :
    ErrPost h i s err (finalH h1 i s1 err xs t) { s1 with msg := .ref (.blk h1.nextBlk) 0 } := by
  have inv1 := c.inv1
  have hlim' : xs.length + t.length + 3 < 2 ^ 63 := by have := hlim; unfold C.mallocLimit at this; exact this
  have hfresh1 : ∀ b, h1.nextBlk ≤ b → h1.bytes b = none ∧ h1.words b = none ∧ h1.streams b = none ∧
      h1.gzheaders b = none ∧ h1.dstates b = none ∧ h1.istates b = none ∧ h1.gzstates b = none := by
    intro b hb
    have := inv1.common.fresh b hb
    simp only [Heap.live, not_or, ne_eq, Classical.not_not] at this
    exact this
  have hc : copiedS h1 s1 err = { s1 with msg := .ref (.blk h1.nextBlk) 0 } := by
    rw [← c.err1]; rfl
  rw [finalH_put, hc]
  obtain ⟨fw, fst, fgh, fds, fis, fgz, fsta, fok, fgar, fnext, fnal⟩ := addH_fields h1 i s1 err xs t
  have h1n := (hfresh1 (h1.nextBlk + 1) (by omega)).1
  have hAb : ∀ b, (addH h1 i s1 err xs t).bytes b =
      if b = h1.nextBlk then some ((chars xs t).push 0) else h1.bytes b := by
    intro b
    rw [addH_bytes]
    by_cases e1 : b = h1.nextBlk
    · simp [e1]
    · by_cases e2 : b = h1.nextBlk + 1
      · subst e2; simp [h1n]
      · simp [e1, e2]
  have hAro := addH_ro h1 i s1 err xs t
  have hAget := addH_get h1 i s1 err xs t
  generalize addH h1 i s1 err xs t = hA at fw fst fgh fds fis fgz fsta fok fgar fnext fnal hAb hAro hAget ⊢
  have hAlive : ∀ b, hA.live b ↔ b = h1.nextBlk ∨ h1.live b := by
    intro b
    unfold Heap.live
    rw [hAb, fw, fst, fgh, fds, fis, fgz]
    by_cases e : b = h1.nextBlk
    · subst e; simp
    · simp [e]
  have h1lt : ∀ b, h1.live b → b < h1.nextBlk := by
    intro b hb
    refine Classical.byContradiction fun hge => ?_
    exact inv1.common.fresh b (by omega) hb
  have frA : ∀ C : Nat → Prop, Frame h1 hA C := by
    intro C
    refine ⟨fsta.symm, fok.symm, fgar.symm, by rw [fnext]; omega, by rw [fnal]; omega, ?_⟩
    intro b hb _
    have hlt := h1lt b hb
    refine ⟨by rw [hAb, if_neg (by omega)], by rw [fw], by rw [fst], by rw [fgh], by rw [fds], by rw [fis],
      by rw [fgz], ?_⟩
    rw [hAro, if_neg (by omega)]
  have freshA : Fresh hA := by
    intro b hb hl
    rw [fnext] at hb
    rcases (hAlive b).1 hl with e | e
    · omega
    · have := h1lt b e; omega
  have uniqA : Zlib.Gzlib.Spec.Uniq hA := by
    intro b
    rw [hAb, fw, fst, fgh, fds, fis, fgz]
    by_cases e : b = h1.nextBlk
    · subst e
      obtain ⟨-, a2, a3, a4, a5, a6, a7⟩ := hfresh1 h1.nextBlk (Nat.le_refl _)
      simp [a2, a3, a4, a5, a6, a7]
    · rw [if_neg e]; exact inv1.common.uniq b
  have globalsA : LibraryGlobals hA := by
    unfold LibraryGlobals; rw [fsta]; exact inv1.common.globals
  have fitA : ZlibF.PlatformMemory.ByteObjectsFit hA := by
    intro r a hra
    cases r with
    | blk b =>
      have e : hA.bytes b = some a := hra
      rw [hAb] at e
      by_cases eb : b = h1.nextBlk
      · rw [if_pos eb] at e
        cases e
        simp [chars, ZlibF.PlatformMemory.byteObjectLimit]
        omega
      · rw [if_neg eb] at e
        exact inv1.common.fit (.blk b) a e
    | str j =>
      rw [hAget _ (fun _ e => by cases e)] at hra
      exact inv1.common.fit _ a hra
    | dstate_depth k =>
      rw [hAget _ (fun _ e => by cases e)] at hra
      exact inv1.common.fit _ a hra
    | st_dist_code =>
      rw [hAget _ (fun _ e => by cases e)] at hra
      exact inv1.common.fit _ a hra
    | st_length_code =>
      rw [hAget _ (fun _ e => by cases e)] at hra
      exact inv1.common.fit _ a hra
  obtain ⟨invA, ownA⟩ := inv1.frame_core (frA _) freshA uniqA globalsA fitA
  have hnbown : ¬ GzOwned hA i s1 h1.nextBlk := by
    intro ho
    have := h1lt _ (inv1.common.live _ ((ownA _).1 ho))
    omega
  have hptr : ∀ p, p ∈ ownedPtrs s1 → blkOf p ≠ some h1.nextBlk := by
    intro p hp e
    have := h1lt _ (inv1.ptr_live hp e)
    omega
  have h0 : (0 : UInt8) ∉ xs ++ [58, 32] ++ t := by
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, not_or]
    exact ⟨⟨hpx.2.1, by decide, by decide⟩, ct.2.1⟩
  have hAnb : hA.bytes h1.nextBlk = some ((xs ++ [58, 32] ++ t) ++ [0]).toArray := by
    rw [hAb, if_pos rfl]
    simp [chars]
  have hAro' : hA.ro h1.nextBlk = false := by rw [hAro, if_pos (Or.inl rfl)]
  obtain ⟨invB, ownB⟩ := invA.put_message c.msg1 (by rw [c.err1]; exact herr) hAnb hAro' h0
    (by simp; omega) hnbown hptr
  have hnbh : ¬ h.live h1.nextBlk := by rw [c.next1]; exact c.fresh0
  have hbk : blkOf ({ s1 with msg := .ref (.blk h1.nextBlk) 0 } : GzState).msg = some h1.nextBlk := rfl
  refine ⟨invB, ?_, Or.inl c.err1, ?_, ?_, ?_, invB.common.record, ?_⟩
  · exact (show ({ s1 with msg := .ref (.blk h1.nextBlk) 0 } : GzState) =
      { s1 with err := s1.err, msg := .ref (.blk h1.nextBlk) 0 } from rfl).trans (c.shape1 _ _)
  · refine frame_comp c.frame1 ?_
    obtain ⟨g1, g2, g3, g4, g5, g6⟩ := frA (fun _ => False)
    refine ⟨g1, g2, g3, g4, g5, ?_⟩
    intro b hb hc'
    have hbi : b ≠ i := fun e => hc' (Or.inl e)
    obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ := g6 b hb id
    exact ⟨e1, e2, e3, e4, e5, e6, (upd_ne _ _ _ _ hbi).trans e7, e8⟩
  · intro b
    rw [putGz_live invA.common.record, hAlive, c.live1 b, hbk]
    constructor
    · rintro (e | ⟨hl, hm⟩)
      · subst e; exact Or.inr ⟨rfl, hnbh⟩
      · exact Or.inl ⟨hl, hm⟩
    · rintro (⟨hl, hm⟩ | ⟨e, -⟩)
      · exact Or.inr ⟨hl, hm⟩
      · cases e; exact Or.inl rfl
  · intro b e
    rw [hbk] at e
    cases e
    exact hnbh
  · intro b hb
    rcases (ownB b).1 hb with ho | e
    · exact Or.inl ((c.own1 b).1 ((ownA b).1 ho)).1
    · subst e; exact Or.inr hnbh

open GzErrorRun in
/-- **`gz_error` keeps `GzInv`**, with the skeleton's post-condition, the record of the result and no grab. -/
theorem GzInv.gz_error_full {h : Heap} {i : Nat} {s : GzState} (inv : GzInv h i s) (err : Int32) (msg : BPtr)
    (hmsg : msg = .null ∨ ∃ t, CString h msg t ∧ ∀ b, ByteRoot msg b → ¬ GzOwned h i s b) :
    ∃ after s', C.run (Zlib.Gzlib.gz_error (gzSt i) err msg) h = .ok ((), after) ∧ ErrPost h i s err after s' := by
  have c := cleared_of inv err
  have hrun0 := gz_error_prefix inv err msg
  generalize ({ s with eof := s.eof, past := s.past, msg := .null, err := err } : GzState) = s1 at c hrun0
  generalize putGz (freeStr h s.msg) i s1 = h1 at c hrun0
  have hs1 : h1.gzstates i = some s1 := c.inv1.common.record
  have hsame : Zlib.Gzlib.Spec.setS h1 i s1 = h1 := by
    have e := upd_self h1.gzstates i s1 hs1
    simp only [Zlib.Gzlib.Spec.setS, e]
  have run : ∀ after, Zlib.Gzlib.gz_error (gzSt i) err msg h1 = .ok ((), after) →
      C.run (Zlib.Gzlib.gz_error (gzSt i) err msg) h = .ok ((), after) := by
    intro after e
    show Zlib.Gzlib.gz_error _ _ _ h = _
    rw [hrun0, e]
  rcases hmsg with hnull | ⟨t, ct, hno⟩
  · subst hnull
    exact ⟨h1, s1, run _ (by rw [tail_null hs1 c.msg1 c.err1, hsame]), post_stop c⟩
  by_cases hmem : err = Z_MEM_ERROR
  · subst hmem
    exact ⟨h1, s1, run _ (by rw [tail_memerr hs1 c.msg1 c.err1, hsame]), post_stop c⟩
  obtain ⟨xs, hpx, _⟩ := c.inv1.common.path
  have ct1 := c.keep msg t ct hno
  have hxs := cstring_len_fit c.inv1.common.fit hpx
  have hts := cstring_len_fit c.inv1.common.fit ct1
  by_cases hok : h1.allocOk h1.nalloc = true ∧ xs.length + t.length + 3 < C.mallocLimit
  · exact ⟨_, _, run _ (tail_copied hs1 c.msg1 hmem hpx ct1 c.inv1.common.fresh hxs hts hok.1 hok.2),
      post_copied c hmem hpx ct1 hok.2⟩
  · exact ⟨_, _, run _ (tail_refused hs1 c.msg1 hmem hpx ct1 hxs hts hok), post_refused c⟩

end ZlibF.Spec.Public
