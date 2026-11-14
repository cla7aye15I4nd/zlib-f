import ZlibF.Proof.«deflate.c.universal-ops-copy»
import ZlibF.Proof.«deflate.c.init.storage»
import ZlibF.Proof.«deflate.c.life.end»
import ZlibF.Spec.Public.Memory
import ZlibF.Spec.Public.Initialisation

/-!
# deflate.c: `deflateCopy` when an allocation fails (`copy_failure`)

`deflateCopy` makes five requests: the state record, then `window`, `prev`, `head` and
`pending_buf`. The four buffer requests all run even when one of them fails. When the state
request fails, the copy clears `dest->state` and returns `Z_MEM_ERROR`. When a buffer request
fails, the copy frees every non-null buffer (`pending_buf`, `head`, `prev`, `window`, in this
order) and the state record, clears `dest->state` and returns `Z_MEM_ERROR`.

The heap after a failure differs from the heap before only in the destination record, in the
allocation counter and in the write permissions of blocks that were allocated and freed again.
So the source and its state are intact, the frame is the destination record, at least one
request failed, and the set of live blocks is the old one.
-/

namespace Zlib.Deflate.Universal
open C ZlibF.Spec ZlibF.Spec.Public Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Engine.Proofs
open Zlib.Deflate.Proofs Zlib.Deflate.Proofs.DefaultInit
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-! ## Monad steps -/

theorem copyFail_bind {α β : Type} {m : M α} {f : α → M β} {h h1 : Heap} {a : α}
    (e : m h = .ok (a, h1)) : (m >>= f) h = f a h1 := by
  simp [e]

/-! ## The heap after a failure, compared with the heap before -/

/-- Every table but the write permissions agrees with the heap before; the permissions agree
on the old blocks; the counters only grow. -/
structure FailSame (h F : Heap) : Prop where
  bytes : ∀ x, F.bytes x = h.bytes x
  words : ∀ x, F.words x = h.words x
  streams : ∀ x, F.streams x = h.streams x
  gzheaders : ∀ x, F.gzheaders x = h.gzheaders x
  dstates : ∀ x, F.dstates x = h.dstates x
  istates : ∀ x, F.istates x = h.istates x
  gzstates : ∀ x, F.gzstates x = h.gzstates x
  ro : ∀ x, x < h.nextBlk → F.ro x = h.ro x
  static : F.static = h.static
  allocOk : F.allocOk = h.allocOk
  garbage : F.garbage = h.garbage
  next : h.nextBlk ≤ F.nextBlk
  count : h.nalloc ≤ F.nalloc

theorem FailSame.get {h F : Heap} (s : FailSame h F) (r : ZStreamRef) : r.get F = r.get h := by
  cases r with
  | tab i => simp only [ZStreamRef.get, s.streams]
  | in_gzstate_strm i => simp only [ZStreamRef.get, s.gzstates]

/-- Writing one stream record leaves every other stream record. -/
theorem copyFail_get_put_other (h : Heap) {source dest : ZStreamRef}
    (different : source ≠ dest) (v : ZStream) :
    source.get (dest.put h v) = source.get h := by
  cases source with
  | tab si =>
    cases dest with
    | tab di =>
      have ne : si ≠ di := by
        intro eq
        cases eq
        exact different rfl
      cases hd : h.streams di <;>
        simp [ZStreamRef.get, ZStreamRef.put, hd, upd_ne _ _ _ _ ne]
    | in_gzstate_strm di =>
      cases hd : h.gzstates di <;>
        simp [ZStreamRef.get, ZStreamRef.put, hd]
  | in_gzstate_strm si =>
    cases dest with
    | tab di =>
      cases hd : h.streams di <;>
        simp [ZStreamRef.get, ZStreamRef.put, hd]
    | in_gzstate_strm di =>
      have ne : si ≠ di := by
        intro eq
        cases eq
        exact different rfl
      cases hd : h.gzstates di <;>
        simp [ZStreamRef.get, ZStreamRef.put, hd, upd_ne _ _ _ _ ne]

/-- A stream write changes no block other than the stream root. -/
theorem copyFail_put_other_block (h : Heap) (dest : ZStreamRef) (v : ZStream) {b : Nat}
    (root : ¬ StreamRoot dest b) :
    (dest.put h v).streams b = h.streams b ∧ (dest.put h v).gzstates b = h.gzstates b := by
  cases dest with
  | tab k =>
    have ne : b ≠ k := fun e => root (by simp [StreamRoot, e])
    simp only [ZStreamRef.put]
    split <;> simp [upd_ne _ _ _ _ ne]
  | in_gzstate_strm k =>
    have ne : b ≠ k := fun e => root (by simp [StreamRoot, e])
    simp only [ZStreamRef.put]
    split <;> simp [upd_ne _ _ _ _ ne]

/-- The destination write after a heap that agrees with the one before gives every clause of
the goal except the result and the failed request. -/
theorem copyFail_finish {h F : Heap} {source dest : ZStreamRef} {z zd : ZStream}
    (s : FailSame h F) (fresh : Fresh h) (distinct : source ≠ dest)
    (hz : source.get h = some z) (get : dest.get h = some zd) (v : ZStream) :
    source.get (dest.put F v) = some z ∧ (∀ i, (dest.put F v).dstates i = h.dstates i) ∧
      Frame h (dest.put F v) (StreamRoot dest) ∧ dest.get (dest.put F v) = some v ∧
      LiveChange h (dest.put F v) (fun _ => False) (fun _ => False) := by
  have getF : dest.get F = some zd := (s.get dest).trans get
  refine ⟨?_, ?_, ?_, ZStreamRef.get_put_same getF v, ?_⟩
  · rw [copyFail_get_put_other F distinct v, s.get source, hz]
  · intro i
    rw [ZStreamRef.put_dstates]
    exact s.dstates i
  · refine ⟨by simp [s.static], by simp [s.allocOk], by simp [s.garbage], by simpa using s.next,
      by simpa using s.count, ?_⟩
    intro b live root
    have lt : b < h.nextBlk := by
      rcases Nat.lt_or_ge b h.nextBlk with l | g
      · exact l
      · exact absurd live (fresh b g)
    obtain ⟨st, gz⟩ := copyFail_put_other_block F dest v root
    refine ⟨?_, ?_, st.trans (s.streams b), ?_, ?_, ?_, gz.trans (s.gzstates b), ?_⟩
    · rw [ZStreamRef.put_bytes]; exact s.bytes b
    · rw [ZStreamRef.put_words]; exact s.words b
    · rw [ZStreamRef.put_gzheaders]; exact s.gzheaders b
    · rw [ZStreamRef.put_dstates]; exact s.dstates b
    · rw [ZStreamRef.put_istates]; exact s.istates b
    · rw [ZStreamRef.put_ro]; exact s.ro b lt
  · intro b
    rw [(shape_put getF v).live b]
    simp only [Heap.live, s.bytes, s.words, s.streams, s.gzheaders, s.dstates, s.istates,
      s.gzstates]
    simp

/-! ## The buffer requests and the cleanup -/

/-- The heap after the four buffer requests, from the heap `X` after the record copy. -/
def failBuf (X : Heap) (n : Nat) (d : DeflateState) : Heap :=
  setD (copyB X d) n (copyBufState X d)

/-- The heap after the four `TRY_FREE` calls. -/
def failFreed (X : Heap) (n : Nat) (d : DeflateState) : Heap :=
  freeBytes (freeWords (freeWords (freeBytes (failBuf X n d) (bytePtr (copyQ X d)))
    (wordPtr (copyP X d))) (wordPtr (copyW X d))) (bytePtr X)

/-- The heap after `ZFREE(source, ds)`. -/
def failEnd (X : Heap) (n : Nat) (d : DeflateState) : Heap :=
  { failFreed X n d with dstates := upd (failFreed X n d).dstates n none }

/-- Each `TRY_FREE` frees a null pointer or a live block of the heap it runs on. -/
theorem fail_freeable (X : Heap) (n : Nat) (d : DeflateState) :
    (bytePtr (copyQ X d) = .null ∨ ∃ b a, bytePtr (copyQ X d) = .ref (.blk b) 0 ∧
        (failBuf X n d).bytes b = some a ∧ (failBuf X n d).ro b = false) ∧
    (wordPtr (copyP X d) = .null ∨ ∃ b a, wordPtr (copyP X d) = .ref (.blk b) 0 ∧
        (freeBytes (failBuf X n d) (bytePtr (copyQ X d))).words b = some a) ∧
    (wordPtr (copyW X d) = .null ∨ ∃ b a, wordPtr (copyW X d) = .ref (.blk b) 0 ∧
        (freeWords (freeBytes (failBuf X n d) (bytePtr (copyQ X d))) (wordPtr (copyP X d))).words b =
          some a) ∧
    (bytePtr X = .null ∨ ∃ b a, bytePtr X = .ref (.blk b) 0 ∧
        (freeWords (freeWords (freeBytes (failBuf X n d) (bytePtr (copyQ X d))) (wordPtr (copyP X d)))
          (wordPtr (copyW X d))).bytes b = some a ∧
        (freeWords (freeWords (freeBytes (failBuf X n d) (bytePtr (copyQ X d))) (wordPtr (copyP X d)))
          (wordPtr (copyW X d))).ro b = false) := by
  by_cases h0 : X.allocOk X.nalloc = true <;>
  by_cases h1 : X.allocOk (X.nalloc + 1) = true <;>
  by_cases h2 : X.allocOk (X.nalloc + 2) = true <;>
  by_cases h3 : X.allocOk (X.nalloc + 3) = true
  all_goals simp [failBuf, copyB, copyQ, copyP, copyW, byteResult, wordResult, bytePtr, wordPtr,
    byteHeap, wordHeap, failedHeap, Zlib.Zutil.Proofs.allocHeap, setD, freeBytes, freeWords,
    upd_apply, h0, h1, h2, h3, Nat.add_assoc]

/-- The cleanup gives back every byte and word object of the heap after the record copy. -/
theorem fail_arrays {X : Heap} (hf : Fresh X) (n : Nat) (d : DeflateState) (x : Nat) :
    (failFreed X n d).bytes x = X.bytes x ∧ (failFreed X n d).words x = X.words x := by
  have fW : Fresh (copyW X d) := fresh_byteResult hf ((d.w_size * 2).toNat)
  have fP : Fresh (copyP X d) := fresh_wordResult fW ((d.w_size * 2).toNat / 2)
  have fQ : Fresh (copyQ X d) := fresh_wordResult fP ((d.hash_size * 2).toNat / 2)
  have popB : (freeBytes (copyB X d) (bytePtr (copyQ X d))).bytes x = (copyQ X d).bytes x :=
    byte_pop_at fQ ((d.lit_bufsize * 4).toNat) x
  have popQ : (freeWords (copyQ X d) (wordPtr (copyP X d))).words x = (copyP X d).words x :=
    word_pop_at fP ((d.hash_size * 2).toNat / 2) x
  have popP : (freeWords (copyP X d) (wordPtr (copyW X d))).words x = (copyW X d).words x :=
    word_pop_at fW ((d.w_size * 2).toNat / 2) x
  have popW : (freeBytes (copyW X d) (bytePtr X)).bytes x = X.bytes x :=
    byte_pop_at hf ((d.w_size * 2).toNat) x
  have b1 : (freeBytes (failBuf X n d) (bytePtr (copyQ X d))).bytes x = (copyQ X d).bytes x := by
    rw [freeBytes_congr_at (failBuf X n d) (copyB X d) (bytePtr (copyQ X d)) x rfl]
    exact popB
  have w1 : (freeBytes (failBuf X n d) (bytePtr (copyQ X d))).words x = (copyQ X d).words x := by
    rw [freeBytes_words]
    show (copyB X d).words x = _
    simp [copyB]
  have w2 : (freeWords (freeBytes (failBuf X n d) (bytePtr (copyQ X d))) (wordPtr (copyP X d))).words x =
      (copyP X d).words x := by
    rw [freeWords_congr_at _ (copyQ X d) _ x w1]
    exact popQ
  have w3 : (freeWords (freeWords (freeBytes (failBuf X n d) (bytePtr (copyQ X d))) (wordPtr (copyP X d)))
      (wordPtr (copyW X d))).words x = (copyW X d).words x := by
    rw [freeWords_congr_at _ (copyP X d) _ x w2]
    exact popP
  have b3 : (freeWords (freeWords (freeBytes (failBuf X n d) (bytePtr (copyQ X d))) (wordPtr (copyP X d)))
      (wordPtr (copyW X d))).bytes x = (copyW X d).bytes x := by
    rw [freeWords_bytes, freeWords_bytes, b1]
    simp [copyQ, copyP]
  constructor
  · unfold failFreed
    rw [freeBytes_congr_at _ (copyW X d) _ x b3]
    exact popW
  · unfold failFreed
    rw [freeBytes_words, w3]
    simp [copyW]

/-- The heap after a buffer failure agrees with the heap before the copy. -/
theorem fail_same {h : Heap} {d : DeflateState} (fresh : Fresh h) :
    FailSame h (failEnd (copyH0 h d) h.nextBlk d) := by
  have hfX : Fresh (copyH0 h d) :=
    fresh_setD_below (fresh_stateHeap fresh _) h.nextBlk (by simp [stateHeap]) d
  have arr := fail_arrays hfX h.nextBlk d
  have s1 : StableFields (copyH0 h d) (copyB (copyH0 h d) d) :=
    (((byteResult_stable _ _).trans (wordResult_stable _ _)).trans (wordResult_stable _ _)).trans
      (byteResult_stable _ _)
  have s2 : StableFields (failBuf (copyH0 h d) h.nextBlk d) (failFreed (copyH0 h d) h.nextBlk d) :=
    (((freeBytes_stable _ _).trans (freeWords_stable _ _)).trans (freeWords_stable _ _)).trans
      (freeBytes_stable _ _)
  have nW := byteResult_next (copyH0 h d) ((d.w_size * 2).toNat)
  have nP := wordResult_next (copyW (copyH0 h d) d) ((d.w_size * 2).toNat / 2)
  have nQ := wordResult_next (copyP (copyH0 h d) d) ((d.hash_size * 2).toNat / 2)
  have nB := byteResult_next (copyQ (copyH0 h d) d) ((d.lit_bufsize * 4).toNat)
  have n0 : (copyH0 h d).nextBlk = h.nextBlk + 1 := by simp [copyH0, stateHeap]
  have none0 : h.dstates h.nextBlk = none := (Heap.not_live.mp (fresh _ (Nat.le_refl _))).2.2.2.2.1
  refine ⟨fun x => (arr x).1, fun x => (arr x).2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    show (failFreed (copyH0 h d) h.nextBlk d).streams x = _
    rw [s2.streams]
    show (copyB (copyH0 h d) d).streams x = _
    rw [s1.streams]
    rfl
  · intro x
    show (failFreed (copyH0 h d) h.nextBlk d).gzheaders x = _
    rw [s2.gzheaders]
    show (copyB (copyH0 h d) d).gzheaders x = _
    rw [s1.gzheaders]
    rfl
  · intro x
    show upd (failFreed (copyH0 h d) h.nextBlk d).dstates h.nextBlk none x = _
    rw [s2.dstates]
    show upd (upd (copyB (copyH0 h d) d).dstates h.nextBlk _) h.nextBlk none x = _
    rw [s1.dstates]
    by_cases hx : x = h.nextBlk
    · subst hx
      simp [none0]
    · simp [upd_ne _ _ _ _ hx, copyH0, setD, stateHeap]
  · intro x
    show (failFreed (copyH0 h d) h.nextBlk d).istates x = _
    rw [s2.istates]
    show (copyB (copyH0 h d) d).istates x = _
    rw [s1.istates]
    rfl
  · intro x
    show (failFreed (copyH0 h d) h.nextBlk d).gzstates x = _
    rw [s2.gzstates]
    show (copyB (copyH0 h d) d).gzstates x = _
    rw [s1.gzstates]
    rfl
  · intro x hx
    have lt0 : x < (copyH0 h d).nextBlk := by omega
    have sW : SlotSame (copyH0 h d) (copyW (copyH0 h d) d) x := byteResult_old _ _ x lt0
    have sP : SlotSame (copyW (copyH0 h d) d) (copyP (copyH0 h d) d) x :=
      wordResult_old _ _ x (by simp only [copyW] at *; omega)
    have sQ : SlotSame (copyP (copyH0 h d) d) (copyQ (copyH0 h d) d) x :=
      wordResult_old _ _ x (by simp only [copyP, copyW] at *; omega)
    have sB : SlotSame (copyQ (copyH0 h d) d) (copyB (copyH0 h d) d) x :=
      byteResult_old _ _ x (by simp only [copyQ, copyP, copyW] at *; omega)
    have ro := ((sW.trans sP).trans sQ).trans sB
    show (failFreed (copyH0 h d) h.nextBlk d).ro x = _
    simp only [failFreed, freeBytes_ro, freeWords_ro]
    exact ro.2.2.2.2.2.2.2
  · show (failFreed (copyH0 h d) h.nextBlk d).static = _
    rw [s2.static]
    show (copyB (copyH0 h d) d).static = _
    rw [s1.static]
    rfl
  · show (failFreed (copyH0 h d) h.nextBlk d).allocOk = _
    rw [s2.allocOk]
    show (copyB (copyH0 h d) d).allocOk = _
    rw [s1.allocOk]
    rfl
  · show (failFreed (copyH0 h d) h.nextBlk d).garbage = _
    rw [s2.garbage]
    show (copyB (copyH0 h d) d).garbage = _
    rw [s1.garbage]
    rfl
  · show h.nextBlk ≤ (failFreed (copyH0 h d) h.nextBlk d).nextBlk
    simp only [failFreed, failBuf, freeBytes_nextBlk, freeWords_nextBlk, setD_nextBlk]
    simp only [copyB, copyQ, copyP, copyW] at *
    omega
  · show h.nalloc ≤ (failFreed (copyH0 h d) h.nextBlk d).nalloc
    simp [failFreed, failBuf, copyB, copyQ, copyP, copyW, copyH0, stateHeap]
    omega

theorem fail_count (h : Heap) (d : DeflateState) :
    (failEnd (copyH0 h d) h.nextBlk d).nalloc = h.nalloc + 5 := by
  show (failFreed (copyH0 h d) h.nextBlk d).nalloc = _
  simp [failFreed, failBuf, copyB, copyQ, copyP, copyW, copyH0, stateHeap, Nat.add_assoc]

/-- A `TRY_FREE` of a byte buffer. -/
theorem tryB_run {β : Type} {X : Heap} {r : ZStreamRef} {z : ZStream} {p : BPtr} {k : M β}
    (hz : r.get X = some z) (hf : z.zfree = .fn "zcfree")
    (hp : p = .null ∨ ∃ b a, p = .ref (.blk b) 0 ∧ X.bytes b = some a ∧ X.ro b = false) :
    (if p != .null then ZFREE_bytes (some r) p >>= (fun _ => k) else k) X = k (freeBytes X p) := by
  have run := zfreeB_run hz hf hp
  rcases hp with rfl | ⟨b, a, rfl, -, -⟩
  · simp [freeBytes]
  · simp [run]

/-- A `TRY_FREE` of a word buffer. -/
theorem tryW_run {β : Type} {X : Heap} {r : ZStreamRef} {z : ZStream} {p : WPtr} {k : M β}
    (hz : r.get X = some z) (hf : z.zfree = .fn "zcfree")
    (hp : p = .null ∨ ∃ b a, p = .ref (.blk b) 0 ∧ X.words b = some a) :
    (if p != .null then ZFREE_words (some r) p >>= (fun _ => k) else k) X = k (freeWords X p) := by
  have run := zfreeW_run hz hf hp
  rcases hp with rfl | ⟨b, a, rfl, -⟩
  · simp [freeWords]
  · simp [run]

theorem bytePtr_null {X : Heap} (e : bytePtr X = .null) : X.allocOk X.nalloc = false := by
  unfold bytePtr at e
  cases hx : X.allocOk X.nalloc
  · rfl
  · rw [hx] at e
    simp at e

theorem wordPtr_null {X : Heap} (e : wordPtr X = .null) : X.allocOk X.nalloc = false := by
  unfold wordPtr at e
  cases hx : X.allocOk X.nalloc
  · rfl
  · rw [hx] at e
    simp at e

/-! ## The goal -/

/-- **`deflateCopy` when an allocation fails.** If the state request or one of the four buffer
requests fails, the copy returns `Z_MEM_ERROR`; the source and its state are intact, only the
destination record changed (its `state` is `NULL`), a request failed, and the live blocks are
the old ones: everything allocated was freed. -/
theorem copy_failure {h : Heap} {source dest : ZStreamRef} {ds : Nat} {z zd : ZStream} {d : DeflateState}
    (inv : DInv h source ds z d) (distinct : source ≠ dest) (get : dest.get h = some zd)
    (fail : ¬ (h.allocOk h.nalloc = true ∧ bytePtr (copyH0 h d) ≠ .null ∧ wordPtr (copyW (copyH0 h d) d) ≠ .null ∧
      wordPtr (copyP (copyH0 h d) d) ≠ .null ∧ bytePtr (copyQ (copyH0 h d) d) ≠ .null)) :
    ∃ after, C.run (deflateCopy (some dest) (some source)) h = .ok (Z_MEM_ERROR, after) ∧
      source.get after = some z ∧ after.dstates ds = some d ∧
      ZlibF.Spec.Public.Frame h after (ZlibF.Spec.Public.StreamRoot dest) ∧
      ZlibF.Spec.Public.AllocationFailed h after ∧
      dest.get after = some { zd with state := none } ∧
      ZlibF.Spec.Public.LiveChange h after (fun _ => False) (fun _ => False) := by
  have good := inv.good
  have hL := good.live
  have fresh := good.fresh
  have hfree : z.zfree = .fn "zcfree" := inv.alloc.2
  have dsLt : ds < h.nextBlk := by
    rcases Nat.lt_or_ge ds h.nextBlk with lt | ge
    · exact lt
    · exact absurd (owned_live good (Or.inl rfl)) (fresh ds ge)
  have ne : h.nextBlk ≠ ds := by omega
  have e2 : zrd (some source) (·.state) h = .ok (z.state, h) := by rw [zrd_eq, hL.hz]
  by_cases ho : h.allocOk h.nalloc = true
  · -- the state is allocated and a buffer request fails
    have cond : (bytePtr (copyH0 h d) == .null || wordPtr (copyW (copyH0 h d) d) == .null ||
        wordPtr (copyP (copyH0 h d) d) == .null || bytePtr (copyQ (copyH0 h d) d) == .null) = true := by
      apply Classical.byContradiction
      intro hc
      simp only [Bool.not_eq_true, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hc
      exact fail ⟨ho, hc.1.1.1, hc.1.1.2, hc.1.2, hc.2⟩
    have freshH : Fresh (copyH0 h d) :=
      fresh_setD_below (fresh_stateHeap fresh _) h.nextBlk (by simp [stateHeap]) d
    have hzH : source.get (copyH0 h d) = some z := by simp [copyH0, hL.hz]
    have hsH : (copyH0 h d).dstates h.nextBlk = some d := by simp [copyH0]
    have e6 : copyDeflateState (some (.tab h.nextBlk)) (some (.tab ds))
        (stateHeap h (DeflateState.garbage (h.garbage h.nalloc))) = .ok ((), copyH0 h d) := by
      simp [copyDeflateState, ne, bind_app, ldD_eq, stD_eq, stateHeap, upd_ne _ _ _ _ (Ne.symm ne),
        hL.hs, copyH0, setD]
    have e7 : ldDeflateState (some (.tab h.nextBlk)) (copyH0 h d) = .ok (d, copyH0 h d) := by
      simp [ldD_eq, hsH]
    have e8 := copy_buffers_run freshH hzH inv.alloc.1 hsH (by simp [copyH0, stateHeap])
    obtain ⟨fB, fQ, fP, fW⟩ := fail_freeable (copyH0 h d) h.nextBlk d
    have zB : source.get (failBuf (copyH0 h d) h.nextBlk d) = some z := by
      simp [failBuf, copyB, copyQ, copyP, copyW, hzH]
    have dF : (failFreed (copyH0 h d) h.nextBlk d).dstates h.nextBlk =
        some (copyBufState (copyH0 h d) d) := by
      simp [failFreed, failBuf, setD]
    have same := fail_same (d := d) fresh
    obtain ⟨srcGet, dstates, frame, destGet, live⟩ :=
      copyFail_finish same fresh distinct hL.hz get { zd with state := none }
    have getEnd : dest.get (failEnd (copyH0 h d) h.nextBlk d) = some zd := (same.get dest).trans get
    refine ⟨dest.put (failEnd (copyH0 h d) h.nextBlk d) { zd with state := none }, ?_, srcGet,
      (dstates ds).trans hL.hs, frame, ?_, destGet, live⟩
    · rw [C.run]
      unfold deflateCopy
      simp only [show (some dest == (none : ZStreamPtr)) = false from rfl, Bool.false_eq_true, ↓reduceIte]
      simp only [copyFail_bind (stateCheck_live hL), bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      simp only [copyFail_bind e2, hL.zst]
      simp only [copyFail_bind castD]
      simp only [copyFail_bind (allocator_run hL.hz inv.alloc.1)]
      simp only [copyFail_bind (allocDeflateState_some ho (Heap.slotUsed_eq_false.mpr (fresh _ (Nat.le_refl _))))]
      simp only [show (some (DeflateStateRef.tab h.nextBlk) == none) = false from rfl, Bool.false_eq_true,
        ↓reduceIte]
      rw [show ({ h with dstates := upd h.dstates h.nextBlk (some (DeflateState.garbage (h.garbage h.nalloc))), nextBlk := h.nextBlk + 1, nalloc := h.nalloc + 1 } : Heap) =
        stateHeap h (DeflateState.garbage (h.garbage h.nalloc)) from rfl]
      simp only [copyFail_bind e6]
      simp only [copyFail_bind e7]
      rw [copyBuffers_bind]
      simp only [copyFail_bind e8]
      rw [ite_eq_left cond]
      rw [show setD (copyB (copyH0 h d) d) h.nextBlk (copyBufState (copyH0 h d) d) =
        failBuf (copyH0 h d) h.nextBlk d from rfl]
      rw [tryB_run zB hfree fB]
      rw [tryW_run (by simpa using zB) hfree fQ]
      rw [tryW_run (by simpa using zB) hfree fP]
      rw [tryB_run (by simpa using zB) hfree fW]
      rw [show freeBytes (freeWords (freeWords (freeBytes (failBuf (copyH0 h d) h.nextBlk d)
          (bytePtr (copyQ (copyH0 h d) d))) (wordPtr (copyP (copyH0 h d) d))) (wordPtr (copyW (copyH0 h d) d)))
          (bytePtr (copyH0 h d)) = failFreed (copyH0 h d) h.nextBlk d from rfl]
      rw [copyFail_bind (zfree_default_run (by simpa [failFreed] using zB) hfree)]
      rw [copyFail_bind (freeDeflateState_free_ok dF)]
      rw [show ({ failFreed (copyH0 h d) h.nextBlk d with dstates := upd (failFreed (copyH0 h d) h.nextBlk d).dstates h.nextBlk none } : Heap) =
        failEnd (copyH0 h d) h.nextBlk d from rfl]
      simp [zwr_eq, getEnd]
    · have nul : bytePtr (copyH0 h d) = .null ∨ wordPtr (copyW (copyH0 h d) d) = .null ∨
          wordPtr (copyP (copyH0 h d) d) = .null ∨ bytePtr (copyQ (copyH0 h d) d) = .null := by
        apply Classical.byContradiction
        intro hc
        simp only [not_or] at hc
        exact fail ⟨ho, hc.1, hc.2.1, hc.2.2.1, hc.2.2.2⟩
      have cnt : (dest.put (failEnd (copyH0 h d) h.nextBlk d) { zd with state := none }).nalloc =
          h.nalloc + 5 := by rw [ZStreamRef.put_nalloc, fail_count]
      rw [AllocationFailed, cnt]
      rcases nul with n1 | n2 | n3 | n4
      · have a := bytePtr_null n1
        simp [copyH0, stateHeap] at a
        exact ⟨_, by omega, by omega, a⟩
      · have a := wordPtr_null n2
        simp [copyW, copyH0, stateHeap] at a
        exact ⟨_, by omega, by omega, a⟩
      · have a := wordPtr_null n3
        simp [copyP, copyW, copyH0, stateHeap] at a
        exact ⟨_, by omega, by omega, a⟩
      · have a := bytePtr_null n4
        simp [copyQ, copyP, copyW, copyH0, stateHeap] at a
        exact ⟨_, by omega, by omega, a⟩
  · -- the state request fails
    have same : FailSame h ({ h with nalloc := h.nalloc + 1 } : Heap) :=
      ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl,
        fun _ _ => rfl, rfl, rfl, rfl, Nat.le_refl _, Nat.le_succ _⟩
    obtain ⟨srcGet, dstates, frame, destGet, live⟩ :=
      copyFail_finish same fresh distinct hL.hz get { zd with state := none }
    have getF : dest.get ({ h with nalloc := h.nalloc + 1 } : Heap) = some zd := (same.get dest).trans get
    refine ⟨dest.put ({ h with nalloc := h.nalloc + 1 } : Heap) { zd with state := none }, ?_, srcGet,
      (dstates ds).trans hL.hs, frame, ⟨h.nalloc, Nat.le_refl _, by simp, by simpa using ho⟩, destGet, live⟩
    rw [C.run]
    unfold deflateCopy
    simp only [show (some dest == (none : ZStreamPtr)) = false from rfl, Bool.false_eq_true, ↓reduceIte]
    simp only [copyFail_bind (stateCheck_live hL), bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    simp only [copyFail_bind e2, hL.zst]
    simp only [copyFail_bind castD]
    simp only [copyFail_bind (allocator_run hL.hz inv.alloc.1)]
    simp only [copyFail_bind (allocDeflateState_none ho)]
    simp only [show (none == (none : DeflateStatePtr)) = true from rfl, ↓reduceIte]
    simp [zwr_eq, getF]

end Zlib.Deflate.Universal

#print axioms Zlib.Deflate.Universal.copy_failure
