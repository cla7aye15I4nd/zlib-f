import ZlibF.Proof.«deflate.c.life.end»

/-! # deflate.c: cleanup of a partially allocated initializer state -/

namespace Zlib.Deflate.Proofs.DefaultInit
open C Zlib.Deflate Zlib.Deflate.Spec
set_option autoImplicit false

def FreeableB (h : Heap) (p : BPtr) : Prop :=
  p = .null ∨ ∃ b a, p = .ref (.blk b) 0 ∧ h.bytes b = some a ∧ h.ro b = false

def FreeableW (h : Heap) (p : WPtr) : Prop :=
  p = .null ∨ ∃ b a, p = .ref (.blk b) 0 ∧ h.words b = some a

theorem freeableB_after {h : Heap} {p q : BPtr} (hq : FreeableB h q)
    (hp : FreeableB h p) (hsep : p = .null ∨ q = .null ∨ p ≠ q) : FreeableB (freeBytes h p) q := by
  rcases hq with rfl | ⟨qb, qa, rfl, hqa, hqr⟩
  · exact Or.inl rfl
  · rcases hp with rfl | ⟨pb, pa, rfl, hpa, hpr⟩
    · exact Or.inr ⟨qb, qa, rfl, hqa, hqr⟩
    · have hn : qb ≠ pb := by
        rcases hsep with impossible | impossible | hn
        · cases impossible
        · cases impossible
        · intro he
          subst qb
          exact hn rfl
      exact Or.inr ⟨qb, qa, rfl, by simpa [freeBytes, upd_ne _ _ _ _ hn] using hqa, hqr⟩

theorem freeableW_after {h : Heap} {p q : WPtr} (hq : FreeableW h q)
    (hp : FreeableW h p) (hsep : p = .null ∨ q = .null ∨ p ≠ q) : FreeableW (freeWords h p) q := by
  rcases hq with rfl | ⟨qb, qa, rfl, hqa⟩
  · exact Or.inl rfl
  · rcases hp with rfl | ⟨pb, pa, rfl, hpa⟩
    · exact Or.inr ⟨qb, qa, rfl, hqa⟩
    · have hn : qb ≠ pb := by
        rcases hsep with impossible | impossible | hn
        · cases impossible
        · cases impossible
        · intro he
          subst qb
          exact hn rfl
      exact Or.inr ⟨qb, qa, rfl, by simpa [freeWords, upd_ne _ _ _ _ hn] using hqa⟩

theorem freeB_continue {α : Type} {h : Heap} {r : ZStreamRef} {z : ZStream} {p : BPtr}
    (hz : r.get h = some z) (hf : z.zfree = .fn "zcfree") (hp : FreeableB h p) (k : M α) :
    (if p != .null then do ZFREE_bytes (some r) p; k else k) h = k (freeBytes h p) := by
  by_cases hn : p = .null
  · subst p
    rfl
  · have hr := zfreeB_run hz hf hp
    simp [hn, bind_app, hr]

theorem freeW_continue {α : Type} {h : Heap} {r : ZStreamRef} {z : ZStream} {p : WPtr}
    (hz : r.get h = some z) (hf : z.zfree = .fn "zcfree") (hp : FreeableW h p) (k : M α) :
    (if p != .null then do ZFREE_words (some r) p; k else k) h = k (freeWords h p) := by
  by_cases hn : p = .null
  · subst p
    rfl
  · have hr := zfreeW_run hz hf hp
    simp [hn, bind_app, hr]

/-- `int deflateEnd(z_streamp strm)`.
The actual cleanup also executes on partially allocated init buffers. The
source accepts NULL buffers; no DGood or complete-buffer premise is needed.
Distinct non-NULL buffers of each element type are freed once. -/
theorem end_partial_run {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (hl : DLive h r ds z d) (hf : z.zfree = .fn "zcfree")
    (hb : FreeableB h d.pending_buf) (hw : FreeableB h d.window)
    (hq : FreeableW h d.head) (hp : FreeableW h d.prev)
    (hwb : d.pending_buf = .null ∨ d.window = .null ∨ d.pending_buf ≠ d.window)
    (hpq : d.head = .null ∨ d.prev = .null ∨ d.head ≠ d.prev) :
    deflateEnd (some r) h =
      .ok ((if d.status == BUSY_STATE then Z_DATA_ERROR else Z_OK), endHeap h r ds z d) := by
  have hq1 : FreeableW (freeBytes h d.pending_buf) d.head := by
    simpa only [FreeableW, freeBytes_words] using hq
  have hp1 : FreeableW (freeBytes h d.pending_buf) d.prev := by
    simpa only [FreeableW, freeBytes_words] using hp
  have hp2 := freeableW_after hp1 hq1 hpq
  have hw1 := freeableB_after hw hb hwb
  have hw3 : FreeableB (freeWords (freeWords (freeBytes h d.pending_buf) d.head) d.prev) d.window := by
    simpa only [FreeableB, freeWords_bytes, freeWords_ro] using hw1
  unfold deflateEnd
  simp only [bind_app, stateCheck_live hl, bne_self_eq_false, Bool.false_eq_true, ite_false,
    zrd_eq, hl.hz, hl.zst, castD, rdD_eq, hl.hs]
  rw [freeB_continue hl.hz hf hb]
  simp only [bind_app, rdD_eq, freeBytes_dstates, hl.hs]
  rw [freeW_continue (by simpa using hl.hz) hf hq1]
  simp only [bind_app, rdD_eq, freeWords_dstates, freeBytes_dstates, hl.hs]
  rw [freeW_continue (by simpa using hl.hz) hf hp2]
  simp only [bind_app, rdD_eq, freeWords_dstates, freeBytes_dstates, hl.hs]
  rw [freeB_continue (by simpa using hl.hz) hf hw3]
  rw [bind_app, zfree_default_run (by simpa using hl.hz) hf]
  simp only []
  rw [bind_app, freeDeflateState_free_ok (d := d) (by simpa using hl.hs)]
  simp only [zwr_eq, ZStreamRef.get_dstates, ZStreamRef.get_freeBytes, ZStreamRef.get_freeWords,
    hl.hz, bind_app, pure_app, ZStreamRef.put_with_dstates, endHeap, freeBytes_dstates, freeWords_dstates]

end Zlib.Deflate.Proofs.DefaultInit
