import ZlibF.Proof.«inflate.c.window»

/-!
# inflate.c: non-vacuity witnesses for the stream-management theorems

A heap with one writable `z_stream` (all zero: the caller gave no allocator functions) and nothing else. The real
`inflateInit2_` runs on it (through `inflateInit2_ok`, whose hypotheses are checked here), and the heap it makes
satisfies the hypotheses (`Good`) of `inflateResetKeep_safe`, `inflateReset_safe`, `inflateReset2_safe`,
`inflateEnd_safe` and `inflateStateCheck_total`, which are then applied to it.
-/

namespace Zlib.Inflate.Witness
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs

/-- One stream (block 0, all zero: no allocator functions) and a read-only byte block 1 holding "1" (the version
string's first character); the next free block is 2. -/
def h0 : Heap :=
  { Heap.empty with
    streams := upd Heap.empty.streams 0 (some ZStream.zeroed),
    bytes := upd Heap.empty.bytes 1 (some #[49, 0]),
    ro := upd Heap.empty.ro 1 true,
    nextBlk := 2 }

theorem h0_uniq : Uniq h0 := by
  intro b
  by_cases h1 : b = 1
  · subst h1; simp [h0, Heap.empty, upd_ne _ _ _ _ (by decide : (1 : Nat) ≠ 0)]
  by_cases h0' : b = 0
  · subst h0'; simp [h0, Heap.empty, upd_ne _ _ _ _ (by decide : (0 : Nat) ≠ 1)]
  · simp [h0, Heap.empty, upd_ne _ _ _ _ h1, upd_ne _ _ _ _ h0']

theorem h0_fresh : Fresh h0 := by
  intro b hb hl
  have hb' : 2 ≤ b := hb
  have h1 : b ≠ 1 := by omega
  have h0' : b ≠ 0 := by omega
  simp [Heap.live, h0, Heap.empty, upd_ne _ _ _ _ h1, upd_ne _ _ _ _ h0'] at hl

theorem h0_get : (ZStreamRef.tab 0).get h0 = some ZStream.zeroed := by
  simp [ZStreamRef.get, h0, upd_ne _ _ _ _ (by decide : (0 : Nat) ≠ 1)]

theorem h0_version : OkOn h0 (index8 (.ref (.blk 1) 0) 0) 49 := by
  have := index8_ok (h := h0) (blk := 1) (off := 0) (i := 0) (bytes := #[49, 0]) (by simp [h0]) (by simp)
  simpa using this

theorem params15 : reset2Params 15 = some (5, 15) := by decide

/-- The real `inflateInit2_` runs on `h0` (all hypotheses of `inflateInit2_ok` hold there) and makes a heap that
satisfies the hypotheses `Good` of the other theorems. -/
theorem init_witness : ∃ (h1 : Heap) (z1 : ZStream) (st1 : InflateState),
    C.run (inflateInit2_ (some (.tab 0)) 15 (.ref (.blk 1) 0) 112) h0 = .ok (Z_OK, h1) ∧
    Good h1 (.tab 0) 2 z1 st1 ∧ z1.zfree = .fn "zcfree" := by
  obtain ⟨h1, hr, -, hG, -⟩ := inflateInit2_ok (r := .tab 0) (z := ZStream.zeroed) (w := 15) (version := .ref (.blk 1) 0)
    h0_uniq h0_fresh h0_get (by simp [h0, Heap.empty]) (Or.inl rfl) (Or.inl rfl) (by simp) h0_version params15 |>.imp
    fun h' hh => hh
  refine ⟨h1, _, _, hr, hG, ?_⟩
  have e : ZStream.zeroed.zfree = FnPtr.null := rfl
  simp [resetKeepStream, initStream2, initStream, e]

end Zlib.Inflate.Witness
