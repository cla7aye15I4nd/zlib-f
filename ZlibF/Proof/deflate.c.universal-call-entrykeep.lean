import ZlibF.Proof.«deflate.c.universal-call-contpend»

/-!
# deflate.c: the entry flush keeps the caller's bytes at any cursor (T2)

`CallerKeep.of_flush` states that a low-bit `flush_pending` keeps every caller byte range outside
the output range whose root is neither `pending_buf` nor the state record, with the pending cursor
at `pending_buf`. The entry flush of a call starts at whatever cursor the previous call left. Its
heap frame at any cursor is `StageFrame.of_flush_low`: the changed blocks are the stream root, the
state record, `pending_buf` and the output block (`OutputStorage`), and in the output block only
the written interval changes (`BufferFrame`). From that frame, `entry_keep_any` proves `EntryKeep`,
the premise of `cont_pending`: the caller bytes are kept, and so are the header records.
-/

namespace Zlib.Deflate.Universal.Call
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Deflate.Engine.Proofs
set_option autoImplicit false

/-- **A low-bit flush at any cursor keeps the caller bytes** outside the output range and outside
`pending_buf` and the state record. -/
theorem flush_keeps_bytes_any {h after : Heap} {r : ZStreamRef} {ds pb produced : Nat} {z z' : ZStream}
    {d : DeflateState} (good : DGood h r ds z d) (buffers : StreamBuffers h r)
    (pbuf : d.pending_buf = .ref (.blk pb) 0) (low : d.bi_valid.toInt < 8) (out : z.next_out ≠ .null)
    (run : flush_pending (some r) h = .ok ((), after)) (live : r.get after = some z')
    (account : StreamAccounting z z' 0 produced)
    {p : BPtr} {n : Nat} {xs : List UInt8} (bytes : Bytes h p n xs)
    (apart : Separate p n z.next_out z.avail_out.toNat) (keys : ∀ b, ByteRoot p b → b ≠ pb ∧ b ≠ ds) :
    Bytes after p n xs := by
  have stage := StageFrame.of_flush_low good buffers pbuf low out run live account
  rcases bytes with ⟨rfl, rfl, rfl⟩ | ⟨rp, ip, a, rfl, get, fits, rfl⟩
  · exact Or.inl ⟨rfl, rfl, rfl⟩
  right
  have le : produced ≤ z.avail_out.toNat := account.2.1
  have borrow : after.libcErrorBorrow = h.libcErrorBorrow :=
    Zlib.Deflate.BorrowProofs.stable_flush_pending (some r) h () after run
  have notPb : ∀ x, (rp = .blk x ∨ rp = .dstate_depth x) → x ≠ pb ∧ x ≠ ds := by
    intro x e
    have root : ByteRoot (.ref rp ip) x := by rcases e with rfl | rfl <;> rfl
    exact keys x root
  -- the output reference and its block
  obtain ⟨ob, oref, oo, ptr, kind, present⟩ : ∃ ob oref oo, z.next_out = .ref oref oo ∧
      (oref = .blk ob ∨ oref = .dstate_depth ob) ∧
      ((oref = .blk ob → h.bytes ob ≠ none) ∧ (oref = .dstate_depth ob → h.dstates ob ≠ none)) := by
    obtain ⟨ob, pointer⟩ := Block.output_pointer_cases good buffers out
    rcases pointer with ⟨oo, ptr⟩ | ⟨oo, ptr⟩
    · obtain ⟨output, outGet, _⟩ := caller_raw_output good buffers ptr
      exact ⟨ob, .blk ob, oo, ptr, Or.inl rfl,
        ⟨fun _ => by rw [outGet]; simp, fun e => BRef.noConfusion e⟩⟩
    · obtain ⟨foreign, outGet, _⟩ := caller_foreign_output good buffers ptr
      exact ⟨ob, .dstate_depth ob, oo, ptr, Or.inr rfl,
        ⟨fun e => BRef.noConfusion e, fun _ => by rw [outGet]; simp⟩⟩
  have root : ByteRoot z.next_out ob := by
    rcases kind with e | e <;> subst e <;> rw [ptr] <;> rfl
  have storage := stage.2 ob root
  by_cases onOut : rp = oref
  · subst onOut
    obtain ⟨a', getA, sizeA, keep⟩ := stage.1.1.2.2.2.1.2 ⟨z.next_out, produced⟩ (by simp) rp oo a ptr get
    rw [ptr] at apart
    have sep : n = 0 ∨ z.avail_out.toNat = 0 ∨ ip + n ≤ oo ∨ oo + z.avail_out.toNat ≤ ip := by
      rcases apart with e | e | e
      · exact Or.inl e
      · exact Or.inr (Or.inl e)
      · rcases e with e | e
        · exact absurd rfl e
        · exact Or.inr (Or.inr e)
    refine ⟨rp, ip, a', rfl, getA, by omega, (slice_of_pointwise ?_).symm⟩
    intro j lo hi
    apply keep j (by omega)
    rintro ⟨region, member, off, pointer, lo2, hi2⟩
    simp only [List.mem_singleton] at member
    subst member
    rw [ptr] at pointer
    simp only [Ptr.ref.injEq] at pointer
    obtain ⟨_, rfl⟩ := pointer
    exact separate_outside sep le lo hi ⟨lo2, hi2⟩
  · refine ⟨rp, ip, a, rfl, frame_view_same storage.frame borrow get ?_, fits, rfl⟩
    intro x e changed
    obtain ⟨xPb, xDs⟩ := notPb x e
    rcases changed with rootX | e2 | e2 | e2
    · rcases e with rfl | rfl
      · have b : h.bytes x ≠ none := by change h.bytes x = some a at get; rw [get]; simp
        obtain ⟨s1, _, s3⟩ := uniq_two good.uniq b
        rcases stream_root_tables good.live.hz rootX with t | t
        · exact t s1
        · exact t s3
      · have st : h.dstates x ≠ none := by
          change (h.dstates x).map (·.depth) = some a at get; intro e; rw [e] at get; cases get
        obtain ⟨_, s2, s3⟩ := uniq_dstates good.uniq st
        rcases stream_root_tables good.live.hz rootX with t | t
        · exact t s2
        · exact t s3
    · exact xDs e2
    · exact xPb e2
    · subst e2
      rcases e with rfl | rfl <;> rcases kind with rfl | rfl
      · exact onOut rfl
      · have b : h.bytes x ≠ none := by change h.bytes x = some a at get; rw [get]; simp
        exact present.2 rfl (uniq_two good.uniq b).2.1
      · have st : h.dstates x ≠ none := by
          change (h.dstates x).map (·.depth) = some a at get; intro e; rw [e] at get; cases get
        exact present.1 rfl (uniq_dstates good.uniq st).1
      · exact onOut rfl

/-- A low-bit flush at any cursor keeps the header records: its run changes only the stream
record, the state record and the output block. -/
theorem flush_keeps_gzheaders {h after : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream}
    {d : DeflateState} (good : DGood h r ds z d) (buffers : StreamBuffers h r)
    (pbuf : d.pending_buf = .ref (.blk pb) 0) (low : d.bi_valid.toInt < 8) (out : z.next_out ≠ .null)
    (run : flush_pending (some r) h = .ok ((), after)) : after.gzheaders = h.gzheaders := by
  obtain ⟨w, p, q, b, blocks⟩ := good.inv.blocks
  have key : b = pb := by simpa only [pbuf, Ptr.ref.injEq, BRef.blk.injEq, and_true] using blocks.pbuf.symm
  subst b
  obtain ⟨buf, get, size⟩ := blocks.ba
  obtain ⟨po, cursor, bound⟩ := blocks.pout
  have sourceBound : po + d.pending.toNat ≤ buf.size := by rw [size, ← blocks.psize]; exact bound
  by_cases zero : pendingLen d.pending z.avail_out = 0
  · have run0 := flush_pending_low_zero good.live.hz good.live.zst good.live.hs low zero
    have heaps := (Prod.mk.inj (Except.ok.inj (run0.symm.trans run))).2
    rw [← heaps]
  obtain ⟨ob, pointer⟩ := Block.output_pointer_cases good buffers out
  rcases pointer with ⟨oo, ptr⟩ | ⟨oo, ptr⟩
  · obtain ⟨output, outGet, writable, outBound, outside⟩ := caller_raw_output good buffers ptr
    have separate : ob ≠ pb := by
      intro e; subst e; exact outside (Or.inr (Or.inr (Or.inr (Or.inr pbuf))))
    have run0 := flush_pending_low_raw good.live.hz good.live.zst good.live.hs low ptr cursor outGet get writable
      separate outBound sourceBound zero
    have heaps := (Prod.mk.inj (Except.ok.inj (run0.symm.trans run))).2
    rw [← heaps]
    simp
  · obtain ⟨foreign, outGet, outBound, different, _, _⟩ := caller_foreign_output good buffers ptr
    have run0 := flush_pending_low_foreign good.live.hz good.live.zst good.live.hs low ptr cursor outGet get
      (Ne.symm different) outBound sourceBound zero
    have heaps := (Prod.mk.inj (Except.ok.inj (run0.symm.trans run))).2
    rw [← heaps]
    simp

/-- **T2: the entry flush at any cursor** keeps the caller's bytes outside the output range,
`pending_buf` and the state record, and the header records (`EntryKeep`, the premise of
`cont_pending`). -/
theorem entry_keep_any : EntryKeep := by
  intro h after r ds pb produced z z' d good buffers pbuf low out run live account
  exact ⟨fun _ _ _ bytes apart keys =>
      flush_keeps_bytes_any good buffers pbuf low out run live account bytes apart keys,
    flush_keeps_gzheaders good buffers pbuf low out run⟩

end Zlib.Deflate.Universal.Call
