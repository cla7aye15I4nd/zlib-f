import ZlibF.Proof.«inflate.c.default-invariant»
import ZlibF.Proof.«inflate.c.table-rebuffer»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Caller edits preserve every stream-owned decoder allocation. -/
theorem rebuffer_inflate_owned {h after : Heap} {r : ZStreamRef} {zs b : Nat}
    {z : ZStream} {s : InflateState} (good : Good h r zs z s) (edit : Rebuffer h after r)
    (owned : InflateOwned zs s b) :
    after.bytes b = h.bytes b ∧ after.ro b = h.ro b := by
  have streamOwn : StreamOwned h r b :=
    ⟨z, good.live.hz, Or.inl ⟨zs, s, good.live.zst, good.live.hs, owned⟩⟩
  have live : h.live b := by
    rcases owned with equal | window
    · subst b
      simp [Heap.live, good.live.hs]
    · rcases good.inv.win.block with null | ⟨w, array, pointer, get, _⟩
      · rw [null] at window
        cases window
      · rw [window] at pointer
        cases pointer
        simp [Heap.live, get]
  have slot := edit.2.2.2.1.2.2.2.2.2 b live (by intro unowned; exact unowned streamOwn)
  exact ⟨slot.1, slot.2.2.2.2.2.2.2⟩

/-- The public rebuffer frame preserves Good and the exact decoder state.
No fact about the old or new caller buffer contents is assumed. -/
theorem rebuffer_inflate_good {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (good : Good h r zs z s) (edit : Rebuffer h after r) :
    ∃ stream, stream = { z with next_in := stream.next_in, avail_in := stream.avail_in, next_out := stream.next_out, avail_out := stream.avail_out } ∧ Good after r zs stream s := by
  have changes := edit
  obtain ⟨fresh, uniq, globals, frame, old, stream, oldGet, newGet, changed⟩ := changes
  have same : old = z := Option.some.inj (oldGet.symm.trans good.live.hz)
  subst old
  have owned : StreamOwned h r zs :=
    ⟨z, good.live.hz, Or.inl ⟨zs, s, good.live.zst, good.live.hs, Or.inl rfl⟩⟩
  have live : h.live zs := by simp [Heap.live, good.live.hs]
  have slot := frame.2.2.2.2.2 zs live (by intro unowned; exact unowned owned)
  have state : after.istates zs = some s := slot.2.2.2.2.2.1.trans good.live.hs
  have window : WinInv after s := by
    refine { good.inv.win with block := ?_ }
    rcases good.inv.win.block with null | ⟨b, array, pointer, get, writable, size⟩
    · exact Or.inl null
    · have kept := rebuffer_inflate_owned good edit (Or.inr pointer)
      exact Or.inr ⟨b, array, pointer, kept.1.trans get, kept.2.trans writable, size⟩
  have inv : StInv after zs s := ⟨good.inv.wf, window, good.inv.reqbits, good.inv.bits, good.inv.ptr⟩
  refine ⟨stream, changed, ⟨⟨newGet, state, ?_, good.live.back, good.live.mode, ?_, ?_⟩, inv, uniq, fresh⟩⟩
  all_goals rw [changed]
  · exact good.live.zst
  · exact good.live.zalloc
  · exact good.live.zfree

/-- Replacing public buffers retains the complete default relation. The
new caller storage must satisfy the explicit platform scope; this bound
is not inferred from the allocator or imposed on its byte contents. -/
theorem rebuffer_default_J {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (invariant : DefaultDecodeJ h r zs z s)
    (edit : Rebuffer h after r) (platform : ZlibF.PlatformMemory.ByteObjectsFit after) :
    ∃ stream, DefaultDecodeJ after r zs stream s := by
  obtain ⟨stream, _, good⟩ := rebuffer_inflate_good invariant.good edit
  have tables := (rebuffer_dataTableInvariant invariant.good edit invariant.tables).2
  exact ⟨stream, ⟨good, tables, invariant.pending, invariant.lengths, invariant.headerLengths,
    invariant.held, invariant.window, invariant.wrapper, invariant.header, invariant.modes,
    invariant.trailer, edit.2.2.1, platform⟩⟩


/-- Default-wrapper histories cannot register a borrowed gzip header.
The actual call rejects every header argument before reading its object. -/
theorem inflateGetHeader_default_J {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (invariant : DefaultDecodeJ h r zs z s) (head : GzHeaderPtr) :
    C.run (inflateGetHeader (some r) head) h = .ok (Z_STREAM_ERROR, h) ∧ DefaultDecodeJ h r zs z s := by
  have noGzip : s.wrap &&& 2 = 0 := by
    rcases invariant.wrapper with wrap | wrap | wrap <;> rw [wrap] <;> decide
  exact ⟨inflateGetHeader_nogzip invariant.good.live head noGzip, invariant⟩

/-- The selected build refuses undermining and retains the initialized
sane value. Its actual write leaves the complete default relation intact. -/
theorem inflateUndermine_default_J {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (invariant : DefaultDecodeJ h r zs z s) (subvert : Int32) :
    C.run (inflateUndermine (some r) subvert) h = .ok (Z_DATA_ERROR, h) ∧ DefaultDecodeJ h r zs z s := by
  obtain ⟨after, run, heap, _⟩ := inflateUndermine_safe invariant.good subvert
  have state : { s with sane := 1 } = s := by rw [← invariant.pending.sane]
  have same : after = h := by rw [heap, state, tcSetI_same invariant.good.live.hs]
  exact ⟨by simpa only [same] using run, invariant⟩

end Zlib.Inflate.Proofs
