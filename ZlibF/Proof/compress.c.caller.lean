import ZlibF.Proof.«compress.c.loop»
import ZlibF.Proof.«deflate.c.engine.common-ordinary-history-completes»
import ZlibF.Proof.«deflate.c.default-core-rebuffer»

/-! # Actual automatic stream and caller edits in compress.c

This is an explicitly internal Uniq/raw-output milestone. It does not
replace the broader public utility domain or its capacity guarantee.
-/
namespace ZlibF.Spec.Public.Proofs.CompressCaller
open C Zlib.Compress Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open Zlib.Deflate.Engine.Proofs
open ZlibF.Spec.Public.Proofs.CompressLoop
set_option autoImplicit false
set_option maxRecDepth 100000

/-- The real automatic record after the three allocator-field assignments. -/
def localStream (h : Heap) : ZStream :=
  { ZStream.garbage (h.garbage h.nalloc) with
    zalloc := .null, zfree := .null, «opaque» := .null }

def localHeap (h : Heap) : Heap :=
  { h with streams := upd h.streams h.nextBlk (some (localStream h)), nextBlk := h.nextBlk + 1 }

private theorem version_index : strIndex ZLIB_VERSION = some 57 := by decide +kernel

private theorem version_run (h : Heap) :
    Zlib.Zutil.zlibVersion h = .ok (.ref (.str 57) 0, h) := by
  simp [Zlib.Zutil.zlibVersion, Zlib.Zutil.strLit, strLitRef, version_index]

/-- The actual pre-init program in compress2_z allocates its local stream,
writes the three fields, and fetches the actual version without consuming
an allocation-failure index. -/
theorem automatic_stream_run (h : Heap) (fresh : Fresh h) :
    C.run (do
      let strm ← allocLocalZ
      zwr strm (fun z => { z with zalloc := .null, zfree := .null, «opaque» := .null })
      let version ← Zlib.Zutil.zlibVersion
      pure (strm, version)) h =
      .ok ((some (.tab h.nextBlk), .ref (.str 57) 0), localHeap h) := by
  have slot : ({ h with allocOk := fun _ => true } : Heap).slotUsed h.nextBlk = false :=
    fresh.slotUsed_next
  simp [C.run, allocLocalZ, allocZStream, slot, zwr, ldZStream, stZStream,
    ZStreamRef.get, ZStreamRef.put, ZStreamRef.isRo, localHeap, localStream, upd_upd, version_run]

/-- The InitDomain needed by the queued real-initializer theorem is
established by the actual automatic record. Global Uniq is explicit in
this internal milestone and has not been added to the public utility goal. -/
theorem automatic_stream_domain (h : Heap) (fresh : Fresh h)
    (unique : Zlib.Inflate.Spec.Uniq h) (globals : LibraryGlobals h) :
    InitDomain (localHeap h) (.tab h.nextBlk) (.ref (.str 57) 0) := by
  have freshA : Fresh (localHeap h) := by
    intro b bound live
    have different : b ≠ h.nextBlk := by change h.nextBlk + 1 ≤ b at bound; omega
    apply fresh b (by change h.nextBlk + 1 ≤ b at bound; omega)
    simpa only [localHeap, Heap.live, upd_ne _ _ _ _ different] using live
  have uniqueA : Zlib.Inflate.Spec.Uniq (localHeap h) := by
    intro b
    by_cases same : b = h.nextBlk
    · subst b
      obtain ⟨e0, e1, e2, e3, e4, e5, e6⟩ := Heap.not_live.mp (fresh _ (Nat.le_refl _))
      simp [Zlib.Inflate.Spec.cnt, localHeap, e0, e1, e3, e4, e5, e6]
    · simpa only [localHeap, upd_ne _ _ _ _ same] using unique b
  have versionBytes : Space.get (localHeap h) (BRef.str 57) = some (strBytes ZLIB_VERSION) := by
    rw [BRef.get_str]
    rfl
  refine ⟨freshA, uniqueA, globals, ?_, localStream h, ?_, ?_, rfl⟩
  · exact Or.inr ⟨49, rfl, Or.inr ⟨.str 57, 0, strBytes ZLIB_VERSION,
      rfl, versionBytes, by decide +kernel, by decide +kernel⟩⟩
  · simp [ZStreamRef.get, localHeap]
  · exact ⟨Or.inl rfl, Or.inl rfl⟩

/-- An actual caller-only update of the four buffer fields is a legal
Rebuffer. The live stream representation comes from the real initializer
or an actual request history, not a callee-contract assumption. -/
theorem buffer_fields_rebuffer {h : Heap} {slot ds : Nat} {z : ZStream} {d : DeflateState}
    (good : DGood h (.tab slot) ds z d) (globals : LibraryGlobals h)
    (next : ZStream)
    (fields : next = { z with next_in := next.next_in, avail_in := next.avail_in, next_out := next.next_out, avail_out := next.avail_out }) :
    Rebuffer h ((ZStreamRef.tab slot).put h next) (.tab slot) := by
  have shape := shape_put good.live.hz next
  have getNext := ZStreamRef.get_put_same good.live.hz next
  have frame := full_frame_weaken (stream_store_full_frame h (.tab slot) next)
    (fun b root => ZlibF.Spec.Public.Proofs.DeflateCore.stream_root_unowned good root)
  have globalsNext : LibraryGlobals ((ZStreamRef.tab slot).put h next) := by
    simpa [LibraryGlobals, ZStreamRef.put, show h.streams slot = some z from good.live.hz] using globals
  exact ⟨shape.fresh (by simp) good.fresh, shape.uniq good.uniq, globalsNext,
    frame, z, next, good.live.hz, getNext, fields⟩

/-- The prepare heap in the actual loop is exactly a four-field caller
update of its live local stream, including iterations with no refill. -/
theorem prepare_eq_put (h : Heap) (slot : Nat) (z : ZStream) (left sourceLen : UInt64)
    (get : h.streams slot = some z) :
    (prepare h slot z left sourceLen).2.2 =
      (ZStreamRef.tab slot).put h (CompressLoop.preparedStream z left sourceLen) := by
  by_cases outEmpty : z.avail_out = 0 <;>
    by_cases inEmpty : z.avail_in = 0 <;>
    simp [prepare, CompressLoop.preparedStream, ZStreamRef.put, get, outEmpty, inEmpty, upd_upd]
  simpa only [ZStreamRef.put, get] using (ZStreamRef.put_self (r := .tab slot) get).symm

/-- Every actual loop refill is a proved legal Rebuffer of the same
local stream and private compressor state. -/
theorem prepare_rebuffer {h : Heap} {slot ds : Nat} {z : ZStream} {d : DeflateState}
    (good : DGood h (.tab slot) ds z d) (globals : LibraryGlobals h)
    (left sourceLen : UInt64) :
    Rebuffer h (prepare h slot z left sourceLen).2.2 (.tab slot) := by
  rw [prepare_eq_put h slot z left sourceLen good.live.hz]
  apply buffer_fields_rebuffer good globals
  rfl

/-- Caller-owned extents include the current avail counts and the bytes
not yet offered by the wrapper. The source is the exact unread suffix,
not a promised encoding or an engine invariant. -/
structure Ranges (h : Heap) (r : ZStreamRef) (z : ZStream)
    (left sourceLen : UInt64) (source : List UInt8) : Prop where
  input : CallerRange h r z.next_in (z.avail_in.toNat + sourceLen.toNat) false
  output : CallerRange h r z.next_out (z.avail_out.toNat + left.toNat) true
  separate : Separate z.next_in (z.avail_in.toNat + sourceLen.toNat)
    z.next_out (z.avail_out.toNat + left.toNat)
  snapshot : Bytes h z.next_in (z.avail_in.toNat + sourceLen.toNat) source

/-- Taking a prefix retains a readable caller range on the same heap. -/
theorem bytes_take {h : Heap} {p : BPtr} {n m : Nat} {xs : List UInt8}
    (bytes : Bytes h p n xs) (bound : m ≤ n) : Bytes h p m (xs.take m) := by
  rcases bytes with ⟨rfl, rfl, rfl⟩ | ⟨ref, off, a, rfl, get, fit, value⟩
  · have zero : m = 0 := by omega
    subst m
    exact Or.inl ⟨rfl, rfl, rfl⟩
  · refine Or.inr ⟨ref, off, a, rfl, get, by omega, ?_⟩
    rw [value, List.take_take, Nat.min_eq_left bound]

/-- Storing a stream record changes no readable caller byte snapshot. -/
theorem bytes_put {h : Heap} {p : BPtr} {n : Nat} {xs : List UInt8}
    (bytes : Bytes h p n xs) (r : ZStreamRef) (next : ZStream) :
    Bytes (r.put h next) p n xs := by
  rcases bytes with null | ⟨ref, off, a, pointer, get, bound, value⟩
  · exact Or.inl null
  · exact Or.inr ⟨ref, off, a, pointer, (byte_get_stream_put h r next ref).trans get, bound, value⟩

/-- Restricting caller extents to current avail counts establishes the
real engine's StreamBuffers domain and its exact offered input snapshot. -/
theorem ranges_current {h : Heap} {r : ZStreamRef} {z : ZStream}
    {left sourceLen : UInt64} {source : List UInt8}
    (get : r.get h = some z) (ranges : Ranges h r z left sourceLen source) :
    StreamBuffers h r ∧ Bytes h z.next_in z.avail_in.toNat (source.take z.avail_in.toNat) := by
  have sizes : ByteSizes h h := ⟨fun _ _ eq => ⟨_, eq, rfl⟩, fun _ => rfl⟩
  have own : ∀ b, StreamOwned h r b ↔ StreamOwned h r b := fun _ => Iff.rfl
  have input := caller_range_sizes ranges.input sizes own (used := 0) (remaining := z.avail_in.toNat) (by omega)
  have output := caller_range_sizes ranges.output sizes own (used := 0) (remaining := z.avail_out.toNat) (by omega)
  have separated := separate_advance_right
    (separate_advance_left ranges.separate (used := 0) (remaining := z.avail_in.toNat) (by omega))
    (used := 0) (remaining := z.avail_out.toNat) (by omega)
  exact ⟨⟨z, get, by simpa only [advance_zero] using input,
    by simpa only [advance_zero] using output, by simpa only [advance_zero] using separated⟩,
    bytes_take ranges.snapshot (by omega)⟩

/-- Actual refill preserves the full unread source and unwritten output
extents. In particular newly offered chunks are justified by the original
caller memory, rather than assuming StreamBuffers anew at every iteration. -/
theorem prepare_ranges {h : Heap} {slot ds : Nat} {z : ZStream} {d : DeflateState}
    {left sourceLen : UInt64} {source : List UInt8}
    (good : DGood h (.tab slot) ds z d) (ranges : Ranges h (.tab slot) z left sourceLen source) :
    Ranges (prepare h slot z left sourceLen).2.2 (.tab slot)
      (CompressLoop.preparedStream z left sourceLen)
      (prepare h slot z left sourceLen).1 (prepare h slot z left sourceLen).2.1 source := by
  let next := CompressLoop.preparedStream z left sourceLen
  have goodNext : DGood ((ZStreamRef.tab slot).put h next) (.tab slot) ds next d :=
    stream_control_good good rfl good.live.zalloc good.live.zfree
  have own := stream_owned_keys good goodNext rfl rfl rfl rfl
  have sizes := stream_control_sizes h (.tab slot) next
  have counts := prepare_counts h slot z left sourceLen
  change (prepare h slot z left sourceLen).1.toNat + next.avail_out.toNat = _ ∧
    (prepare h slot z left sourceLen).2.1.toNat + next.avail_in.toNat = _ at counts
  rw [prepare_eq_put h slot z left sourceLen good.live.hz]
  have input := caller_range_sizes ranges.input sizes own (used := 0)
    (remaining := next.avail_in.toNat + (prepare h slot z left sourceLen).2.1.toNat) (by omega)
  have output := caller_range_sizes ranges.output sizes own (used := 0)
    (remaining := next.avail_out.toNat + (prepare h slot z left sourceLen).1.toNat) (by omega)
  refine ⟨by simpa only [advance_zero, next, CompressLoop.preparedStream] using input,
    by simpa only [advance_zero, next, CompressLoop.preparedStream] using output, ?_, ?_⟩
  · change Separate z.next_in _ z.next_out _
    have inputCount : next.avail_in.toNat + (prepare h slot z left sourceLen).2.1.toNat =
        z.avail_in.toNat + sourceLen.toNat := by omega
    have outputCount : next.avail_out.toNat + (prepare h slot z left sourceLen).1.toNat =
        z.avail_out.toNat + left.toNat := by omega
    rw [inputCount, outputCount]
    exact ranges.separate
  · change Bytes ((ZStreamRef.tab slot).put h next) z.next_in _ source
    have snapshot := bytes_put ranges.snapshot (.tab slot) next
    have inputCount : next.avail_in.toNat + (prepare h slot z left sourceLen).2.1.toNat =
        z.avail_in.toNat + sourceLen.toNat := by omega
    rw [inputCount]
    exact snapshot

end ZlibF.Spec.Public.Proofs.CompressCaller
