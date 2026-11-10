import ZlibF.Proof.«compress.c.caller»
import ZlibF.Proof.«deflate.c.borrow-stable-lifecycle»

/-! # Real default initialization establishes the wrapper's caller-memory seed

Uniq and raw output are explicit internal scope. Caller input may use any
readable BRef and separated input/output ranges may share an allocation.
-/
namespace ZlibF.Spec.Public.Proofs.CompressCaller
open C Zlib.Compress Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open Zlib.Deflate.Engine.Proofs Zlib.Deflate.Proofs.DefaultInit
set_option autoImplicit false
set_option maxRecDepth 100000

private theorem old_view_after_init {h initialized : Heap} {p : ZlibF.Spec.Api.DeflParams}
    (fresh : Fresh h) (initial : DeflateInitial (localHeap h) initialized (.tab h.nextBlk) p)
    (borrow : initialized.libcErrorBorrow = h.libcErrorBorrow)
    {ref : BRef} {a : Array UInt8} (get : Space.get h ref = some a) :
    Space.get initialized ref = some a ∧ Space.ro initialized ref = Space.ro h ref ∧
      ∀ off b, ByteRoot (.ref ref off) b → ¬ StreamOwned initialized (.tab h.nextBlk) b := by
  obtain ⟨z, d, good, _a, _f, _level, _strategy, _bits, _hash, _wrap, _start, _look,
    _pending, _valid, _header, _tin, _tout, _msg, frame, _live, owned⟩ := initial
  have oldSlot : ∀ b, h.live b → SlotSame (localHeap h) initialized b := by
    intro b live
    have below := fresh.lt live
    have different : b ≠ h.nextBlk := by omega
    apply frame.2.2.2.2.2 b
    · simpa only [localHeap, Heap.live, upd_ne _ _ _ _ different] using live
    · change b ≠ h.nextBlk
      exact different
  have outside : ∀ b, h.live b → ¬ StreamOwned initialized (.tab h.nextBlk) b := by
    intro b live now
    have low := ((owned b).mp ((stream_owned_deflate good b).mp now)).1
    have below := fresh.lt live
    change h.nextBlk + 1 ≤ b at low
    omega
  cases ref with
  | blk b =>
    have live : h.live b := by simp [Heap.live, show h.bytes b = some a from get]
    have slot := oldSlot b live
    exact ⟨slot.1.trans get, slot.2.2.2.2.2.2.2,
      fun _ x root => by change x = b at root; subst x; exact outside b live⟩
  | dstate_depth b =>
    cases state : h.dstates b with
    | none => simp [Space.get, state] at get
    | some d0 =>
      have live : h.live b := by simp [Heap.live, state]
      have slot := oldSlot b live
      refine ⟨?_, rfl, fun _ x root => by change x = b at root; subst x; exact outside b live⟩
      change (initialized.dstates b).map (·.depth) = some a
      rw [slot.2.2.2.2.1]
      exact get
  | str i => exact ⟨(C.LibcBorrow.str_view_stable (Or.inr borrow)).trans get, rfl, fun _ _ impossible => False.elim impossible⟩
  | st_dist_code =>
    refine ⟨?_, rfl, fun _ _ impossible => False.elim impossible⟩
    change some initialized.static.dist_code = some a
    rw [← frame.1]
    exact get
  | st_length_code =>
    refine ⟨?_, rfl, fun _ _ impossible => False.elim impossible⟩
    change some initialized.static.length_code = some a
    rw [← frame.1]
    exact get

private theorem old_bytes_after_init {h initialized : Heap} {p : ZlibF.Spec.Api.DeflParams}
    (fresh : Fresh h) (initial : DeflateInitial (localHeap h) initialized (.tab h.nextBlk) p)
    (borrow : initialized.libcErrorBorrow = h.libcErrorBorrow)
    {pointer : BPtr} {n : Nat} {xs : List UInt8} (bytes : Bytes h pointer n xs) :
    Bytes initialized pointer n xs ∧ CallerRange initialized (.tab h.nextBlk) pointer n false := by
  rcases bytes with null | ⟨ref, off, a, pointerEq, get, bound, value⟩
  · exact ⟨Or.inl null, Or.inl null.1⟩
  · obtain ⟨getA, _ro, outside⟩ := old_view_after_init fresh initial borrow get
    have data : Bytes initialized pointer n xs := Or.inr ⟨ref, off, a, pointerEq, getA, bound, value⟩
    refine ⟨data, Or.inr ⟨⟨xs, data⟩, by simp, ?_⟩⟩
    rw [pointerEq]
    exact outside off

private theorem old_writable_after_init {h initialized : Heap} {p : ZlibF.Spec.Api.DeflParams}
    (fresh : Fresh h) (initial : DeflateInitial (localHeap h) initialized (.tab h.nextBlk) p)
    (borrow : initialized.libcErrorBorrow = h.libcErrorBorrow)
    {pointer : BPtr} {n : Nat} (writable : Writable h pointer n) :
    CallerRange initialized (.tab h.nextBlk) pointer n true := by
  rcases writable with null | ⟨ref, off, a, pointerEq, get, ro, bound⟩
  · exact Or.inl null.1
  · obtain ⟨getA, roA, outside⟩ := old_view_after_init fresh initial borrow get
    refine Or.inr ⟨⟨(a.toList.drop off).take n,
      Or.inr ⟨ref, off, a, pointerEq, getA, bound, rfl⟩⟩,
      fun _ => Or.inr ⟨ref, off, a, pointerEq, getA, roA.trans ro, bound⟩, ?_⟩
    rw [pointerEq]
    exact outside off

/-- The exact four stream-field assignments immediately before the real
compress2_z loop. -/
def bindings (z : ZStream) (dest source : BPtr) : ZStream :=
  { z with next_out := dest, avail_out := 0, next_in := source, avail_in := 0 }

/-- `int compress2_z(Bytef *dest, z_size_t *destLen, const Bytef *source,
z_size_t sourceLen, int level)`.
Real local-stream preparation and a real successful default initialization
establish the wrapper seed from its ORIGINAL caller buffers. Neither an
initialized invariant nor a callee specification is an input premise.
The init run is an actual execution event; failure branches are separate.
Global Uniq is explicit internal scope, not a changed public utility goal. -/
theorem successful_default_seed {h initialized : Heap} {dest source : BPtr}
    {capacity sourceLen : UInt64} {xs : List UInt8}
    (fresh : Fresh h) (unique : Zlib.Inflate.Spec.Uniq h) (globals : LibraryGlobals h)
    (bytes : Bytes h source sourceLen.toNat xs) (writable : Writable h dest capacity.toNat)
    (separate : Separate source sourceLen.toNat dest capacity.toNat)
    (actual : C.run (deflateInit_ (some (.tab h.nextBlk)) Z_DEFAULT_COMPRESSION
      (.ref (.str 57) 0) 112) (localHeap h) = .ok (Z_OK, initialized)) :
    ∃ ready z, C.run (zwr (some (.tab h.nextBlk)) (fun s => bindings s dest source)) initialized =
        .ok ((), ready) ∧
      DefaultDataTrace (.tab h.nextBlk) ready {} ∧ ready.streams h.nextBlk = some z ∧
      Ranges ready (.tab h.nextBlk) z capacity sourceLen xs ∧
      z.next_out = dest ∧ z.next_in = source ∧ z.avail_out = 0 ∧ z.avail_in = 0 := by
  have domain := automatic_stream_domain h fresh unique globals
  let p := ZlibF.Spec.Public.Proofs.DeflateInit.settings 6
  have params : ZlibF.Spec.Api.deflInit? Z_DEFAULT_COMPRESSION.toInt 8 15 8 0 = some p := by decide +kernel
  obtain ⟨zf, sf, start, initial, _first⟩ := common_observed_initialization_first_ordinary_encoding domain
    params (by decide +kernel) (by decide +kernel) actual
  let next := bindings zf dest source
  let ready := (ZStreamRef.tab h.nextBlk).put initialized next
  have globalsI := ZlibF.Spec.Public.Proofs.DeflateCore.initialized_globals domain actual
  have edit : Rebuffer initialized ready (.tab h.nextBlk) := buffer_fields_rebuffer start.good globalsI next rfl
  have nextGet := ZStreamRef.get_put_same start.good.live.hz next
  have goodNext : DGood ready (.tab h.nextBlk) (localHeap h).nextBlk next sf :=
    stream_control_good start.good rfl start.good.live.zalloc start.good.live.zfree
  have own := stream_owned_keys start.good goodNext rfl rfl rfl rfl
  have sizes := stream_control_sizes initialized (.tab h.nextBlk) next
  have borrow : initialized.libcErrorBorrow = h.libcErrorBorrow := by
    have actualBorrow := Zlib.Deflate.BorrowProofs.stable_deflateInit_
      (some (.tab h.nextBlk)) Z_DEFAULT_COMPRESSION (.ref (.str 57) 0) 112
      (localHeap h) Z_OK initialized actual
    simpa only [localHeap] using actualBorrow
  obtain ⟨bytesI, inputI⟩ := old_bytes_after_init fresh initial borrow bytes
  have outputI := old_writable_after_init fresh initial borrow writable
  have inputA := caller_range_sizes inputI sizes own (used := 0) (remaining := sourceLen.toNat) (by omega)
  have outputA := caller_range_sizes outputI sizes own (used := 0) (remaining := capacity.toNat) (by omega)
  have bytesA := bytes_put bytesI (.tab h.nextBlk) next
  have ranges : Ranges ready (.tab h.nextBlk) next capacity sourceLen xs := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa only [advance_zero, ready, next, bindings, UInt32.toNat_zero, Nat.zero_add] using inputA
    · simpa only [advance_zero, ready, next, bindings, UInt32.toNat_zero, Nat.zero_add] using outputA
    · simpa only [ready, next, bindings, UInt32.toNat_zero, Nat.zero_add] using separate
    · simpa only [ready, next, bindings, UInt32.toNat_zero, Nat.zero_add] using bytesA
  refine ⟨ready, next, ?_, DefaultDataTrace.caller (.init domain actual) edit, nextGet,
    ranges, rfl, rfl, rfl, rfl⟩
  have get : initialized.streams h.nextBlk = some zf := start.good.live.hz
  simp [C.run, zwr, ldZStream, stZStream, ZStreamRef.get, ZStreamRef.isRo, get, ready, next]

end ZlibF.Spec.Public.Proofs.CompressCaller
