import ZlibF.Proof.«compress.c.loop-budget»

/-! # The actual compressor tail: difference, scalar result, end and automatic free

Nonnull raw output has a same-object, representable pointer difference,
including a zero-capacity one-past pointer. The existing D-4 NULL-NULL
convention is kept as a model-only result and is not ISO C definedness.
-/
namespace ZlibF.Spec.Public.Proofs.CompressTail
open C Zlib.Compress Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open Zlib.Deflate.Engine.Proofs Zlib.Deflate.Proofs.DefaultInit
open ZlibF.Spec.Public.Proofs.CompressLoop ZlibF.Spec.Public.Proofs.CompressCaller
open ZlibF.Spec.Public.Proofs.CompressPrefix
set_option autoImplicit false
set_option maxRecDepth 100000

/-- The original tail order is unchanged: read cursor, subtract pointers,
compute the stored length, call real deflateEnd, free the automatic stream,
and normalize the old return code. -/
def tail (strm : ZStreamPtr) (dest : BPtr) (err : Int32) : M (Int32 × Option UInt64) := do
  let no ← zrd strm (·.next_out)
  let n ← ptrDiff no dest
  let _ ← deflateEnd strm
  freeZStream strm
  return (if err == Z_STREAM_END then Z_OK else err, some n.toUInt64)

def releaseLocal (h : Heap) (slot : Nat) : Heap := { h with streams := upd h.streams slot none }

/-- D-4 is an existing runtime convention only. This theorem provides no
ISO C definedness justification for subtracting NULL from NULL. -/
theorem ptrDiff_null_model (h : Heap) : ptrDiff .null .null h = .ok (0, h) := rfl

/-- Both pointers name the same live output object, including one-past
endpoints. The difference equals exactly the emitted-byte length and fits
ptrdiff_t. Unlike the D-4 branch, this is ordinary nonnull subtraction. -/
theorem raw_ptrdiff_exact {h : Heap} {ob oo : Nat} {output : List UInt8}
    (bytes : Bytes h (.ref (.blk ob) oo) output.length output)
    (small : output.length < 2 ^ 63) :
    ptrDiff (.ref (.blk ob) (oo + output.length)) (.ref (.blk ob) oo) h =
      .ok (Int64.ofInt (output.length : Int), h) := by
  rcases bytes with ⟨impossible, _⟩ | ⟨ref, off, a, eq, get, bound, _value⟩
  · cases impossible
  · obtain ⟨rfl, rfl⟩ := Ptr.ref.inj eq
    have difference : ((oo + output.length : Nat) : Int) - (oo : Int) = output.length := by omega
    have rule := Ptr.diff_ok (o1 := oo + output.length) (o2 := oo) get (by omega) (by omega) (by omega)
    have guard : ((Ptr.ref (BRef.blk ob) (oo + output.length) == (.null : BPtr)) &&
      (Ptr.ref (BRef.blk ob) oo == (.null : BPtr))) = false := rfl
    simpa only [OkOn, ptrDiff, guard, Bool.false_eq_true, ite_false, difference] using rule

private theorem count_zero_none {α : Type} {value : Option α} (zero : cnt value = 0) : value = none := by
  cases value <;> simp_all only [cnt_some, cnt_none, reduceCtorEq]

/-- Freeing the actual unique automatic stream removes exactly that one
live object. The backing table may retain a dead trailing slot. -/
theorem release_local_live {h : Heap} {slot : Nat} {z : ZStream}
    (unique : Uniq h) (get : h.streams slot = some z) (b : Nat) :
    (releaseLocal h slot).live b ↔ h.live b ∧ b ≠ slot := by
  by_cases same : b = slot
  · subst b
    have counts := unique slot
    simp only [get, cnt_some] at counts
    have bytes := count_zero_none (value := h.bytes slot) (by omega)
    have words := count_zero_none (value := h.words slot) (by omega)
    have headers := count_zero_none (value := h.gzheaders slot) (by omega)
    have states := count_zero_none (value := h.dstates slot) (by omega)
    have inflates := count_zero_none (value := h.istates slot) (by omega)
    have gzip := count_zero_none (value := h.gzstates slot) (by omega)
    simp [releaseLocal, Heap.live, bytes, words, headers, states, inflates, gzip]
  · have live : (releaseLocal h slot).live b ↔ h.live b := by
      simp only [releaseLocal, Heap.live, upd_ne _ _ _ _ same]
    exact live.trans ⟨fun yes => ⟨yes, same⟩, And.left⟩

/-- One concrete observed tail uses the actual end theorem and actual
free. A pointer-difference execution equation is discharged separately by
the nonnull geometry theorem or the explicitly model-only D-4 convention. -/
theorem tail_run_of_difference {h : Heap} {slot : Nat} {log : DataLog} {z : ZStream}
    (history : DefaultDataTrace (.tab slot) h log) (get : h.streams slot = some z)
    (dest : BPtr) (err : Int32) (n : Int64)
    (difference : ptrDiff z.next_out dest h = .ok (n, h)) :
    ∃ ds d ended after,
      DGood h (.tab slot) ds z d ∧
      tail (some (.tab slot)) dest err h =
        .ok ((if err == Z_STREAM_END then Z_OK else err, some n.toUInt64), after) ∧
      after = releaseLocal ended slot ∧ after.streams slot = none ∧
      LiveChange h after (fun _ => False) (fun b => DeflateOwned ds d b ∨ b = slot) ∧
      Frame h after (fun b => StreamRoot (.tab slot) b ∨ DeflateOwned ds d b) ∧
      after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  obtain ⟨ds, current, d, ended, good, runEnd, getEnd, liveEnd, frameEnd, allocEnd, nextEnd⟩ := history.cleanup
  have same : current = z := Option.some.inj (good.live.hz.symm.trans get)
  subst current
  obtain ⟨za, getZ, allocators⟩ := history.allocators
  have sameZ : za = z := Option.some.inj (getZ.symm.trans get)
  subst za
  obtain ⟨w, p, q, b, blocks⟩ := good.inv.blocks
  have expected := deflateEnd_run good.live allocators.2 blocks
  have heaps : ended = endHeap h (.tab slot) ds z d := by
    have eq : (.ok ((if d.status = BUSY_STATE then Z_DATA_ERROR else Z_OK), ended) :
        Except Fault (Int32 × Heap)) = .ok ((if d.status == BUSY_STATE then Z_DATA_ERROR else Z_OK), endHeap h (.tab slot) ds z d) :=
      runEnd.symm.trans expected
    exact (Prod.mk.inj (Except.ok.inj eq)).2
  have uniqueEnd : Uniq ended := by rw [heaps]; exact endHeap_uniq blocks good.uniq good.live.hz
  have getEnded : ended.streams slot = some { z with state := none } := getEnd
  refine ⟨ds, d, ended, releaseLocal ended slot, good, ?_, rfl, by simp [releaseLocal], ?_, ?_, allocEnd, nextEnd⟩
  · change deflateEnd (some (.tab slot)) h = _ at runEnd
    simp only [tail, bind_app, zrd_eq, ZStreamRef.get, get, pure_app, difference, runEnd]
    simp [freeZStream, getEnded, releaseLocal]
  · intro x
    rw [release_local_live uniqueEnd getEnded x]
    have ledger := liveEnd x
    simp only [LiveChange, not_false_eq_true, and_true, or_false] at ledger
    rw [ledger]
    simp only [LiveChange, not_false_eq_true, or_false]
    simp only [not_or, and_assoc]
  · refine ⟨frameEnd.1, frameEnd.2.1, frameEnd.2.2.1, frameEnd.2.2.2.1, frameEnd.2.2.2.2.1, ?_⟩
    intro x live outside
    have different : x ≠ slot := fun eq => outside (Or.inl eq)
    simpa only [releaseLocal, upd_ne _ _ _ _ different] using frameEnd.2.2.2.2.2 x live outside

/-- This is an unconditional equation of the real translated function.
It checks that the named tail has the original call order and return
normalization, including every entry and initializer-error branch. -/
theorem compress2_z_tail_unfold (dest : BPtr) (destLen : Option UInt64)
    (source : BPtr) (sourceLen : UInt64) (level : Int32) :
    compress2_z dest destLen source sourceLen level =
    (do
    -- if ((sourceLen > 0 && source == Z_NULL) || destLen == Z_NULL || (*destLen > 0 && dest == Z_NULL)) return Z_STREAM_ERROR;
    let some dl := destLen | return (Z_STREAM_ERROR, none)
    if (sourceLen > 0 && source == .null) || (dl > 0 && dest == .null) then return (Z_STREAM_ERROR, destLen)
    -- left = *destLen; *destLen = 0;
    let mut left : UInt64 := dl
    -- z_stream stream;  stream.zalloc = 0; stream.zfree = 0; stream.opaque = 0;
    let strm ← allocLocalZ
    zwr strm (fun z => { z with zalloc := FnPtr.null, zfree := FnPtr.null, «opaque» := .null })
    -- err = deflateInit(&stream, level); if (err != Z_OK) return err;
    let ver ← Zlib.Zutil.zlibVersion
    let mut err ← deflateInit_ strm level ver sizeof_z_stream
    if err != Z_OK then
      freeZStream strm
      return (err, some 0)
    -- stream.next_out = dest; stream.avail_out = 0; stream.next_in = source; stream.avail_in = 0;
    zwr strm (fun z => { z with next_out := dest, avail_out := 0, next_in := source, avail_in := 0 })
    let mut sourceLen := sourceLen
    -- do { ... } while (err == Z_OK);
    let (e, l, sl) ← loop strm
      (err, left, sourceLen)
    err := e
    left := l
    sourceLen := sl
    CompressTail.tail strm dest err) := by
  rw [compress2_z_unfold]
  rfl

private theorem raw_bytes_same {before after : Heap} {ob oo n : Nat} {xs : List UInt8}
    (same : after.bytes ob = before.bytes ob) (bytes : Bytes before (.ref (.blk ob) oo) n xs) :
    Bytes after (.ref (.blk ob) oo) n xs := by
  rcases bytes with ⟨impossible, _⟩ | ⟨ref, off, a, pointer, get, bound, value⟩
  · cases impossible
  · obtain ⟨rfl, rfl⟩ := Ptr.ref.inj pointer
    exact Or.inr ⟨.blk ob, oo, a, rfl, same.trans get, bound, value⟩

/-- The actual nonnull tail returns the exact emitted length, preserves
the emitted bytes and releases the private objects plus the automatic
stream. The same-object pointer-difference preconditions are proved here,
including length zero with both cursors one past the same allocation. -/
theorem tail_nonnull_exact {h : Heap} {slot ob oo : Nat} {log : DataLog} {z : ZStream}
    {output : List UInt8} (history : DefaultDataTrace (.tab slot) h log)
    (get : h.streams slot = some z) (buffers : StreamBuffers h (.tab slot))
    (cursor : z.next_out = .ref (.blk ob) (oo + output.length))
    (bytes : Bytes h (.ref (.blk ob) oo) output.length output)
    (small : output.length < 2 ^ 63) (err : Int32) :
    ∃ ds d after,
      DGood h (.tab slot) ds z d ∧
      tail (some (.tab slot)) (.ref (.blk ob) oo) err h =
        .ok ((if err == Z_STREAM_END then Z_OK else err, some (UInt64.ofNat output.length)), after) ∧
      Bytes after (.ref (.blk ob) oo) output.length output ∧ after.streams slot = none ∧
      LiveChange h after (fun _ => False) (fun b => DeflateOwned ds d b ∨ b = slot) ∧
      Frame h after (fun b => StreamRoot (.tab slot) b ∨ DeflateOwned ds d b) ∧
      after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk ∧
      (UInt64.ofNat output.length).toNat = output.length := by
  have difference := raw_ptrdiff_exact bytes small
  rw [← cursor] at difference
  obtain ⟨ds, d, ended, after, good, run, _heap, dead, live, frame, count, next⟩ :=
    tail_run_of_difference history get (.ref (.blk ob) oo) err _ difference
  have sameOutput := (private_frame_raw_output_same good buffers cursor frame).1
  have word : (Int64.ofInt (output.length : Int)).toUInt64 = UInt64.ofNat output.length := rfl
  rw [word] at run
  exact ⟨ds, d, after, good, run, raw_bytes_same sameOutput bytes, dead, live, frame, count, next,
    UInt64.toNat_ofNat_of_lt' (by change output.length < 18446744073709551616; omega)⟩

/-- The NULL-NULL tail branch is a model theorem only, relying on D-4.
It must not be used to claim ISO C safety for the original subtraction. -/
theorem tail_null_model {h : Heap} {slot : Nat} {log : DataLog} {z : ZStream}
    (history : DefaultDataTrace (.tab slot) h log) (get : h.streams slot = some z)
    (null : z.next_out = .null) (err : Int32) :
    ∃ ds d ended after,
      DGood h (.tab slot) ds z d ∧
      tail (some (.tab slot)) .null err h =
        .ok ((if err == Z_STREAM_END then Z_OK else err, some 0), after) ∧
      after = releaseLocal ended slot ∧ after.streams slot = none ∧
      LiveChange h after (fun _ => False) (fun b => DeflateOwned ds d b ∨ b = slot) ∧
      Frame h after (fun b => StreamRoot (.tab slot) b ∨ DeflateOwned ds d b) ∧
      after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  exact tail_run_of_difference history get .null err 0 (by rw [null]; rfl)

end ZlibF.Spec.Public.Proofs.CompressTail
