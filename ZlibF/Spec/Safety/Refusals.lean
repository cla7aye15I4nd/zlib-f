import ZlibF.Spec.Public.Copy

namespace ZlibF.Spec.Public
open C

/-!
# Stream refusals

zlib.h documents `Z_STREAM_ERROR` for a stream that is `NULL` or inconsistent: its state is
`NULL`, its `zalloc` or `zfree` is `NULL`, or its state is not the one an init gave it. That
covers a record after `End`, after a failed init, the destination of a failed copy, and a struct
copy of a live record. These goals state that every stream function of a family refuses such a
stream without a fault and without a change. The domain is `RefusedInflate` and
`RefusedDeflate`. A record whose state field holds a garbage pointer, such as a never-initialised
automatic `z_stream`, is outside the domain: reading through that pointer is undefined in C
(`docs/deviations.md`).

The functions already covered by `CheckedInflate`/`CheckedDeflate` goals, and `deflateEnd`,
`deflateReset`, `deflatePrime` and `deflateBound`, are not repeated here.
-/

/-- **Inflate stream refusals.** `inflate` makes and frees its local four-byte array, so its
refusal is stated with a frame and an unchanged ledger; the other functions leave the heap
exactly as it was. `inflateCopy` from a refused source clears the destination state. -/
def Goal.inflate_refusal : Prop :=
  (∀ h p flush, Fresh h → RefusedInflate h p →
    ∃ after, C.run (Zlib.Inflate.inflate p flush) h = .ok (Z_STREAM_ERROR, after) ∧
      Frame h after (fun _ => False) ∧ LiveChange h after (fun _ => False) (fun _ => False)) ∧
  (∀ h p, RefusedInflate h p → C.run (Zlib.Inflate.inflateEnd p) h = .ok (Z_STREAM_ERROR, h)) ∧
  (∀ h p, RefusedInflate h p → C.run (Zlib.Inflate.inflateReset p) h = .ok (Z_STREAM_ERROR, h)) ∧
  (∀ h p windowBits, RefusedInflate h p →
    C.run (Zlib.Inflate.inflateReset2 p windowBits) h = .ok (Z_STREAM_ERROR, h)) ∧
  (∀ h p dictionary dictLength, RefusedInflate h p →
    C.run (Zlib.Inflate.inflateGetDictionary p dictionary dictLength) h =
      .ok ((Z_STREAM_ERROR, dictLength), h)) ∧
  (∀ h p dictionary dictLength, RefusedInflate h p →
    C.run (Zlib.Inflate.inflateSetDictionary p dictionary dictLength) h = .ok (Z_STREAM_ERROR, h)) ∧
  (∀ h dest oldDest source, dest.get h = some oldDest → RefusedInflate h source →
    C.run (Zlib.Inflate.inflateCopy (some dest) source) h =
      .ok (Z_STREAM_ERROR, dest.put h { oldDest with state := none }))

/-- **Deflate stream refusals.** Each function refuses a refused stream and leaves the heap
exactly as it was. `deflateCopy` from a refused source clears the destination state; this
includes a source whose live state the check refuses (a wrong back pointer or status). -/
def Goal.deflate_refusal : Prop :=
  (∀ h p flush, RefusedDeflate h p → C.run (Zlib.Deflate.deflate p flush) h = .ok (Z_STREAM_ERROR, h)) ∧
  (∀ h p dictionary dictLength, RefusedDeflate h p →
    C.run (Zlib.Deflate.deflateSetDictionary p dictionary dictLength) h = .ok (Z_STREAM_ERROR, h)) ∧
  (∀ h p level strategy, RefusedDeflate h p →
    C.run (Zlib.Deflate.deflateParams p level strategy) h = .ok (Z_STREAM_ERROR, h)) ∧
  (∀ h p dictionary hasDictLength, RefusedDeflate h p →
    C.run (Zlib.Deflate.deflateGetDictionary p dictionary hasDictLength) h = .ok ((Z_STREAM_ERROR, none), h)) ∧
  (∀ h dest oldDest source, dest.get h = some oldDest → RefusedDeflate h source →
    C.run (Zlib.Deflate.deflateCopy (some dest) source) h =
      .ok (Z_STREAM_ERROR, dest.put h { oldDest with state := none }))

end ZlibF.Spec.Public
