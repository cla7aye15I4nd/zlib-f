import ZlibF.Spec.Public.Lifecycle
import ZlibF.Spec.Functional.Checksums

/-!
# Lifecycle: functional goals and the definitions only they use

Split from `ZlibF/Spec/Public/Lifecycle.lean` without a change of statement or name
(`docs/design/safety-functional-split.md`). The namespace stays `ZlibF.Spec.Public`.
-/

namespace ZlibF.Spec.Public
open C ZlibF.Spec

/-- `int inflateResetKeep(z_streamp strm)`.
Clear decode progress and counters; retain the allocated window and its dictionary. -/
def Goal.inflateResetKeep : Prop :=
  ∀ h r i z s, InflateView h r i z s →
    C.run (Zlib.Inflate.inflateResetKeep (some r)) h = .ok (Z_OK,
      putInflate (r.put h (inflateResetStream z s)) i (inflateResetState i s))

/-- `int inflateReset(z_streamp strm)`.
Restore the requested wrapper and window, forget the dictionary, and free an obsolete window. -/
def Goal.inflateReset : Prop :=
  ∀ h r i z s, InflateView h r i z s → z.zfree = .fn "zcfree" →
    WindowAllocation h s.window →
    let base := if s.wbits = s.reqbits then h else dropWindow h s.window
    let reset := inflateResetPre s
    C.run (Zlib.Inflate.inflateReset (some r)) h = .ok (Z_OK,
      putInflate (r.put base (inflateResetStream z reset)) i (inflateResetState i reset))

/-- `int inflateReset2(z_streamp strm, int windowBits)`.
Invalid parameters leave the heap unchanged. A changed window size releases the old window.
The new request restores validation even if `inflateValidate` previously disabled it. -/
def Goal.inflateReset2 : Prop :=
  ∀ h r i z s wb, InflateView h r i z s → z.zfree = .fn "zcfree" →
    WindowAllocation h s.window →
    C.run (Zlib.Inflate.inflateReset2 (some r) wb) h =
      match Api.inflWbits wb.toInt with
      | none => .ok (Z_STREAM_ERROR, h)
      | some (wrap, bits) =>
        let w : Int32 := match wrap with | .raw => 0 | .zlib => 5 | .gzip => 6 | .auto => 7
        let base := if s.wbits.toNat = bits then h else dropWindow h s.window
        let reset := { s with
          window := if s.wbits.toNat = bits then s.window else .null
          reqbits := UInt32.ofNat bits, wbits := UInt32.ofNat bits
          wrap := w, reqwrap := w, wsize := 0, whave := 0, wnext := 0 }
        .ok (Z_OK, putInflate (r.put base (inflateResetStream z reset)) i (inflateResetState i reset))

/-- `int inflateEnd(z_streamp strm)`.
Release exactly the state and its optional window; retain caller buffers and clear `state`. -/
def Goal.inflateEnd : Prop :=
  ∀ h r i z s, Zlib.Inflate.Spec.Good h r i z s → z.zfree = .fn "zcfree" →
    ∃ after, C.run (Zlib.Inflate.inflateEnd (some r)) h = .ok (Z_OK, after) ∧
      r.get after = some { z with state := none } ∧
      LiveChange h after (fun _ => False) (InflateOwned i s) ∧
      Frame h after (fun b => StreamRoot r b ∨ InflateOwned i s b) ∧
      after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk

/-- `int inflateGetDictionary(z_streamp strm, Bytef *dictionary, uInt *dictLength)`.
Return the chronological window, optionally copy it, and preserve an omitted length cell. -/
def Goal.inflateGetDictionary : Prop :=
  ∀ h r i z s dest oldLength xs,
    Zlib.Inflate.Spec.Good h r i z s → InflateDictionary h s xs →
    (dest ≠ .null → Writable h dest xs.length ∧ Separate dest xs.length s.window s.wsize.toNat) →
    ∃ after, C.run (Zlib.Inflate.inflateGetDictionary (some r) dest oldLength) h =
      .ok ((Z_OK, oldLength.map (fun _ => UInt32.ofNat xs.length)), after) ∧
      Store h dest (if dest = .null then [] else xs) after

/-- `int inflateGetHeader(z_streamp strm, gz_headerp head)`.
Only gzip-capable wrappers accept the header. Set `done` to zero and retain all other fields. -/
def Goal.inflateGetHeader : Prop :=
  ∀ h r i z s head, InflateView h r i z s →
    ((s.wrap &&& 2) ≠ 0 → ∃ g gh, head = some (.tab g) ∧ h.gzheaders g = some gh) →
    ∃ rc after, C.run (Zlib.Inflate.inflateGetHeader (some r) head) h = .ok (rc, after) ∧
      (if (s.wrap &&& 2) = 0 then rc = Z_STREAM_ERROR ∧ after = h
       else ∃ g gh, head = some (.tab g) ∧ h.gzheaders g = some gh ∧ rc = Z_OK ∧
         after = { putInflate h i { s with head := head } with
           gzheaders := upd h.gzheaders g (some { gh with done := 0 }) })

/-- `int deflateGetDictionary(z_streamp strm, Bytef *dictionary, uInt *dictLength)`.
Return the last window of accepted input, including pending lookahead. -/
def Goal.deflateGetDictionary : Prop :=
  ∀ h r i z s dest lengthPresent xs,
    Zlib.Deflate.Spec.DGood h r i z s → DeflateDictionary h s xs →
    (dest ≠ .null → Writable h dest xs.length ∧ Separate dest xs.length s.window s.window_size.toNat) →
    ∃ after, C.run (Zlib.Deflate.deflateGetDictionary (some r) dest lengthPresent) h =
      .ok ((Z_OK, if lengthPresent then some (UInt32.ofNat xs.length) else none), after) ∧
      Store h dest (if dest = .null then [] else xs) after

/-- `int deflateEnd(z_streamp strm)`.
Free all five owned blocks. An unfinished busy stream returns `Z_DATA_ERROR` after freeing. -/
def Goal.deflateEnd : Prop :=
  ∀ h r i z s, Zlib.Deflate.Spec.DGood h r i z s → z.zfree = .fn "zcfree" →
    ∃ after, C.run (Zlib.Deflate.deflateEnd (some r)) h =
      .ok ((if s.status = BUSY_STATE then Z_DATA_ERROR else Z_OK), after) ∧
      r.get after = some { z with state := none } ∧
      LiveChange h after (fun _ => False) (DeflateOwned i s) ∧
      Frame h after (fun b => StreamRoot r b ∨ DeflateOwned i s b) ∧
      after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk

/-- `int deflateResetKeep(z_streamp strm)`; reset progress while retaining the match history. -/
def Goal.deflateResetKeep : Prop := DeflateResetContract Zlib.Deflate.deflateResetKeep true

/-- `int deflateReset(z_streamp strm)`; reset progress and clear the dictionary hash. -/
def Goal.deflateReset : Prop := DeflateResetContract Zlib.Deflate.deflateReset false

/-- `int inflateSetDictionary(z_streamp strm, const Bytef *dictionary, uInt dictLength)`.
Raw streams append to their window. Wrapped streams require DICT mode and the exact Adler id. -/
def Goal.inflateSetDictionary : Prop :=
  ∀ h r i z s source n xs old,
    Zlib.Inflate.Spec.Good h r i z s → z.zalloc = .fn "zcalloc" →
    InflateDictionary h s old → (source ≠ .null → Bytes h source n.toNat xs) →
    Separate source n.toNat s.window (2 ^ s.wbits.toNat) →
    ((s.wrap = 0 ∨ s.mode = DICT) → 8 ≤ s.wbits.toNat) →
    ∃ rc after, C.run (Zlib.Inflate.inflateSetDictionary (some r) source n) h = .ok (rc, after) ∧
      (source = .null ∨ (s.wrap ≠ 0 ∧ s.mode ≠ DICT) → rc = Z_STREAM_ERROR ∧ after = h) ∧
      (source ≠ .null → (s.wrap = 0 ∨ s.mode = DICT) →
        if s.mode = DICT ∧ s.check ≠ (ZlibF.Spec.adler32 xs).toUInt64 then rc = Z_DATA_ERROR ∧ after = h
        else (rc = Z_MEM_ERROR ∧ AllocationFailed h after ∧
          ∃ s', Zlib.Inflate.Spec.Good after r i z s' ∧ s'.mode = MEM) ∨
          (rc = Z_OK ∧ ∃ s', Zlib.Inflate.Spec.Good after r i z s' ∧
            s'.havedict = 1 ∧ s'.mode = s.mode ∧
            InflateDictionary after s' ((old ++ xs).drop ((old ++ xs).length - 2 ^ s.wbits.toNat)))) ∧
      Frame h after (fun b => StreamRoot r b ∨ InflateOwned i s b) ∧
      (∃ s', h.istates i = some s ∧ after.istates i = some s' ∧
        LiveChange h after (fun b => InflateOwned i s' b ∧ ¬ h.live b) (fun _ => False))

/-- `int deflateSetDictionary(z_streamp strm, const Bytef *dictionary, uInt dictLength)`.
The raw path checks the block boundary. Repeated zlib dictionaries accumulate their checksum.
The temporary input binding is restored, and no allocation is performed. -/
def Goal.deflateSetDictionary : Prop :=
  ∀ h r i z s source n xs old,
    Zlib.Deflate.Spec.DGood h r i z s → LibraryGlobals h →
    DeflateDictionary h s old → (source ≠ .null → Bytes h source n.toNat xs) →
    Separate source n.toNat s.window s.window_size.toNat →
    ∃ rc after, C.run (Zlib.Deflate.deflateSetDictionary (some r) source n) h = .ok (rc, after) ∧
      (if source = .null ∨ s.wrap = 2 ∨ (s.wrap = 1 ∧ s.status ≠ INIT_STATE) ∨
          s.lookahead ≠ 0 ∨ (s.wrap = 0 ∧ s.strstart.toUInt64.toInt64 ≠ s.block_start) then
        rc = Z_STREAM_ERROR ∧ after = h
       else rc = Z_OK ∧ ∃ z' s' dict,
         Zlib.Deflate.Spec.DGood after r i z' s' ∧ DeflateDictionary after s' dict ∧
         z' = { z with
           total_in := z.total_in + UInt64.ofNat (min xs.length s.w_size.toNat)
           adler := if s.wrap = 1 then adlerValue z.adler xs else z.adler } ∧
         s'.wrap = s.wrap ∧ s'.lookahead = 0 ∧ s'.block_start = s'.strstart.toUInt64.toInt64 ∧
         dict <:+ old ++ xs ∧ dict.length ≤ s.w_size.toNat ∧
         min (old.length + xs.length) (s.w_size.toNat - 262) ≤ dict.length) ∧
      Frame h after (fun b => StreamRoot r b ∨ DeflateOwned i s b) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧ after.nalloc = h.nalloc

end ZlibF.Spec.Public
