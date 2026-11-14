import ZlibF.Spec.Public.StreamQueries

/-!
# StreamQueries: functional goals and the definitions only they use

Split from `ZlibF/Spec/Public/StreamQueries.lean` without a change of statement or name
(`docs/design/safety-functional-split.md`). The namespace stays `ZlibF.Spec.Public`.
-/

namespace ZlibF.Spec.Public
open C

/-- `int inflateSyncPoint(z_streamp strm)`.
The answer is exactly the stored-block boundary test; all memory is preserved. -/
def Goal.inflateSyncPoint : Prop :=
  CheckedInflate Zlib.Inflate.inflateSyncPoint Z_STREAM_ERROR <|
  ∀ h r i z s, InflateView h r i z s →
    C.run (Zlib.Inflate.inflateSyncPoint (some r)) h =
      .ok ((if s.mode = STORED ∧ s.bits = 0 then 1 else 0), h)

/-- `long inflateMark(z_streamp strm)`.
The high half counts code bits; the low half counts remaining stored bytes or match bytes
already copied. The internal ranges are obligations of the stream invariant. -/
def Goal.inflateMark : Prop :=
  CheckedInflate Zlib.Inflate.inflateMark (-65536) <|
  ∀ h r i z s, InflateView h r i z s →
    C.run (Zlib.Inflate.inflateMark (some r)) h = .ok
      (Int64.ofInt (s.back.toInt * 65536 +
        (if s.mode = COPY then s.length.toNat else
         if s.mode = MATCH then (s.was - s.length).toNat else 0)), h)

/-- `unsigned long inflateCodesUsed(z_streamp strm)`.
Return the number of used decode-table slots, with no memory effect. The fixed C
array has 1444 entries; init and stream preservation establish this representation fact. -/
def Goal.inflateCodesUsed : Prop :=
  CheckedInflate Zlib.Inflate.inflateCodesUsed 0xffffffffffffffff <|
  ∀ h r i z s n, InflateView h r i z s → s.codes.size = 1444 →
    s.next = .ref (.istate_codes i) n → n ≤ s.codes.size →
    C.run (Zlib.Inflate.inflateCodesUsed (some r)) h = .ok (UInt64.ofNat n, h)

/-- `int inflateUndermine(z_streamp strm, int subvert)`.
The default build refuses the extension and restores strict distance checking. -/
def Goal.inflateUndermine : Prop :=
  ∀ subvert, CheckedInflate (fun p => Zlib.Inflate.inflateUndermine p subvert) Z_STREAM_ERROR <|
  ∀ h r i z s, InflateView h r i z s →
    C.run (Zlib.Inflate.inflateUndermine (some r) subvert) h =
      .ok (Z_DATA_ERROR, putInflate h i { s with sane := 1 })

/-- `int inflateValidate(z_streamp strm, int check)`.
Toggle validation in both current and requested wrappers; retain every other field. -/
def Goal.inflateValidate : Prop :=
  ∀ check, CheckedInflate (fun p => Zlib.Inflate.inflateValidate p check) Z_STREAM_ERROR <|
  ∀ h r i z s, InflateView h r i z s →
    C.run (Zlib.Inflate.inflateValidate (some r) check) h = .ok
      (Z_OK, putInflate h i { s with
        wrap := if check ≠ 0 ∧ s.wrap ≠ 0 then s.wrap ||| 4 else s.wrap &&& ~~~4
        reqwrap := if check ≠ 0 ∧ s.reqwrap ≠ 0 then s.reqwrap ||| 4 else s.reqwrap &&& ~~~4 })

/-- `int inflatePrime(z_streamp strm, int bits, int value)`.
Negative counts clear pending bits. Counts above 16 or a total above 32 are refused.
Otherwise append exactly the requested low bits, without allocation. -/
def Goal.inflatePrime : Prop :=
  ∀ bits value, CheckedInflate (fun p => Zlib.Inflate.inflatePrime p bits value) Z_STREAM_ERROR <|
  ∀ h r i z s, InflateView h r i z s → s.bits.toNat ≤ 39 →
    C.run (Zlib.Inflate.inflatePrime (some r) bits value) h =
      if bits = 0 then .ok (Z_OK, h)
      else if bits.toInt < 0 then .ok (Z_OK, putInflate h i { s with hold := 0, bits := 0 })
      else if 16 < bits.toInt ∨ 32 < s.bits.toNat + bits.toInt.toNat then .ok (Z_STREAM_ERROR, h)
      else .ok (Z_OK, putInflate h i { s with
        hold := s.hold + ((value.toUInt32 &&& ((1 <<< bits.toUInt32) - 1)).toUInt64 <<< s.bits.toUInt64)
        bits := s.bits + bits.toUInt32 })

/-- `int deflatePending(z_streamp strm, unsigned *pending, int *bits)`.
Optional output cells are independent; omitted cells remain absent. -/
def Goal.deflatePending : Prop :=
  ∀ pending bits, CheckedDeflate (fun p => Zlib.Deflate.deflatePending p pending bits)
    (Z_STREAM_ERROR, none, none) <|
  ∀ h r i z s, DeflateView h r i z s →
    C.run (Zlib.Deflate.deflatePending (some r) pending bits) h =
      .ok (((if pending ∧ 2 ^ 32 ≤ s.pending.toNat then Z_BUF_ERROR else Z_OK),
        if pending then some (if 2 ^ 32 ≤ s.pending.toNat then 0xffffffff else s.pending.toUInt32) else none,
        if bits then some s.bi_valid else none), h)

/-- `int deflateUsed(z_streamp strm, int *bits)`.
Return the modulo-eight bit-use count through the optional scalar result. -/
def Goal.deflateUsed : Prop :=
  ∀ bits, CheckedDeflate (fun p => Zlib.Deflate.deflateUsed p bits) (Z_STREAM_ERROR, none) <|
  ∀ h r i z s, DeflateView h r i z s →
    C.run (Zlib.Deflate.deflateUsed (some r) bits) h =
      .ok ((Z_OK, if bits then some s.bi_used else none), h)

/-- `int deflateTune(z_streamp strm, int good_length, int max_lazy, int nice_length, int max_chain)`.
All signed arguments are covered. The three unsigned fields use C conversion. -/
def Goal.deflateTune : Prop :=
  ∀ good lazy nice chain,
  CheckedDeflate (fun p => Zlib.Deflate.deflateTune p good lazy nice chain) Z_STREAM_ERROR <|
  ∀ h r i z s, DeflateView h r i z s →
    C.run (Zlib.Deflate.deflateTune (some r) good lazy nice chain) h =
      .ok (Z_OK, putDeflate h i { s with
        good_match := good.toUInt32
        max_lazy_match := lazy.toUInt32
        nice_match := nice
        max_chain_length := chain.toUInt32 })

/-- `int deflateSetHeader(z_streamp strm, gz_headerp head)`.
Only the gzip wrapper accepts the pointer. The record is retained and read by later calls. -/
def Goal.deflateSetHeader : Prop :=
  ∀ head, CheckedDeflate (fun p => Zlib.Deflate.deflateSetHeader p head) Z_STREAM_ERROR <|
  ∀ h r i z s, DeflateView h r i z s →
    C.run (Zlib.Deflate.deflateSetHeader (some r) head) h =
      if s.wrap = 2 then .ok (Z_OK, putDeflate h i { s with gzhead := head })
      else .ok (Z_STREAM_ERROR, h)

end ZlibF.Spec.Public
