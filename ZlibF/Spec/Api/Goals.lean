import ZlibF.Spec.Api.Iface

/-!
# API model: the proof goals

Every statement that the project has to prove about the public API, as a `def ... : Prop`. A goal
is proved when a theorem listed in `tests/audit/goals.txt` has exactly the goal as its type.

*Model goals* (`Goal.format_*`, `Goal.inflate_decodes`, ..., `Goal.gz_roundtrip`) do not mention the
heap: they say that the model of `Inflate.lean`, `Deflate.lean`, `Compress.lean`, `Gz.lean` has
the properties `C1` to `C7` of `docs/overview.md`. Their proofs are about the model alone.

*Refinement goals* (`Goal.*_refines`, `Goal.*_copy`) take a `HeapApi` (the placeholder of
`Iface.lean`). They say that the translated C functions never fault and that every outcome is an
outcome of the model, with `Matches` before and after. The correctness of the library is the
composition: refinement says that the heap does what the model does; the model goals say what
the model does.

`docs/spec/api-lean.md` lists, for each goal, what its proof needs.
-/

namespace ZlibF.Spec.Api

open ZlibF.Spec

/-- The window bits and wrapper are one that `inflateInit2` / `inflateReset2` accepts. -/
def InflCfg (w : Wrap) (b : Nat) : Prop := ∃ wb, inflWbits wb = some (w, b)

/-- The parameters are one that `deflateInit2` accepts. -/
def DeflCfg (p : DeflParams) : Prop := ∃ l m wb ml s, deflInit? l m wb ml s = some p

/-- The state in which a run over a stream that needs the dictionary `d` starts: a fresh stream; a raw
stream (which has no `Z_NEED_DICT`) is given the dictionary before the first byte, as `zlib.h`
requires. (Without it a raw stream that uses the dictionary is rightly a data error.) -/
def InflStart (w : Wrap) (b : Nat) (d : List UInt8) : InflState :=
  if w = .raw then { InflState.fresh w b with dict := some d } else InflState.fresh w b

/-! ## The format is deterministic and self-delimiting (needed by C1, C2, C7) -/

/-- Decoding is a function: one stream has one decoding. -/
def Goal.format_deterministic : Prop :=
  ∀ (w : Wrap) (b : Nat) (d z o1 o2 : List UInt8),
    Layer.Decodes w b d z o1 → Layer.Decodes w b d z o2 → o1 = o2

/-- A complete stream has no complete extension: where a stream ends is determined by its bytes. -/
def Goal.format_prefix_free : Prop :=
  ∀ (w : Wrap) (b : Nat) (d z t o1 o2 : List UInt8),
    Layer.Decodes w b d z o1 → Layer.Decodes w b d (z ++ t) o2 → t = []

/-! ## C2, C3: inflate decodes valid streams and rejects invalid ones -/

/-- `C2`. For every valid stream `z` (zlib, gzip or raw, with the dictionary `d`) decoding to `o`,
in a configuration that accepts every format-valid stream (`FullWindow`), every run of `inflate`
over `z` -- any way of cutting the input into calls, any room, any flush value, with or without
`inflateSetDictionary` -- never fails, only produces a prefix of `o`, consumes only a prefix of `z`,
and if it ends (`Z_STREAM_END`) it has produced exactly `o` from exactly `z`. -/
def Goal.inflate_decodes : Prop :=
  ∀ (w : Wrap) (b : Nat) (d z o : List UInt8) (s : InflState),
    InflCfg w b → Layer.Decodes w b d z o → FullWindow w b z →
    InflTrace z d (InflStart w b d) s →
    s.phase ≠ .bad ∧ s.phase ≠ .syncing ∧ s.out <+: o ∧ s.seen <+: z ∧
    (s.phase = .done → s.out = o ∧ s.seen = z)

/-- `C2`, liveness. From any state of such a run in which the stream is still running, a call that
presents all the remaining input, with room for the remaining output and a flush value
`Z_NO_FLUSH`, `Z_SYNC_FLUSH` or `Z_FINISH`, ends the stream: `Z_STREAM_END`, the rest of `o` produced, all
of `z` consumed; or `Z_MEM_ERROR` (the window could not be allocated, `InflRunMem`). (Streams that need a dictionary are covered by `Goal.dict_roundtrip`.) -/
def Goal.inflate_completes : Prop :=
  ∀ (w : Wrap) (b : Nat) (d z o : List UInt8) (s : InflState) (c : InflCall) (r : InflRes)
    (s' : InflState),
    InflCfg w b → Layer.Decodes w b d z o → FullWindow w b z → ¬ HdrNeedsDict w b z →
    InflTrace z d (InflStart w b d) s → s.phase = .running →
    c.badBuf = false → c.inp = z.drop s.seen.length → o.length ≤ s.out.length + c.availOut →
    (c.flush = .noFlush ∨ c.flush = .syncFlush ∨ c.flush = .finish) →
    InflModel s (.inflate c) r s' →
    (r.rc = Z.streamEnd ∧ r.out.consumed = z.length - s.seen.length ∧
      r.out.produced = o.drop s.out.length) ∨ r.rc = Z.memError

/-- `C3`, inflate side. If an input has a prefix that is not viable, at least `detectLag` bytes
before its end (`Layer.Detectable`: a corrupt stream, with the corruption not in the last bytes),
then no run over it ends the stream, and a call that presents all the remaining input and has room
left over answers `Z_DATA_ERROR`. -/
def Goal.inflate_rejects_invalid : Prop :=
  ∀ (w : Wrap) (b : Nat) (d z : List UInt8) (s : InflState),
    InflCfg w b → Layer.Detectable w b d z → ¬ HdrNeedsDict w b z →
    InflTrace z d (InflStart w b d) s →
    s.phase ≠ .done ∧
    (s.phase = .running → ∀ (c : InflCall) (r : InflRes) (s' : InflState),
      c.badBuf = false → c.inp = z.drop s.seen.length →
      (c.flush = .noFlush ∨ c.flush = .syncFlush ∨ c.flush = .finish) →
      InflModel s (.inflate c) r s' → r.out.produced.length < c.availOut →
      r.rc = Z.dataError ∨ r.rc = Z.memError)

/-- `C3`, deflate side: whenever a run of `deflate` has delivered the whole stream
(`Z_STREAM_END`), the output is a valid stream of the layer for exactly the input that was
accepted (`F-deflate-valid`), for every level, strategy, `memLevel`, `windowBits`, flush schedule and
chunking of the input. -/
def Goal.deflate_valid : Prop :=
  ∀ (p : DeflParams) (x : List UInt8) (s : DeflState),
    DeflCfg p → DeflTrace x (DeflState.fresh p) s → s.done = true → s.precise = true →
    s.Valid s.produced s.input

/-- `C3`, deflate side, liveness: a `Z_FINISH` call that presents all the remaining input, with room
for what is still owed up to `deflateBound`, delivers the whole stream. -/
def Goal.deflate_completes : Prop :=
  ∀ (p : DeflParams) (x : List UInt8) (s : DeflState) (c : DeflCall) (r : DeflRes) (s' : DeflState),
    DeflCfg p → DeflTrace x (DeflState.fresh p) s → s.clean = true → s.precise = true →
    s.finishing = false → s.done = false → c.badBuf = false → c.flush = .finish →
    c.inp = x.drop s.input.length → 0 < c.availOut →
    s.bound x.length ≤ s.produced.length + c.availOut →
    DeflModel s (.deflate c) r s' → r.rc = Z.streamEnd ∧ s'.done = true ∧ s'.input = x

/-- `C3`, `Z_FULL_FLUSH` (raw deflate): everything after a completed full flush is a valid
stream by itself, for the input accepted after it. -/
def Goal.deflate_full_flush_resync : Prop :=
  ∀ (p : DeflParams) (x : List UInt8) (s : DeflState) (pl il : Nat),
    DeflCfg p → p.wrap = .raw → DeflTrace x (DeflState.fresh p) s → s.done = true →
    s.precise = true → s.dict = none → s.fullAt = some (pl, il) →
    Deflate.Decodes [] (s.produced.drop pl) (s.input.drop il)

/-! ## C1: the round trip -/

/-- The inflate configuration reads what the deflate parameters write, with a full window. -/
def Compatible (p : DeflParams) (w : Wrap) (b : Nat) : Prop :=
  InflCfg w b ∧ b = 15 ∧
  ((p.wrap = .raw ∧ w = .raw) ∨ (p.wrap = .zlib ∧ (w = .zlib ∨ w = .auto)) ∨
   (p.wrap = .gzip ∧ (w = .gzip ∨ w = .auto)))

/-- `C1`. Whatever the parameters, the flush schedule and the chunking of the input of `deflate`,
whatever the chunking and the room of `inflate`: a run of `inflate` over what `deflate` delivered
never fails, only produces a prefix of the original input, and if it ends it has produced the whole
original input. (The dictionary, if any, is supplied.) -/
def Goal.roundtrip : Prop :=
  ∀ (p : DeflParams) (x : List UInt8) (sd : DeflState) (w : Wrap) (b : Nat) (si : InflState),
    DeflCfg p → Compatible p w b →
    DeflTrace x (DeflState.fresh p) sd → sd.done = true → sd.precise = true → sd.input = x →
    InflTrace sd.produced sd.dictEff (InflStart w b sd.dictEff) si →
    si.phase ≠ .bad ∧ si.out <+: x ∧ (si.phase = .done → si.out = x ∧ si.seen = sd.produced)

/-- `C1`, liveness (no dictionary): from any state of such a run, a call that presents the rest of
the stream, with room for the rest of the input, ends the stream with exactly the original input. -/
def Goal.roundtrip_completes : Prop :=
  ∀ (p : DeflParams) (x : List UInt8) (sd : DeflState) (w : Wrap) (b : Nat) (si : InflState)
    (c : InflCall) (r : InflRes) (si' : InflState),
    DeflCfg p → Compatible p w b →
    DeflTrace x (DeflState.fresh p) sd → sd.done = true → sd.precise = true → sd.input = x →
    sd.dictEff = [] →
    InflTrace sd.produced [] (InflStart w b []) si → si.phase = .running →
    c.badBuf = false → c.inp = sd.produced.drop si.seen.length →
    x.length ≤ si.out.length + c.availOut →
    (c.flush = .noFlush ∨ c.flush = .syncFlush ∨ c.flush = .finish) →
    InflModel si (.inflate c) r si' →
    (r.rc = Z.streamEnd ∧ r.out.produced = x.drop si.out.length) ∨ r.rc = Z.memError

/-! ## C4: dictionaries and headers -/

/-- `C4`, dictionary. A zlib stream that `deflate` wrote with the preset dictionary `d` (not empty)
is accepted with `d`, is rejected with a dictionary of another Adler-32 (format level), and
`inflateSetDictionary` of such a dictionary answers `Z_DATA_ERROR` at every point where the stream is
waiting for its dictionary. -/
def Goal.dict_roundtrip : Prop :=
  ∀ (p : DeflParams) (d x : List UInt8) (sd : DeflState),
    DeflCfg p → p.wrap = .zlib → DeflTrace x (DeflState.fresh p) sd → sd.done = true →
    sd.precise = true → sd.input = x → sd.dict = some d → d ≠ [] →
    Layer.Decodes .zlib 15 d sd.produced x ∧
    (∀ d', adler32 d' ≠ adler32 d → ¬ Zlib.Decodes d' sd.produced x) ∧
    (∀ (s : InflState) (d' : List UInt8) (rc : Int) (s' : InflState),
      InflTrace sd.produced d (InflState.fresh .zlib 15) s → s.phase = .needDict →
      InflSetDict s d' rc s' → adler32 d' ≠ adler32 d → rc = Z.dataError)

/-- What `inflateGetHeader` stores for the header that `deflateSetHeader` was given and `deflate`
wrote, under the buffers `req`. -/
def expectedHdr (req : HdrReq) (p : DeflParams) (h : GzHead) : GzHdrOut :=
  fillHeader req h.flg (h.time % 2 ^ 32) (xflOf p) (h.os % 256) (h.extra.getD []) (h.name.getD [])
    (h.comment.getD [])

/-- `C4`, header. Whatever `inflate` reads as the header of a stream that `deflate` wrote with the
header `h` is `expectedHdr`: `deflateSetHeader` is reproduced by `inflateGetHeader`. -/
def Goal.header_roundtrip : Prop :=
  ∀ (p : DeflParams) (h : GzHead) (x : List UInt8) (sd : DeflState) (req : HdrReq) (g : GzHdrOut),
    DeflCfg p → p.wrap = .gzip → h.Valid → DeflTrace x (DeflState.fresh p) sd → sd.done = true →
    sd.precise = true → sd.hdr = some h → HeaderRead req sd.produced g → g = expectedHdr req p h

/-! ## C5: bounds -/

/-- `C5`, `deflateBound`. If the stream was only fed input and `Z_FINISH` (`clean`) and ended, the
output is at most `deflateBound` of the input, whatever the input (any ratio). -/
def Goal.deflate_bound_adequate : Prop :=
  ∀ (p : DeflParams) (x : List UInt8) (s : DeflState),
    DeflCfg p → DeflTrace x (DeflState.fresh p) s → s.done = true → s.clean = true →
    s.produced.length ≤ s.bound s.input.length

/-- `C5`, `compressBound`. A destination of `compressBound` bytes is enough for `compress2` at every
level, and the output is never larger. -/
def Goal.compress_bound_adequate : Prop :=
  ∀ (level : Int) (src : List UInt8) (cap : Nat) (rc : Int) (dst : List UInt8),
    compressBound src.length ≤ cap → Compress2 true level src cap rc dst →
    rc ≠ Z.bufError ∧ dst.length ≤ compressBound src.length

/-- `C1` for `compress2` and `uncompress2`: what `compress2` writes, `uncompress2` reads back, with
a destination as large as the source. -/
def Goal.compress_roundtrip : Prop :=
  ∀ (level : Int) (src : List UInt8) (cap cap2 : Nat) (dst src2 : List UInt8) (used : Nat)
    (rc2 : Int),
    Compress2 true level src cap Z.ok dst → src.length ≤ cap2 →
    Uncompress2 true dst cap2 rc2 src2 used →
    (rc2 = Z.ok → src2 = src ∧ used = dst.length) ∧ (rc2 ≠ Z.ok → rc2 = Z.memError)

/-! ## C7: gz files -/

/-- `C7`, write then read. A file that a writer closed, with nothing failing and nothing before
it, reads back as exactly the bytes written (`gzdirect` 0, status `Z_OK`). -/
def Goal.gz_roundtrip : Prop :=
  ∀ (h : GzHandle) (rc : Int) (final : List UInt8),
    h.mode = .write → h.base = [] → h.failed = false → h.direct ≠ 1 →
    GzClose h rc final → rc = Z.ok → GzDecoded false final h.written Z.ok

/-- `C7`, seek and tell. After a successful `gzseek` of a reader, `gztell` is the position returned,
and the next read returns the data from there. -/
def Goal.gz_seek_read : Prop :=
  ∀ (h h1 h2 : GzHandle) (off whence ret : Int) (n : Nat) (bytes : List UInt8) (ret2 : Int),
    h.mode = .read → h.pushed = [] → n ≤ 2 ^ 31 - 1 →
    (h.past = false ∨ h.CopyMode ∨ ret < h.tell) → GzSeek h off whence ret h1 → 0 ≤ ret →
    h1.tell = ret ∧ (h1.pushed = [] → GzReadFn h1 n bytes ret2 h2 →
      bytes = (h.dec.drop ret.toNat).take n)

/-! ## Refinement goals (need the placeholder `HeapApi`) -/

/-- Every inflate operation on a stream that `Matches` a model state, with its arguments in the
heap as `zlib.h` requires: the translated function does not fault, and what it returns and
leaves is allowed by the model (`InflModel`), with `Matches` again. -/
def Goal.inflate_refines (A : HeapApi) : Prop :=
  ∀ (h : A.Heap) (s : A.Strm) (st : InflState) (op : InflOp),
    A.inflMatches h s st → A.inflArgs h s op →
    ∀ out, A.inflRun h s op out →
      ∃ h' r st', out = .ret h' r ∧ InflModel st op r st' ∧ A.inflMatches h' s st'

/-- `inflateInit` / `inflateInit2`: no fault; the result is `InflInit`; a stream is created exactly
when the code is `Z_OK`, otherwise `state` is null and nothing stays allocated. -/
def Goal.inflate_init_refines (A : HeapApi) : Prop :=
  ∀ (h : A.Heap) (s : A.Strm) (wb : Int) (vok : Bool),
    A.inflInitArgs h s → ∀ out, A.inflInit h s wb vok out →
      ∃ h' rc r, out = .ret h' rc ∧ InflInit wb vok rc r ∧
        (match r with | some st => A.inflMatches h' s st | none => A.inflNoState h' s)

/-- `inflateEnd`: no fault, `Z_OK`, and the stream has no state afterwards. -/
def Goal.inflate_end_refines (A : HeapApi) : Prop :=
  ∀ (h : A.Heap) (s : A.Strm) (st : InflState),
    A.inflMatches h s st → ∀ out, A.inflEnd h s out →
      ∃ h' rc, out = .ret h' rc ∧ InflEnd st rc ∧ A.inflNoState h' s

/-- `inflateCopy` (`C6`): no fault; the source is unchanged; on `Z_OK` the destination is a stream
with the same model state and its own storage (disjoint from the source). -/
def Goal.inflate_copy_refines (A : HeapApi) : Prop :=
  ∀ (h : A.Heap) (dst src : A.Strm) (st : InflState),
    A.inflMatches h src st → A.inflNoState h dst → ∀ out, A.inflCopy h dst src out →
      ∃ h' rc d, out = .ret h' rc ∧ InflCopy st rc d ∧ A.inflMatches h' src st ∧
        (match d with | some st2 => A.inflMatches h' dst st2 ∧ A.inflDisjoint h' src dst
                      | none => True)

/-- `inflateBack`: no fault; the result is allowed by `InflBack`. -/
def Goal.inflate_back_refines (A : HeapApi) : Prop :=
  ∀ (h : A.Heap) (s : A.Strm) (wb : Nat) (first : List UInt8) (cb : BackCallbacks),
    ∀ out, A.inflBack h s wb first cb out →
      ∃ h' r, out = .ret h' r ∧ InflBack wb first cb r

/-- Every deflate operation, as `Goal.inflate_refines`. -/
def Goal.deflate_refines (A : HeapApi) : Prop :=
  ∀ (h : A.Heap) (s : A.Strm) (st : DeflState) (op : DeflOp),
    A.deflMatches h s st → A.deflArgs h s op →
    ∀ out, A.deflRun h s op out →
      ∃ h' r st', out = .ret h' r ∧ DeflModel st op r st' ∧ A.deflMatches h' s st'

/-- `deflateInit` / `deflateInit2`, as `Goal.inflate_init_refines`. -/
def Goal.deflate_init_refines (A : HeapApi) : Prop :=
  ∀ (h : A.Heap) (s : A.Strm) (l m wb ml st : Int) (vok : Bool),
    A.deflInitArgs h s → ∀ out, A.deflInit h s l m wb ml st vok out →
      ∃ h' rc r, out = .ret h' rc ∧ DeflInit l m wb ml st vok rc r ∧
        (match r with | some ds => A.deflMatches h' s ds | none => A.deflNoState h' s)

/-- `deflateEnd`: no fault, `DeflEnd`, no state afterwards. -/
def Goal.deflate_end_refines (A : HeapApi) : Prop :=
  ∀ (h : A.Heap) (s : A.Strm) (st : DeflState),
    A.deflMatches h s st → ∀ out, A.deflEnd h s out →
      ∃ h' rc, out = .ret h' rc ∧ DeflEnd st rc ∧ A.deflNoState h' s

/-- `deflateCopy` (`C6`), as `Goal.inflate_copy_refines`. -/
def Goal.deflate_copy_refines (A : HeapApi) : Prop :=
  ∀ (h : A.Heap) (dst src : A.Strm) (st : DeflState),
    A.deflMatches h src st → A.deflNoState h dst → ∀ out, A.deflCopy h dst src out →
      ∃ h' rc d, out = .ret h' rc ∧ DeflCopy st rc d ∧ A.deflMatches h' src st ∧
        (match d with | some st2 => A.deflMatches h' dst st2 ∧ A.deflDisjoint h' src dst
                      | none => True)

/-- `compress2`: no fault; the result is `Compress2`. -/
def Goal.compress2_refines (A : HeapApi) : Prop :=
  ∀ (h : A.Heap) (ok : Bool) (level : Int) (src : List UInt8) (cap : Nat),
    A.utilArgs h ok src cap → ∀ out, A.compress2 h ok level src cap out →
      ∃ h' rc dst, out = .ret h' (rc, dst) ∧ Compress2 ok level src cap rc dst

/-- `compress`: no fault; the result is `Compress`. -/
def Goal.compress_refines (A : HeapApi) : Prop :=
  ∀ (h : A.Heap) (ok : Bool) (src : List UInt8) (cap : Nat),
    A.utilArgs h ok src cap → ∀ out, A.compress h ok src cap out →
      ∃ h' rc dst, out = .ret h' (rc, dst) ∧ Compress ok src cap rc dst

/-- `uncompress2`: no fault; the result is `Uncompress2`. -/
def Goal.uncompress2_refines (A : HeapApi) : Prop :=
  ∀ (h : A.Heap) (ok : Bool) (src : List UInt8) (cap : Nat),
    A.utilArgs h ok src cap → ∀ out, A.uncompress2 h ok src cap out →
      ∃ h' rc dst used, out = .ret h' (rc, dst, used) ∧ Uncompress2 ok src cap rc dst used

/-- `uncompress`: no fault; the result is `Uncompress`. -/
def Goal.uncompress_refines (A : HeapApi) : Prop :=
  ∀ (h : A.Heap) (ok : Bool) (src : List UInt8) (cap : Nat),
    A.utilArgs h ok src cap → ∀ out, A.uncompress h ok src cap out →
      ∃ h' rc dst, out = .ret h' (rc, dst) ∧ Uncompress ok src cap rc dst

/-- `gzopen` / `gzdopen`: no fault; `NULL` or a handle that `Matches` a model handle allowed by
`GzOpen` for the content of the file. -/
def Goal.gz_open_refines (A : HeapApi) : Prop :=
  ∀ (h : A.Heap) (mode : List Char) (existing : Option (List UInt8)),
    ∀ out, A.gzOpen h mode existing out →
      ∃ h' r hd?, out = .ret h' r ∧ GzOpen mode existing hd? ∧
        (match r, hd? with
         | none, none => True
         | some f, some hd => A.gzMatches h' f hd
         | _, _ => False)

/-- Every gz operation on an open file: no fault; the result is allowed by `GzModel`. -/
def Goal.gz_refines (A : HeapApi) : Prop :=
  ∀ (h : A.Heap) (f : A.GzFile) (hd : GzHandle) (op : GzOp),
    A.gzMatches h f hd → A.gzArgs h f op →
    ∀ out, A.gzRun h f op out →
      ∃ h' r hd', out = .ret h' r ∧ GzModel hd op r hd' ∧ A.gzMatches h' f hd'

/-- `gzclose`: no fault; the result and the content of the file afterwards are allowed by `GzClose`
(`C7`: a writer's file reads back as what was written). -/
def Goal.gz_close_refines (A : HeapApi) : Prop :=
  ∀ (h : A.Heap) (f : A.GzFile) (hd : GzHandle),
    A.gzMatches h f hd → ∀ out, A.gzClose h f out →
      ∃ h' rc final, out = .ret h' (rc, final) ∧ GzClose hd rc final

end ZlibF.Spec.Api
