import ZlibF.Spec.Public.Initialisation

/-!
# Initialisation: functional goals and the definitions only they use

Split from `ZlibF/Spec/Public/Initialisation.lean` without a change of statement or name
(`docs/design/safety-functional-split.md`). The namespace stays `ZlibF.Spec.Public`.
-/

namespace ZlibF.Spec.Public
open C

/-- `int inflateInit2_(z_streamp strm, int windowBits, const char *version, int stream_size)`.
All signed window arguments and every allocation oracle are included, in source error order. -/
def Goal.inflateInit2_ : Prop :=
  ∀ wb, InflateInitContract (fun p v size => Zlib.Inflate.inflateInit2_ p wb v size) wb

/-- `int inflateInit_(z_streamp strm, const char *version, int stream_size)`.
The same version, stream, allocation, cleanup and invariant contract at window bits 15. -/
def Goal.inflateInit_ : Prop := InflateInitContract Zlib.Inflate.inflateInit_ 15

/-- `int deflateInit2_(z_streamp strm, int level, int method, int windowBits, int memLevel,
int strategy, const char *version, int stream_size)`.
Every signed argument, source-ordered refusal, five allocations, failure cleanup and success invariant. -/
def Goal.deflateInit2_ : Prop :=
  ∀ level method wb mem strategy,
    DeflateInitContract (fun p v size => Zlib.Deflate.deflateInit2_ p level method wb mem strategy v size)
      level method wb mem strategy

/-- `int deflateInit_(z_streamp strm, int level, const char *version, int stream_size)`.
The default method, window, memory level and strategy; the level remains arbitrary. -/
def Goal.deflateInit_ : Prop :=
  ∀ level, DeflateInitContract (fun p v size => Zlib.Deflate.deflateInit_ p level v size)
    level 8 15 8 0

end ZlibF.Spec.Public
