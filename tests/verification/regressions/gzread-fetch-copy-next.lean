import ZlibF.Proof.«gzread.c.fetch-copy»

open C Zlib.Gzguts Zlib.GzFs Zlib.Gzread Zlib.Gzread.LoadErrno

/-! Upstream PR 1363 (`patches/0003-gzread-partial-copy-read-error.patch`): in `gz_fetch`, `case COPY`, the unpatched source set
`x.next = out` only after a successful `gz_load`. When `gz_load` failed after a partial read,
`x.have` counted the partial bytes while `x.next` kept its old value, and the readers copied from
there (R-2 in `docs/proof/gzip.md`; an out-of-bounds read on the real C). This regression separates the two orders on the translation: after a refused read in `COPY` mode, `x.next` is `out`. It is false for the
unpatched order, where `x.next` keeps whatever it held before. -/
namespace GzreadFetchCopyNextRegression

theorem copy_refusal_sets_next (h : Heap) (fs : Fs) (i : Nat) (s : GzState) (r : BRef)
    (a : Array UInt8) (e : Int32)
    (hs : h.gzstates i = some s) (how : s.how = GZ_COPY) (err : s.err = Z_OK)
    (out : s.out = .ref r 0) (ha : Space.get h r = some a)
    (hc : fs.readChoice fs.nos = .regular) (he : ReadRefusal s.fd fs e)
    {res : Int32} {fs' : Fs} {after : Heap}
    (run : gz_fetch (some (.tab i)) fs h = .ok ((res, fs'), after)) :
    res = -1 ∧ ∃ s', after.gzstates i = some s' ∧ s'.x.next = s.out ∧ s'.x.«have» = 0 :=
  Zlib.Gzread.FetchCopy.fetch_copy_refusal_next h fs i s r a e hs how err out ha hc he run

end GzreadFetchCopyNextRegression
