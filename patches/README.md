# Patches

The verified source is the pinned `zlib/` submodule plus any `*.patch` files in this
directory, applied in name order.

## 0001-inflate-copy-pointer-equality.patch

Avoid relational comparisons between the static fixed-code table and the
state's internal code array in `inflateCopy`. The retained
[reproduction](../docs/findings/inflate-copy-fixed/README.md) diagnoses the
unpatched C. This blocks the corresponding total safety proof.

The patch exactly matches commit
`300fea14353d2e2ca61210aca7c48861ded5788c` in
[upstream PR #1369](https://github.com/madler/zlib/pull/1369).
The maintainer confirmed application on 6 November 2026. The publicly
fetchable `develop` and `master` heads still name
`99623ef7097352da7993ba614161fd6a311e046e`, whose `inflate.c` retains the old
comparison. Keep the current pin and this submitted fix until the applied
commit is available on the upstream branch. Then advance the pin and remove
the patch.

## 0002-gzseek-negative-position-overflow.patch

Avoid signed overflow in `gzseek64` after an initial `gzungetc`, which sets
`state->x.pos` to -1: the `SEEK_CUR` range check evaluated `GZ_OFF_MAX - pos`
with a negative `pos`, and a `SEEK_SET` target near `GZ_OFF_MAX` overflowed in
`pos - state->x.pos`. UndefinedBehaviorSanitizer reports both on the unpatched
C. This is R-1 in [the gzip proof notes](../docs/proof/gzip.md) and blocks the
safety proof of `gzseek64` and `gzseek`.

The patch is the `gzlib.c` part of
[upstream PR #1361](https://github.com/madler/zlib/pull/1361) at head
`ce2248ee9750`. The `test/example.c` part of that pull request is not part of
the verified source. The pull request is open.

## 0003-gzread-partial-copy-read-error.patch

In transparent (`COPY`) mode, set `state->x.next = state->out` before
`gz_load`. If `read` supplies some bytes and then fails, `gz_load` leaves the
partial count in `x.have` and returns -1, and `gz_fetch` returned before its
assignment of `x.next`. The readers then consumed the partial bytes through a
stale `x.next`: an out-of-bounds read when the previous output buffer was
exhausted. This is R-2 in [the gzip proof notes](../docs/proof/gzip.md) and
blocks the safety proof of the read side.

The patch is exactly the change of
[upstream PR #1363](https://github.com/madler/zlib/pull/1363) at head
`37627fd3bb47`. The pull request is open.

## 0004-gz-position-overflow.patch

Local, not yet submitted upstream; approved by the owner on 2026-11-12.

Keep the uncompressed position `state->x.pos` within `z_off64_t`. Reading: `gz_fetch` fills the
output buffer only with bytes whose position is representable (at least one, to find the end of
the input), and `gz_read` and `gzgets` deliver no byte past `GZ_OFF_MAX`; data beyond it gives
`Z_DATA_ERROR` "position overflow". Writing: `gz_write`, the fast path of `gzputc` and `gzprintf`
refuse a write that would carry the position past `GZ_OFF_MAX`, with the same error. Findings:
[gzread-pos-overflow](../docs/findings/gzread-pos-overflow/README.md) (F-1) and
[gzwrite-pos-overflow](../docs/findings/gzwrite-pos-overflow/README.md) (W7). Evidence:
UndefinedBehaviorSanitizer reports the signed overflow on x86_64 Linux for both, with
`/dev/zero` and the real `/dev/null`; reproductions under `tests/regression/`. This blocks the
safety proof of the gz readers and writers. A pull request draft is in the read-side finding.

## 0005-gz-next-zero-advance.patch

Local, not yet submitted upstream; approved by the owner on 2026-11-12.

In `gzseek64` and `gz_skip_have`, advance `state->x.next` only when the advance `n` is not zero.
With `n == 0` the field may never have been written (`gz_reset` does not set it: R-3) or may point
into a caller buffer that has been freed after a direct `gzread` (R-4); arithmetic on either is
undefined in C. No result or state changes. Findings:
[gz-reset-next-uninitialised](../docs/findings/gz-reset-next-uninitialised/README.md) (R-3) and
[gz-next-dangling-after-direct-read](../docs/findings/gz-next-dangling-after-direct-read/README.md)
(R-4). Evidence: undefined by the letter of C; no sanitizer reports either. A probe in the
reproductions shows the zero advance on the never-written and on the dangling value, and its
absence with the patch. The proof rule that a pointer field is written before it is read, and the
model's fault on arithmetic with a dangling pointer, block the gz reader proofs without it. A pull
request draft is in the R-3 finding.

The submodule is never edited. A patch is allowed only for a confirmed upstream bug
that blocks a proof. It must be minimal, match a submitted upstream fix, and be listed
here. A patch approved by the owner may land before its upstream submission; its entry
then says it is local and pending, and it is replaced by the upstream fix when one
exists. Remove a patch once upstream incorporates the fix and the pin moves past it.
