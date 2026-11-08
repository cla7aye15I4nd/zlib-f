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

The submodule is never edited. A patch is allowed only for a confirmed upstream bug
that blocks a proof. It must be minimal, match a submitted upstream fix, and be listed
here. Remove it once upstream incorporates the fix and the pin moves past it.
