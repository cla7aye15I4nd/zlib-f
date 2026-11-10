# Fixed-block stream copy compares unrelated pointers

Confidence: high for the diagnosed unpatched C issue. The verified source now
includes the accepted upstream fix. This is not a proof of all copy histories.

Source pin: `757f0527154291bcf6bfbd6396ecde6bedd2db95`.
The reproduction compiles the unmodified decoder sources. It calls default
`inflateInit`, supplies a valid zlib stream with a fixed block, and provides
one output byte. `inflate` returns OK after producing `A`. It then calls
`inflateCopy` with a distinct zeroed destination.

Run from the repository root:

```sh
python3 docs/findings/inflate-copy-fixed/reproduce.py
```

The compiler and runtime must support address and pointer-comparison sanitizers.
Set `CC` to select the compiler. The script requires a nonzero execution exit
and the specific pointer-pair diagnosis; a compile error or another failure
does not count as reproduction.

The retained reproduction was run successfully on an LP64 build. The diagnostic
identifies `inflateCopy` at `inflate.c:1383`, the static `lenfix` object, and the
separately allocated inflate state. This is the source expression
`state->lencode >= state->codes`. Neither caller buffer is oversized or aliased.
The default LP64 Linux build has not been rerun for this finding.

The old translation retained that expression, and its pointer model rejected
ordering pointers from those different objects. No kernel-checked refutation
of `Goal.inflateCopy` is claimed. A faulting copy does not by itself establish
a successful copied destination in `StreamReachable`.

## Applied fix

[Upstream PR #1369](https://github.com/madler/zlib/pull/1369) contains the fix.
The maintainer confirmed application on 6 November 2026. The publicly fetched
`develop` and `master` heads still point to
`99623ef7097352da7993ba614161fd6a311e046e` and retain the old comparison.
The [temporary patch](../../../patches/README.md) exactly matches the submitted
commit `300fea14353d2e2ca61210aca7c48861ded5788c`.

The verified C and Lean translation now use pointer equality to distinguish
internal tables from fixed tables. Internal `lencode` is set to the copied
array base; `distcode` retains its offset. Pointer semantics and the caller
domain are unchanged. The historical reproduction above intentionally builds
the unpatched source. The [copy regression](../../../tests/regression/inflate-copy/README.md)
instead builds the patched source and compares actual successful copy calls
with the translation.
