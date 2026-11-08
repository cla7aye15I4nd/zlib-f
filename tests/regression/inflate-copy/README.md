# Inflate copy regression

Run `python3 tests/regression/inflate-copy/run.py` from the repository root.
The runner builds the actual Lean driver and three copied C libraries with all
repository patches. Address/undefined-behavior and address/pointer-pair checks
run in separate builds. The upstream submodule remains unchanged.

Eleven cases copy after the second inflate call, then end the original stream
and finish decoding with the copy. They cover fixed, stored and dynamic blocks,
split input, small output, and zlib, raw and gzip wrappers. Every case must
observe a successful copy, STREAM_END and the complete expected payload.
All three C outputs must match all Lean output fields byte for byte. Sanitizer
diagnostics are rejected. Leak detection is not part of this regression.

The C driver calls `inflateCopy` for fixed tables. It no longer substitutes
a synthetic fault for that call. Evidence goes under `tests/build/inflate-copy/`.
These finite execution checks are evidence of translation fidelity, not proof
of the full public copy contract or calling histories.
