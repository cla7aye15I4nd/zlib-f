# Sliding subtraction translation regression

Run `bash tests/regression/deflate-slide/run.sh` with a built C library for the current source and patches.
The fixture includes the real C file to call its internal `fill_window`.
The Lean fixture calls the translated function.

Three states exercise ordinary subtraction, the lowest representable result,
and a large positive input. Their observed results must match. A fourth state
sets `block_start` to the signed minimum before a slide. The C sanitizer must
reject the subtraction, and the translation must return its signed-overflow
fault. The former direct `Int64` subtraction instead returned a positive value.

These are artificial internal states. The fixture does not show that a legal
API sequence can reach the overflowing state. It diagnoses the translation's
overflow semantics; it is not a confirmed issue in zlib. Differential checks
are evidence of fidelity, not proof.

The runner also restores unchecked subtraction in an isolated copy. The three
defined results must stay equal, and only the overflow observation must change.
This checks that the regression detects the former translation.
