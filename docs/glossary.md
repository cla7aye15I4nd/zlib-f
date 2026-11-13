# Glossary

Terms used in the specifications and proofs, in the order a reader needs them.
Status words are defined in [contributing](checking/contributing.md) and in
[progress](progress.md#scope).

**Target.** A statement the project proves about one C function or call sequence. Its Lean name starts with `Goal.`.

**Goal.** A target written as a Lean proposition in `ZlibF/Spec/`. A goal is proved only by a theorem whose type is exactly the goal.

**Checked.** The theorem is on `dev` and the fast gate is green. **Accepted.** The theorem is also registered and the acceptance suite is green on a named commit.

**Registered.** Listed in `tests/audit/theorems.txt`.

**Not planned.** A target the project does not work on. It is never called proved.

**Fault.** The model's result for undefined behaviour. Every undefined behaviour the C can reach raises `Fault.ub`. A safety theorem shows that no run raises it.

**Heap, pointer.** The runtime model of memory in `ZlibF/Runtime/`. A pointer in fresh memory is NULL. A proof shows that a pointer field was written before it is read.

**Precondition.** What a theorem assumes about its inputs. A precondition narrower than `zlib.h` allows is written in the theorem's docstring and listed in [deviations](deviations.md).

**Separation precondition.** The caller's buffers do not overlap each other or the stream's own storage. `zlib.h` states this in prose. A theorem states it as a hypothesis.

**Representation invariant.** A property of a stream's state that every call preserves, for example `DGood` for a deflate stream and `Good` for an inflate stream. The init function establishes it.

**`StreamBuffers`.** The hypothesis on `next_in`, `avail_in`, `next_out` and `avail_out`. Each range is NULL or readable (the output range writable), neither lies in the stream's own storage, and the input and output ranges are separate. `Goal.inflate` and `Goal.deflate` assume it.

**Sequence goal.** A statement about any sequence of calls on one stream, such as `inflate_sequence`.

**Differential test.** A run of the real C and of the Lean translation on the same input, compared. It is evidence of fidelity, not proof.

**Proof mutant.** A deliberately wrong translation, such as a dropped check. A sound proof must fail on it.

**Fast gate.** The jobs `build` and `no-sorry`. They run on every push and pull request.

**Acceptance suite.** Axiom gate, exact goal match, proof mutants and differential tests. It runs nightly on `main` and on request.

**Milestone.** `inflate` proved, `deflate` proved, a sequence goal proved, or about twenty newly checked targets.
