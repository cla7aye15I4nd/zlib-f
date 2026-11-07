# Proof mutants

A proof must reject deliberate errors in the function it verifies. A proof mutant changes
one translated function in a temporary copy and requires the failure to occur in that
function's proof. The unmodified proof must pass first.

This is different from the differential self-test in `tests/selftest.sh`, which requires an
execution comparison to detect a mutation. A mutant caught only by testing can expose missing
proof coverage. A proof's rejection is evidence of sensitivity, not proof that the mutation
changes observable behaviour or that the theorem covers every error. Review must establish
that a required mutant changes behaviour on a permitted input.

## Run the checks

From the repository root, with a warm `.lake` build cache:

```sh
python3 scripts/verification.py mutants
bash tests/audit/proofmut.sh tests/audit/proofmut/adler32.tsv
bash tests/audit/proofmut.sh tests/audit/proofmut/crc32.tsv '^combine'
```

The first command builds the project, checks parsed public mutation boundaries, replays the
original exact public proofs and runs the model list plus every referenced public-function
list in strict mode. The other commands run an individual legacy list, optionally filtered
by mutant name. They are useful during development and do not replace final acceptance.

The list runner copies the workspace and warm cache into a temporary directory. It builds
the unmodified listed proof modules, applies each replacement exactly once and builds only
the designated modules. The first reported error must be in an expected proof module.
The original cache is left untouched. One mutant runs at a time.

| Verdict | Interpretation |
| --- | --- |
| `KILLED` | The first error is in an expected proof module. The mutation check passes. |
| `SAME ok` | An explicitly equivalent mutation still builds. Review the equivalence reason. |
| `GAP (known)` | A documented proof gap survives in development mode. It is not coverage and fails strict acceptance. |
| `SURVIVED` | An unexcused mutation still builds. Investigate missing coverage or equivalence. |
| `BAD MUTANT` | The translation or a file outside the proof tree fails. Repair the mutation. |
| `WRONG PLACE` | Another proof fails first. This does not satisfy the designated function's check. |
| `NO ERROR` | The build failed without a recognized error, even after one retry. No proof rejection was established. |
| `UNEXPECTED` | A mutation marked equivalent failed. Review the marker and mutation. |
| `NOT APPLIED` | The replacement text did not occur exactly once, or was unchanged. Update the mutation. |

A killed mutation with a stale `gap:` marker also fails. Remove the marker through the
reviewed audit update once the gap is closed. Strict mode forces the positive baseline and
rejects known gaps. Skipping the baseline cannot support final acceptance.

## Public entry requirements

Every exactly proved public entry needs a record in `tests/audit/public-mutants.json`.
The record names mutations of that function's translated body, with the signature preserved.
The parser checks both versions without loading candidate imports. Mutations of another
function, specification-only changes, injected declarations and marked proof gaps do not count.

In addition to rebuilding the designated proof modules, the public check takes the original
registered exact proof and substitutes only the changed source declarations into its
dependency closure. A fresh-kernel replay must accept the original and reject the mutation.
Failure of an unrelated theorem, or a stronger theorem with extra premises, is insufficient.
The authority and locking rules are in [the anti-cheating policy](../anti-cheating.md).

## List format

Lists use one tab-separated row per mutant. Lines starting with `#` are comments.

```text
NAME <TAB> FILE <TAB> OLD <TAB> NEW <TAB> PROOF_MODULES [<TAB> same:REASON | gap:REASON]
```

| Field | Meaning |
| --- | --- |
| `FILE` | Translation source relative to the repository root, such as `ZlibF/Zlib/adler32.c.lean`. |
| `OLD`, `NEW` | Replacement text. A literal `\n` denotes a newline; `OLD` must occur exactly once. |
| `PROOF_MODULES` | Comma-separated paths under `ZlibF/Proof`, without `.lean`, naming the expected function proofs. |
| Optional marker | `same:` explains equivalence; `gap:` records missing coverage for development only. Neither is allowed in a required public mutant record. |

Useful mutations drop a check or assignment, change a bound or comparison, alter an index or
shift, or return a wrong result. Choose different parts of a proved function. A syntax error
or a mutation that merely breaks a source-equality lemma is insufficient evidence for its
execution contract.

The checked-in lists under `tests/audit/proofmut/` cover checksum, utility, tree, inflate,
deflate and decode-table proof groups. Additional lists live under `tests/proof-mutants/`
and `tests/proofmut/`. The files and public mapping define their exact scope; a list's existence
or a historical result is not proof that every function in its C file is covered.

## Runner settings

`PROOFMUT_CACHE` selects the warm cache. `PROOFMUT_TIMEOUT` sets seconds per build, defaulting
to 3600. `PROOFMUT_KEEP=1` retains temporary copies; `PROOFMUT_SHOWLOG=1` prints failure details.
`PROOFMUT_BASELINE=0` skips the positive build for local diagnosis only.
`PROOFMUT_STRICT=1` overrides that skip and rejects all known gaps.

Final acceptance runs every list in the three supported directories in strict mode. CI also
runs the public/model mutation command. Neither a proposed workflow snippet nor an unexecuted
list counts as a passing check. Current coverage work is recorded in [progress](../progress.md).
