# Reference material for verification

Reference snapshot: [zlib-formal, 0f1428677ebf5b1614ff77f4702bbb382b2bf3c6](https://github.com/cla7aye15I4nd/zlib-formal/tree/0f1428677ebf5b1614ff77f4702bbb382b2bf3c6).
This review read its source and audit documents. It did not rebuild that snapshot or import its
results as established theorems in this repository.

## Ideas used here

| Reference | Adaptation |
| --- | --- |
| `lean/ZlibLean/Spec/Api/InflateApi.lean`, `Call` and `exec` | `ZlibF/Spec/Public/Calls.lean` has a closed call alphabet and direct dispatch to the translated entries. It covers all 95 default-build public functions and retains their result types. |
| `lean/scripts/translation_map.py` | The public inventory checks header names, defining translation files and manual sections. This is a public-entry coverage check, not the reference's full preprocessed AST comparison. |
| `lean/scripts/check_imports.py` | The verification gate checks the transitive root import closure and rejects missing source files even if stale compiled objects exist. |
| `lean/scripts/final_check.sh` | Development checks, specification readiness and final acceptance have different commands. Final acceptance also runs the slow evidence checks. A fast green build is not a completed result. |
| `lean/ZlibLean/Spec/crc32.lean`, `Spec/adler32.lean` | Public checksum contracts use the same independent bit/register and modular-sum approach. The current one-byte Adler behaviour is stated separately; no canonical-seed narrowing is hidden in the safety domain. |
| `lean/scripts/check_axioms.py` | Empty and duplicate registries fail. The Python gate has no correctness-critical assertions that disappear under optimisation. The compiled declaration audit checks all declarations, not just registered theorem names. |
| `lean/ZlibLean/Witness/`, `docs/CONTRACT_AUDIT.md` | Initialisation-domain targets accompany the public sequence targets. The same actual initialisation must establish the shared invariant; unrelated or impossible contract instances do not establish non-vacuity. |

## Boundaries of reuse

The reference heap uses typed cells and byte blocks. This repository uses object records and
per-kind tables. Heap-level statements and proof terms need adaptation. Pure arithmetic,
bitstream arguments, loop measures and stage decompositions are useful starting points.

The reference's sequence theorem `Zlib.Api.seq_safe` takes `ApiContract` as a hypothesis.
Its contract audit records instances with `pre = False`, and records false strategy contracts.
We reuse the call alphabet and induction structure. A final theorem here must discharge every
library callee contract with an actual translated-callee theorem and establish the domain from
init. A conditional sequence theorem alone is not final API safety.

The reference's `ub.patch` policy and its enabled source patches differ from this repository's
policy. Its machine configuration, build instructions and proof status do not transfer.
Only source at this repository's pin plus its reviewed patches is being verified.

```mermaid
flowchart LR
    R["Pinned reference source"] --> M["Mathematics, call alphabet and proof structure"]
    M --> T["Adapt to the current translation and object heap"]
    T --> K["Kernel check and project audit"]
    K --> C["Count only the result accepted here"]
```

Current proof work and specification blockers remain in [overview.md](overview.md).
