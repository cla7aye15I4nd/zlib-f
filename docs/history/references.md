# Reference material for verification

The main source snapshot is
[zlib-formal at `0f1428677ebf5b1614ff77f4702bbb382b2bf3c6`](https://github.com/cla7aye15I4nd/zlib-formal/tree/0f1428677ebf5b1614ff77f4702bbb382b2bf3c6).
The reference review read its source and audit documents. It did not rebuild the snapshot or
establish its results in this repository. This is a reuse record; [overview](../overview.md)
owns current work and [checking](../checking/README.md) defines acceptance.

## Ideas adapted

| Reference source | Adaptation here | Boundary |
| --- | --- | --- |
| `Spec/Api/InflateApi.lean`: `Call`, `exec` | Closed public-call alphabet and direct dispatch in `ZlibF/Spec/Public/Calls.lean` | Entry coverage does not prove each entry or a sequence |
| `translation_map.py` | Inventory checks public names, defining files and manual sections | This is not a full preprocessed syntax comparison |
| `check_imports.py` | Check the transitive root import closure and missing source files | A source module in the closure need not prove its public goal |
| `final_check.sh` | Distinguish development, specification readiness and final acceptance | A fast build is not final acceptance |
| `Spec/crc32.lean`, `Spec/adler32.lean` | Independent bit/register and modular-sum checksum specifications | Retain noncanonical seeds and the distinct one-byte Adler behaviour |
| `check_axioms.py` | Reject empty/duplicate registries; avoid checks disabled by optimisation; inspect declarations beyond registered names | Registration alone cannot validate a statement's domain or translation fidelity |
| `Witness/`, `CONTRACT_AUDIT.md` | Init-domain targets and non-vacuity requirements beside sequence goals | Actual init must establish the same invariant used by calls |

The table uses paths relative to the reference's `lean/` directory. The
[migration records](../migration/README.md) map the function families and changed representations.

## What does not transfer

The reference heap uses typed cells and byte blocks. The present heap uses object records and
tables. Heap statements and proof terms need adaptation. Pure arithmetic, bitstream relations,
loop measures and decomposition can retain their meaning only after their definitions and
domains are compared.

The reference sequence theorem `Zlib.Api.seq_safe` takes `ApiContract` as a hypothesis. Its
contract audit records instances with false preconditions and false strategy contracts. The call
alphabet and induction structure are useful. A conditional sequence theorem does not establish
safety here: every library callee needs a theorem about its actual translation, and actual init
must establish the invariant. Unrelated witnesses cannot supply that connection.

The reference's `ub.patch` policy and enabled patches differ. Its build configuration and proof
status do not transfer. This repository verifies its own upstream pin plus reviewed patches,
under its own public domains and acceptance rules.

```mermaid
flowchart LR
    R[Pinned reference] --> M[Extract mathematics and argument structure]
    M --> T[Restate for the present source and heap]
    T --> K[Kernel check, audit and mutants]
    K --> C[Accept only evidence for this repository]
```

[Design history](README.md) preserves the experiments that informed the representation.
[Proof documentation](../proof/README.md) explains the present argument structure. Neither a
reference link nor a historical reported test is a new validation run.
