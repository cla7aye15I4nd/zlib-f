# zlib-f

A Lean 4 project for formal verification of [zlib](https://github.com/madler/zlib).

The proof sources, translation checks, and CI are being prepared for a public release. The first reviewable source snapshot will arrive through a pull request.

Overview: [docs/overview.md](docs/overview.md).
Verification scope and final acceptance: [docs/spec/public-goals.md](docs/spec/public-goals.md).
Fixed definitions and editable proofs: [docs/anti-cheating.md](docs/anti-cheating.md).

Findings in zlib itself: [docs/findings.md](docs/findings.md).

## Layout

| Path | Contents |
| --- | --- |
| `zlib/` | upstream zlib, a pinned submodule, never modified |
| `patches/` | upstream fixes applied to the pinned source, see `patches/README.md` |
| `ZlibF/Runtime/` | the C-in-Lean runtime on the object heap: pointers, loops, faults, the heap tables (`Space`, `Monad`, `Ptr`), the C library (`Libc.lean`: `memcpy`, `memset`, `strlen`, `malloc`, `free`, string literals), and the rules for reasoning about them. `Schema.lean`, `Tables.lean` and `LibcTables.lean` are generated from the C headers |
| `scripts/` | `gen_schema.py` writes `Schema.lean`, `Tables.lean`, `LibcTables.lean` and `docs/runtime-schema.md` from the headers of the verified source |
| `ZlibF/Zlib/` | the translation: one module per C file, named like the C file: `zlib/adler32.c` is `ZlibF/Zlib/adler32.c.lean` |
| `ZlibF/Proof/` | the proofs: `ZlibF/Proof/adler32.c.lean` holds the proofs about `ZlibF/Zlib/adler32.c.lean`; big files are split into `X.c.<part>.lean`; proofs about the format specification are in `ZlibF/Proof/Format/` |
| `ZlibF/Runtime/Pilot.lean` | the object-heap experiment, now on the runtime (the only proofs that stay in `Runtime/`), see `docs/pilot.md` |
| `tests/audit/` | the audit program (see `docs/anti-cheating.md`), the list of theorems, and the locks on trusted definitions and statements |
| `docs/` | overview, specification (the per-function manual is [docs/spec/functions/index.md](docs/spec/functions/index.md)), proof method, proofs in text |

## Checking

```bash
lake build ZlibF            # build all modules
lake env lean --run tests/audit/Audit.lean tests/audit/theorems.txt   # audit of every declaration
scripts/check-sorry.sh      # no `sorry` is allowed in a final result (own CI job)
python3 scripts/gen_schema.py --zlib <verified source>   # regenerates the schema; the result must not change
```
