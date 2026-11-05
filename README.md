# zlib-f

A Lean 4 project for formal verification of [zlib](https://github.com/madler/zlib).

The proof sources, translation checks, and CI are being prepared for a public release. The first reviewable source snapshot will arrive through a pull request.

Overview: [docs/overview.md](docs/overview.md).

## Layout

| Path | Contents |
| --- | --- |
| `zlib/` | upstream zlib, a pinned submodule, never modified |
| `patches/` | upstream fixes applied to the pinned source, see `patches/README.md` |
| `ZlibF/Runtime/` | the C-in-Lean runtime: heap, pointers, loops, faults, and the rules for reasoning about them |
| `ZlibF/Zlib/` | one module per C file, named like the C file: `zlib/adler32.c` is `ZlibF/Zlib/adler32.c.lean` |
| `Check.lean` | the axiom gate |
| `docs/` | overview, specification, proof method, proofs in text |

## Checking

```bash
lake build ZlibF            # build all modules
lake env lean Check.lean    # axiom gate over the listed theorems
scripts/check-sorry.sh      # the number of `sorry` may not exceed sorry-budget.txt
```
