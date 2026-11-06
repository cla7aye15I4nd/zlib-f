# Reviewed recursive execution helpers

The audit lists six generated execution helpers for total logical definitions.
Each entry is the listed name followed by `._unsafe_rec`.

| Logical definition | Decreasing argument |
| --- | --- |
| `Zlib.Trees.Math.nextCode` | Natural-number predecessor. |
| `Zlib.Trees.Math.reverseLowBits` | Natural-number predecessor. |
| `Zlib.Trees.Math.scanCount` | Natural-number predecessor. |
| `Zlib.Trees.Math.scanMax` | Natural-number predecessor. |
| `Zlib.Trees.Proofs.Math.blMaxIdx` | Natural-number predecessor. |
| `Zlib.Trees.Proofs.tallyCalls` | List tail. |

The logical definitions have checked `Nat.rec` or `List.rec` equations.
The actual generated types and branch bodies were checked independently.
The body comparison replaces only the helper's self-reference with its total
logical counterpart. The recursive arguments were also inspected directly.
The inspected environment has no safe declaration that refers to these helpers.
They are absent from the registered theorems' logical dependency closure.

Only these exact declarations are added to the existing execution-helper list.
Their full exported syntax is locked. This does not permit partial definitions
in project source or establish compiler or machine-code correctness.
Current acceptance status remains in [the overview](../overview.md).
