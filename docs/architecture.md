# Architecture

The layers, the runtime, the pilot that chooses the heap model, and the checks. Safety goals:
[safety.md](safety.md). Proof method and order: [method.md](method.md).

## 1. Layers

```mermaid
flowchart LR
    subgraph SRC["Source of truth"]
        direction LR
        C["zlib/*.c<br/>pinned submodule"]
        PA["patches/*.patch<br/>upstream fixes only"]
    end
    subgraph L0["L0: runtime (trusted by review)"]
        R["ZlibF/Runtime/*.lean<br/>heap, pointers, loops, Fault.ub"]
    end
    subgraph L1["L1: translation (trusted by review and difftest)"]
        T["ZlibF/Zlib/X.c.lean<br/>one module per C file<br/>statement by statement"]
    end
    subgraph SAFE["Safety (checked by the kernel)"]
        direction LR
        INV["Inv, Pre, Frame, Owns<br/>one invariant per struct"]
        MATH["math lemmas F1 F7 F8 F9<br/>no heap"]
        FS["f_safe theorems"]
        SEQ["sequence safety<br/>and leak-freedom"]
    end
    subgraph COR["Correctness (checked by the kernel)"]
        direction LR
        L2["L2 functional model"]
        L3["L3 specification<br/>from lean-zip and the RFCs"]
        FC["f_correct theorems<br/>round trip"]
    end

    PA --> C
    C --> T
    R --> T
    T --> FS
    INV --> FS
    MATH --> FS
    FS --> SEQ
    SEQ --> L2
    L2 --> FC
    L3 --> FC

    classDef src fill:#e9ecef,stroke:#495057,color:#111;
    classDef trust fill:#fff3cd,stroke:#b8860b,color:#111;
    classDef proof fill:#d4edda,stroke:#2e7d32,color:#111;
    classDef corr fill:#cfe2ff,stroke:#1565c0,color:#111;
    class C,PA src;
    class T,R trust;
    class INV,FS,SEQ,MATH proof;
    class L2,L3,FC corr;
```

Yellow is trusted: the kernel does not check that the translation matches the C or that the
runtime matches the C standard. Those two are covered by review and by differential tests.
Green is the safety proof, blue is the correctness proof. Both are checked by the kernel, and both
are built on the same state records.

## 2. Repository layout

```
zlib/                      upstream submodule, never modified
patches/                   upstream fixes, applied in name order
ZlibF/
  Runtime/                 the runtime
    Core.lean              heap, pointers, loops, faults
    Reasoning.lean         rules for reasoning about runtime programs
  Zlib/                    mirrors zlib/: same names, with .lean appended
    zlib.h.lean            constants, return codes, z_stream layout
    zutil.h.lean  zutil.c.lean
    adler32.c.lean         translation + invariant + proofs of adler32.c
    crc32.c.lean
    inftrees.h.lean  inftrees.c.lean
    inffast.c.lean
    inflate.h.lean  inflate.c.lean   (split into inflate.c/*.lean when large)
    deflate.h.lean  deflate.c.lean
    trees.h.lean  trees.c.lean
  Math/                    heap-free lemmas: Kraft, Huffman, cost model
Check.lean                 axiom gate over the listed theorems
Tests/                     differential tests against the real C
docs/
  spec/                    the specification in natural language
  proof/                   the proofs in natural language
```

A module name follows the C file: `zlib/X.c` maps to `ZlibF/Zlib/X.c.lean`. Math lemmas live in
`Math/` and import nothing from the runtime, so people can work on them in parallel.

## 3. The heap model (decision D1)

The recommendation is the **object heap**. Its parts:

```mermaid
flowchart LR
    subgraph H["Heap"]
        direction LR
        O1["structs<br/>blk to record<br/>InflateState, DeflateState, ZStream, …"]
        O2["byte arrays<br/>blk to Array UInt8<br/>window, pending_buf, caller buffers"]
        O3["word arrays<br/>blk to Array UInt16<br/>prev, head, lens, work"]
        O4["table arrays<br/>blk to Array Code / CtData"]
        G1["ghost: initialised flags"]
        G2["ghost: read-only set"]
        G3["ghost: alignment per block"]
        G4["allocation counter and oracle"]
    end
    P["pointer<br/>null, or block id + path + index"]
    P --> H

    classDef real fill:#cfe2ff,stroke:#1565c0,color:#111;
    classDef ghost fill:#fff3cd,stroke:#b8860b,color:#111;
    classDef ptr fill:#e2d9f3,stroke:#6f42c1,color:#111;
    class O1,O2,O3,O4 real;
    class G1,G2,G3,G4 ghost;
    class P ptr;
```

### Why this shape

| Property | Effect on proofs |
| --- | --- |
| A struct is a Lean `structure`. Reading a field is a projection. Writing is `{ s with f := v }` | `simp` computes read-after-write; no `Array.set!` |
| Arrays of different element types sit in different tables | writing a byte array cannot change a struct; framing between kinds is free |
| Pointers carry a path (`state.codes[i]`) instead of an ABI offset | `lencode` pointing into `codes[]` or into a static table is a value, not an address trick |
| A struct is one value | `memcpy` of a whole struct is a value copy; an embedded struct can be copied too |
| The initialised flag is a separate table | values have no `Option` wrapper, so the `Inv` clauses stay readable |

### What it costs

| Cost | Answer |
| --- | --- |
| Not ABI-faithful: a struct cannot be read as bytes | accepted (decision D6); the only default-build case is `(Bytef *)&stream.reserved`, never dereferenced |
| `sizeof(struct)` is needed for `ZALLOC` | recorded as a constant per struct, checked against the real compiler by a difftest |
| Pointer comparison across objects | model keeps `==` defined, relational operators across objects are a fault; `ub.patch` removes the one use |
| Alignment | each block carries a ghost alignment (section 4) |

The alternative models (tagged cells as before; per-field maps) are tested against it in the
pilot (section 6), because "simpler" is a claim to measure.

## 4. Memory operations: the semantics the runtime must give

The runtime is where a mistake costs the most, so each operation is a row to review.

| Operation | Result | Fault when |
| --- | --- | --- |
| `p + n` | pointer in the same object | result outside `0 .. size` (one past the end is allowed); `NULL + n` for `n ≠ 0` |
| `NULL + 0`, `NULL - NULL` | `NULL`, `0` | never (decision: allowed; C17 says undefined, C2y defines it) |
| `*p` read | value; for an uninitialised **integer** an arbitrary value (every theorem holds for all values); for an uninitialised **pointer**, a fault | null; freed; out of bounds; wrong type |
| `*p = v` write | updated heap, flag set | null; freed; out of bounds; read-only; wrong type |
| `memcpy(d, s, n)` | bytes copied, **flags copied** | null with `n > 0`; either range out of bounds; ranges overlap; destination read-only |
| `memset`, `zmemzero` | bytes set, flags set | like write |
| `malloc`/`zcalloc` | fresh block, flags clear (or set for `calloc`) | `items * size` wraps (the C wraps; the model reports it) |
| `free(p)` | block marked freed | not a block start; already freed |
| `p == q` | defined for all pointers | never |
| `p < q` | defined only inside one object | different objects |
| `(z_size_t)p & 7` | `(alignment(blk) + offset) % 8` | never |
| loop | runs body until the condition fails | fuel bound reached (`2^64` iterations) |

Two rows are subtle and wrong in the earlier attempt:

- **`memcpy` copies flags.** The C allows copying indeterminate bytes. The earlier model refused
  a copy of an uninitialised cell, which would block `deflateCopy` (`prev`). Reading garbage is not
  a fault either (D5): `slide_hash` reads all of `prev`.
- **Alignment is per block, not assumed.** The earlier model assumed every block starts at an
  8-byte boundary, which cannot hold for a caller's buffer. The `crc32_z` theorem must be stated
  for all alignments.

### Review checklist for the runtime

1. Every row above matches the C standard (C17, with the two documented relaxations).
2. Every `Fault.ub` the runtime raises corresponds to a real undefined behaviour, and every
   undefined behaviour zlib can reach corresponds to a fault.
3. The loop rule is sound: fuel exhaustion is a fault, never a silent exit.
4. A small set of programs is run both in the model and, compiled, in the real C under
   ASan and UBSan; results and faults agree.

## 5. Verification-condition generation (decision D2)

```mermaid
flowchart LR
    F["translated function<br/>in the C monad"] --> G["wp calculus<br/>one rule per primitive"]
    G --> V["verification conditions<br/>one per hazard and loop"]
    V --> S{"closed by"}
    S --> A1["omega"]
    S --> A2["grind"]
    S --> A3["named lemma"]
    S --> A4["simp with ghost lemmas"]

    classDef a fill:#e9ecef,stroke:#495057,color:#111;
    classDef b fill:#d4edda,stroke:#2e7d32,color:#111;
    class F,G,V a;
    class A1,A2,A3,A4 b;
```

Each runtime primitive (`load`, `store`, `memcpy`, `alloc`, `free`, `ptr+`, loops) gets one
weakest-precondition rule, proved once. A function's verification conditions are then
generated, not written.

Lean ships a generator for monadic `do` code (`mvcgen`). Current releases are moving it to a new
tactic (`vcgen`) and the migration has open issues. We pin the toolchain and decide in the pilot
between that tool and a small own `wp` tactic for our monad. The runtime rules are the same for
both, so the choice is reversible.

## 6. The pilot (milestone M1)

```mermaid
flowchart LR
    S["Pick 3 functions<br/>flush_pending<br/>updatewindow<br/>fill_window"] --> A["Candidate A<br/>tagged cell heap<br/>(earlier model)"]
    S --> B["Candidate B<br/>object heap"]
    S --> C["Candidate C<br/>per-field maps<br/>(only if A and B tie)"]
    A --> P["Prove the same statements:<br/>no fault, Inv preserved, frame"]
    B --> P
    C --> P
    P --> M["Measure<br/>proof lines, framework lines<br/>build time, peak memory<br/>heartbeat overrides"]
    M --> D{"clear winner?"}
    D -->|"yes"| R["Record decision D1 and D2"]
    D -->|"no, within 20%"| T["Pick the one closest to L2"]
    T --> R

    classDef a fill:#e9ecef,stroke:#495057,color:#111;
    classDef b fill:#cfe2ff,stroke:#1565c0,color:#111;
    classDef c fill:#fff3cd,stroke:#b8860b,color:#111;
    classDef d fill:#d4edda,stroke:#2e7d32,color:#111;
    class S,P,M a;
    class A b;
    class B,C c;
    class R,T d;
```

The three functions cover three shapes of memory access:

| Function | Shape |
| --- | --- |
| `flush_pending` with `putShortMSB` | struct fields plus a caller buffer plus `memcpy` |
| `updatewindow` | lazy allocation plus ring-buffer arithmetic plus copy from the caller's output |
| `fill_window` | a loop with a sliding copy, hash rewriting, and the in-bounds bound for later matches (F6) |

Pass criteria, written before the run so the result cannot be bent afterwards:

1. All three theorems (no fault, `Inv` preserved, frame) proved with no `sorry` and no
   heartbeat override.
2. The best candidate uses at most 5 proof lines per translated line, or is at least 2 times
   shorter than the worst candidate.
3. The statements read like the English description of the function.

## 7. Gates

```mermaid
flowchart LR
    PUSH["push or pull request"] --> B["lake build"]
    B --> AX["Check.lean<br/>axiom gate"]
    B --> FB["forbidden construct grep"]
    B --> PT["patches apply to pinned zlib"]
    B --> DT["difftest against real C<br/>from M2"]
    B --> MU["mutation checks<br/>from M3"]
    AX --> OK(("green"))
    FB --> OK
    PT --> OK
    DT --> OK
    MU --> OK

    classDef now fill:#d4edda,stroke:#2e7d32,color:#111;
    classDef soon fill:#fff3cd,stroke:#b8860b,color:#111;
    classDef res fill:#cfe2ff,stroke:#1565c0,color:#111;
    class B,AX,FB,PT now;
    class DT,MU soon;
    class OK res;
```

| Gate | What it catches |
| --- | --- |
| `lake build` | a proof that does not check |
| `Check.lean` | a theorem that uses `sorry`, `native_decide` or another axiom |
| forbidden grep | the same constructs written in the source |
| patch check | a patch that no longer applies to the pinned source |
| difftest | a translation that differs from the real C on sampled inputs (evidence, not proof) |
| mutation | a theorem that still checks after the translation is broken, so it constrains nothing |

Green means "checked by the kernel, within the trusted base of [trusted-base](trusted-base.md)
(created with the first code change)". It never means "the C is correct": only that the stated
theorems hold of the translation.

## 8. Milestones

```mermaid
flowchart LR
    M0["M0<br/>runtime, adler32"] --> M1["M1<br/>pilot"]
    M1 --> M2["M2<br/>runtime final<br/>crc32, zutil, difftest"]
    M2 --> M3["M3<br/>inflate side<br/>safety"]
    M2 --> M4["M4<br/>deflate side<br/>safety"]
    M3 --> M5["M5<br/>sequence safety<br/>and leak-freedom"]
    M4 --> M5
    M3 --> M6["M6<br/>inflate<br/>correctness"]
    M4 --> M7["M7<br/>deflate correctness<br/>and round trip"]
    M6 --> M7
    M5 --> M8["M8<br/>compress, uncompress<br/>infback"]
    M7 --> M8
    M8 --> M9["M9<br/>gz layer"]
    M9 --> M10["M10<br/>other configurations"]

    classDef done fill:#d4edda,stroke:#2e7d32,color:#111;
    classDef saf fill:#cfe2ff,stroke:#1565c0,color:#111;
    classDef cor fill:#fff3cd,stroke:#b8860b,color:#111;
    classDef rest fill:#e9ecef,stroke:#495057,color:#111;
    class M0 done;
    class M1,M2,M3,M4,M5 saf;
    class M6,M7 cor;
    class M8,M9,M10 rest;
```

Green is prepared, blue is safety, yellow is correctness of `inflate` and `deflate`, grey is the rest of the library and the other configurations.
