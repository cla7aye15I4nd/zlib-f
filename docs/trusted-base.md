# Trusted base

A theorem here is only as good as the following, which the kernel does not check.

1. **Lean kernel** and the three standard axioms `propext`, `Classical.choice`,
   `Quot.sound` (enforced by `Check.lean`).
2. **The runtime** (`ZlibF/Runtime/Core.lean`): heap, pointers, loops, and the rule
   that every undefined behaviour reachable in C becomes `Fault.ub`. Unsigned
   arithmetic is modular, signed arithmetic is checked. Loops run on a fuel
   bound of `2^64`; running out is a fault that the theorems rule out. A read of an
   uninitialised integer returns an arbitrary value (theorems hold for all values); a read of an
   uninitialised pointer is a fault ([safety.md](safety.md), section 3).
3. **The translation** (`ZlibF/Zlib/*.c.lean`) matches the C. It is written by hand,
   statement by statement. A mismatch is a translation bug, never fixed to ease
   a proof. Differential tests against the real C would be evidence, not proof;
   they are not part of this repository yet.
4. **The source** is `zlib/` at the pinned commit plus `patches/*.patch`. A
   patch exists only for a confirmed zlib bug that blocks a proof and matches an
   upstream pull request. Current: `0003-adler32-null-one.patch`
   ([madler/zlib#1364](https://github.com/madler/zlib/pull/1364)), which moves the
   `Z_NULL` check of `adler32_z` before the `len == 1` fast path.
5. **Memory model scope:** the target is LP64; allocation and typed objects are
   modelled only as far as translated functions need them.
6. **The statements.** The kernel checks that a proof proves its theorem. It does not check that
   the theorem says what [spec/](spec/index.md) says. Each theorem's docstring names the
   specification identifiers it formalises, and a reviewer reads statements, not proofs.
