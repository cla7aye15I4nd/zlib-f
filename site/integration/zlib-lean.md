---
date: 2026-11-07
tags: [compression, verification, lean]
title: "zlib × Lean"
description: "An interactive essay: how zlib works, then how to verify it."
---

# zlib × Lean

How does a back-reference copy from bytes it has just produced? Why can a
compressed block fit in its buffer and still overwrite unread symbols along the way?

I put these questions into a standalone interactive essay. The first part builds
up zlib's compression and decoding algorithms. The second uses the same examples
to explain specifications, invariants, and the connection to actual execution.
The same site includes the complete public API contracts, detailed engine proof
guides, and the Lean source behind the arguments.

<a href="/zlib-f/" data-no-spa>Read zlib × Lean →</a>

The essay and its interactions live in the zlib-f project site. This post is only
an entry point. Full zlib verification is still in progress.
