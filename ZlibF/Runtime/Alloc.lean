import ZlibF.Runtime.Libc

/-!
# Runtime: allocation (moved)

`malloc`, `free` and the string literals model the C library, so they are in `Libc.lean` (with `memcpy`, `memset`,
`strlen`). This module only imports it, so that the modules that import `ZlibF.Runtime.Alloc` keep working.
-/
