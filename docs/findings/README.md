# Confirmed source issues and reproductions

[Evidence register](../findings.md) · [Current work](../overview.md)

## Adler-32 null buffer with a one-byte length

The existing [patch register](../../patches/README.md) records this confirmed issue and
its submitted upstream fix. In the unpatched pin, `adler32_z` tests `len == 1` and reads
`buf[0]` before testing for a null buffer. The documented null-buffer call should return 1.
The verified build moves the null check before that read.

Minimal reproduction:

```c
#include "zlib.h"

int main(void) {
    return adler32_z(0, Z_NULL, 1) == 1 ? 0 : 1;
}
```

Build the pinned library and this program with address and undefined-behaviour sanitizers,
then link against that build's static library. Run once without the patch and once with it.
The expected distinction is a null read in the former and return code zero in the latter.
These are reproduction instructions, not a report of a sanitizer run during this documentation edit.

**Confidence:** confirmed in the retained patch record. **Scope:** null `buf` with `len == 1`
in the pinned unpatched `adler32_z`, including callers reaching that branch. This is not a claim
about every later upstream revision. The patch remains until the pin incorporates the fix.

Other historical reports and their evidence limits are in the [evidence register](../findings.md).
They do not become confirmed issues merely by appearing there.
