# Patches

The verified source is the pinned `zlib/` submodule with these patches applied in name order.
`zlib/` itself is never modified. A patch exists only for a confirmed zlib bug that blocks a
proof, is minimal, and matches an upstream pull request. Delete it when upstream merges the fix
and the pin moves past it.

| Patch | Fixes | Upstream |
| --- | --- | --- |
| `0003-adler32-null-one.patch` | `adler32_z` reads `buf[0]` for `len == 1` before the documented check for a null `buf`. The patch checks for null at function entry | [madler/zlib#1364](https://github.com/madler/zlib/pull/1364) |
