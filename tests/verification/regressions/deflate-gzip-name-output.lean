import ZlibF.Spec.Public.History

open C ZlibF.Spec.Public

/-! `ActiveHeader` did not separate the gzip header name from the bytes a `deflate` call
writes. With the name in the caller's output buffer (one 1024-byte block, the NUL at index 505,
`avail_out = 1024`), the real C reads past the buffer
(`tests/regression/deflate-gzip-name-output/output.c`). The old clauses asked only that the name
be a C string. The new clause `DeflateHeaderApart` asks that the name range (through its NUL) be
separate from the output range; this layout is not. -/
namespace DeflateGzipNameOutputRegression

/-- The name (506 bytes with its NUL) and the output range (1024 bytes) of the reproduction
start at the same byte of the same block, so they are not separate. -/
theorem layout_excluded :
    ¬ Separate (.ref (.blk 7) 0) (505 + 1) (.ref (.blk 7) 0) 1024 := by
  simp [Separate]

end DeflateGzipNameOutputRegression
