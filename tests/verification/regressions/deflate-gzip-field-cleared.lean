import ZlibF.Spec.Public.History

open C ZlibF.Spec.Public

/-! `DeflateHeaderProgress` said nothing about a field of the caller's `gz_header` that is `NULL`
in the state that writes it. A caller that sets `extra` to `NULL` while `deflate` is inside the
extra field (`EXTRA_STATE`, `gzindex = 500`) makes the next call skip the field without resetting
`gzindex`, and the name loop reads from `name[500]`, past a three-byte name
(`tests/regression/deflate-history-domain/clear.c`). The clause now asks `gzindex = 0` for a
`NULL` field in `EXTRA_STATE`, `NAME_STATE` and `COMMENT_STATE`; this state does not meet it. -/
namespace DeflateGzipFieldClearedRegression

theorem cleared_excluded : ¬ ((500 : UInt64) = 0) := by decide

end DeflateGzipFieldClearedRegression
