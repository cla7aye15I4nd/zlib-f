# Statement test: `Goal.inflate_refusal` and `Goal.deflate_refusal`

`run.sh` builds the pinned zlib with its patches under AddressSanitizer and
UndefinedBehaviorSanitizer (LeakSanitizer as well on Linux) and runs `harness.c`. It hands every
refused stream of the goals' domain to every function of each family:
- a `NULL` stream;
- a record with no state: zeroed, after `End`, after a failed init, and the destination of a failed
  copy;
- a record with a null `zalloc` or a null `zfree` and a live state;
- a struct copy of a live record, whose state points back to the original.

Inflate side: `inflate` with every flush, `inflateEnd`, `inflateReset`, `inflateReset2`,
`inflateGetDictionary`, `inflateSetDictionary` and `inflateCopy` from the refused source.
Deflate side: `deflate` with every flush, `deflateSetDictionary`, `deflateParams`,
`deflateGetDictionary`, `deflateEnd`, `deflateReset` and `deflateCopy`. Each call must return
`Z_STREAM_ERROR`, allocate nothing, and leave the record unchanged. A copy must leave its source
unchanged and change only `dest->state`, to `NULL`.

Result on 2026-11-13: 192 calls, no violation and no sanitizer report. This is evidence, not
proof. A never-initialised record whose state field holds a garbage pointer is not tested: the
check reads through that pointer, which is undefined behaviour (`docs/deviations.md`).
