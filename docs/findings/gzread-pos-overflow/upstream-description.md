# Upstream pull request draft: gz position overflow

For the owner to submit. One pull request covers both sides
([gzread-pos-overflow](README.md), [gzwrite-pos-overflow](../gzwrite-pos-overflow/README.md));
the diff is [0004-gz-position-overflow.patch](../../../patches/0004-gz-position-overflow.patch).
Nothing has been sent.

---

**Title:** gzread/gzwrite: do not let the uncompressed position overflow z_off64_t

**Problem**

`state->x.pos` (signed `z_off64_t`) is advanced by every byte delivered or accepted, with no
bound. `gzseek` only checks that its own target fits, so it can leave `x.pos` at or near
`GZ_OFF_MAX`, and the next read or write overflows a signed integer.

Read side, on Linux: `lseek` on `/dev/zero` succeeds without moving, so after a transparent
`gzread` a `gzseek(f, INT64_MAX, SEEK_SET)` takes the COPY path and sets `x.pos = INT64_MAX`.
The next `gzread` overflows in `gz_read` (`state->x.pos += n`). With a seek to `INT64_MAX - 4`,
the overflow happens in the `gzgetc()` macro in the application, because `gz_fetch` filled the
whole output buffer although only four more bytes have a representable position.

Write side: a transparent writer on `/dev/null`, `gzseek(f, INT64_MAX - 10, SEEK_SET)`, then
`gzwrite(f, buf, 100)`: `gz_zero` writes the zeros up to `INT64_MAX - 10`, then the copy
overflows `x.pos` (`state->x.pos += copy` in `gz_write`). `gzputc` at `INT64_MAX` overflows in
its fast path. The zero fill takes about 17 minutes on x86_64 Linux.

**Reproduction**

```c
int fd = open("/dev/zero", O_RDONLY);
gzFile f = gzdopen(fd, "r");
char buf[16];
gzread(f, buf, 1);
gzseek(f, INT64_MAX, SEEK_SET);
gzread(f, buf, sizeof buf);   /* gzread.c: signed integer overflow: 9223372036854775807 + 16 */
```

```c
int fd = open("/dev/null", O_WRONLY);
gzFile f = gzdopen(fd, "wT");
char buf[100] = {0};
gzbuffer(f, 1u << 29);
gzseek(f, INT64_MAX - 10, SEEK_SET);
gzwrite(f, buf, sizeof buf);  /* gzwrite.c: signed integer overflow: 9223372036854775797 + 100 */
```

Built with `-fsanitize=undefined`, x86_64 Linux, gcc 15.2.

**Fix**

Reading: a helper `gz_room()` gives how many more bytes can be delivered without passing
`GZ_OFF_MAX`. `gz_fetch` fills at most that many (at least one, so that end of file is still
detected), which keeps `x.pos + x.have <= GZ_OFF_MAX` and so keeps the `gzgetc()` macro defined.
`gz_read` and `gzgets` deliver at most that many; data that cannot be delivered is discarded
with `Z_DATA_ERROR` "position overflow". Writing: `gz_write`, `gzputc` (fast path) and
`gzprintf` refuse with `Z_DATA_ERROR` "position overflow" a write that would carry `x.pos` past
`GZ_OFF_MAX`. Positions below `GZ_OFF_MAX - 2 * size` behave exactly as before; at the limit, end
of file is reported as before.

**Testing**

- `make test`, default and with `-fsanitize=address,undefined`: passes.
- The two histories above, and `gzputc` at `INT64_MAX`, before and after, under ASan and UBSan:
  the reports are gone; the calls return an error with "position overflow".
- About 30 000 random gz call histories with fault injection (failing and short `read`/`write`,
  failing `lseek`, `malloc`, `close`), half of them with a device-like `lseek`, under ASan and
  UBSan on macOS and x86_64 Linux (with LeakSanitizer): no report, no leak, no hang.
