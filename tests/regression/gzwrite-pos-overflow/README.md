# gzwrite position overflow after a forward seek

Finding: [docs/findings/gzwrite-pos-overflow](../../../docs/findings/gzwrite-pos-overflow/README.md).

`wpos.c` opens `/dev/null` with `gzdopen(fd, "wT")` (transparent writer), sets a 2^29-byte
buffer, seeks to `INT64_MAX - 10` and writes 100 bytes. With the argument `putc` it seeks to
`INT64_MAX` and writes one byte with `gzputc`. Each run first writes the zeros of the pending
seek: 2^34 writes of 2^29 bytes.

`run.sh` builds the pinned source twice: with `patches/*.patch` except 0004, and with all of them.
Before 0004 both runs must report a signed overflow of the position (`gz_write`, `gzputc`); with
0004 nothing may be reported, and the write fails with `Z_DATA_ERROR` "position overflow".
By default the program is linked with `fastwrite.c`, a `write()` that accepts every byte for the
`/dev/null` descriptor without a system call: about a minute per run. `FULL=1` uses the real
`/dev/null`: about 17 minutes per run on x86_64 Linux. Both modes build with UBSan only; under
ASan the 2^34 intercepted writes take hours (a run with ASan was stopped after more than an hour).

`report.txt` is the raw output of runs on x86_64 Linux (kernel 7.0, gcc 15.2): the default mode,
and the real `/dev/null`.
