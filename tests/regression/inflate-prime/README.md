# inflatePrime boundary regression

Evidence for the `inflatePrime` model boundary where `value.toNat` would map a
negative `int` to zero: both the C and the actual Lean translation mask a negative
`value` to its low bits. These paired drivers show that the two agree, byte for
byte, on exactly that boundary. Differential tests are evidence, not proof.

## What runs

* `prime.c` — the real patched zlib: `inflateInit2_(-15)`, real `inflatePrime`,
  `hold`/`bits` read from the real `struct inflate_state`, `inflateEnd`.
  LP64 widths: `int` value, `unsigned` bits, `unsigned long` hold.
* `prime.lean` — the actual translated `inflateInit2_`, `inflatePrime`,
  `inflateEnd` of `ZlibF/Zlib/inflate.c.lean`, on the runtime heap
  (`allocZStream`, the default allocator fields, `zlibVersion`, `castInflateState`
  /`ldInflateState`, `freeZStream`). No specification import; the prime call is
  never replaced by a formula. Any runtime fault prints `FAULT` and exits nonzero.
* `run.sh` — builds the C harness and imported translation modules, runs the Lean file with
  `lake env lean --run`, compares with strict `cmp`.

## Cases

Fresh stream per case, every `bits` in `-2, -1, 0..17` crossed with every `value`
in `INT_MIN, -65537, -2, -1, 0, 1, 65535, 65536, INT_MAX` (180 cases). The
baseline cell is `bits=1, value=-1`: it must return `Z_OK` with `hold=1`,
`bits=1`. This records the C behavior behind the separate model regression. Then one append
sequence: two `prime(16, -1)` calls (reaching `hold=4294967295`, `bits=32`), a
rejected extra bit, a zero-bit no-op, a negative-bit reset. Every call prints the
observed state; every stream is ended and released.

## Use

```sh
bash tests/regression/inflate-prime/run.sh            # normal
SAN=1 bash tests/regression/inflate-prime/run.sh      # ASan/UBSan/LSan (SAN requires
                                                      # a sanitized ZLIB_BUILD)
ZLIB_BUILD=<dir> bash tests/regression/inflate-prime/run.sh
```

Artifacts go to `tests/build/inflate-prime/` (git-ignored). Exit 0 identical,
1 difference or fault, 2 setup error.

The drivers compare actual executions. They do not import or validate the API model.
The separate model witness must reject the old negative-value clause.
