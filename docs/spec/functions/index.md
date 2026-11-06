# Function contracts

Each entry has its C signature, purpose, **Pre**, **Post**, **Effects** and essential edge cases.
[Contract conventions](../contracts.md) define **restricted domain** and **full type domain**, independently of pure, read-only and stateful effects.

These are focused contracts, not exhaustive API or proof-completion claims. A narrower Pre does not change registered goals or make excluded calls undefined. See [deviations](../../deviations.md), [public goals](../public-goals.md) and [remaining work](../../overview.md).

## Pages

| Page | Source files | What is in it |
| --- | --- | --- |
| [deflate-stream.md](deflate-stream.md) | `deflate.c` | compression through a `z_stream` |
| [inflate-stream.md](inflate-stream.md) | `inflate.c` | decompression through a `z_stream` |
| [inflate-back.md](inflate-back.md) | `infback.c` | decompression with callbacks, no output window copy |
| [utility.md](utility.md) | `compress.c`, `uncompr.c`, `zutil.c` | one-call compress and uncompress, release string, flags, error text |
| [checksums.md](checksums.md) | `adler32.c`, `crc32.c` | Adler-32 and CRC-32 |
| [gz-file.md](gz-file.md) | `gzlib.c`, `gzread.c`, `gzwrite.c`, `gzclose.c` | the gzip file API |

## deflate-stream.md

| Function | One line |
| --- | --- |
| [deflateInit_](deflate-stream.md#deflateinit_) | initialise with default window, memory level and strategy |
| [deflateInit2_](deflate-stream.md#deflateinit2_) | initialise with all parameters |
| [deflateSetDictionary](deflate-stream.md#deflatesetdictionary) | preload a dictionary |
| [deflateGetDictionary](deflate-stream.md#deflategetdictionary) | copy out the current dictionary window |
| [deflateResetKeep](deflate-stream.md#deflateresetkeep) | restart a stream but keep the window and hash (undocumented) |
| [deflateReset](deflate-stream.md#deflatereset) | restart a stream |
| [deflateSetHeader](deflate-stream.md#deflatesetheader) | give the gzip header to write |
| [deflatePending](deflate-stream.md#deflatepending) | report pending output |
| [deflateUsed](deflate-stream.md#deflateused) | report the bits used in the last byte of the last flush |
| [deflatePrime](deflate-stream.md#deflateprime) | insert bits into the output |
| [deflateParams](deflate-stream.md#deflateparams) | change level and strategy |
| [deflateTune](deflate-stream.md#deflatetune) | set the internal match-search tuning values |
| [deflateBound_z](deflate-stream.md#deflatebound_z) | upper bound on the compressed size (size type) |
| [deflateBound](deflate-stream.md#deflatebound) | upper bound on the compressed size (`uLong`) |
| [deflate](deflate-stream.md#deflate) | compress |
| [deflateEnd](deflate-stream.md#deflateend) | free the stream |
| [deflateCopy](deflate-stream.md#deflatecopy) | duplicate a stream |

## inflate-stream.md

| Function | One line |
| --- | --- |
| [inflateResetKeep](inflate-stream.md#inflateresetkeep) | restart a stream and keep the window contents (undocumented) |
| [inflateReset](inflate-stream.md#inflatereset) | restart a stream, drop the window contents |
| [inflateReset2](inflate-stream.md#inflatereset2) | restart a stream with a new window size |
| [inflateInit2_](inflate-stream.md#inflateinit2_) | initialise with a window size |
| [inflateInit_](inflate-stream.md#inflateinit_) | initialise with the default window size |
| [inflatePrime](inflate-stream.md#inflateprime) | insert bits into the input |
| [inflate](inflate-stream.md#inflate) | decompress |
| [inflateEnd](inflate-stream.md#inflateend) | free the stream |
| [inflateGetDictionary](inflate-stream.md#inflategetdictionary) | copy out the window |
| [inflateSetDictionary](inflate-stream.md#inflatesetdictionary) | give the dictionary |
| [inflateGetHeader](inflate-stream.md#inflategetheader) | ask for the gzip header |
| [inflateSync](inflate-stream.md#inflatesync) | search for a full flush point |
| [inflateSyncPoint](inflate-stream.md#inflatesyncpoint) | test whether stopped at a sync flush point |
| [inflateCopy](inflate-stream.md#inflatecopy) | duplicate a stream |
| [inflateUndermine](inflate-stream.md#inflateundermine) | test aid: no effect in the default build, returns `Z_DATA_ERROR` |
| [inflateValidate](inflate-stream.md#inflatevalidate) | turn the check value on or off |
| [inflateMark](inflate-stream.md#inflatemark) | report where `inflate` is inside a block or code |
| [inflateCodesUsed](inflate-stream.md#inflatecodesused) | report the code table entries used by the current block (undocumented) |

## inflate-back.md

| Function | One line |
| --- | --- |
| [inflateBackInit_](inflate-back.md#inflatebackinit_) | initialise for callback decompression |
| [inflateBack](inflate-back.md#inflateback) | decompress with input and output callbacks |
| [inflateBackEnd](inflate-back.md#inflatebackend) | free the stream |

## utility.md

| Function | One line |
| --- | --- |
| [compress2_z](utility.md#compress2_z) | compress a buffer at a level (size type) |
| [compress2](utility.md#compress2) | compress a buffer at a level |
| [compress_z](utility.md#compress_z) | compress a buffer at the default level (size type) |
| [compress](utility.md#compress) | compress a buffer at the default level |
| [compressBound_z](utility.md#compressbound_z) | bound on the compressed size (size type) |
| [compressBound](utility.md#compressbound) | bound on the compressed size |
| [uncompress2_z](utility.md#uncompress2_z) | decompress a buffer, report input used (size type) |
| [uncompress2](utility.md#uncompress2) | decompress a buffer, report input used |
| [uncompress_z](utility.md#uncompress_z) | decompress a buffer (size type) |
| [uncompress](utility.md#uncompress) | decompress a buffer |
| [zlibVersion](utility.md#zlibversion) | the release string of the library |
| [zlibCompileFlags](utility.md#zlibcompileflags) | the type sizes and options the library was built with |
| [zError](utility.md#zerror) | text for a return code |

## checksums.md

| Function | One line |
| --- | --- |
| [adler32_z](checksums.md#adler32_z) | Adler-32 of a buffer (size type) |
| [adler32](checksums.md#adler32) | Adler-32 of a buffer |
| [adler32_combine](checksums.md#adler32_combine) | combine two Adler-32 values |
| [adler32_combine64](checksums.md#adler32_combine64) | combine two Adler-32 values (64-bit length) |
| [get_crc_table](checksums.md#get_crc_table) | the CRC-32 table |
| [crc32_z](checksums.md#crc32_z) | CRC-32 of a buffer (size type) |
| [crc32](checksums.md#crc32) | CRC-32 of a buffer |
| [crc32_combine_gen64](checksums.md#crc32_combine_gen64) | operator for combining (64-bit length) |
| [crc32_combine_gen](checksums.md#crc32_combine_gen) | operator for combining |
| [crc32_combine_op](checksums.md#crc32_combine_op) | combine with an operator |
| [crc32_combine64](checksums.md#crc32_combine64) | combine two CRC-32 values (64-bit length) |
| [crc32_combine](checksums.md#crc32_combine) | combine two CRC-32 values |

## gz-file.md

| Function | One line |
| --- | --- |
| [gzopen](gz-file.md#gzopen), [gzopen64](gz-file.md#gzopen64), [gzdopen](gz-file.md#gzdopen), [gzopen_w](gz-file.md#gzopen_w) | open a file |
| [gzbuffer](gz-file.md#gzbuffer), [gzsetparams](gz-file.md#gzsetparams) | buffer size, compression parameters |
| [gzread](gz-file.md#gzread), [gzfread](gz-file.md#gzfread), [gzgetc](gz-file.md#gzgetc), [gzgetc_](gz-file.md#gzgetc_), [gzungetc](gz-file.md#gzungetc), [gzgets](gz-file.md#gzgets) | read |
| [gzwrite](gz-file.md#gzwrite), [gzfwrite](gz-file.md#gzfwrite), [gzputc](gz-file.md#gzputc), [gzputs](gz-file.md#gzputs), [gzprintf](gz-file.md#gzprintf), [gzvprintf](gz-file.md#gzvprintf), [gzflush](gz-file.md#gzflush) | write |
| [gzrewind](gz-file.md#gzrewind), [gzseek](gz-file.md#gzseek), [gzseek64](gz-file.md#gzseek64), [gztell](gz-file.md#gztell), [gztell64](gz-file.md#gztell64), [gzoffset](gz-file.md#gzoffset), [gzoffset64](gz-file.md#gzoffset64) | position |
| [gzeof](gz-file.md#gzeof), [gzdirect](gz-file.md#gzdirect), [gzerror](gz-file.md#gzerror), [gzclearerr](gz-file.md#gzclearerr) | state |
| [gzclose](gz-file.md#gzclose), [gzclose_r](gz-file.md#gzclose_r), [gzclose_w](gz-file.md#gzclose_w) | close |

## Not compiled, or not functions

Compared with the functions that `zlib.h` declares, these are not compiled into the default Linux
library:

| Name | Why |
| --- | --- |
| `gzopen_w` | declared only for Windows (`_WIN32`); the definition in `gzlib.c` is under the wide-character option |
| `deflateInit`, `deflateInit2`, `inflateInit`, `inflateInit2`, `inflateBackInit` | these are macros in `zlib.h`; they call `deflateInit_`, `deflateInit2_`, `inflateInit_`, `inflateInit2_`, `inflateBackInit_` with the header's own release string and `sizeof(z_stream)` |
| `gzgetc` as a macro | `zlib.h` also defines `gzgetc` as a macro that reads the buffer directly and calls `gzgetc_` when empty; the function `gzgetc` exists as well |

Internal helpers are described in [internal.md](../internal.md). All 95 default-build entries are indexed above; `gzopen_w` is the separate Windows entry.
