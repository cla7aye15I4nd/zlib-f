# zlib API manual

[Documentation](../../README.md) / API manual

Start here to find a zlib function, understand its caller obligations, or follow a stream's
lifetime. Each entry gives the C signature, purpose, **Pre** (requirements), **Post**
(result), **Effects** (permitted changes), and edge cases that affect use.

## Choose a starting point

| If you want to… | Read |
| --- | --- |
| Understand the contract vocabulary and build scope | [How to read a contract](contracts.md) |
| Manage buffers, ownership, resets and stream call order | [Shared stream rules](streams.md) |
| Compress incrementally through `z_stream` | [Stream compression](deflate-stream.md) |
| Decompress incrementally through `z_stream` | [Stream decompression](inflate-stream.md) |
| Supply decompression input and receive output through callbacks | [Callback decompression](inflate-back.md) |
| Compress or decompress a whole buffer, or query the library | [Buffer utilities and library information](utility.md) |
| Compute or combine Adler-32 and CRC-32 checksums | [Checksums](checksums.md) |
| Read, write, position or close a gzip file handle | [Gzip files](gz-file.md) |

The manual follows the pinned source plus the listed patches, first for the default LP64
Linux static build and default allocator. Entries state their additional limits. The Windows
`gzopen_w` entry is separate from that build. These are focused documentary contracts;
some preconditions are narrower than the public header. Outside a stated Pre is outside that
contract, not automatically undefined C. See [scope deviations](../../deviations.md).

The behavior read from C is **to confirm** by implementation proof. This manual does not
report completed verification or change the broader [registered public goals](../../checking/goals.md).
[Overview](../../overview.md) is the single record of proof status and remaining work.

## Find a function

The following index links all 96 entries, grouped by how they are used. The function pages
retain C names, including trailing underscores supplied by initialization macros.

### Stream compression

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

### Stream decompression

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
| [inflateUndermine](inflate-stream.md#inflateundermine) | request distance-checking option; default build returns `Z_DATA_ERROR` |
| [inflateValidate](inflate-stream.md#inflatevalidate) | control wrapper integrity checks |
| [inflateMark](inflate-stream.md#inflatemark) | report where `inflate` is inside a block or code |
| [inflateCodesUsed](inflate-stream.md#inflatecodesused) | report the code table entries used by the current block (undocumented) |

### Callback decompression

| Function | One line |
| --- | --- |
| [inflateBackInit_](inflate-back.md#inflatebackinit_) | initialise for callback decompression |
| [inflateBack](inflate-back.md#inflateback) | decompress with input and output callbacks |
| [inflateBackEnd](inflate-back.md#inflatebackend) | free the stream |

### Whole-buffer operations and library information

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

### Checksums

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

### Gzip files

| Function | One line |
| --- | --- |
| [gzopen](gz-file.md#gzopen), [gzopen64](gz-file.md#gzopen64), [gzdopen](gz-file.md#gzdopen), [gzopen_w](gz-file.md#gzopen_w) | open a file |
| [gzbuffer](gz-file.md#gzbuffer), [gzsetparams](gz-file.md#gzsetparams) | buffer size, compression parameters |
| [gzread](gz-file.md#gzread), [gzfread](gz-file.md#gzfread), [gzgetc](gz-file.md#gzgetc), [gzgetc_](gz-file.md#gzgetc_), [gzungetc](gz-file.md#gzungetc), [gzgets](gz-file.md#gzgets) | read |
| [gzwrite](gz-file.md#gzwrite), [gzfwrite](gz-file.md#gzfwrite), [gzputc](gz-file.md#gzputc), [gzputs](gz-file.md#gzputs), [gzprintf](gz-file.md#gzprintf), [gzvprintf](gz-file.md#gzvprintf), [gzflush](gz-file.md#gzflush) | write |
| [gzrewind](gz-file.md#gzrewind), [gzseek](gz-file.md#gzseek), [gzseek64](gz-file.md#gzseek64), [gztell](gz-file.md#gztell), [gztell64](gz-file.md#gztell64), [gzoffset](gz-file.md#gzoffset), [gzoffset64](gz-file.md#gzoffset64) | position |
| [gzeof](gz-file.md#gzeof), [gzdirect](gz-file.md#gzdirect), [gzerror](gz-file.md#gzerror), [gzclearerr](gz-file.md#gzclearerr) | state |
| [gzclose](gz-file.md#gzclose), [gzclose_r](gz-file.md#gzclose_r), [gzclose_w](gz-file.md#gzclose_w) | close |

## Build variants and macros

Compared with the functions that `zlib.h` declares, these are not compiled into the default Linux
library:

| Name | Why |
| --- | --- |
| `gzopen_w` | declared only for Windows (`_WIN32`); the definition in `gzlib.c` is under the wide-character option |
| `deflateInit`, `deflateInit2`, `inflateInit`, `inflateInit2`, `inflateBackInit` | these are macros in `zlib.h`; they call `deflateInit_`, `deflateInit2_`, `inflateInit_`, `inflateInit2_`, `inflateBackInit_` with the header's own release string and `sizeof(z_stream)` |
| `gzgetc` as a macro | `zlib.h` also defines `gzgetc` as a macro that reads the buffer directly and calls `gzgetc_` when empty; the function `gzgetc` exists as well |

The index contains all 95 default-build entries and the separate Windows entry `gzopen_w`.
[Internal helper contracts](../internal-contracts.md) describe routines used inside the library.
