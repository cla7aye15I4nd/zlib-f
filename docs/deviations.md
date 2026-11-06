# Scope and representation limits

This file records limits of the public API model and its concrete adapters. It does not make
an incomplete entry-point refinement a completed proof. Remaining review work is in
[overview.md](overview.md).

| Area | Limit | Consequence |
| --- | --- | --- |
| Initial target | Default x86_64 Linux, LP64, static build, default allocator | Other configurations and custom allocator implementations are outside the current target. Allocation failure of the default allocator remains in scope. |
| Compressor scalar pointer | `Concrete.compress2_z` and `Concrete.compress2` represent the length cell by an optional value and a returned value | Aliasing this cell with input or output memory is not represented. The adapters cannot yet justify a theorem for those calls if the public C API permits them. The null-cell cases remain distinct for `_z` and the compatibility wrapper. |
| Compressor data model | `Compress2` is a data-only relation with a coarse rejection flag | Use `Compress2Z` and `Compress2Wrapper` for null shapes, error ordering and stored-length effects. A theorem about `Compress2` alone is not an entry-point refinement. |
| Concrete bound goal | Both lengths are 64 bits on LP64 | `Goal.compress_bound_value` covers every `UInt64` argument without a smaller numeric precondition. Other ABIs need their own size conversion statements. |
| Deflate dictionary model | The zlib branch of `DeflSetDict` describes the documented ordering before compression and rejects a call after `started` | The actual C can accept a dictionary after stream end. No operational refinement theorem may use this rejection outside the documented ordering. The model theorem `deflate_valid` is not a theorem about those C executions. |

| Utility scalar cells | The counted decompression contracts keep length cells separate from input, output and each other | Aliasing is outside these draft adapters. It must be resolved before claiming the full pointer domain permitted by C. The early and late memory-failure scalar results remain separate. |
| Callback footprint | The draft callback protocol currently separates the window allocation from callback-owned objects | Caller descriptors sharing another slice of that allocation need a range-based frame before the complete callback domain can be claimed. Callback allocation and freeing of other owned objects are allowed. |
| Formatted gz output | The external formatter represents integer, character and string arguments | Floating-point, pointer and write-count conversions need an external-world model extension and review. The draft contracts explicitly require a represented, valid formatting result. |
