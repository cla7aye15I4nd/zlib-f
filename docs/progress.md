# Proof target evidence

<!-- proof-link-revision: 87f98689ee25635b430144ee2826922cfc10ec2b -->

[All-target graph and current work](overview.md#proof-progress-graph) · [Input configurations](input-configurations.md)

This index contains **181 fixed targets**: public execution,
sequence and initialization targets, internal obligations and abstract models.
There is one status graph, in overview. A model result is not implementation refinement.
Input coverage and proof registration are separate. An exact local proof can
cover its complete stated domain while still awaiting registration and CI.
Internal premises remain part of the statement; green does not remove them.
A source-only candidate never grants coverage. Disallowed axioms stop generation.

Why can an isolated node be unfinished? Its proof dependencies have not been
established. Missing arrows neither prove independence nor supply a proof plan.
Some Markdown viewers disable diagram links; use these ordinary source links.

## Status key

<a id="status-registered"></a>Registered proof: an exact checked theorem is listed.
<a id="status-local"></a>Locally checked: an exact theorem exists but is not listed.
<a id="status-open"></a>Not proved: no exact theorem covers this target.
<a id="status-blocked"></a>Blocked: a documented obstacle applies to the target.
These labels do not assign input coverage or replace named-commit CI acceptance.

<a id="group-queries"></a>

## Library queries

| Target statement | Coverage / evidence state | Contract / input range | Proof evidence | Reviewed next work |
| --- | --- | --- | --- | --- |
| <a id="target-zlibf-spec-public-goal-compressbound"></a>[compressBound](../ZlibF/Spec/Public/Queries.lean#L35) | All stated inputs / Registered proof | [Contract](../docs/api/utility.md#compressbound); [input range](input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.Proofs.compressBound](../ZlibF/Proof/public-compress-bound.lean#L49) | — |
| <a id="target-zlibf-spec-public-goal-compressbound-z"></a>[compressBound_z](../ZlibF/Spec/Public/Queries.lean#L40) | All stated inputs / Registered proof | [Contract](../docs/api/utility.md#compressbound_z); [input range](input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.Proofs.compressBound_z](../ZlibF/Proof/public-compress-bound.lean#L46) | — |
| <a id="target-zlibf-spec-public-goal-zlibversion"></a>[zlibVersion](../ZlibF/Spec/Public/Queries.lean#L46) | All stated inputs / Registered proof | [Contract](../docs/api/utility.md#zlibversion); [input range](input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.Proofs.zlibVersion](../ZlibF/Proof/public-zlib-version.lean#L8) | — |
| <a id="target-zlibf-spec-public-goal-zlibcompileflags"></a>[zlibCompileFlags](../ZlibF/Spec/Public/Queries.lean#L53) | All stated inputs / Registered proof | [Contract](../docs/api/utility.md#zlibcompileflags); [input range](input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.Proofs.zlibCompileFlags](../ZlibF/Proof/public-zlib-compile-flags.lean#L6) | — |
| <a id="target-zlibf-spec-public-goal-zerror"></a>[zError](../ZlibF/Spec/Public/Queries.lean#L59) | All stated inputs / Registered proof | [Contract](../docs/api/utility.md#zerror); [input range](input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.Proofs.zError](../ZlibF/Proof/public-zerror.lean#L37) | — |
| <a id="target-zlibf-spec-public-goal-get-crc-table"></a>[get_crc_table](../ZlibF/Spec/Public/Checksums.lean#L126) | All stated inputs / Registered proof | [Contract](../docs/api/checksums.md#get_crc_table); [input range](input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.Proofs.get_crc_table](../ZlibF/Proof/public-get-crc-table.lean#L13) | — |

<a id="group-checksums"></a>

## Checksums

| Target statement | Coverage / evidence state | Contract / input range | Proof evidence | Reviewed next work |
| --- | --- | --- | --- | --- |
| <a id="target-zlibf-spec-public-goal-adler32"></a>[adler32](../ZlibF/Spec/Public/Checksums.lean#L66) | All stated inputs / Registered proof | [Contract](../docs/api/checksums.md#adler32); [input range](input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.AdlerUpdateProof.adler_public](../ZlibF/Proof/public-adler-update.lean#L46) | — |
| <a id="target-zlibf-spec-public-goal-adler32-z"></a>[adler32_z](../ZlibF/Spec/Public/Checksums.lean#L61) | All stated inputs / Registered proof | [Contract](../docs/api/checksums.md#adler32_z); [input range](input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.AdlerUpdateProof.adler_z_public](../ZlibF/Proof/public-adler-update.lean#L36) | — |
| <a id="target-zlibf-spec-public-goal-adler32-combine"></a>[adler32_combine](../ZlibF/Spec/Public/Checksums.lean#L86) | All stated inputs / Registered proof | [Contract](../docs/api/checksums.md#adler32_combine); [input range](input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.AdlerCombineProof.combine_public](../ZlibF/Proof/public-adler-combine.lean#L118) | — |
| <a id="target-zlibf-spec-public-goal-adler32-combine64"></a>[adler32_combine64](../ZlibF/Spec/Public/Checksums.lean#L90) | All stated inputs / Registered proof | [Contract](../docs/api/checksums.md#adler32_combine64); [input range](input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.AdlerCombineProof.combine64_public](../ZlibF/Proof/public-adler-combine.lean#L121) | — |
| <a id="target-zlibf-spec-public-goal-crc32"></a>[crc32](../ZlibF/Spec/Public/Checksums.lean#L117) | All stated inputs / Registered proof | [Contract](../docs/api/checksums.md#crc32); [input range](input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.Proofs.crc32](../ZlibF/Proof/public-crc-updates.lean#L28) | — |
| <a id="target-zlibf-spec-public-goal-crc32-z"></a>[crc32_z](../ZlibF/Spec/Public/Checksums.lean#L109) | All stated inputs / Registered proof | [Contract](../docs/api/checksums.md#crc32_z); [input range](input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.Proofs.crc32_z](../ZlibF/Proof/public-crc-updates.lean#L18) | — |
| <a id="target-zlibf-spec-public-goal-crc32-combine-gen"></a>[crc32_combine_gen](../ZlibF/Spec/Public/Checksums.lean#L140) | All stated inputs / Registered proof | [Contract](../docs/api/checksums.md#crc32_combine_gen); [input range](input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.CrcCombineProof.gen](../ZlibF/Proof/public-crc-combine.lean#L76) | — |
| <a id="target-zlibf-spec-public-goal-crc32-combine-gen64"></a>[crc32_combine_gen64](../ZlibF/Spec/Public/Checksums.lean#L143) | All stated inputs / Registered proof | [Contract](../docs/api/checksums.md#crc32_combine_gen64); [input range](input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.CrcCombineProof.gen64](../ZlibF/Proof/public-crc-combine.lean#L82) | — |
| <a id="target-zlibf-spec-public-goal-crc32-combine-op"></a>[crc32_combine_op](../ZlibF/Spec/Public/Checksums.lean#L150) | All stated inputs / Registered proof | [Contract](../docs/api/checksums.md#crc32_combine_op); [input range](input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.CrcCombineProof.op](../ZlibF/Proof/public-crc-combine.lean#L88) | — |
| <a id="target-zlibf-spec-public-goal-crc32-combine"></a>[crc32_combine](../ZlibF/Spec/Public/Checksums.lean#L162) | All stated inputs / Registered proof | [Contract](../docs/api/checksums.md#crc32_combine); [input range](input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.CrcCombineProof.combine](../ZlibF/Proof/public-crc-combine.lean#L94) | — |
| <a id="target-zlibf-spec-public-goal-crc32-combine64"></a>[crc32_combine64](../ZlibF/Spec/Public/Checksums.lean#L165) | All stated inputs / Registered proof | [Contract](../docs/api/checksums.md#crc32_combine64); [input range](input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.CrcCombineProof.combine64](../ZlibF/Proof/public-crc-combine.lean#L100) | — |

<a id="group-addresses"></a>

## Byte-address model

| Target statement | Coverage / evidence state | Contract / input range | Proof evidence | Reviewed next work |
| --- | --- | --- | --- | --- |
| <a id="target-c-byteaddress-spec-goal-address-read-is-pure"></a>[address_read_is_pure](../ZlibF/Spec/ByteAddress.lean#L39) | All stated inputs / Registered proof | Exact target statement; [input range](input-configurations.md#entry-inputs) | [C.ByteAddress.Proofs.address_read_is_pure](../ZlibF/Proof/ByteAddress.lean#L28) | — |
| <a id="target-c-byteaddress-spec-goal-raw-block-unchanged"></a>[raw_block_unchanged](../ZlibF/Spec/ByteAddress.lean#L43) | All stated inputs / Registered proof | Exact target statement; [input range](input-configurations.md#entry-inputs) | [C.ByteAddress.Proofs.raw_block_unchanged](../ZlibF/Proof/ByteAddress.lean#L33) | — |
| <a id="target-c-byteaddress-spec-goal-every-layout-is-representable"></a>[every_layout_is_representable](../ZlibF/Spec/ByteAddress.lean#L50) | All stated inputs / Registered proof | Exact target statement; [input range](input-configurations.md#entry-inputs) | [C.ByteAddress.Proofs.every_layout_is_representable](../ZlibF/Proof/ByteAddress.lean#L39) | — |
| <a id="target-c-byteaddress-spec-goal-every-existing-heap-accepts-layout"></a>[every_existing_heap_accepts_layout](../ZlibF/Spec/ByteAddress.lean#L57) | All stated inputs / Registered proof | Exact target statement; [input range](input-configurations.md#entry-inputs) | [C.ByteAddress.Proofs.every_existing_heap_accepts_layout](../ZlibF/Proof/ByteAddress.lean#L94) | — |
| <a id="target-c-byteaddress-spec-goal-mask-refines-base-plus-offset"></a>[mask_refines_base_plus_offset](../ZlibF/Spec/ByteAddress.lean#L65) | All stated inputs / Registered proof | Exact target statement; [input range](input-configurations.md#entry-inputs) | [C.ByteAddress.Proofs.mask_refines_base_plus_offset](../ZlibF/Proof/ByteAddress.lean#L54) | — |
| <a id="target-c-byteaddress-spec-goal-pointer-advance-preserves-low-bits"></a>[pointer_advance_preserves_low_bits](../ZlibF/Spec/ByteAddress.lean#L70) | All stated inputs / Registered proof | Exact target statement; [input range](input-configurations.md#entry-inputs) | [C.ByteAddress.Proofs.pointer_advance_preserves_low_bits](../ZlibF/Proof/ByteAddress.lean#L60) | — |
| <a id="target-c-byteaddress-spec-goal-first-aligned-offset"></a>[first_aligned_offset](../ZlibF/Spec/ByteAddress.lean#L77) | All stated inputs / Registered proof | Exact target statement; [input range](input-configurations.md#entry-inputs) | [C.ByteAddress.Proofs.first_aligned_offset](../ZlibF/Proof/ByteAddress.lean#L67) | — |
| <a id="target-c-byteaddress-spec-goal-byte-stores-preserve-bases"></a>[byte_stores_preserve_bases](../ZlibF/Spec/ByteAddress.lean#L83) | All stated inputs / Registered proof | Exact target statement; [input range](input-configurations.md#entry-inputs) | [C.ByteAddress.Proofs.byte_stores_preserve_bases](../ZlibF/Proof/ByteAddress.lean#L81) | — |
| <a id="target-c-byteaddress-spec-goal-byte-modifies-preserve-bases"></a>[byte_modifies_preserve_bases](../ZlibF/Spec/ByteAddress.lean#L87) | All stated inputs / Registered proof | Exact target statement; [input range](input-configurations.md#entry-inputs) | [C.ByteAddress.Proofs.byte_modifies_preserve_bases](../ZlibF/Proof/ByteAddress.lean#L88) | — |

<a id="group-inflate"></a>

## Inflate streams

| Target statement | Coverage / evidence state | Contract / input range | Proof evidence | Reviewed next work |
| --- | --- | --- | --- | --- |
| <a id="target-zlibf-spec-public-goal-inflatecopy"></a>[inflateCopy](../ZlibF/Spec/Public/Copy.lean#L27) | Not proved / Not proved | [Contract](../docs/api/inflate-stream.md#inflatecopy); [input range](input-configurations.md#inflate-inputs) | — | [Start: copy and relocation](overview.md#readiness-inflatecopy) |
| <a id="target-zlibf-spec-public-goal-inflateinit2"></a>[inflateInit2_](../ZlibF/Spec/Public/Initialisation.lean#L90) | Not proved / Blocked | [Contract](../docs/api/inflate-stream.md#inflateinit2_); [input range](input-configurations.md#inflate-inputs) | — [Blocker: Inflate initialization cleanup](overview.md#inflate-initialization-cleanup) | [Blocked: cleanup contract](overview.md#readiness-inflateinit2) |
| <a id="target-zlibf-spec-public-goal-inflateinit"></a>[inflateInit_](../ZlibF/Spec/Public/Initialisation.lean#L95) | All stated inputs / Registered proof | [Contract](../docs/api/inflate-stream.md#inflateinit_); [input range](input-configurations.md#inflate-inputs) | [ZlibF.Spec.Public.Proofs.InflateInit.init15_public](../ZlibF/Proof/public-inflate-init.lean#L83) | — |
| <a id="target-zlibf-spec-public-goal-inflateresetkeep"></a>[inflateResetKeep](../ZlibF/Spec/Public/Lifecycle.lean#L20) | All stated inputs / Registered proof | [Contract](../docs/api/inflate-stream.md#inflateresetkeep); [input range](input-configurations.md#inflate-inputs) | [ZlibF.Spec.Public.InflateResetKeepProof.resetkeep_public](../ZlibF/Proof/public-inflate-reset-keep.lean#L8) | — |
| <a id="target-zlibf-spec-public-goal-inflatereset"></a>[inflateReset](../ZlibF/Spec/Public/Lifecycle.lean#L32) | All stated inputs / Registered proof | [Contract](../docs/api/inflate-stream.md#inflatereset); [input range](input-configurations.md#inflate-inputs) | [ZlibF.Spec.Public.InflateResetProof.reset_public](../ZlibF/Proof/public-inflate-reset.lean#L16) | — |
| <a id="target-zlibf-spec-public-goal-inflatereset2"></a>[inflateReset2](../ZlibF/Spec/Public/Lifecycle.lean#L43) | All stated inputs / Registered proof | [Contract](../docs/api/inflate-stream.md#inflatereset2); [input range](input-configurations.md#inflate-inputs) | [ZlibF.Spec.Public.InflateReset2Proof.reset2_public](../ZlibF/Proof/public-inflate-reset2.lean#L61) | — |
| <a id="target-zlibf-spec-public-goal-inflateend"></a>[inflateEnd](../ZlibF/Spec/Public/Lifecycle.lean#L60) | All stated inputs / Registered proof | [Contract](../docs/api/inflate-stream.md#inflateend); [input range](input-configurations.md#inflate-inputs) | [ZlibF.Spec.Public.InflateEndProof.inflate_end_public](../ZlibF/Proof/public-inflate-end.lean#L55) | — |
| <a id="target-zlibf-spec-public-goal-inflategetdictionary"></a>[inflateGetDictionary](../ZlibF/Spec/Public/Lifecycle.lean#L77) | All stated inputs / Registered proof | [Contract](../docs/api/inflate-stream.md#inflategetdictionary); [input range](input-configurations.md#inflate-inputs) | [ZlibF.Spec.Public.InflateDictionaryProof.inflate_getdict_public](../ZlibF/Proof/public-inflate-getdict.lean#L10) | — |
| <a id="target-zlibf-spec-public-goal-inflategetheader"></a>[inflateGetHeader](../ZlibF/Spec/Public/Lifecycle.lean#L87) | All stated inputs / Registered proof | [Contract](../docs/api/inflate-stream.md#inflategetheader); [input range](input-configurations.md#inflate-inputs) | [ZlibF.Spec.Public.InflateHeaderProof.getheader_public](../ZlibF/Proof/public-inflate-header.lean#L34) | — |
| <a id="target-zlibf-spec-public-goal-inflatesetdictionary"></a>[inflateSetDictionary](../ZlibF/Spec/Public/Lifecycle.lean#L153) | All stated inputs / Registered proof | [Contract](../docs/api/inflate-stream.md#inflatesetdictionary); [input range](input-configurations.md#inflate-inputs) | [ZlibF.Spec.Public.Proofs.inflateSetDictionary_public](../ZlibF/Proof/public-inflate-setdict.lean#L92) | — |
| <a id="target-zlibf-spec-public-goal-inflatesyncpoint"></a>[inflateSyncPoint](../ZlibF/Spec/Public/StreamQueries.lean#L53) | All stated inputs / Registered proof | [Contract](../docs/api/inflate-stream.md#inflatesyncpoint); [input range](input-configurations.md#inflate-inputs) | [ZlibF.Spec.Public.InflateQueryProof.syncpoint_public](../ZlibF/Proof/public-inflate-small-queries.lean#L44) | — |
| <a id="target-zlibf-spec-public-goal-inflatemark"></a>[inflateMark](../ZlibF/Spec/Public/StreamQueries.lean#L62) | All stated inputs / Registered proof | [Contract](../docs/api/inflate-stream.md#inflatemark); [input range](input-configurations.md#inflate-inputs) | [ZlibF.Spec.Public.InflateMarkProof.mark_public](../ZlibF/Proof/public-inflate-mark.lean#L71) | — |
| <a id="target-zlibf-spec-public-goal-inflatecodesused"></a>[inflateCodesUsed](../ZlibF/Spec/Public/StreamQueries.lean#L73) | All stated inputs / Registered proof | [Contract](../docs/api/inflate-stream.md#inflatecodesused); [input range](input-configurations.md#inflate-inputs) | [ZlibF.Spec.Public.Proofs.inflate_codes_used](../ZlibF/Proof/Api/QueryLayout.lean#L71) | — |
| <a id="target-zlibf-spec-public-goal-inflateundermine"></a>[inflateUndermine](../ZlibF/Spec/Public/StreamQueries.lean#L81) | All stated inputs / Registered proof | [Contract](../docs/api/inflate-stream.md#inflateundermine); [input range](input-configurations.md#inflate-inputs) | [ZlibF.Spec.Public.InflateQueryProof.undermine_public](../ZlibF/Proof/public-inflate-small-queries.lean#L60) | — |
| <a id="target-zlibf-spec-public-goal-inflatevalidate"></a>[inflateValidate](../ZlibF/Spec/Public/StreamQueries.lean#L89) | All stated inputs / Registered proof | [Contract](../docs/api/inflate-stream.md#inflatevalidate); [input range](input-configurations.md#inflate-inputs) | [ZlibF.Spec.Public.InflateQueryProof.validate_public](../ZlibF/Proof/public-inflate-small-queries.lean#L75) | — |
| <a id="target-zlibf-spec-public-goal-inflateprime"></a>[inflatePrime](../ZlibF/Spec/Public/StreamQueries.lean#L100) | All stated inputs / Registered proof | [Contract](../docs/api/inflate-stream.md#inflateprime); [input range](input-configurations.md#inflate-inputs) | [ZlibF.Spec.Public.InflatePrimeProof.prime_public](../ZlibF/Proof/public-inflate-prime.lean#L117) | — |
| <a id="target-zlibf-spec-public-goal-inflate"></a>[inflate](../ZlibF/Spec/Public/Streams.lean#L24) | Not proved / Not proved | [Contract](../docs/api/inflate-stream.md#inflate); [input range](input-configurations.md#inflate-inputs) | — | [Needs: dispatch invariants](overview.md#readiness-inflate) |
| <a id="target-zlibf-spec-public-goal-inflatesync"></a>[inflateSync](../ZlibF/Spec/Public/Streams.lean#L160) | Not proved / Not proved | [Contract](../docs/api/inflate-stream.md#inflatesync); [input range](input-configurations.md#inflate-inputs) | — | [Needs: scan and history](overview.md#readiness-inflatesync) |

<a id="group-fast"></a>

## Fast decoder obligations

| Target statement | Coverage / evidence state | Contract / input range | Proof evidence | Reviewed next work |
| --- | --- | --- | --- | --- |
| <a id="target-zlib-inffast-spec-bodyorigin-goal-actual-body-preserves-origin"></a>[actual_body_preserves_origin](../ZlibF/Spec/InflateFastBodyOrigin.lean#L18) | All stated inputs / Locally checked | Exact target statement; [input range](input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.BodyOriginProof.actual_body_preserves_origin](../ZlibF/Proof/inffast.c.body-origin.lean#L374); [Zlib.Inffast.Proofs.actual_body_preserves_origin](../ZlibF/Proof/inffast.c.body-origin.lean#L374) | — |
| <a id="target-zlib-inffast-spec-bodytoken-goal-actual-body-refines-token"></a>[actual_body_refines_token](../ZlibF/Spec/InflateFastBodyToken.lean#L73) | All stated inputs / Locally checked | Exact target statement; [input range](input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.BodyTokenProof.actual_body_refines_token](../ZlibF/Proof/inffast.c.body-token.lean#L564); [Zlib.Inffast.Proofs.actual_body_refines_token](../ZlibF/Proof/inffast.c.body-token.lean#L564) | — |
| <a id="target-zlib-inffast-spec-callorigin-goal-actual-fast-preserves-origin"></a>[actual_fast_preserves_origin](../ZlibF/Spec/InflateFastCallOrigin.lean#L24) | All stated inputs / Locally checked | Exact target statement; [input range](input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.actual_fast_preserves_origin](../ZlibF/Proof/inffast.c.call-origin.lean#L176) | — |
| <a id="target-zlib-inffast-spec-distanceorigin-goal-actual-distance-block-preserves-origin"></a>[actual_distance_block_preserves_origin](../ZlibF/Spec/InflateFastDistanceOrigin.lean#L18) | All stated inputs / Locally checked | Exact target statement; [input range](input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.actual_distance_block_preserves_origin](../ZlibF/Proof/inffast.c.distance-origin.lean#L324) | — |
| <a id="target-zlib-inffast-spec-distanceresult-goal-actual-distance-refines-lz77"></a>[actual_distance_refines_lz77](../ZlibF/Spec/InflateFastDistanceResult.lean#L101) | All stated inputs / Locally checked | Exact target statement; [input range](input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.actual_distance_refines_lz77](../ZlibF/Proof/inffast.c.distance-result.lean#L382) | — |
| <a id="target-zlib-inffast-spec-distancesemantics-goal-distance-lookup-matches-format"></a>[distance_lookup_matches_format](../ZlibF/Spec/InflateFastDistanceSemantics.lean#L20) | All stated inputs / Locally checked | Exact target statement; [input range](input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.distance_lookup_matches_format](../ZlibF/Proof/inffast.c.distance-semantics.lean#L22) | — |
| <a id="target-zlib-inffast-spec-goal-fast-safe"></a>[fast_safe](../ZlibF/Spec/InflateFast.lean#L68) | All stated inputs / Locally checked | Exact target statement; [input range](input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.inflate_fast_safe](../ZlibF/Proof/inffast.c.final.lean#L257) | — |
| <a id="target-zlib-inffast-spec-goal-step-safe"></a>[step_safe](../ZlibF/Spec/InflateFast.lean#L40) | All stated inputs / Locally checked | Exact target statement; [input range](input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.inflate_fast_body_step_safe](../ZlibF/Proof/inffast.c.body.lean#L315) | — |
| <a id="target-zlib-inffast-spec-lengthsemantics-goal-length-lookup-matches-format"></a>[length_lookup_matches_format](../ZlibF/Spec/InflateFastLengthSemantics.lean#L34) | All stated inputs / Locally checked | Exact target statement; [input range](input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.length_lookup_matches_format](../ZlibF/Proof/inffast.c.length-semantics.lean#L22) | — |
| <a id="target-zlib-inffast-spec-lengthtrace-goal-actual-body-retains-selected-length"></a>[actual_body_retains_selected_length](../ZlibF/Spec/InflateFastLengthTrace.lean#L51) | All stated inputs / Locally checked | Exact target statement; [input range](input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.LengthTraceProof.actual_body_retains_selected_length](../ZlibF/Proof/inffast.c.length-trace.lean#L247); [Zlib.Inffast.Proofs.actual_body_retains_selected_length](../ZlibF/Proof/inffast.c.length-trace.lean#L247) | — |
| <a id="target-zlib-inffast-spec-matchhistory-goal-actual-copy-match-refines-lz77"></a>[actual_copy_match_refines_lz77](../ZlibF/Spec/InflateFastMatchHistory.lean#L39) | All stated inputs / Locally checked | Exact target statement; [input range](input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.actual_copy_match_refines_lz77](../ZlibF/Proof/inffast.c.match-history.lean#L329) | — |
| <a id="target-zlib-inffast-spec-matchhistory-goal-match-array-refines-lz77"></a>[match_array_refines_lz77](../ZlibF/Spec/InflateFastMatchHistory.lean#L25) | All stated inputs / Locally checked | Exact target statement; [input range](input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.fast_match_array_refines_lz77](../ZlibF/Math/InflateFastMatchHistory.lean#L56) | — |
| <a id="target-zlib-inffast-spec-origin-goal-actual-drop-preserves-origin"></a>[actual_drop_preserves_origin](../ZlibF/Spec/InflateFastOrigin.lean#L68) | All stated inputs / Locally checked | Exact target statement; [input range](input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.actual_drop_preserves_origin](../ZlibF/Proof/inffast.c.origin.lean#L138) | — |
| <a id="target-zlib-inffast-spec-origin-goal-actual-pull-preserves-origin"></a>[actual_pull_preserves_origin](../ZlibF/Spec/InflateFastOrigin.lean#L57) | All stated inputs / Locally checked | Exact target statement; [input range](input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.actual_pull_preserves_origin](../ZlibF/Proof/inffast.c.origin.lean#L127) | — |
| <a id="target-zlib-inffast-spec-origin-goal-actual-rollback-preserves-origin"></a>[actual_rollback_preserves_origin](../ZlibF/Spec/InflateFastOrigin.lean#L81) | All stated inputs / Locally checked | Exact target statement; [input range](input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.actual_rollback_preserves_origin](../ZlibF/Proof/inffast.c.origin.lean#L150) | — |
| <a id="target-zlib-inffast-spec-origin-goal-drop-preserves-origin"></a>[drop_preserves_origin](../ZlibF/Spec/InflateFastOrigin.lean#L38) | All stated inputs / Locally checked | Exact target statement; [input range](input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.drop_preserves_origin](../ZlibF/Proof/inffast.c.origin.lean#L41) | — |
| <a id="target-zlib-inffast-spec-origin-goal-initial-origin"></a>[initial_origin](../ZlibF/Spec/InflateFastOrigin.lean#L27) | All stated inputs / Locally checked | Exact target statement; [input range](input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.initial_origin](../ZlibF/Proof/inffast.c.origin.lean#L16) | — |
| <a id="target-zlib-inffast-spec-origin-goal-pull-preserves-origin"></a>[pull_preserves_origin](../ZlibF/Spec/InflateFastOrigin.lean#L32) | All stated inputs / Locally checked | Exact target statement; [input range](input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.pull_preserves_origin](../ZlibF/Proof/inffast.c.origin.lean#L21) | — |
| <a id="target-zlib-inffast-spec-origin-goal-rollback-preserves-origin"></a>[rollback_preserves_origin](../ZlibF/Spec/InflateFastOrigin.lean#L46) | All stated inputs / Locally checked | Exact target statement; [input range](input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.rollback_preserves_origin](../ZlibF/Proof/inffast.c.origin.lean#L83) | — |

<a id="group-tables"></a>

## Decode-table obligations

| Target statement | Coverage / evidence state | Contract / input range | Proof evidence | Reviewed next work |
| --- | --- | --- | --- | --- |
| <a id="target-zlib-inftrees-spec-decoderejection-goal-decode-table-classifies-input"></a>[decode_table_classifies_input](../ZlibF/Spec/InflateDecodeTableRejection.lean#L19) | Not proved / Not proved | Exact target statement; [input range](input-configurations.md#entry-inputs) | — | Prerequisites unreviewed |
| <a id="target-zlib-inftrees-spec-decodesemantics-goal-decode-table-matches-format"></a>[decode_table_matches_format](../ZlibF/Spec/InflateDecodeTableSemantics.lean#L51) | Not proved / Not proved | Exact target statement; [input range](input-configurations.md#entry-inputs) | — | Prerequisites unreviewed |
| <a id="target-zlib-inftrees-spec-decodeshort-goal-short-decode-table-leaf-sound"></a>[short_decode_table_leaf_sound](../ZlibF/Spec/InflateDecodeTableShort.lean#L26) | Not proved / Not proved | Exact target statement; [input range](input-configurations.md#entry-inputs) | — | Prerequisites unreviewed |
| <a id="target-zlib-inftrees-spec-decodesoundness-goal-decode-table-leaf-sound"></a>[decode_table_leaf_sound](../ZlibF/Spec/InflateDecodeTableSoundness.lean#L31) | Not proved / Not proved | Exact target statement; [input range](input-configurations.md#entry-inputs) | — | Prerequisites unreviewed |
| <a id="target-zlib-inftrees-spec-decodetableframe-goal-decode-table-read-preserved"></a>[decode_table_read_preserved](../ZlibF/Spec/InflateDecodeTableFrame.lean#L20) | All stated inputs / Locally checked | Exact target statement; [input range](input-configurations.md#entry-inputs) | [Zlib.Inftrees.Proofs.decode_table_read_preserved](../ZlibF/Proof/inftrees.c.decode.frame.lean#L55) | — |
| <a id="target-zlib-inftrees-spec-decodetableinvariant-goal-constructor-establishes-decode-table-invariant"></a>[constructor_establishes_decode_table_invariant](../ZlibF/Spec/InflateDecodeTableInvariant.lean#L51) | Not proved / Not proved | Exact target statement; [input range](input-configurations.md#entry-inputs) | — | Prerequisites unreviewed |
| <a id="target-zlib-inftrees-spec-decodetableinvariant-goal-decode-table-invariant-of-prefix"></a>[decode_table_invariant_of_prefix](../ZlibF/Spec/InflateDecodeTableInvariant.lean#L68) | Not proved / Not proved | Exact target statement; [input range](input-configurations.md#entry-inputs) | — | Prerequisites unreviewed |
| <a id="target-zlib-inftrees-spec-decodetablestability-goal-constructor-establishes-query-stability"></a>[constructor_establishes_query_stability](../ZlibF/Spec/InflateDecodeTableStability.lean#L30) | Not proved / Not proved | Exact target statement; [input range](input-configurations.md#entry-inputs) | — | Prerequisites unreviewed |
| <a id="target-zlib-inftrees-spec-decodetablestability-goal-query-stability-of-prefix"></a>[query_stability_of_prefix](../ZlibF/Spec/InflateDecodeTableStability.lean#L43) | All stated inputs / Locally checked | Exact target statement; [input range](input-configurations.md#entry-inputs) | [Zlib.Inftrees.Proofs.query_stability_of_prefix](../ZlibF/Proof/inftrees.c.decode.stability-rejection.lean#L20) | — |
| <a id="target-zlib-inftrees-spec-decodetablestability-goal-short-rejected-leaf-stays-invalid"></a>[short_rejected_leaf_stays_invalid](../ZlibF/Spec/InflateDecodeTableStability.lean#L54) | All stated inputs / Locally checked | Exact target statement; [input range](input-configurations.md#entry-inputs) | [Zlib.Inftrees.Proofs.short_rejected_leaf_stays_invalid](../ZlibF/Proof/inftrees.c.decode.stability-rejection.lean#L31) | — |
| <a id="target-zlib-inftrees-spec-fasttableflags-goal-constructor-establishes-fast-leaf-flags"></a>[constructor_establishes_fast_leaf_flags](../ZlibF/Spec/InflateFastTableFlags.lean#L52) | Not proved / Not proved | Exact target statement; [input range](input-configurations.md#entry-inputs) | — | Prerequisites unreviewed |
| <a id="target-zlib-inftrees-spec-fasttableflags-goal-fast-leaf-flags-of-prefix"></a>[fast_leaf_flags_of_prefix](../ZlibF/Spec/InflateFastTableFlags.lean#L66) | Not proved / Not proved | Exact target statement; [input range](input-configurations.md#entry-inputs) | — | Prerequisites unreviewed |
| <a id="target-zlib-inftrees-spec-fasttableflags-goal-fixed-tables-have-fast-leaf-flags"></a>[fixed_tables_have_fast_leaf_flags](../ZlibF/Spec/InflateFastTableFlags.lean#L76) | Not proved / Not proved | Exact target statement; [input range](input-configurations.md#entry-inputs) | — | Prerequisites unreviewed |
| <a id="target-zlib-inftrees-spec-fasttableflags-goal-leaf-classification-agrees"></a>[leaf_classification_agrees](../ZlibF/Spec/InflateFastTableFlags.lean#L42) | Not proved / Not proved | Exact target statement; [input range](input-configurations.md#entry-inputs) | — | Prerequisites unreviewed |
| <a id="target-zlib-inftrees-spec-goal-inflate-table-content"></a>[inflate_table_content](../ZlibF/Spec/InflateTableContent.lean#L32) | Not proved / Not proved | Exact target statement; [input range](input-configurations.md#entry-inputs) | — | Prerequisites unreviewed |
| <a id="target-zlib-inftrees-spec-goal-inflate-table-decoder-safe"></a>[inflate_table_decoder_safe](../ZlibF/Spec/InflateTableSafety.lean#L28) | Not proved / Not proved | Exact target statement; [input range](input-configurations.md#entry-inputs) | — | Prerequisites unreviewed |
| <a id="target-zlib-inftrees-spec-goal-inflate-table-read-extent"></a>[inflate_table_read_extent](../ZlibF/Spec/InflateTableExtent.lean#L28) | Not proved / Not proved | Exact target statement; [input range](input-configurations.md#entry-inputs) | — | Prerequisites unreviewed |
| <a id="target-zlib-inftrees-spec-roottable-goal-constructor-root-bits"></a>[constructor_root_bits](../ZlibF/Spec/InflateRootTable.lean#L21) | Not proved / Not proved | Exact target statement; [input range](input-configurations.md#entry-inputs) | — | Prerequisites unreviewed |
| <a id="target-zlib-inftrees-spec-subtable-goal-constructor-subtable-bits"></a>[constructor_subtable_bits](../ZlibF/Spec/InflateSubtable.lean#L26) | Not proved / Not proved | Exact target statement; [input range](input-configurations.md#entry-inputs) | — | Prerequisites unreviewed |

<a id="group-copy"></a>

## Match-copy mathematics

| Target statement | Coverage / evidence state | Contract / input range | Proof evidence | Reviewed next work |
| --- | --- | --- | --- | --- |
| <a id="target-zlibf-math-lz77copy-goal-output-copy-refines-lz77"></a>[output_copy_refines_lz77](../ZlibF/Math/LZ77CopySpec.lean#L22) | All stated inputs / Locally checked | Exact target statement; [input range](input-configurations.md#entry-inputs) | [ZlibF.Math.LZ77Copy.output_copy_refines_lz77](../ZlibF/Math/LZ77Copy.lean#L65) | — |
| <a id="target-zlibf-math-lz77copy-goal-window-copy-refines-lz77"></a>[window_copy_refines_lz77](../ZlibF/Math/LZ77CopySpec.lean#L32) | All stated inputs / Locally checked | Exact target statement; [input range](input-configurations.md#entry-inputs) | [ZlibF.Math.LZ77Copy.window_copy_refines_lz77](../ZlibF/Math/LZ77Copy.lean#L124) | — |
| <a id="target-zlibf-math-lz77history-goal-copy-back-compose"></a>[copy_back_compose](../ZlibF/Math/LZ77HistorySpec.lean#L21) | All stated inputs / Locally checked | Exact target statement; [input range](input-configurations.md#entry-inputs) | [ZlibF.Math.LZ77History.copy_back_compose](../ZlibF/Math/LZ77History.lean#L31) | — |
| <a id="target-zlibf-math-lz77history-goal-copy-back-extends-history"></a>[copy_back_extends_history](../ZlibF/Math/LZ77HistorySpec.lean#L15) | All stated inputs / Locally checked | Exact target statement; [input range](input-configurations.md#entry-inputs) | [ZlibF.Math.LZ77History.copy_back_extends_history](../ZlibF/Math/LZ77History.lean#L17) | — |
| <a id="target-zlibf-math-lz77history-goal-retained-history-agrees"></a>[retained_history_agrees](../ZlibF/Math/LZ77HistorySpec.lean#L29) | All stated inputs / Locally checked | Exact target statement; [input range](input-configurations.md#entry-inputs) | [ZlibF.Math.LZ77History.retained_history_agrees](../ZlibF/Math/LZ77History.lean#L59) | — |
| <a id="target-zlibf-math-lz77history-goal-window-distance-check-agrees"></a>[window_distance_check_agrees](../ZlibF/Math/LZ77HistorySpec.lean#L39) | All stated inputs / Locally checked | Exact target statement; [input range](input-configurations.md#entry-inputs) | [ZlibF.Math.LZ77History.window_distance_check_agrees](../ZlibF/Math/LZ77History.lean#L72) | — |

<a id="group-deflate"></a>

## Deflate streams

| Target statement | Coverage / evidence state | Contract / input range | Proof evidence | Reviewed next work |
| --- | --- | --- | --- | --- |
| <a id="target-zlibf-spec-public-goal-deflatecopy"></a>[deflateCopy](../ZlibF/Spec/Public/Copy.lean#L67) | Not proved / Not proved | [Contract](../docs/api/deflate-stream.md#deflatecopy); [input range](input-configurations.md#deflate-inputs) | — | [Start: copy and relocation](overview.md#readiness-inflatecopy) |
| <a id="target-zlibf-spec-public-goal-deflateinit2"></a>[deflateInit2_](../ZlibF/Spec/Public/Initialisation.lean#L138) | Not proved / Not proved | [Contract](../docs/api/deflate-stream.md#deflateinit2_); [input range](input-configurations.md#deflate-inputs) | — | [Start: init and allocation](overview.md#readiness-deflateinit2) |
| <a id="target-zlibf-spec-public-goal-deflateinit"></a>[deflateInit_](../ZlibF/Spec/Public/Initialisation.lean#L145) | All stated inputs / Registered proof | [Contract](../docs/api/deflate-stream.md#deflateinit_); [input range](input-configurations.md#deflate-inputs) | [ZlibF.Spec.Public.Proofs.DeflateInit.deflateInit_proof](../ZlibF/Proof/public-deflate-init.lean#L161) | — |
| <a id="target-zlibf-spec-public-goal-deflategetdictionary"></a>[deflateGetDictionary](../ZlibF/Spec/Public/Lifecycle.lean#L105) | All stated inputs / Registered proof | [Contract](../docs/api/deflate-stream.md#deflategetdictionary); [input range](input-configurations.md#deflate-inputs) | [ZlibF.Spec.Public.DeflateDictionaryProof.deflate_getdict_public](../ZlibF/Proof/public-deflate-getdict.lean#L10) | — |
| <a id="target-zlibf-spec-public-goal-deflateend"></a>[deflateEnd](../ZlibF/Spec/Public/Lifecycle.lean#L115) | All stated inputs / Registered proof | [Contract](../docs/api/deflate-stream.md#deflateend); [input range](input-configurations.md#deflate-inputs) | [ZlibF.Spec.Public.DeflateEndProof.deflate_end_public](../ZlibF/Proof/public-deflate-end.lean#L10) | — |
| <a id="target-zlibf-spec-public-goal-deflateresetkeep"></a>[deflateResetKeep](../ZlibF/Spec/Public/Lifecycle.lean#L146) | All stated inputs / Registered proof | [Contract](../docs/api/deflate-stream.md#deflateresetkeep); [input range](input-configurations.md#deflate-inputs) | [ZlibF.Spec.Public.DeflateResetKeepProof.deflate_resetkeep_public](../ZlibF/Proof/public-deflate-reset-keep.lean#L19) | — |
| <a id="target-zlibf-spec-public-goal-deflatereset"></a>[deflateReset](../ZlibF/Spec/Public/Lifecycle.lean#L149) | All stated inputs / Registered proof | [Contract](../docs/api/deflate-stream.md#deflatereset); [input range](input-configurations.md#deflate-inputs) | [ZlibF.Spec.Public.DeflateResetProof.deflate_reset_public](../ZlibF/Proof/public-deflate-reset.lean#L52) | — |
| <a id="target-zlibf-spec-public-goal-deflatesetdictionary"></a>[deflateSetDictionary](../ZlibF/Spec/Public/Lifecycle.lean#L175) | Not proved / Not proved | [Contract](../docs/api/deflate-stream.md#deflatesetdictionary); [input range](input-configurations.md#deflate-inputs) | — | [Start: window and hash](overview.md#readiness-deflatesetdictionary) |
| <a id="target-zlibf-spec-public-goal-deflatepending"></a>[deflatePending](../ZlibF/Spec/Public/StreamQueries.lean#L113) | All stated inputs / Registered proof | [Contract](../docs/api/deflate-stream.md#deflatepending); [input range](input-configurations.md#deflate-inputs) | [ZlibF.Spec.Public.DeflateQueryProof.pending_public](../ZlibF/Proof/public-deflate-small-queries.lean#L145) | — |
| <a id="target-zlibf-spec-public-goal-deflateused"></a>[deflateUsed](../ZlibF/Spec/Public/StreamQueries.lean#L124) | All stated inputs / Registered proof | [Contract](../docs/api/deflate-stream.md#deflateused); [input range](input-configurations.md#deflate-inputs) | [ZlibF.Spec.Public.DeflateQueryProof.used_public](../ZlibF/Proof/public-deflate-small-queries.lean#L48) | — |
| <a id="target-zlibf-spec-public-goal-deflatetune"></a>[deflateTune](../ZlibF/Spec/Public/StreamQueries.lean#L132) | All stated inputs / Registered proof | [Contract](../docs/api/deflate-stream.md#deflatetune); [input range](input-configurations.md#deflate-inputs) | [ZlibF.Spec.Public.DeflateQueryProof.tune_public](../ZlibF/Proof/public-deflate-small-queries.lean#L61) | — |
| <a id="target-zlibf-spec-public-goal-deflatesetheader"></a>[deflateSetHeader](../ZlibF/Spec/Public/StreamQueries.lean#L145) | All stated inputs / Registered proof | [Contract](../docs/api/deflate-stream.md#deflatesetheader); [input range](input-configurations.md#deflate-inputs) | [ZlibF.Spec.Public.DeflateQueryProof.header_public](../ZlibF/Proof/public-deflate-small-queries.lean#L74) | — |
| <a id="target-zlibf-spec-public-goal-deflate"></a>[deflate](../ZlibF/Spec/Public/Streams.lean#L51) | Not proved / Not proved | [Contract](../docs/api/deflate-stream.md#deflate); [input range](input-configurations.md#deflate-inputs) | — | [Needs: dispatch invariants](overview.md#readiness-inflate) |
| <a id="target-zlibf-spec-public-goal-deflatebound-z"></a>[deflateBound_z](../ZlibF/Spec/Public/Streams.lean#L105) | Not proved / Not proved | [Contract](../docs/api/deflate-stream.md#deflatebound_z); [input range](input-configurations.md#deflate-inputs) | — | [Start: bound and header review](overview.md#readiness-deflatebound-z) |
| <a id="target-zlibf-spec-public-goal-deflatebound"></a>[deflateBound](../ZlibF/Spec/Public/Streams.lean#L109) | Not proved / Not proved | [Contract](../docs/api/deflate-stream.md#deflatebound); [input range](input-configurations.md#deflate-inputs) | — | [Start: bound and header review](overview.md#readiness-deflatebound-z) |
| <a id="target-zlibf-spec-public-goal-deflateprime"></a>[deflatePrime](../ZlibF/Spec/Public/Streams.lean#L119) | Not proved / Not proved | [Contract](../docs/api/deflate-stream.md#deflateprime); [input range](input-configurations.md#deflate-inputs) | — | [Start: compaction and bits](overview.md#readiness-deflateprime) |
| <a id="target-zlibf-spec-public-goal-deflateparams"></a>[deflateParams](../ZlibF/Spec/Public/Streams.lean#L137) | Not proved / Not proved | [Contract](../docs/api/deflate-stream.md#deflateparams); [input range](input-configurations.md#deflate-inputs) | — | [Needs: block flush and parameter state](overview.md#readiness-deflateparams) |

<a id="group-back"></a>

## Callback decoding

| Target statement | Coverage / evidence state | Contract / input range | Proof evidence | Reviewed next work |
| --- | --- | --- | --- | --- |
| <a id="target-zlibf-spec-public-goal-inflatebackinit"></a>[inflateBackInit_](../ZlibF/Spec/Public/Back.lean#L22) | All stated inputs / Registered proof | [Contract](../docs/api/inflate-back.md#inflatebackinit_); [input range](input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.InflateBackInitProof.back_init_public](../ZlibF/Proof/public-infback-init.lean#L135) | — |
| <a id="target-zlibf-spec-public-goal-inflateback"></a>[inflateBack](../ZlibF/Spec/Public/Back.lean#L115) | Not proved / Not proved | [Contract](../docs/api/inflate-back.md#inflateback); [input range](input-configurations.md#entry-inputs) | — | [Needs: tables, window and callbacks](overview.md#readiness-inflateback) |
| <a id="target-zlibf-spec-public-goal-inflatebackend"></a>[inflateBackEnd](../ZlibF/Spec/Public/Back.lean#L142) | All stated inputs / Registered proof | [Contract](../docs/api/inflate-back.md#inflatebackend); [input range](input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.InflateBackEndProof.back_end_public](../ZlibF/Proof/public-infback-end.lean#L20) | — |

<a id="group-gzip"></a>

## Gzip files

| Target statement | Coverage / evidence state | Contract / input range | Proof evidence | Reviewed next work |
| --- | --- | --- | --- | --- |
| <a id="target-zlibf-spec-public-goal-gzclose-r"></a>[gzclose_r](../ZlibF/Spec/Public/GzClose.lean#L35) | Not proved / Not proved | [Contract](../docs/api/gz-file.md#gzclose_r); [input range](input-configurations.md#entry-inputs) | — | [Needs: resource history](overview.md#readiness-gzclose-r) |
| <a id="target-zlibf-spec-public-goal-gzclose-w"></a>[gzclose_w](../ZlibF/Spec/Public/GzClose.lean#L40) | Not proved / Not proved | [Contract](../docs/api/gz-file.md#gzclose_w); [input range](input-configurations.md#entry-inputs) | — | [Needs: flush and cleanup](overview.md#readiness-gzclose-w) |
| <a id="target-zlibf-spec-public-goal-gzclose"></a>[gzclose](../ZlibF/Spec/Public/GzClose.lean#L44) | Not proved / Not proved | [Contract](../docs/api/gz-file.md#gzclose); [input range](input-configurations.md#entry-inputs) | — | [Needs: flush and cleanup](overview.md#readiness-gzclose-w) |
| <a id="target-zlibf-spec-public-goal-gzbuffer"></a>[gzbuffer](../ZlibF/Spec/Public/GzControl.lean#L12) | All stated inputs / Registered proof | [Contract](../docs/api/gz-file.md#gzbuffer); [input range](input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.Proofs.gzbuffer_public](../ZlibF/Proof/public-gzbuffer.lean#L49) | — |
| <a id="target-zlibf-spec-public-goal-gzeof"></a>[gzeof](../ZlibF/Spec/Public/GzControl.lean#L22) | All stated inputs / Registered proof | [Contract](../docs/api/gz-file.md#gzeof); [input range](input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.Proofs.gzeof_public](../ZlibF/Proof/public-gzeof.lean#L18) | — |
| <a id="target-zlibf-spec-public-goal-gztell64"></a>[gztell64](../ZlibF/Spec/Public/GzControl.lean#L36) | Not proved / Not proved | [Contract](../docs/api/gz-file.md#gztell64); [input range](input-configurations.md#entry-inputs) | — | [Needs: position history](overview.md#readiness-gztell64) |
| <a id="target-zlibf-spec-public-goal-gztell"></a>[gztell](../ZlibF/Spec/Public/GzControl.lean#L39) | Not proved / Not proved | [Contract](../docs/api/gz-file.md#gztell); [input range](input-configurations.md#entry-inputs) | — | [Needs: position history](overview.md#readiness-gztell64) |
| <a id="target-zlibf-spec-public-goal-gzoffset64"></a>[gzoffset64](../ZlibF/Spec/Public/GzControl.lean#L53) | All stated inputs / Registered proof | [Contract](../docs/api/gz-file.md#gzoffset64); [input range](input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.OffsetProof.gzoffset64_public_goal](../ZlibF/Proof/public-gz-offset.lean#L199) | — |
| <a id="target-zlibf-spec-public-goal-gzoffset"></a>[gzoffset](../ZlibF/Spec/Public/GzControl.lean#L56) | All stated inputs / Registered proof | [Contract](../docs/api/gz-file.md#gzoffset); [input range](input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.OffsetProof.gzoffset_public_goal](../ZlibF/Proof/public-gz-offset.lean#L211) | — |
| <a id="target-zlibf-spec-public-goal-gzerror"></a>[gzerror](../ZlibF/Spec/Public/GzControl.lean#L63) | All stated inputs / Registered proof | [Contract](../docs/api/gz-file.md#gzerror); [input range](input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.GzErrorProof.gzerror](../ZlibF/Proof/public-gz-error.lean#L197) | — |
| <a id="target-zlibf-spec-public-goal-gzclearerr"></a>[gzclearerr](../ZlibF/Spec/Public/GzControl.lean#L74) | All stated inputs / Registered proof | [Contract](../docs/api/gz-file.md#gzclearerr); [input range](input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.Proofs.gzclearerr](../ZlibF/Proof/gzlib.c.public-clearerr.lean#L28) | — |
| <a id="target-zlibf-spec-public-goal-gzrewind"></a>[gzrewind](../ZlibF/Spec/Public/GzControl.lean#L91) | All stated inputs / Registered proof | [Contract](../docs/api/gz-file.md#gzrewind); [input range](input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.GzRewindProof.rewind_public](../ZlibF/Proof/public-gz-rewind.lean#L67) | — |
| <a id="target-zlibf-spec-public-goal-gzseek64"></a>[gzseek64](../ZlibF/Spec/Public/GzControl.lean#L116) | Not proved / Not proved | [Contract](../docs/api/gz-file.md#gzseek64); [input range](input-configurations.md#entry-inputs) | — | [Needs: seek and history](overview.md#readiness-gzseek64) |
| <a id="target-zlibf-spec-public-goal-gzseek"></a>[gzseek](../ZlibF/Spec/Public/GzControl.lean#L119) | Not proved / Not proved | [Contract](../docs/api/gz-file.md#gzseek); [input range](input-configurations.md#entry-inputs) | — | [Needs: seek and history](overview.md#readiness-gzseek64) |
| <a id="target-zlibf-spec-public-goal-gzopen"></a>[gzopen](../ZlibF/Spec/Public/GzOpen.lean#L61) | Not proved / Not proved | [Contract](../docs/api/gz-file.md#gzopen); [input range](input-configurations.md#entry-inputs) | — | [Start: open and cleanup](overview.md#readiness-gzopen) |
| <a id="target-zlibf-spec-public-goal-gzopen64"></a>[gzopen64](../ZlibF/Spec/Public/GzOpen.lean#L65) | Not proved / Not proved | [Contract](../docs/api/gz-file.md#gzopen64); [input range](input-configurations.md#entry-inputs) | — | [Start: open and cleanup](overview.md#readiness-gzopen) |
| <a id="target-zlibf-spec-public-goal-gzdopen"></a>[gzdopen](../ZlibF/Spec/Public/GzOpen.lean#L70) | Not proved / Not proved | [Contract](../docs/api/gz-file.md#gzdopen); [input range](input-configurations.md#entry-inputs) | — | [Start: open and cleanup](overview.md#readiness-gzopen) |
| <a id="target-zlibf-spec-public-goal-gzread"></a>[gzread](../ZlibF/Spec/Public/GzRead.lean#L22) | Not proved / Not proved | [Contract](../docs/api/gz-file.md#gzread); [input range](input-configurations.md#entry-inputs) | — | [Needs: reader path proofs](overview.md#readiness-gzdirect) |
| <a id="target-zlibf-spec-public-goal-gzfread"></a>[gzfread](../ZlibF/Spec/Public/GzRead.lean#L37) | Not proved / Not proved | [Contract](../docs/api/gz-file.md#gzfread); [input range](input-configurations.md#entry-inputs) | — | [Needs: reader path proofs](overview.md#readiness-gzdirect) |
| <a id="target-zlibf-spec-public-goal-gzgetc"></a>[gzgetc](../ZlibF/Spec/Public/GzRead.lean#L58) | Not proved / Not proved | [Contract](../docs/api/gz-file.md#gzgetc); [input range](input-configurations.md#entry-inputs) | — | [Needs: reader path proofs](overview.md#readiness-gzdirect) |
| <a id="target-zlibf-spec-public-goal-gzgetc"></a>[gzgetc_](../ZlibF/Spec/Public/GzRead.lean#L61) | Not proved / Not proved | [Contract](../docs/api/gz-file.md#gzgetc_); [input range](input-configurations.md#entry-inputs) | — | [Needs: reader path proofs](overview.md#readiness-gzdirect) |
| <a id="target-zlibf-spec-public-goal-gzungetc"></a>[gzungetc](../ZlibF/Spec/Public/GzRead.lean#L66) | Not proved / Not proved | [Contract](../docs/api/gz-file.md#gzungetc); [input range](input-configurations.md#entry-inputs) | — | [Needs: reader path proofs](overview.md#readiness-gzdirect) |
| <a id="target-zlibf-spec-public-goal-gzgets"></a>[gzgets](../ZlibF/Spec/Public/GzRead.lean#L80) | Not proved / Not proved | [Contract](../docs/api/gz-file.md#gzgets); [input range](input-configurations.md#entry-inputs) | — | [Needs: reader path proofs](overview.md#readiness-gzdirect) |
| <a id="target-zlibf-spec-public-goal-gzdirect"></a>[gzdirect](../ZlibF/Spec/Public/GzRead.lean#L103) | Not proved / Not proved | [Contract](../docs/api/gz-file.md#gzdirect); [input range](input-configurations.md#entry-inputs) | — | [Needs: reader path proofs](overview.md#readiness-gzdirect) |
| <a id="target-zlibf-spec-public-goal-gzwrite"></a>[gzwrite](../ZlibF/Spec/Public/GzWrite.lean#L28) | Not proved / Not proved | [Contract](../docs/api/gz-file.md#gzwrite); [input range](input-configurations.md#entry-inputs) | — | [Needs: writer path proofs](overview.md#readiness-gzwrite) |
| <a id="target-zlibf-spec-public-goal-gzfwrite"></a>[gzfwrite](../ZlibF/Spec/Public/GzWrite.lean#L43) | Not proved / Not proved | [Contract](../docs/api/gz-file.md#gzfwrite); [input range](input-configurations.md#entry-inputs) | — | [Needs: writer path proofs](overview.md#readiness-gzwrite) |
| <a id="target-zlibf-spec-public-goal-gzputc"></a>[gzputc](../ZlibF/Spec/Public/GzWrite.lean#L59) | Not proved / Not proved | [Contract](../docs/api/gz-file.md#gzputc); [input range](input-configurations.md#entry-inputs) | — | [Needs: writer path proofs](overview.md#readiness-gzwrite) |
| <a id="target-zlibf-spec-public-goal-gzputs"></a>[gzputs](../ZlibF/Spec/Public/GzWrite.lean#L71) | Not proved / Not proved | [Contract](../docs/api/gz-file.md#gzputs); [input range](input-configurations.md#entry-inputs) | — | [Needs: writer path proofs](overview.md#readiness-gzwrite) |
| <a id="target-zlibf-spec-public-goal-gzvprintf"></a>[gzvprintf](../ZlibF/Spec/Public/GzWrite.lean#L102) | Not proved / Not proved | [Contract](../docs/api/gz-file.md#gzvprintf); [input range](input-configurations.md#entry-inputs) | — | [Needs: writer path proofs](overview.md#readiness-gzwrite) |
| <a id="target-zlibf-spec-public-goal-gzprintf"></a>[gzprintf](../ZlibF/Spec/Public/GzWrite.lean#L106) | Not proved / Not proved | [Contract](../docs/api/gz-file.md#gzprintf); [input range](input-configurations.md#entry-inputs) | — | [Needs: writer path proofs](overview.md#readiness-gzwrite) |
| <a id="target-zlibf-spec-public-goal-gzflush"></a>[gzflush](../ZlibF/Spec/Public/GzWrite.lean#L111) | Not proved / Not proved | [Contract](../docs/api/gz-file.md#gzflush); [input range](input-configurations.md#entry-inputs) | — | [Needs: writer path proofs](overview.md#readiness-gzwrite) |
| <a id="target-zlibf-spec-public-goal-gzsetparams"></a>[gzsetparams](../ZlibF/Spec/Public/GzWrite.lean#L128) | Not proved / Not proved | [Contract](../docs/api/gz-file.md#gzsetparams); [input range](input-configurations.md#entry-inputs) | — | [Needs: writer path proofs](overview.md#readiness-gzwrite) |

<a id="group-buffers"></a>

## Whole-buffer operations

| Target statement | Coverage / evidence state | Contract / input range | Proof evidence | Reviewed next work |
| --- | --- | --- | --- | --- |
| <a id="target-zlibf-spec-public-goal-compress2-z"></a>[compress2_z](../ZlibF/Spec/Public/Utilities.lean#L40) | Not proved / Not proved | [Contract](../docs/api/utility.md#compress2_z); [input range](input-configurations.md#entry-inputs) | — | [Needs: compressor execution](overview.md#readiness-compress2-z) |
| <a id="target-zlibf-spec-public-goal-compress2"></a>[compress2](../ZlibF/Spec/Public/Utilities.lean#L45) | Not proved / Not proved | [Contract](../docs/api/utility.md#compress2); [input range](input-configurations.md#entry-inputs) | — | [Needs: compressor execution](overview.md#readiness-compress2-z) |
| <a id="target-zlibf-spec-public-goal-compress-z"></a>[compress_z](../ZlibF/Spec/Public/Utilities.lean#L52) | Not proved / Not proved | [Contract](../docs/api/utility.md#compress_z); [input range](input-configurations.md#entry-inputs) | — | [Needs: compressor execution](overview.md#readiness-compress2-z) |
| <a id="target-zlibf-spec-public-goal-compress"></a>[compress](../ZlibF/Spec/Public/Utilities.lean#L57) | Not proved / Not proved | [Contract](../docs/api/utility.md#compress); [input range](input-configurations.md#entry-inputs) | — | [Needs: compressor execution](overview.md#readiness-compress2-z) |
| <a id="target-zlibf-spec-public-goal-uncompress2-z"></a>[uncompress2_z](../ZlibF/Spec/Public/Utilities.lean#L103) | Not proved / Not proved | [Contract](../docs/api/utility.md#uncompress2_z); [input range](input-configurations.md#entry-inputs) | — | [Needs: decoder execution](overview.md#readiness-uncompress2-z) |
| <a id="target-zlibf-spec-public-goal-uncompress2"></a>[uncompress2](../ZlibF/Spec/Public/Utilities.lean#L107) | Not proved / Not proved | [Contract](../docs/api/utility.md#uncompress2); [input range](input-configurations.md#entry-inputs) | — | [Needs: decoder execution](overview.md#readiness-uncompress2-z) |
| <a id="target-zlibf-spec-public-goal-uncompress-z"></a>[uncompress_z](../ZlibF/Spec/Public/Utilities.lean#L132) | Not proved / Not proved | [Contract](../docs/api/utility.md#uncompress_z); [input range](input-configurations.md#entry-inputs) | — | [Needs: decoder execution](overview.md#readiness-uncompress2-z) |
| <a id="target-zlibf-spec-public-goal-uncompress"></a>[uncompress](../ZlibF/Spec/Public/Utilities.lean#L136) | Not proved / Not proved | [Contract](../docs/api/utility.md#uncompress); [input range](input-configurations.md#entry-inputs) | — | [Needs: decoder execution](overview.md#readiness-uncompress2-z) |

<a id="group-models"></a>

## Format and API models

| Target statement | Coverage / evidence state | Contract / input range | Proof evidence | Reviewed next work |
| --- | --- | --- | --- | --- |
| <a id="target-zlibf-spec-api-goal-format-deterministic"></a>[format_deterministic](../ZlibF/Spec/Api/Goals.lean#L42) | All stated inputs / Registered proof | Exact target statement; [input range](input-configurations.md#entry-inputs) | [ZlibF.Spec.Api.Proofs.format_deterministic](../ZlibF/Proof/Format/Api.lean#L51) | — |
| <a id="target-zlibf-spec-api-goal-format-prefix-free"></a>[format_prefix_free](../ZlibF/Spec/Api/Goals.lean#L47) | All stated inputs / Registered proof | Exact target statement; [input range](input-configurations.md#entry-inputs) | [ZlibF.Spec.Api.Proofs.format_prefix_free](../ZlibF/Proof/Format/Api.lean#L56) | — |
| <a id="target-zlibf-spec-api-goal-inflate-decodes"></a>[inflate_decodes](../ZlibF/Spec/Api/Goals.lean#L58) | All stated inputs / Registered proof | Exact target statement; [input range](input-configurations.md#entry-inputs) | [ZlibF.Spec.Api.Proofs.inflate_decodes](../ZlibF/Proof/Api/Inflate.lean#L346) | — |
| <a id="target-zlibf-spec-api-goal-inflate-completes"></a>[inflate_completes](../ZlibF/Spec/Api/Goals.lean#L69) | All stated inputs / Registered proof | Exact target statement; [input range](input-configurations.md#entry-inputs) | [ZlibF.Spec.Api.Proofs.inflate_completes](../ZlibF/Proof/Api/Inflate.lean#L353) | — |
| <a id="target-zlibf-spec-api-goal-inflate-rejects-invalid"></a>[inflate_rejects_invalid](../ZlibF/Spec/Api/Goals.lean#L84) | Not proved / Not proved | Exact target statement; [input range](input-configurations.md#entry-inputs) | — | Prerequisites unreviewed |
| <a id="target-zlibf-spec-api-goal-deflate-valid"></a>[deflate_valid](../ZlibF/Spec/Api/Goals.lean#L99) | All stated inputs / Registered proof | Exact target statement; [input range](input-configurations.md#entry-inputs) | [ZlibF.Spec.Api.Proofs.deflate_valid](../ZlibF/Proof/Api/Deflate.lean#L181) | — |
| <a id="target-zlibf-spec-api-goal-deflate-completes"></a>[deflate_completes](../ZlibF/Spec/Api/Goals.lean#L106) | All stated inputs / Registered proof | Exact target statement; [input range](input-configurations.md#entry-inputs) | [ZlibF.Spec.Api.Proofs.deflate_completes](../ZlibF/Proof/Api/DeflateBounds.lean#L164) | — |
| <a id="target-zlibf-spec-api-goal-deflate-full-flush-resync"></a>[deflate_full_flush_resync](../ZlibF/Spec/Api/Goals.lean#L116) | All stated inputs / Registered proof | Exact target statement; [input range](input-configurations.md#entry-inputs) | [ZlibF.Spec.Api.Proofs.deflate_full_flush_resync](../ZlibF/Proof/Api/DeflateFlush.lean#L169) | — |
| <a id="target-zlibf-spec-api-goal-roundtrip"></a>[roundtrip](../ZlibF/Spec/Api/Goals.lean#L134) | All stated inputs / Registered proof | Exact target statement; [input range](input-configurations.md#entry-inputs) | [ZlibF.Spec.Api.Proofs.roundtrip](../ZlibF/Proof/Api/GzipRoundtrip.lean#L177) | — |
| <a id="target-zlibf-spec-api-goal-roundtrip-completes"></a>[roundtrip_completes](../ZlibF/Spec/Api/Goals.lean#L143) | All stated inputs / Registered proof | Exact target statement; [input range](input-configurations.md#entry-inputs) | [ZlibF.Spec.Api.Proofs.roundtrip_completes](../ZlibF/Proof/Api/GzipRoundtrip.lean#L186) | — |
| <a id="target-zlibf-spec-api-goal-dict-roundtrip"></a>[dict_roundtrip](../ZlibF/Spec/Api/Goals.lean#L162) | All stated inputs / Locally checked | Exact target statement; [input range](input-configurations.md#entry-inputs) | [ZlibF.Spec.Api.Proofs.dict_roundtrip](../ZlibF/Proof/Api/DictionaryRoundtrip.lean#L121) | — |
| <a id="target-zlibf-spec-api-goal-header-roundtrip"></a>[header_roundtrip](../ZlibF/Spec/Api/Goals.lean#L180) | All stated inputs / Locally checked | Exact target statement; [input range](input-configurations.md#entry-inputs) | [ZlibF.Spec.Api.Proofs.header_roundtrip](../ZlibF/Proof/Api/HeaderRoundtrip.lean#L89) | — |
| <a id="target-zlibf-spec-api-goal-deflate-bound-adequate"></a>[deflate_bound_adequate](../ZlibF/Spec/Api/Goals.lean#L189) | All stated inputs / Registered proof | Exact target statement; [input range](input-configurations.md#entry-inputs) | [ZlibF.Spec.Api.Proofs.deflate_bound_adequate](../ZlibF/Proof/Api/DeflateBounds.lean#L103) | — |
| <a id="target-zlibf-spec-api-goal-compress-bound-adequate"></a>[compress_bound_adequate](../ZlibF/Spec/Api/Goals.lean#L196) | All stated inputs / Registered proof | Exact target statement; [input range](input-configurations.md#entry-inputs) | [ZlibF.Spec.Api.Proofs.compress_bound_adequate](../ZlibF/Proof/Api/Compress.lean#L8) | — |
| <a id="target-zlibf-spec-api-goal-compress-roundtrip"></a>[compress_roundtrip](../ZlibF/Spec/Api/Goals.lean#L203) | All stated inputs / Registered proof | Exact target statement; [input range](input-configurations.md#entry-inputs) | [ZlibF.Spec.Api.Proofs.compress_roundtrip](../ZlibF/Proof/Api/CompressRoundtrip.lean#L32) | — |
| <a id="target-zlibf-spec-api-goal-gz-roundtrip"></a>[gz_roundtrip](../ZlibF/Spec/Api/Goals.lean#L214) | All stated inputs / Registered proof | Exact target statement; [input range](input-configurations.md#entry-inputs) | [ZlibF.Spec.Api.Proofs.gz_roundtrip](../ZlibF/Proof/Api/GzRoundtrip.lean#L15) | — |
| <a id="target-zlibf-spec-api-goal-gz-seek-read"></a>[gz_seek_read](../ZlibF/Spec/Api/Goals.lean#L221) | Not proved / Blocked | Exact target statement; [input range](input-configurations.md#entry-inputs) | — [Blocker: Gzip seek mode](overview.md#gzip-seek-mode) | — |
| <a id="target-zlibf-spec-api-goal-compress-bound-value"></a>[compress_bound_value](../ZlibF/Spec/Api/Concrete.lean#L57) | All stated inputs / Registered proof | Exact target statement; [input range](input-configurations.md#entry-inputs) | [ZlibF.Spec.Api.Proofs.compress_bound_value](../ZlibF/Proof/Api/Concrete.lean#L57) | — |
| <a id="target-zlibf-spec-api-goal-compress2-z-first-alloc-failure"></a>[compress2_z_first_alloc_failure](../ZlibF/Spec/Api/Concrete.lean#L67) | All stated inputs / Registered proof | Exact target statement; [input range](input-configurations.md#entry-inputs) | [ZlibF.Spec.Api.Proofs.compress2_z_first_alloc_failure](../ZlibF/Proof/Api/CompressFailure.lean#L29) | — |
| <a id="target-zlibf-spec-api-goal-inflate-deferred-distance"></a>[inflate_deferred_distance](../ZlibF/Spec/Api/Inflate.lean#L267) | All stated inputs / Registered proof | Exact target statement; [input range](input-configurations.md#entry-inputs) | [ZlibF.Spec.Api.Proofs.inflate_deferred_distance](../ZlibF/Proof/Api/InflateCausality.lean#L244) | — |

<a id="group-lifecycle"></a>

## Lifecycles and call sequences

| Target statement | Coverage / evidence state | Contract / input range | Proof evidence | Reviewed next work |
| --- | --- | --- | --- | --- |
| <a id="target-zlibf-spec-public-goal-inflate-sequence"></a>[inflate_sequence](../ZlibF/Spec/Public/Sequences.lean#L158) | Not proved / Not proved | Exact target statement; [input range](input-configurations.md#inflate-inputs) | — | [Needs: execution and format](overview.md#readiness-inflate-sequence) |
| <a id="target-zlibf-spec-public-goal-deflate-sequence"></a>[deflate_sequence](../ZlibF/Spec/Public/Sequences.lean#L172) | Not proved / Not proved | Exact target statement; [input range](input-configurations.md#deflate-inputs) | — | [Needs: execution and format](overview.md#readiness-inflate-sequence) |
| <a id="target-zlibf-spec-public-goal-inflate-back-sequence"></a>[inflate_back_sequence](../ZlibF/Spec/Public/Sequences.lean#L199) | Not proved / Not proved | Exact target statement; [input range](input-configurations.md#entry-inputs) | — | [Needs: execution and format](overview.md#readiness-inflate-sequence) |
| <a id="target-zlibf-spec-public-goal-gz-sequence"></a>[gz_sequence](../ZlibF/Spec/Public/Sequences.lean#L211) | Not proved / Not proved | Exact target statement; [input range](input-configurations.md#entry-inputs) | — | [Needs: execution and format](overview.md#readiness-inflate-sequence) |
| <a id="target-zlibf-spec-public-goal-inflate-initialisation-domain"></a>[inflate_initialisation_domain](../ZlibF/Spec/Public/Domains.lean#L24) | All stated inputs / Registered proof | Exact target statement; [input range](input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.Proofs.InflateInit.inflate_initialisation_domain_public](../ZlibF/Proof/public-inflate-init.lean#L263) | — |
| <a id="target-zlibf-spec-public-goal-deflate-initialisation-domain"></a>[deflate_initialisation_domain](../ZlibF/Spec/Public/Domains.lean#L37) | Not proved / Not proved | Exact target statement; [input range](input-configurations.md#entry-inputs) | — | [Start: init and allocation](overview.md#readiness-deflateinit2) |
| <a id="target-zlibf-spec-public-goal-inflate-back-initialisation-domain"></a>[inflate_back_initialisation_domain](../ZlibF/Spec/Public/Domains.lean#L53) | All stated inputs / Registered proof | Exact target statement; [input range](input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.InflateBackInitProof.back_init_domain_public](../ZlibF/Proof/public-infback-init.lean#L230) | — |
| <a id="target-zlibf-spec-public-goal-gz-initialisation-domain"></a>[gz_initialisation_domain](../ZlibF/Spec/Public/Domains.lean#L77) | Not proved / Not proved | Exact target statement; [input range](input-configurations.md#entry-inputs) | — | [Start: open and cleanup](overview.md#readiness-gzopen) |

<a id="group-internal"></a>

## Internal proof obligations

| Target statement | Coverage / evidence state | Contract / input range | Proof evidence | Reviewed next work |
| --- | --- | --- | --- | --- |
| <a id="target-zlib-crc32-spec-byteviews-goal-crc32-z-all-byte-views"></a>[crc32_z_all_byte_views](../ZlibF/Spec/Crc32ByteViews.lean#L17) | All stated inputs / Registered proof | Exact target statement; [input range](input-configurations.md#entry-inputs) | [Zlib.Crc32.Proofs.crc32_z_all_byte_views](../ZlibF/Proof/crc32.c.views.lean#L567) | — |
| <a id="target-zlib-crc32-spec-byteviews-goal-crc32-all-byte-views"></a>[crc32_all_byte_views](../ZlibF/Spec/Crc32ByteViews.lean#L28) | All stated inputs / Registered proof | Exact target statement; [input range](input-configurations.md#entry-inputs) | [Zlib.Crc32.Proofs.crc32_all_byte_views](../ZlibF/Proof/crc32.c.views.lean#L573) | — |
| <a id="target-zlibf-spec-token-goal-rejected-has-no-symbols"></a>[rejected_has_no_symbols](../ZlibF/Spec/Format/Token.lean#L84) | All stated inputs / Locally checked | Exact target statement; [input range](input-configurations.md#entry-inputs) | [ZlibF.Spec.Token.rejected_has_no_symbols](../ZlibF/Proof/Format/Token.lean#L49) | — |
| <a id="target-zlibf-spec-token-goal-step-composes-symbols"></a>[step_composes_symbols](../ZlibF/Spec/Format/Token.lean#L62) | All stated inputs / Locally checked | Exact target statement; [input range](input-configurations.md#entry-inputs) | [ZlibF.Spec.Token.step_composes_symbols](../ZlibF/Proof/Format/Token.lean#L15) | — |
| <a id="target-zlibf-spec-token-goal-symbols-exposes-step"></a>[symbols_exposes_step](../ZlibF/Spec/Format/Token.lean#L73) | All stated inputs / Locally checked | Exact target statement; [input range](input-configurations.md#entry-inputs) | [ZlibF.Spec.Token.symbols_exposes_step](../ZlibF/Proof/Format/Token.lean#L35) | — |

## Observed proof dependencies

A theorem for the destination actually uses a proof of the source target.

| Source | Destination |
| --- | --- |
No references of this kind between fixed targets were observed in this snapshot.

## C function calls

The destination implementation calls the source entry. This does not require the complete source-entry contract as a proof premise.

| Source | Destination |
| --- | --- |
| [adler32](#target-zlibf-spec-public-goal-adler32) | [deflate](#target-zlibf-spec-public-goal-deflate) |
| [adler32](#target-zlibf-spec-public-goal-adler32) | [deflateResetKeep](#target-zlibf-spec-public-goal-deflateresetkeep) |
| [adler32](#target-zlibf-spec-public-goal-adler32) | [deflateSetDictionary](#target-zlibf-spec-public-goal-deflatesetdictionary) |
| [adler32](#target-zlibf-spec-public-goal-adler32) | [inflate](#target-zlibf-spec-public-goal-inflate) |
| [adler32](#target-zlibf-spec-public-goal-adler32) | [inflateSetDictionary](#target-zlibf-spec-public-goal-inflatesetdictionary) |
| [adler32_z](#target-zlibf-spec-public-goal-adler32-z) | [adler32](#target-zlibf-spec-public-goal-adler32) |
| [compress2](#target-zlibf-spec-public-goal-compress2) | [compress](#target-zlibf-spec-public-goal-compress) |
| [compress2_z](#target-zlibf-spec-public-goal-compress2-z) | [compress2](#target-zlibf-spec-public-goal-compress2) |
| [compress2_z](#target-zlibf-spec-public-goal-compress2-z) | [compress_z](#target-zlibf-spec-public-goal-compress-z) |
| [compressBound_z](#target-zlibf-spec-public-goal-compressbound-z) | [compressBound](#target-zlibf-spec-public-goal-compressbound) |
| [crc32](#target-zlibf-spec-public-goal-crc32) | [deflate](#target-zlibf-spec-public-goal-deflate) |
| [crc32](#target-zlibf-spec-public-goal-crc32) | [deflateResetKeep](#target-zlibf-spec-public-goal-deflateresetkeep) |
| [crc32](#target-zlibf-spec-public-goal-crc32) | [deflateSetDictionary](#target-zlibf-spec-public-goal-deflatesetdictionary) |
| [crc32](#target-zlibf-spec-public-goal-crc32) | [inflate](#target-zlibf-spec-public-goal-inflate) |
| [crc32_combine64](#target-zlibf-spec-public-goal-crc32-combine64) | [crc32_combine](#target-zlibf-spec-public-goal-crc32-combine) |
| [crc32_combine_gen64](#target-zlibf-spec-public-goal-crc32-combine-gen64) | [crc32_combine64](#target-zlibf-spec-public-goal-crc32-combine64) |
| [crc32_combine_gen64](#target-zlibf-spec-public-goal-crc32-combine-gen64) | [crc32_combine_gen](#target-zlibf-spec-public-goal-crc32-combine-gen) |
| [crc32_combine_op](#target-zlibf-spec-public-goal-crc32-combine-op) | [crc32_combine64](#target-zlibf-spec-public-goal-crc32-combine64) |
| [crc32_z](#target-zlibf-spec-public-goal-crc32-z) | [crc32](#target-zlibf-spec-public-goal-crc32) |
| [crc32_z](#target-zlibf-spec-public-goal-crc32-z) | [deflate](#target-zlibf-spec-public-goal-deflate) |
| [deflate](#target-zlibf-spec-public-goal-deflate) | [compress2_z](#target-zlibf-spec-public-goal-compress2-z) |
| [deflate](#target-zlibf-spec-public-goal-deflate) | [deflateParams](#target-zlibf-spec-public-goal-deflateparams) |
| [deflate](#target-zlibf-spec-public-goal-deflate) | [gzclose_w](#target-zlibf-spec-public-goal-gzclose-w) |
| [deflate](#target-zlibf-spec-public-goal-deflate) | [gzflush](#target-zlibf-spec-public-goal-gzflush) |
| [deflate](#target-zlibf-spec-public-goal-deflate) | [gzfwrite](#target-zlibf-spec-public-goal-gzfwrite) |
| [deflate](#target-zlibf-spec-public-goal-deflate) | [gzputc](#target-zlibf-spec-public-goal-gzputc) |
| [deflate](#target-zlibf-spec-public-goal-deflate) | [gzputs](#target-zlibf-spec-public-goal-gzputs) |
| [deflate](#target-zlibf-spec-public-goal-deflate) | [gzsetparams](#target-zlibf-spec-public-goal-gzsetparams) |
| [deflate](#target-zlibf-spec-public-goal-deflate) | [gzvprintf](#target-zlibf-spec-public-goal-gzvprintf) |
| [deflate](#target-zlibf-spec-public-goal-deflate) | [gzwrite](#target-zlibf-spec-public-goal-gzwrite) |
| [deflateBound_z](#target-zlibf-spec-public-goal-deflatebound-z) | [deflateBound](#target-zlibf-spec-public-goal-deflatebound) |
| [deflateEnd](#target-zlibf-spec-public-goal-deflateend) | [compress2_z](#target-zlibf-spec-public-goal-compress2-z) |
| [deflateEnd](#target-zlibf-spec-public-goal-deflateend) | [deflateInit2_](#target-zlibf-spec-public-goal-deflateinit2) |
| [deflateEnd](#target-zlibf-spec-public-goal-deflateend) | [gzclose_w](#target-zlibf-spec-public-goal-gzclose-w) |
| [deflateInit2_](#target-zlibf-spec-public-goal-deflateinit2) | [deflateInit_](#target-zlibf-spec-public-goal-deflateinit) |
| [deflateInit2_](#target-zlibf-spec-public-goal-deflateinit2) | [gzclose_w](#target-zlibf-spec-public-goal-gzclose-w) |
| [deflateInit2_](#target-zlibf-spec-public-goal-deflateinit2) | [gzflush](#target-zlibf-spec-public-goal-gzflush) |
| [deflateInit2_](#target-zlibf-spec-public-goal-deflateinit2) | [gzfwrite](#target-zlibf-spec-public-goal-gzfwrite) |
| [deflateInit2_](#target-zlibf-spec-public-goal-deflateinit2) | [gzputc](#target-zlibf-spec-public-goal-gzputc) |
| [deflateInit2_](#target-zlibf-spec-public-goal-deflateinit2) | [gzputs](#target-zlibf-spec-public-goal-gzputs) |
| [deflateInit2_](#target-zlibf-spec-public-goal-deflateinit2) | [gzsetparams](#target-zlibf-spec-public-goal-gzsetparams) |
| [deflateInit2_](#target-zlibf-spec-public-goal-deflateinit2) | [gzvprintf](#target-zlibf-spec-public-goal-gzvprintf) |
| [deflateInit2_](#target-zlibf-spec-public-goal-deflateinit2) | [gzwrite](#target-zlibf-spec-public-goal-gzwrite) |
| [deflateInit_](#target-zlibf-spec-public-goal-deflateinit) | [compress2_z](#target-zlibf-spec-public-goal-compress2-z) |
| [deflateParams](#target-zlibf-spec-public-goal-deflateparams) | [gzsetparams](#target-zlibf-spec-public-goal-gzsetparams) |
| [deflateReset](#target-zlibf-spec-public-goal-deflatereset) | [deflateInit2_](#target-zlibf-spec-public-goal-deflateinit2) |
| [deflateReset](#target-zlibf-spec-public-goal-deflatereset) | [gzclose_w](#target-zlibf-spec-public-goal-gzclose-w) |
| [deflateReset](#target-zlibf-spec-public-goal-deflatereset) | [gzflush](#target-zlibf-spec-public-goal-gzflush) |
| [deflateReset](#target-zlibf-spec-public-goal-deflatereset) | [gzfwrite](#target-zlibf-spec-public-goal-gzfwrite) |
| [deflateReset](#target-zlibf-spec-public-goal-deflatereset) | [gzputc](#target-zlibf-spec-public-goal-gzputc) |
| [deflateReset](#target-zlibf-spec-public-goal-deflatereset) | [gzputs](#target-zlibf-spec-public-goal-gzputs) |
| [deflateReset](#target-zlibf-spec-public-goal-deflatereset) | [gzsetparams](#target-zlibf-spec-public-goal-gzsetparams) |
| [deflateReset](#target-zlibf-spec-public-goal-deflatereset) | [gzvprintf](#target-zlibf-spec-public-goal-gzvprintf) |
| [deflateReset](#target-zlibf-spec-public-goal-deflatereset) | [gzwrite](#target-zlibf-spec-public-goal-gzwrite) |
| [deflateResetKeep](#target-zlibf-spec-public-goal-deflateresetkeep) | [deflateReset](#target-zlibf-spec-public-goal-deflatereset) |
| [gzclose_r](#target-zlibf-spec-public-goal-gzclose-r) | [gzclose](#target-zlibf-spec-public-goal-gzclose) |
| [gzclose_w](#target-zlibf-spec-public-goal-gzclose-w) | [gzclose](#target-zlibf-spec-public-goal-gzclose) |
| [gzgetc](#target-zlibf-spec-public-goal-gzgetc) | [gzgetc_](#target-zlibf-spec-public-goal-gzgetc) |
| [gzoffset64](#target-zlibf-spec-public-goal-gzoffset64) | [gzoffset](#target-zlibf-spec-public-goal-gzoffset) |
| [gzrewind](#target-zlibf-spec-public-goal-gzrewind) | [gzseek64](#target-zlibf-spec-public-goal-gzseek64) |
| [gzseek64](#target-zlibf-spec-public-goal-gzseek64) | [gzseek](#target-zlibf-spec-public-goal-gzseek) |
| [gztell64](#target-zlibf-spec-public-goal-gztell64) | [gztell](#target-zlibf-spec-public-goal-gztell) |
| [gzvprintf](#target-zlibf-spec-public-goal-gzvprintf) | [gzprintf](#target-zlibf-spec-public-goal-gzprintf) |
| [inflate](#target-zlibf-spec-public-goal-inflate) | [gzfread](#target-zlibf-spec-public-goal-gzfread) |
| [inflate](#target-zlibf-spec-public-goal-inflate) | [gzgetc](#target-zlibf-spec-public-goal-gzgetc) |
| [inflate](#target-zlibf-spec-public-goal-inflate) | [gzgets](#target-zlibf-spec-public-goal-gzgets) |
| [inflate](#target-zlibf-spec-public-goal-inflate) | [gzread](#target-zlibf-spec-public-goal-gzread) |
| [inflate](#target-zlibf-spec-public-goal-inflate) | [gzungetc](#target-zlibf-spec-public-goal-gzungetc) |
| [inflate](#target-zlibf-spec-public-goal-inflate) | [uncompress2_z](#target-zlibf-spec-public-goal-uncompress2-z) |
| [inflateEnd](#target-zlibf-spec-public-goal-inflateend) | [gzclose_r](#target-zlibf-spec-public-goal-gzclose-r) |
| [inflateEnd](#target-zlibf-spec-public-goal-inflateend) | [uncompress2_z](#target-zlibf-spec-public-goal-uncompress2-z) |
| [inflateInit2_](#target-zlibf-spec-public-goal-inflateinit2) | [gzdirect](#target-zlibf-spec-public-goal-gzdirect) |
| [inflateInit2_](#target-zlibf-spec-public-goal-inflateinit2) | [gzfread](#target-zlibf-spec-public-goal-gzfread) |
| [inflateInit2_](#target-zlibf-spec-public-goal-inflateinit2) | [gzgetc](#target-zlibf-spec-public-goal-gzgetc) |
| [inflateInit2_](#target-zlibf-spec-public-goal-inflateinit2) | [gzgets](#target-zlibf-spec-public-goal-gzgets) |
| [inflateInit2_](#target-zlibf-spec-public-goal-inflateinit2) | [gzread](#target-zlibf-spec-public-goal-gzread) |
| [inflateInit2_](#target-zlibf-spec-public-goal-inflateinit2) | [gzungetc](#target-zlibf-spec-public-goal-gzungetc) |
| [inflateInit2_](#target-zlibf-spec-public-goal-inflateinit2) | [inflateInit_](#target-zlibf-spec-public-goal-inflateinit) |
| [inflateInit_](#target-zlibf-spec-public-goal-inflateinit) | [uncompress2_z](#target-zlibf-spec-public-goal-uncompress2-z) |
| [inflateReset](#target-zlibf-spec-public-goal-inflatereset) | [gzdirect](#target-zlibf-spec-public-goal-gzdirect) |
| [inflateReset](#target-zlibf-spec-public-goal-inflatereset) | [gzfread](#target-zlibf-spec-public-goal-gzfread) |
| [inflateReset](#target-zlibf-spec-public-goal-inflatereset) | [gzgetc](#target-zlibf-spec-public-goal-gzgetc) |
| [inflateReset](#target-zlibf-spec-public-goal-inflatereset) | [gzgets](#target-zlibf-spec-public-goal-gzgets) |
| [inflateReset](#target-zlibf-spec-public-goal-inflatereset) | [gzread](#target-zlibf-spec-public-goal-gzread) |
| [inflateReset](#target-zlibf-spec-public-goal-inflatereset) | [gzungetc](#target-zlibf-spec-public-goal-gzungetc) |
| [inflateReset](#target-zlibf-spec-public-goal-inflatereset) | [inflateReset2](#target-zlibf-spec-public-goal-inflatereset2) |
| [inflateReset](#target-zlibf-spec-public-goal-inflatereset) | [inflateSync](#target-zlibf-spec-public-goal-inflatesync) |
| [inflateReset2](#target-zlibf-spec-public-goal-inflatereset2) | [inflateInit2_](#target-zlibf-spec-public-goal-inflateinit2) |
| [inflateResetKeep](#target-zlibf-spec-public-goal-inflateresetkeep) | [inflateReset](#target-zlibf-spec-public-goal-inflatereset) |
| [uncompress2](#target-zlibf-spec-public-goal-uncompress2) | [uncompress](#target-zlibf-spec-public-goal-uncompress) |
| [uncompress2_z](#target-zlibf-spec-public-goal-uncompress2-z) | [uncompress2](#target-zlibf-spec-public-goal-uncompress2) |
| [uncompress2_z](#target-zlibf-spec-public-goal-uncompress2-z) | [uncompress_z](#target-zlibf-spec-public-goal-uncompress-z) |
| [zError](#target-zlibf-spec-public-goal-zerror) | [deflate](#target-zlibf-spec-public-goal-deflate) |
| [zError](#target-zlibf-spec-public-goal-zerror) | [deflateInit2_](#target-zlibf-spec-public-goal-deflateinit2) |
| [zlibVersion](#target-zlibf-spec-public-goal-zlibversion) | [compress2_z](#target-zlibf-spec-public-goal-compress2-z) |

## Specification references

The destination target definition references the source target or implementation. This is not a proof dependency.

| Source | Destination |
| --- | --- |
| [compress2_z](#target-zlibf-spec-public-goal-compress2-z) | [compress2_z_first_alloc_failure](#target-zlibf-spec-api-goal-compress2-z-first-alloc-failure) |
| [compressBound](#target-zlibf-spec-public-goal-compressbound) | [compress_bound_value](#target-zlibf-spec-api-goal-compress-bound-value) |
| [compressBound_z](#target-zlibf-spec-public-goal-compressbound-z) | [compress_bound_value](#target-zlibf-spec-api-goal-compress-bound-value) |
| [crc32](#target-zlibf-spec-public-goal-crc32) | [crc32_all_byte_views](#target-zlib-crc32-spec-byteviews-goal-crc32-all-byte-views) |
| [crc32_z](#target-zlibf-spec-public-goal-crc32-z) | [crc32_z_all_byte_views](#target-zlib-crc32-spec-byteviews-goal-crc32-z-all-byte-views) |
| [deflateInit2_](#target-zlibf-spec-public-goal-deflateinit2) | [deflate_initialisation_domain](#target-zlibf-spec-public-goal-deflate-initialisation-domain) |
| [gzclose](#target-zlibf-spec-public-goal-gzclose) | [gz_sequence](#target-zlibf-spec-public-goal-gz-sequence) |
| [gzflush](#target-zlibf-spec-public-goal-gzflush) | [gz_sequence](#target-zlibf-spec-public-goal-gz-sequence) |
| [gzfread](#target-zlibf-spec-public-goal-gzfread) | [gz_sequence](#target-zlibf-spec-public-goal-gz-sequence) |
| [gzfwrite](#target-zlibf-spec-public-goal-gzfwrite) | [gz_sequence](#target-zlibf-spec-public-goal-gz-sequence) |
| [gzgetc](#target-zlibf-spec-public-goal-gzgetc) | [gz_sequence](#target-zlibf-spec-public-goal-gz-sequence) |
| [gzgets](#target-zlibf-spec-public-goal-gzgets) | [gz_sequence](#target-zlibf-spec-public-goal-gz-sequence) |
| [gzopen](#target-zlibf-spec-public-goal-gzopen) | [gz_initialisation_domain](#target-zlibf-spec-public-goal-gz-initialisation-domain) |
| [gzread](#target-zlibf-spec-public-goal-gzread) | [gz_sequence](#target-zlibf-spec-public-goal-gz-sequence) |
| [gzwrite](#target-zlibf-spec-public-goal-gzwrite) | [gz_sequence](#target-zlibf-spec-public-goal-gz-sequence) |
| [inflateBack](#target-zlibf-spec-public-goal-inflateback) | [inflate_back_sequence](#target-zlibf-spec-public-goal-inflate-back-sequence) |
| [inflateBackEnd](#target-zlibf-spec-public-goal-inflatebackend) | [inflate_back_sequence](#target-zlibf-spec-public-goal-inflate-back-sequence) |
| [inflateBackInit_](#target-zlibf-spec-public-goal-inflatebackinit) | [inflate_back_initialisation_domain](#target-zlibf-spec-public-goal-inflate-back-initialisation-domain) |
| [inflateInit2_](#target-zlibf-spec-public-goal-inflateinit2) | [inflate_initialisation_domain](#target-zlibf-spec-public-goal-inflate-initialisation-domain) |

## Other registered theorems

These declarations are registered supporting execution results, lemmas or witnesses.
They are not additional fixed targets and do not grant a caller coverage colour.

| Declaration | Used by a fixed-target proof |
| --- | --- |
| [Zlib.Adler32.Proofs.adler32_combine64_safe](../ZlibF/Proof/adler32.c.lean#L977) | No fixed-target composition recorded |
| [Zlib.Adler32.Proofs.adler32_combine_c_safe](../ZlibF/Proof/adler32.c.lean#L982) | No fixed-target composition recorded |
| [Zlib.Adler32.Proofs.adler32_combine_correct](../ZlibF/Proof/adler32.c.lean#L953) | No fixed-target composition recorded |
| [Zlib.Adler32.Proofs.adler32_combine_safe](../ZlibF/Proof/adler32.c.lean#L941) | No fixed-target composition recorded |
| [Zlib.Adler32.Proofs.adler32_safe](../ZlibF/Proof/adler32.c.lean#L987) | No fixed-target composition recorded |
| [Zlib.Adler32.Proofs.adler32_z_correct](../ZlibF/Proof/adler32.c.lean#L786) | No fixed-target composition recorded |
| [Zlib.Adler32.Proofs.adler32_z_correct_ne_one](../ZlibF/Proof/adler32.c.lean#L798) | No fixed-target composition recorded |
| [Zlib.Adler32.Proofs.adler32_z_safe](../ZlibF/Proof/adler32.c.lean#L809) | No fixed-target composition recorded |
| [Zlib.Crc32.Proofs.addrOf_safe](../ZlibF/Proof/crc32.c.lean#L2470) | No fixed-target composition recorded |
| [Zlib.Crc32.Proofs.blockLittle_safe](../ZlibF/Proof/crc32.c.lean#L2464) | No fixed-target composition recorded |
| [Zlib.Crc32.Proofs.braidTab_safe](../ZlibF/Proof/crc32.c.lean#L2460) | No fixed-target composition recorded |
| [Zlib.Crc32.Proofs.crc32_combine64_correct](../ZlibF/Proof/crc32.c.lean#L2383) | No fixed-target composition recorded |
| [Zlib.Crc32.Proofs.crc32_combine64_safe](../ZlibF/Proof/crc32.c.lean#L2377) | No fixed-target composition recorded |
| [Zlib.Crc32.Proofs.crc32_combine_correct](../ZlibF/Proof/crc32.c.lean#L2398) | No fixed-target composition recorded |
| [Zlib.Crc32.Proofs.crc32_combine_gen64_correct](../ZlibF/Proof/crc32.c.lean#L2334) | No fixed-target composition recorded |
| [Zlib.Crc32.Proofs.crc32_combine_gen64_safe](../ZlibF/Proof/crc32.c.lean#L2324) | No fixed-target composition recorded |
| [Zlib.Crc32.Proofs.crc32_combine_gen_correct](../ZlibF/Proof/crc32.c.lean#L2353) | No fixed-target composition recorded |
| [Zlib.Crc32.Proofs.crc32_combine_gen_safe](../ZlibF/Proof/crc32.c.lean#L2347) | No fixed-target composition recorded |
| [Zlib.Crc32.Proofs.crc32_combine_op_correct](../ZlibF/Proof/crc32.c.lean#L2406) | No fixed-target composition recorded |
| [Zlib.Crc32.Proofs.crc32_combine_op_diverges](../ZlibF/Proof/crc32.c.lean#L2371) | No fixed-target composition recorded |
| [Zlib.Crc32.Proofs.crc32_combine_op_safe](../ZlibF/Proof/crc32.c.lean#L2362) | No fixed-target composition recorded |
| [Zlib.Crc32.Proofs.crc32_combine_safe](../ZlibF/Proof/crc32.c.lean#L2393) | No fixed-target composition recorded |
| [Zlib.Crc32.Proofs.crc32_correct](../ZlibF/Proof/crc32.c.lean#L2227) | No fixed-target composition recorded |
| [Zlib.Crc32.Proofs.crc32_null](../ZlibF/Proof/crc32.c.lean#L2223) | No fixed-target composition recorded |
| [Zlib.Crc32.Proofs.crc32_safe](../ZlibF/Proof/crc32.c.lean#L2236) | No fixed-target composition recorded |
| [Zlib.Crc32.Proofs.crc32_z_correct](../ZlibF/Proof/crc32.c.lean#L2203) | No fixed-target composition recorded |
| [Zlib.Crc32.Proofs.crc32_z_null](../ZlibF/Proof/crc32.c.lean#L2190) | No fixed-target composition recorded |
| [Zlib.Crc32.Proofs.crc32_z_safe](../ZlibF/Proof/crc32.c.lean#L2217) | No fixed-target composition recorded |
| [Zlib.Crc32.Proofs.crcByte_safe](../ZlibF/Proof/crc32.c.lean#L2448) | No fixed-target composition recorded |
| [Zlib.Crc32.Proofs.crcTab_safe](../ZlibF/Proof/crc32.c.lean#L2439) | No fixed-target composition recorded |
| [Zlib.Crc32.Proofs.crc_word_big_safe](../ZlibF/Proof/crc32.c.lean#L2488) | No fixed-target composition recorded |
| [Zlib.Crc32.Proofs.crc_word_correct](../ZlibF/Proof/crc32.c.lean#L2422) | No fixed-target composition recorded |
| [Zlib.Crc32.Proofs.crc_word_safe](../ZlibF/Proof/crc32.c.lean#L2417) | No fixed-target composition recorded |
| [Zlib.Crc32.Proofs.get_crc_table_correct](../ZlibF/Proof/crc32.c.lean#L2249) | No fixed-target composition recorded |
| [Zlib.Crc32.Proofs.get_crc_table_safe](../ZlibF/Proof/crc32.c.lean#L2244) | No fixed-target composition recorded |
| [Zlib.Crc32.Proofs.loadWord_safe](../ZlibF/Proof/crc32.c.lean#L2434) | No fixed-target composition recorded |
| [Zlib.Crc32.Proofs.multmodp_correct](../ZlibF/Proof/crc32.c.lean#L2283) | No fixed-target composition recorded |
| [Zlib.Crc32.Proofs.multmodp_diverges](../ZlibF/Proof/crc32.c.lean#L986) | No fixed-target composition recorded |
| [Zlib.Crc32.Proofs.multmodp_safe](../ZlibF/Proof/crc32.c.lean#L2276) | No fixed-target composition recorded |
| [Zlib.Crc32.Proofs.shr64_safe](../ZlibF/Proof/crc32.c.lean#L2474) | No fixed-target composition recorded |
| [Zlib.Crc32.Proofs.wordAt_safe](../ZlibF/Proof/crc32.c.lean#L2455) | No fixed-target composition recorded |
| [Zlib.Crc32.Proofs.x2nTab_safe](../ZlibF/Proof/crc32.c.lean#L2443) | No fixed-target composition recorded |
| [Zlib.Crc32.Proofs.x2nmodp_correct](../ZlibF/Proof/crc32.c.lean#L2307) | No fixed-target composition recorded |
| [Zlib.Crc32.Proofs.x2nmodp_safe](../ZlibF/Proof/crc32.c.lean#L2299) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.INSERT_STRING_ok](../ZlibF/Proof/deflate.c.engine.macros.lean#L177) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.UPDATE_HASH_ok](../ZlibF/Proof/deflate.c.engine.macros.lean#L147) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.chain_ok_of_chains](../ZlibF/Proof/deflate.c.engine.chains.lean#L194) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.chains_insert](../ZlibF/Proof/deflate.c.engine.chains.lean#L76) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.chains_slide](../ZlibF/Proof/deflate.c.engine.chains.lean#L138) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.fill_fit](../ZlibF/Proof/deflate.c.engine.window.lean#L45) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.fill_post_room](../ZlibF/Proof/deflate.c.engine.window.lean#L40) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.form_init](../ZlibF/Proof/deflate.c.engine.hash.lean#L126) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.hkey_third](../ZlibF/Proof/deflate.c.engine.hash.lean#L139) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.lm_body_ok](../ZlibF/Proof/deflate.c.engine.lmbody.lean#L102) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.lm_inner_loop](../ZlibF/Proof/deflate.c.engine.lminner.lean#L36) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.lm_loop_ok](../ZlibF/Proof/deflate.c.engine.lmmain.lean#L77) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.longest_match_ok](../ZlibF/Proof/deflate.c.engine.lmmain.lean#L212) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.matchLen_agree](../ZlibF/Proof/deflate.c.engine.match.lean#L100) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.putShortMSB_ok](../ZlibF/Proof/deflate.c.engine.macros.lean#L119) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.put_byte_ok](../ZlibF/Proof/deflate.c.engine.macros.lean#L96) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.read_buf_ok](../ZlibF/Proof/deflate.c.engine.readbuf.lean#L99) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.read_buf_zero](../ZlibF/Proof/deflate.c.engine.readbuf.lean#L75) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.slide_copy](../ZlibF/Proof/deflate.c.engine.window.lean#L52) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.slide_hash_ok](../ZlibF/Proof/deflate.c.engine.slide.lean#L166) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.upd3_indep](../ZlibF/Proof/deflate.c.engine.hash.lean#L45) | No fixed-target composition recorded |
| [Zlib.Deflate.Proofs.deflateBound_nostate](../ZlibF/Proof/deflate.c.life.bound.lean#L330) | No fixed-target composition recorded |
| [Zlib.Deflate.Proofs.deflateBound_safe](../ZlibF/Proof/deflate.c.life.bound.lean#L319) | No fixed-target composition recorded |
| [Zlib.Deflate.Proofs.deflateBound_z_nostate](../ZlibF/Proof/deflate.c.life.bound.lean#L312) | No fixed-target composition recorded |
| [Zlib.Deflate.Proofs.deflateBound_z_safe](../ZlibF/Proof/deflate.c.life.bound.lean#L302) | No fixed-target composition recorded |
| [Zlib.Deflate.Proofs.deflateEnd_reject](../ZlibF/Proof/deflate.c.life.end.lean#L321) | No fixed-target composition recorded |
| [Zlib.Deflate.Proofs.deflateEnd_safe](../ZlibF/Proof/deflate.c.life.end.lean#L270) | No fixed-target composition recorded |
| [Zlib.Deflate.Proofs.deflatePending_reject](../ZlibF/Proof/deflate.c.life.check.lean#L173) | No fixed-target composition recorded |
| [Zlib.Deflate.Proofs.deflatePending_safe](../ZlibF/Proof/deflate.c.life.check.lean#L146) | No fixed-target composition recorded |
| [Zlib.Deflate.Proofs.deflatePrime_invalid_count](../ZlibF/Proof/deflate.c.prime.lean#L24) | No fixed-target composition recorded |
| [Zlib.Deflate.Proofs.deflatePrime_refused](../ZlibF/Proof/deflate.c.prime.lean#L15) | No fixed-target composition recorded |
| [Zlib.Deflate.Proofs.deflateResetKeep_reject](../ZlibF/Proof/deflate.c.life.reset.lean#L424) | No fixed-target composition recorded |
| [Zlib.Deflate.Proofs.deflateResetKeep_safe](../ZlibF/Proof/deflate.c.life.reset.lean#L367) | No fixed-target composition recorded |
| [Zlib.Deflate.Proofs.deflateReset_reject](../ZlibF/Proof/deflate.c.life.reset.lean#L430) | No fixed-target composition recorded |
| [Zlib.Deflate.Proofs.deflateReset_safe](../ZlibF/Proof/deflate.c.life.reset.lean#L401) | No fixed-target composition recorded |
| [Zlib.Deflate.Proofs.deflateSetHeader_not_gzip](../ZlibF/Proof/deflate.c.life.check.lean#L92) | No fixed-target composition recorded |
| [Zlib.Deflate.Proofs.deflateSetHeader_reject](../ZlibF/Proof/deflate.c.life.check.lean#L98) | No fixed-target composition recorded |
| [Zlib.Deflate.Proofs.deflateSetHeader_safe](../ZlibF/Proof/deflate.c.life.check.lean#L83) | No fixed-target composition recorded |
| [Zlib.Deflate.Proofs.deflateStateCheck_total](../ZlibF/Proof/deflate.c.base.lean#L731) | No fixed-target composition recorded |
| [Zlib.Deflate.Proofs.deflateTune_reject](../ZlibF/Proof/deflate.c.life.check.lean#L54) | No fixed-target composition recorded |
| [Zlib.Deflate.Proofs.deflateTune_safe](../ZlibF/Proof/deflate.c.life.check.lean#L44) | No fixed-target composition recorded |
| [Zlib.Deflate.Proofs.deflateUsed_reject](../ZlibF/Proof/deflate.c.life.check.lean#L119) | No fixed-target composition recorded |
| [Zlib.Deflate.Proofs.deflateUsed_safe](../ZlibF/Proof/deflate.c.life.check.lean#L113) | No fixed-target composition recorded |
| [Zlib.Deflate.Proofs.lm_init_safe](../ZlibF/Proof/deflate.c.life.reset.lean#L151) | No fixed-target composition recorded |
| [Zlib.Gzclose.Proofs.gzclose_dispatch](../ZlibF/Proof/gzclose.c.lean#L22) | No fixed-target composition recorded |
| [Zlib.Gzclose.Proofs.gzclose_null](../ZlibF/Proof/gzclose.c.lean#L17) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.GT_OFF_run](../ZlibF/Proof/gzlib.c.simple.lean#L46) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gz_error_null_run](../ZlibF/Proof/gzlib.c.error.lean#L134) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gz_intmax_run](../ZlibF/Proof/gzlib.c.simple.lean#L43) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gz_open_alloc_failure](../ZlibF/Proof/gzlib.c.open.lean#L35) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gz_open_null](../ZlibF/Proof/gzlib.c.open.lean#L17) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gz_reset_run](../ZlibF/Proof/gzlib.c.error.lean#L145) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gz_reset_safe](../ZlibF/Proof/gzlib.c.error.lean#L168) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gzbuffer_null](../ZlibF/Proof/gzlib.c.simple.lean#L52) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gzbuffer_run](../ZlibF/Proof/gzlib.c.simple.lean#L67) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gzbuffer_safe](../ZlibF/Proof/gzlib.c.simple.lean#L84) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gzclearerr_null](../ZlibF/Proof/gzlib.c.simple.lean#L191) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gzclearerr_run](../ZlibF/Proof/gzlib.c.simple.lean#L199) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gzclearerr_safe](../ZlibF/Proof/gzlib.c.simple.lean#L210) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gzdopen_alloc_failure](../ZlibF/Proof/gzlib.c.open.lean#L61) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gzdopen_negative](../ZlibF/Proof/gzlib.c.open.lean#L54) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gzeof_null](../ZlibF/Proof/gzlib.c.simple.lean#L108) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gzeof_run](../ZlibF/Proof/gzlib.c.simple.lean#L111) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gzerror_null_file](../ZlibF/Proof/gzlib.c.simple.lean#L159) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gzerror_run](../ZlibF/Proof/gzlib.c.simple.lean#L163) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gzoffset64_null](../ZlibF/Proof/gzlib.c.rewind.lean#L110) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gzoffset64_run](../ZlibF/Proof/gzlib.c.rewind.lean#L114) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gzoffset_eq](../ZlibF/Proof/gzlib.c.rewind.lean#L136) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gzopen64_alloc_failure](../ZlibF/Proof/gzlib.c.open.lean#L48) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gzopen64_null](../ZlibF/Proof/gzlib.c.open.lean#L29) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gzopen_alloc_failure](../ZlibF/Proof/gzlib.c.open.lean#L42) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gzopen_null](../ZlibF/Proof/gzlib.c.open.lean#L24) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gzrewind_null](../ZlibF/Proof/gzlib.c.rewind.lean#L80) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gzrewind_spec](../ZlibF/Proof/gzlib.c.rewind.lean#L85) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gzseek64_cur_negpos_ub](../ZlibF/Proof/gzlib.c.seek.lean#L867) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gzseek64_dangling_next_ub](../ZlibF/Proof/gzlib.c.seek.lean#L952) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gzseek64_head](../ZlibF/Proof/gzlib.c.seek.lean#L177) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gzseek64_null](../ZlibF/Proof/gzlib.c.seek.lean#L805) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gzseek64_refuse](../ZlibF/Proof/gzlib.c.seek.lean#L837) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gzseek64_safe](../ZlibF/Proof/gzlib.c.seek.lean#L812) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gzseek64_set_negpos_ub](../ZlibF/Proof/gzlib.c.seek.lean#L889) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gzseek64_write_run](../ZlibF/Proof/gzlib.c.seek.lean#L232) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gzseek_eq](../ZlibF/Proof/gzlib.c.seek.lean#L850) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gztell64_null](../ZlibF/Proof/gzlib.c.simple.lean#L122) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gztell64_spec](../ZlibF/Proof/gzlib.c.simple.lean#L143) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gztell_null](../ZlibF/Proof/gzlib.c.simple.lean#L154) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gztell_run](../ZlibF/Proof/gzlib.c.simple.lean#L148) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.seekTail_back](../ZlibF/Proof/gzlib.c.seek.lean#L475) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.seekTail_copy](../ZlibF/Proof/gzlib.c.seek.lean#L315) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.seekTail_copy_ub](../ZlibF/Proof/gzlib.c.seek.lean#L962) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.seekTail_dangling_ub](../ZlibF/Proof/gzlib.c.seek.lean#L919) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.seekTail_fwd](../ZlibF/Proof/gzlib.c.seek.lean#L376) | No fixed-target composition recorded |
| [Zlib.Gzread.Proofs.gzclose_r_null](../ZlibF/Proof/gzread.c.close.lean#L43) | No fixed-target composition recorded |
| [Zlib.Gzread.Proofs.gzclose_r_unbuffered](../ZlibF/Proof/gzread.c.close.lean#L56) | No fixed-target composition recorded |
| [Zlib.Gzread.Proofs.gzclose_r_unbuffered_frame](../ZlibF/Proof/gzread.c.close.lean#L78) | No fixed-target composition recorded |
| [Zlib.Gzread.Proofs.gzclose_r_wrong_mode](../ZlibF/Proof/gzread.c.close.lean#L47) | No fixed-target composition recorded |
| [Zlib.Infback.Proofs.NEEDBITS_run](../ZlibF/Proof/infback.c.macros.lean#L240) | No fixed-target composition recorded |
| [Zlib.Infback.Proofs.PULLBYTE_run](../ZlibF/Proof/infback.c.macros.lean#L156) | No fixed-target composition recorded |
| [Zlib.Infback.Proofs.PULL_run](../ZlibF/Proof/infback.c.pull.lean#L16) | No fixed-target composition recorded |
| [Zlib.Infback.Proofs.ROOM_inv](../ZlibF/Proof/infback.c.stored.lean#L35) | No fixed-target composition recorded |
| [Zlib.Infback.Proofs.ROOM_run](../ZlibF/Proof/infback.c.room.lean#L27) | No fixed-target composition recorded |
| [Zlib.Infback.Proofs.TYPE_last](../ZlibF/Proof/infback.c.inv.lean#L87) | No fixed-target composition recorded |
| [Zlib.Infback.Proofs.TYPE_more](../ZlibF/Proof/infback.c.inv.lean#L145) | No fixed-target composition recorded |
| [Zlib.Infback.Proofs.backInit_witness](../ZlibF/Proof/infback.c.callbacks.lean#L143) | No fixed-target composition recorded |
| [Zlib.Infback.Proofs.badMode_run](../ZlibF/Proof/infback.c.inv.lean#L127) | No fixed-target composition recorded |
| [Zlib.Infback.Proofs.inFinite_eof](../ZlibF/Proof/infback.c.macros.lean#L304) | No fixed-target composition recorded |
| [Zlib.Infback.Proofs.inflateBackEnd_nullstream](../ZlibF/Proof/infback.c.end.lean#L23) | No fixed-target composition recorded |
| [Zlib.Infback.Proofs.inflateBackEnd_ok](../ZlibF/Proof/infback.c.end.lean#L35) | No fixed-target composition recorded |
| [Zlib.Infback.Proofs.inflateBackEnd_refused](../ZlibF/Proof/infback.c.end.lean#L27) | No fixed-target composition recorded |
| [Zlib.Infback.Proofs.inflateBackInit__nullstream](../ZlibF/Proof/infback.c.init.lean#L239) | No fixed-target composition recorded |
| [Zlib.Infback.Proofs.inflateBackInit__ok](../ZlibF/Proof/infback.c.init.lean#L147) | No fixed-target composition recorded |
| [Zlib.Infback.Proofs.inflateBackInit__safe](../ZlibF/Proof/infback.c.init.lean#L203) | No fixed-target composition recorded |
| [Zlib.Infback.Proofs.inflateBack_eof](../ZlibF/Proof/infback.c.back.lean#L133) | No fixed-target composition recorded |
| [Zlib.Infback.Proofs.inflateBack_eof_witness](../ZlibF/Proof/infback.c.back.lean#L174) | No fixed-target composition recorded |
| [Zlib.Infback.Proofs.inflateBack_nostate](../ZlibF/Proof/infback.c.back.lean#L123) | No fixed-target composition recorded |
| [Zlib.Infback.Proofs.inflateBack_nullstream](../ZlibF/Proof/infback.c.back.lean#L118) | No fixed-target composition recorded |
| [Zlib.Infback.Proofs.order_inj](../ZlibF/Proof/infback.c.pure.lean#L17) | No fixed-target composition recorded |
| [Zlib.Infback.Proofs.order_lt](../ZlibF/Proof/infback.c.pure.lean#L14) | No fixed-target composition recorded |
| [Zlib.Infback.Proofs.order_surj](../ZlibF/Proof/infback.c.pure.lean#L21) | No fixed-target composition recorded |
| [Zlib.Infback.Proofs.storedTail_run](../ZlibF/Proof/infback.c.stored.lean#L125) | No fixed-target composition recorded |
| [Zlib.Infback.Proofs.stored_body_run](../ZlibF/Proof/infback.c.stored.lean#L285) | No fixed-target composition recorded |
| [Zlib.Infback.Proofs.stored_check](../ZlibF/Proof/infback.c.pure.lean#L35) | No fixed-target composition recorded |
| [Zlib.Infback.Proofs.stored_len_toNat](../ZlibF/Proof/infback.c.pure.lean#L58) | No fixed-target composition recorded |
| [Zlib.Infback.Proofs.stored_loop_run](../ZlibF/Proof/infback.c.stored.lean#L406) | No fixed-target composition recorded |
| [Zlib.Infback.Proofs.stored_run](../ZlibF/Proof/infback.c.stored.lean#L459) | No fixed-target composition recorded |
| [Zlib.Infback.Proofs.xwhileBrk_wf](../ZlibF/Proof/infback.c.wf.lean#L16) | No fixed-target composition recorded |
| [Zlib.Inffast.Proofs.distfix_tableSafe](../ZlibF/Proof/inffast.c.tableok.lean#L82) | No fixed-target composition recorded |
| [Zlib.Inffast.Proofs.lenfix_tableSafe](../ZlibF/Proof/inffast.c.tableok.lean#L75) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.BITS_run](../ZlibF/Proof/inflate.c.main.macros.lean#L224) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.BITS_toNat](../ZlibF/Proof/inflate.c.main.macros.lean#L234) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.BYTEBITS_inv](../ZlibF/Proof/inflate.c.main.macros.lean#L293) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.BYTEBITS_run](../ZlibF/Proof/inflate.c.main.macros.lean#L283) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.DROPBITS_inv](../ZlibF/Proof/inflate.c.main.macros.lean#L251) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.DROPBITS_run](../ZlibF/Proof/inflate.c.main.macros.lean#L241) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.INITBITS_inv](../ZlibF/Proof/inflate.c.main.macros.lean#L304) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.NEEDBITS_run](../ZlibF/Proof/inflate.c.main.macros.lean#L150) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.PULLBYTE_succ](../ZlibF/Proof/inflate.c.main.macros.lean#L89) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.PULLBYTE_zero](../ZlibF/Proof/inflate.c.main.macros.lean#L44) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.UPDATE_CHECK_run](../ZlibF/Proof/inflate.c.main.check.lean#L21) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.bytesBits_eq_bytesToBits](../ZlibF/Proof/inflate.c.main.bits.lean#L107) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflateCodesUsed_spec](../ZlibF/Proof/inflate.c.misc.lean#L180) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflateEnd_safe](../ZlibF/Proof/inflate.c.end.lean#L119) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflateGetDictionary_spec](../ZlibF/Proof/inflate.c.dict.lean#L82) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflateGetHeader_check](../ZlibF/Proof/inflate.c.hdr.lean#L54) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflateGetHeader_nogzip](../ZlibF/Proof/inflate.c.hdr.lean#L64) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflateGetHeader_null_faults](../ZlibF/Proof/inflate.c.hdr.lean#L114) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflateGetHeader_ok](../ZlibF/Proof/inflate.c.hdr.lean#L80) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflateInit2_ok](../ZlibF/Proof/inflate.c.start.lean#L237) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflateInit2_safe](../ZlibF/Proof/inflate.c.start.lean#L324) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflateInit__ok](../ZlibF/Proof/inflate.c.hdr.lean#L160) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflateInit__safe](../ZlibF/Proof/inflate.c.hdr.lean#L134) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflateMark_spec](../ZlibF/Proof/inflate.c.misc.lean#L140) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflatePrime_spec](../ZlibF/Proof/inflate.c.misc2.lean#L28) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflateReset2_safe](../ZlibF/Proof/inflate.c.init.lean#L395) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflateResetKeep_safe](../ZlibF/Proof/inflate.c.base.lean#L521) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflateReset_safe](../ZlibF/Proof/inflate.c.reset.lean#L160) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflateSetDictionary_dataerr](../ZlibF/Proof/inflate.c.dict.lean#L222) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflateSetDictionary_safe](../ZlibF/Proof/inflate.c.dict.lean#L146) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflateSetDictionary_streamerr](../ZlibF/Proof/inflate.c.dict.lean#L209) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflateStateCheck_total](../ZlibF/Proof/inflate.c.base.lean#L445) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflateSyncPoint_spec](../ZlibF/Proof/inflate.c.misc.lean#L121) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflateSync_buf_error](../ZlibF/Proof/inflate.c.sync2.lean#L131) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflateSync_check](../ZlibF/Proof/inflate.c.sync2.lean#L113) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflateUndermine_safe](../ZlibF/Proof/inflate.c.misc.lean#L109) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflateValidate_safe](../ZlibF/Proof/inflate.c.misc.lean#L95) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflate_CHECK_nowrap](../ZlibF/Proof/inflate.c.main.check.lean#L137) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflate_CHECK_run](../ZlibF/Proof/inflate.c.main.check.lean#L157) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflate_COPY__eq](../ZlibF/Proof/inflate.c.main.stored2.lean#L82) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflate_COPY_done](../ZlibF/Proof/inflate.c.main.stored.lean#L22) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflate_COPY_leave](../ZlibF/Proof/inflate.c.main.stored2.lean#L75) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflate_COPY_run](../ZlibF/Proof/inflate.c.main.stored2.lean#L57) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflate_DONE_run](../ZlibF/Proof/inflate.c.main.simple.lean#L25) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflate_LENGTH_run](../ZlibF/Proof/inflate.c.main.check.lean#L80) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflate_LENGTH_skip](../ZlibF/Proof/inflate.c.main.check.lean#L66) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflate_LENLENS_eq](../ZlibF/Proof/inflate.c.main.table3.lean#L77) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflate_LENLENS_run](../ZlibF/Proof/inflate.c.main.table6.lean#L41) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflate_LIT_full](../ZlibF/Proof/inflate.c.main.simple.lean#L29) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflate_LIT_run](../ZlibF/Proof/inflate.c.main.simple.lean#L37) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflate_STORED_bad](../ZlibF/Proof/inflate.c.main.stored2.lean#L97) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflate_STORED_ok](../ZlibF/Proof/inflate.c.main.stored2.lean#L116) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflate_STORED_wait](../ZlibF/Proof/inflate.c.main.stored2.lean#L88) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflate_TABLE_run](../ZlibF/Proof/inflate.c.main.table.lean#L52) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflate_TYPEDO_head](../ZlibF/Proof/inflate.c.main.type.lean#L61) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflate_TYPEDO_last](../ZlibF/Proof/inflate.c.main.type.lean#L26) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflate_TYPEDO_wait](../ZlibF/Proof/inflate.c.main.type.lean#L37) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflate_TYPE_go](../ZlibF/Proof/inflate.c.main.type.lean#L19) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflate_TYPE_leave](../ZlibF/Proof/inflate.c.main.type.lean#L11) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.ll1_run](../ZlibF/Proof/inflate.c.main.table4.lean#L69) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.llBody_run](../ZlibF/Proof/inflate.c.main.table3.lean#L90) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.llTail_run](../ZlibF/Proof/inflate.c.main.table5.lean#L46) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.lzBody_run](../ZlibF/Proof/inflate.c.main.table4.lean#L225) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.lz_run](../ZlibF/Proof/inflate.c.main.table4.lean#L244) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.noRet_NEEDBITS](../ZlibF/Proof/inflate.c.main.table2.lean#L321) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.ring_spec](../ZlibF/Proof/inflate.c.ring.lean#L116) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.syncDone_good](../ZlibF/Proof/inflate.c.sync2.lean#L372) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.syncDone_owns](../ZlibF/Proof/inflate.c.sync2.lean#L423) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.syncDone_run](../ZlibF/Proof/inflate.c.sync2.lean#L248) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.syncScan_found_iff](../ZlibF/Proof/inflate.c.sync.lean#L342) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.syncScan_spec](../ZlibF/Proof/inflate.c.sync.lean#L300) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.syncStep_spec](../ZlibF/Proof/inflate.c.sync.lean#L202) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.syncTail_run](../ZlibF/Proof/inflate.c.sync2.lean#L543) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.syncsearch_null](../ZlibF/Proof/inflate.c.sync.lean#L450) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.syncsearch_run](../ZlibF/Proof/inflate.c.sync.lean#L381) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.syncsearch_spec](../ZlibF/Proof/inflate.c.sync.lean#L485) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.typedoTail_bad](../ZlibF/Proof/inflate.c.main.type.lean#L154) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.typedoTail_fixed](../ZlibF/Proof/inflate.c.main.type.lean#L116) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.typedoTail_fixed_trees](../ZlibF/Proof/inflate.c.main.type.lean#L132) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.typedoTail_stored](../ZlibF/Proof/inflate.c.main.type.lean#L92) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.typedoTail_table](../ZlibF/Proof/inflate.c.main.type.lean#L104) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.updatewindow_ring](../ZlibF/Proof/inflate.c.ring.lean#L197) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.updatewindow_safe](../ZlibF/Proof/inflate.c.uw.lean#L558) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.uwPost_counts](../ZlibF/Proof/inflate.c.ring.lean#L170) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.uw_null_ok](../ZlibF/Proof/inflate.c.uw.lean#L492) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.uw_post](../ZlibF/Proof/inflate.c.uw.lean#L423) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.xwhileBrk_run](../ZlibF/Proof/inflate.c.main.xloop.lean#L36) | No fixed-target composition recorded |
| [Zlib.Inflate.Witness.init_witness](../ZlibF/Proof/inflate.c.witness.lean#L50) | No fixed-target composition recorded |
| [Zlib.Inftrees.Proofs.Cover.bits_add_drop](../ZlibF/Proof/inftrees.c.cover.leaf.lean#L80) | No fixed-target composition recorded |
| [Zlib.Inftrees.Proofs.Cover.cell_lt_fn](../ZlibF/Proof/inftrees.c.cover.fn.lean#L210) | No fixed-target composition recorded |
| [Zlib.Inftrees.Proofs.Cover.distLeaf_of](../ZlibF/Proof/inftrees.c.cover.leaf.lean#L56) | No fixed-target composition recorded |
| [Zlib.Inftrees.Proofs.Cover.group_cover](../ZlibF/Proof/inftrees.c.cover.group.lean#L64) | No fixed-target composition recorded |
| [Zlib.Inftrees.Proofs.Cover.group_cover_fn](../ZlibF/Proof/inftrees.c.cover.fn.lean#L163) | No fixed-target composition recorded |
| [Zlib.Inftrees.Proofs.Cover.group_cover_idx](../ZlibF/Proof/inftrees.c.cover.group.lean#L161) | No fixed-target composition recorded |
| [Zlib.Inftrees.Proofs.Cover.group_cover_idx_fn](../ZlibF/Proof/inftrees.c.cover.fn.lean#L185) | No fixed-target composition recorded |
| [Zlib.Inftrees.Proofs.Cover.invalid_leaf](../ZlibF/Proof/inftrees.c.cover.leaf.lean#L66) | No fixed-target composition recorded |
| [Zlib.Inftrees.Proofs.Cover.lenLeaf_of](../ZlibF/Proof/inftrees.c.cover.leaf.lean#L40) | No fixed-target composition recorded |
| [Zlib.Inftrees.Proofs.Cover.root_cover](../ZlibF/Proof/inftrees.c.cover.root.lean#L90) | No fixed-target composition recorded |
| [Zlib.Inftrees.Proofs.Cover.root_cover_complete_fn](../ZlibF/Proof/inftrees.c.cover.fn.lean#L140) | No fixed-target composition recorded |
| [Zlib.Inftrees.Proofs.Cover.root_cover_fn](../ZlibF/Proof/inftrees.c.cover.fn.lean#L130) | No fixed-target composition recorded |
| [Zlib.Inftrees.Proofs.Cover.root_single_fn](../ZlibF/Proof/inftrees.c.cover.fn.lean#L226) | No fixed-target composition recorded |
| [Zlib.Inftrees.Proofs.inflate_fixed_ok](../ZlibF/Proof/inftrees.c.fixed.lean#L21) | No fixed-target composition recorded |
| [Zlib.Inftrees.Proofs.inflate_table_correct_ret](../ZlibF/Proof/inftrees.c.lean#L65) | No fixed-target composition recorded |
| [Zlib.Inftrees.Proofs.inflate_table_safe](../ZlibF/Proof/inftrees.c.lean#L34) | No fixed-target composition recorded |
| [Zlib.Trees.Proofs.GB.kraft_clamped](../ZlibF/Proof/trees.c.heap.gbtree.lean#L132) | No fixed-target composition recorded |
| [Zlib.Trees.Proofs.Out.bi_flush_spec](../ZlibF/Proof/trees.c.bits.lean#L548) | No fixed-target composition recorded |
| [Zlib.Trees.Proofs.Out.bi_reverse_correct](../ZlibF/Proof/trees.c.reverse.lean#L91) | No fixed-target composition recorded |
| [Zlib.Trees.Proofs.Out.bi_reverse_safe](../ZlibF/Proof/trees.c.reverse.lean#L51) | No fixed-target composition recorded |
| [Zlib.Trees.Proofs.Out.bi_windup_spec](../ZlibF/Proof/trees.c.bits.lean#L731) | No fixed-target composition recorded |
| [Zlib.Trees.Proofs.Out.init_block_spec](../ZlibF/Proof/trees.c.block.lean#L217) | No fixed-target composition recorded |
| [Zlib.Trees.Proofs.Out.init_block_spec0](../ZlibF/Proof/trees.c.block.lean#L102) | No fixed-target composition recorded |
| [Zlib.Trees.Proofs.Out.send_bits_spec](../ZlibF/Proof/trees.c.bits.lean#L411) | No fixed-target composition recorded |
| [Zlib.Trees.Proofs.Out.tr_align_emit](../ZlibF/Proof/trees.c.align.lean#L42) | No fixed-target composition recorded |
| [Zlib.Trees.Proofs.Out.tr_flush_bits_emit](../ZlibF/Proof/trees.c.align.lean#L30) | No fixed-target composition recorded |
| [Zlib.Trees.Proofs.Out.tr_init_spec](../ZlibF/Proof/trees.c.block.lean#L245) | No fixed-target composition recorded |
| [Zlib.Trees.Proofs.Out.tr_tally_spec](../ZlibF/Proof/trees.c.tally.lean#L327) | No fixed-target composition recorded |
| [Zlib.Trees.Proofs.gen_bitlen_correct](../ZlibF/Proof/trees.c.heap.gbtop.lean#L403) | No fixed-target composition recorded |
| [Zlib.Trees.Proofs.gen_bitlen_safe](../ZlibF/Proof/trees.c.heap.gbtop.lean#L421) | No fixed-target composition recorded |
| [Zlib.Trees.Proofs.pqdownheap_correct](../ZlibF/Proof/trees.c.heap.pqrun.lean#L313) | No fixed-target composition recorded |
| [Zlib.Trees.Proofs.pqdownheap_safe](../ZlibF/Proof/trees.c.heap.pqrun.lean#L330) | No fixed-target composition recorded |
| [Zlib.Trees.Proofs.pqremove_correct](../ZlibF/Proof/trees.c.heap.pqrun.lean#L342) | No fixed-target composition recorded |
| [Zlib.Trees.Proofs.pqremove_safe](../ZlibF/Proof/trees.c.heap.pqrun.lean#L359) | No fixed-target composition recorded |
| [Zlib.Zutil.Proofs.zError_correct](../ZlibF/Proof/zutil.c.lean#L121) | No fixed-target composition recorded |
| [Zlib.Zutil.Proofs.zError_safe](../ZlibF/Proof/zutil.c.lean#L113) | No fixed-target composition recorded |
| [Zlib.Zutil.Proofs.zcalloc_correct_none](../ZlibF/Proof/zutil.c.lean#L265) | No fixed-target composition recorded |
| [Zlib.Zutil.Proofs.zcalloc_correct_size](../ZlibF/Proof/zutil.c.lean#L256) | No fixed-target composition recorded |
| [Zlib.Zutil.Proofs.zcalloc_correct_some](../ZlibF/Proof/zutil.c.lean#L242) | No fixed-target composition recorded |
| [Zlib.Zutil.Proofs.zcalloc_safe](../ZlibF/Proof/zutil.c.lean#L228) | No fixed-target composition recorded |
| [Zlib.Zutil.Proofs.zcalloc_zcfree_no_leak](../ZlibF/Proof/zutil.c.lean#L310) | No fixed-target composition recorded |
| [Zlib.Zutil.Proofs.zcfree_correct](../ZlibF/Proof/zutil.c.lean#L284) | No fixed-target composition recorded |
| [Zlib.Zutil.Proofs.zcfree_correct_null](../ZlibF/Proof/zutil.c.lean#L302) | No fixed-target composition recorded |
| [Zlib.Zutil.Proofs.zcfree_safe](../ZlibF/Proof/zutil.c.lean#L274) | No fixed-target composition recorded |
| [Zlib.Zutil.Proofs.zlibCompileFlags_correct](../ZlibF/Proof/zutil.c.lean#L169) | No fixed-target composition recorded |
| [Zlib.Zutil.Proofs.zlibCompileFlags_safe](../ZlibF/Proof/zutil.c.lean#L163) | No fixed-target composition recorded |
| [Zlib.Zutil.Proofs.zlibVersion_correct](../ZlibF/Proof/zutil.c.lean#L153) | No fixed-target composition recorded |
| [Zlib.Zutil.Proofs.zlibVersion_safe](../ZlibF/Proof/zutil.c.lean#L130) | No fixed-target composition recorded |
| [ZlibF.Spec.Api.Proofs.Layer.ext](../ZlibF/Proof/Format/Api.lean) | No fixed-target composition recorded |
| [ZlibF.Spec.Api.Proofs.inflate_deferred_distance_rejects_legacy_consistency](../ZlibF/Proof/Api/InflateCausality.lean#L229) | No fixed-target composition recorded |
| [ZlibF.Spec.Blocks.append](../ZlibF/Proof/Format/Deflate.lean) | No fixed-target composition recorded |
| [ZlibF.Spec.Blocks.det](../ZlibF/Proof/Format/Deflate.lean) | No fixed-target composition recorded |
| [ZlibF.Spec.Gzip.ext](../ZlibF/Proof/Format/Wrapper.lean) | No fixed-target composition recorded |
| [ZlibF.Spec.Prefix.det](../ZlibF/Proof/Format/Deflate.lean) | No fixed-target composition recorded |
| [ZlibF.Spec.Prefix.ext](../ZlibF/Proof/Format/Deflate.lean) | No fixed-target composition recorded |
| [ZlibF.Spec.Proofs.prefixFree](../ZlibF/Proof/Format/Huffman.lean#L105) | No fixed-target composition recorded |
| [ZlibF.Spec.Public.Proofs.DeflateInit.default_init_witness](../ZlibF/Proof/public-deflate-init.lean#L282) | No fixed-target composition recorded |
| [ZlibF.Spec.Public.Proofs.free_writable_matches_dropWindow](../ZlibF/Proof/Api/HeapCleanup.lean#L55) | No fixed-target composition recorded |
| [ZlibF.Spec.Public.Proofs.legacy_codes_used_impossible](../ZlibF/Proof/Api/QueryLayout.lean#L123) | No fixed-target composition recorded |
| [ZlibF.Spec.Zlib.ext](../ZlibF/Proof/Format/Wrapper.lean) | No fixed-target composition recorded |

## Refresh

Regenerate after proof or registry changes. The generator builds and inspects
exact compiled theorem types. It never changes a proof, target or registry.
Acceptance remains subject to [checking](checking/README.md).

Input fingerprint: `820c338f1870bcbe2f2ea44068d00793ab38e0927d2e226b446e4a200c368e63`.
