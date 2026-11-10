# Unported original test sources

This directory preserves existing mutation harnesses whose baseline modules are
absent from the publication base. The files retain their original bytes, including
every mutation, assertion, option and expected direct proof failure. The `.py.txt`
suffix marks source evidence. These files are not accepted runnable suites.

The original paths, hashes and missing providers are recorded in
[`../original-companions-publication.json`](../original-companions-publication.json).
The [provider review](provider-map.json) records exact identities and unresolved
domain differences. Some current generic contracts cover old scalar conclusions. They are not
identical providers of the old named helper proofs, concrete witnesses and
mutation-sensitive import closure. They have not been substituted as baselines.

Before restoring a harness to its original path, review its baseline providers
and preserve its complete checks. Do not remove options, accept unrelated failures,
raise resource limits or replace proof failures with skipped cases. None of these
archived harnesses was executed as part of this source publication.
