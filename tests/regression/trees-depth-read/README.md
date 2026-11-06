# Merge depth reads

The C conditional reads the selected child depth again after comparing both
children. The translation now preserves that read. The earlier expression
reused a cached comparison value.

Run `bash tests/regression/trees-depth-read/run.sh` after building the tree
translation. The fixture extracts the actual C statement and Lean fragment.
Six initialized cases cover both choices, equal depths and byte wrap at 255.
The C cases run under address and undefined-behavior sanitizers.

The source check rejects the former cached expression. The initialized cases
also agree with that former expression, so matching final values alone cannot
detect the omitted read. These comparisons are fidelity evidence, not proof.
