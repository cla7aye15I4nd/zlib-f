# Documentation

The [documentation website](https://www.dataisland.org/zlib-f/) is the published
reading home. The files here are its content sources.

## Read the zlib articles {#articles}

1. [A complete codec: LZ77 and Huffman](articles/foundations.en.md).
2. [Implementing and optimizing zlib](articles/optimizations.en.md).
3. [Extending zlib: streams and integrity](articles/features.en.md).

Each article is available in English and Chinese. The algorithm series explains
zlib itself; formal verification has its own reference material below.

## Reference {#reference}

- [Specifications](spec/README.md): platform scope, safety, input ranges, public
  API contracts, internal helper contracts and compressed-byte meaning.
- [Model](design/README.md): translation, memory semantics and external I/O.
- [Implementation arguments](proof/README.md): verification method and detailed
  reasoning for the C components.
- [Checking](checking/README.md): acceptance rules and reviewed checks.
- [Progress](progress.md): target dependencies, proof evidence and remaining work.

[Trusted base](trusted-base.md) and [deviations](deviations.md) state model boundaries.
[Findings](findings.md) records source reports and their scope.
[Runtime schema](runtime-schema.md) is the field and type reference.

## Build and preview {#local}

Article sources live in `articles/`. The website builder, interactions, styles and
tests live in `web/`. API return tables live in the same `spec/api/` source files
as their complete contracts. English sources and adjacent `.zh.md` files each
have one maintained version; pages and function views are generated from them.
See the website guide, `web/README.md`, for dependencies and build instructions.
