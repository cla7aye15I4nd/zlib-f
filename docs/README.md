# Documentation

The [documentation website](https://www.dataisland.org/zlib-f/) is the published
reading home. The files here are its content sources. The site is built from the `dev`
branch, so it shows the current work. Every page ends with the commit and date it was built from.

## Where to start

- [Results and status](progress.md#scope): the three core results, what is planned and what is not.
  The website shows the same facts on its home page and on a status page, read from the proof records.
- [Glossary](glossary.md): the terms used in the specifications and proofs.
- [Contributing](checking/contributing.md): numbered steps and commands.

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
- [Checking](checking/README.md): what counts as checked and as accepted.
- [Evidence index](progress.md): every target with its statement, proof and dependencies.

[Trusted base](trusted-base.md) and [deviations](deviations.md) state model boundaries.
[Findings](findings.md) records confirmed source reports and their scope.
[Sanitizer reports](sanitizer-reports.md) lists every sanitizer reproduction and the premise that excludes it.
[Runtime schema](runtime-schema.md) is the field and type reference.

## Build and preview {#local}

Article sources live in `articles/`. The website builder, interactions, styles and
tests live in `web/`. API return tables live in the same `spec/api/` source files
as their complete contracts. English sources and adjacent `.zh.md` files each
have one maintained version; pages and function views are generated from them.
See the website guide, `web/README.md`, for dependencies and build instructions.
