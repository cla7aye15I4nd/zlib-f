# Memory, translation and external-I/O semantics

The project proves statements about an executable Lean translation of C. This section explains
what that translation represents, how specifications describe it, and where the connection to C
still depends on review. It is not a progress report; [progress](../progress.md) holds that record.

Start with [architecture](architecture.md). Then use the page that answers your question:

| Question | Read |
| --- | --- |
| How do C, the runtime, specifications and proofs fit together? | [Architecture](architecture.md) |
| How must a C statement be translated? | [Translation rules](translation.md) |
| What do the heap-free API relations describe? | [API model and concrete boundary](api-model.md) |
| Where are internal helper preconditions specified? | [Internal-call specifications](../spec/internal-contracts.md) |
| What file, formatting and error behaviors does the external world represent? | [External I/O](external-io.md) |
| Which records and pointer kinds exist? | [Generated runtime schema](../runtime-schema.md) |

The [API manual](../spec/api/README.md) describes public calls. The [proof guide](../proof/README.md)
explains how to establish their properties. The [checking guide](../checking/README.md) explains
how a result is accepted. Read [safety](../spec/safety.md), [trusted base](../trusted-base.md) and
[representation limits](../deviations.md) when assessing the scope of any theorem.

[Documentation home](../README.md)
