import ZlibF.Spec.Api.Run

/-!
# API model: the placeholder interface to the heap

**This file is a placeholder.** The goals about the heap-level library (`Goals.lean`) are
stated for an *abstract* `HeapApi`: a type of heaps, the relation `Matches` between a heap
object and a model state, and the translated functions seen as relations from the heap before to
the outcomes. Nothing here is defined from the runtime: the integration step instantiates
`HeapApi` with the object heap of `ZlibF/Runtime` and the translations of `ZlibF/Zlib`, and
`Matches` with the relation generated from the schema (`docs/runtime-schema.md`). Until then no
goal that mentions `HeapApi` is proved.

What each field must mean is written in `docs/design/api-model.md` (the interface and concrete-boundary sections), not here: the types only fix the shape that the goals use.
-/

namespace ZlibF.Spec.Api

/-- The result of running a translated function: it faulted (undefined behaviour reached, or a
missing allocation handled badly: `docs/spec/safety.md`), or it returned the heap after and a value. -/
inductive Outcome (H α : Type) where
  | fault : Outcome H α
  | ret (h : H) (a : α) : Outcome H α

/-- The abstract heap-level API. All `*Run`/`*Init`/... fields are relations: they list *every*
outcome of the translated function from the given heap (nondeterminism: allocation failure,
file failure). The arguments that are not heap objects (buffers' contents, flush values) are
passed in model form; the `*Args` fields say that the heap holds them as `zlib.h` requires:
`strm->next_in` points to the input bytes, `avail_out` is the room, buffers do not overlap
each other or the state (`A-stream-*`). -/
structure HeapApi where
  Heap : Type
  Strm : Type
  GzFile : Type
  -- Inflate
  inflMatches : Heap → Strm → InflState → Prop
  inflArgs : Heap → Strm → InflOp → Prop
  inflRun : Heap → Strm → InflOp → Outcome Heap InflRes → Prop
  inflNoState : Heap → Strm → Prop
  inflInitArgs : Heap → Strm → Prop
  inflInit : Heap → Strm → Int → Bool → Outcome Heap Int → Prop
  inflEnd : Heap → Strm → Outcome Heap Int → Prop
  inflCopy : Heap → Strm → Strm → Outcome Heap Int → Prop
  inflDisjoint : Heap → Strm → Strm → Prop
  inflBack : Heap → Strm → Nat → List UInt8 → BackCallbacks → Outcome Heap BackResult → Prop
  -- Deflate
  deflMatches : Heap → Strm → DeflState → Prop
  deflArgs : Heap → Strm → DeflOp → Prop
  deflRun : Heap → Strm → DeflOp → Outcome Heap DeflRes → Prop
  deflNoState : Heap → Strm → Prop
  deflInitArgs : Heap → Strm → Prop
  deflInit : Heap → Strm → Int → Int → Int → Int → Int → Bool → Outcome Heap Int → Prop
  deflEnd : Heap → Strm → Outcome Heap Int → Prop
  deflCopy : Heap → Strm → Strm → Outcome Heap Int → Prop
  deflDisjoint : Heap → Strm → Strm → Prop
  -- One-call functions
  utilArgs : Heap → Bool → List UInt8 → Nat → Prop
  compress2 : Heap → Bool → Int → List UInt8 → Nat → Outcome Heap (Int × List UInt8) → Prop
  compress : Heap → Bool → List UInt8 → Nat → Outcome Heap (Int × List UInt8) → Prop
  uncompress2 : Heap → Bool → List UInt8 → Nat → Outcome Heap (Int × List UInt8 × Nat) → Prop
  uncompress : Heap → Bool → List UInt8 → Nat → Outcome Heap (Int × List UInt8) → Prop
  -- gz files
  gzMatches : Heap → GzFile → GzHandle → Prop
  gzArgs : Heap → GzFile → GzOp → Prop
  gzRun : Heap → GzFile → GzOp → Outcome Heap GzRes → Prop
  gzOpen : Heap → List Char → Option (List UInt8) → Outcome Heap (Option GzFile) → Prop
  gzClose : Heap → GzFile → Outcome Heap (Int × List UInt8) → Prop

end ZlibF.Spec.Api
