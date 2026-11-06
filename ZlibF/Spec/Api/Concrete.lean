import ZlibF.Spec.Api.Compress
import ZlibF.Spec.Api.Iface
import ZlibF.Zlib.«compress.c»

/-!
# Concrete execution at the API boundary

`execute` is the graph of the translated computation on the actual runtime heap. It has no
replaceable run relation and does not assume that a callee obeys a contract. An allocation oracle
is part of the input heap; the specification must hold for every allowed oracle.

The existing `HeapApi` is still an abstract interface. These definitions do not instantiate its
history relation or establish stream safety. They provide a concrete boundary that later
refinement statements can use without an empty abstract relation hiding a fault.
-/

namespace ZlibF.Spec.Api.Concrete

/-- Execute the translated computation, preserving every returned heap and exposing every fault.
The abstraction forgets the reason for a fault, never the fact that it happened. -/
def execute {α : Type} (program : C.M α) (h : C.Heap) : Outcome C.Heap α :=
  match C.run program h with
  | .error _ => .fault
  | .ok (value, after) => .ret after value

/-- Total correctness for this particular translated computation: for every permitted input heap,
it returns without a runtime fault and satisfies the postcondition, including any frame and
ownership clauses supplied there. The successful run is required explicitly. Non-vacuity of the
precondition still needs an initialisation theorem or a concrete permitted input. -/
def Correct {α : Type} (program : C.M α) (pre : C.Heap → Prop)
    (post : C.Heap → α → C.Heap → Prop) : Prop :=
  ∀ before, pre before → ∃ value after,
    C.run program before = .ok (value, after) ∧ post before value after

/-- The concrete `_z` compressor entry, including argument-error ordering and the stored length.
`none` models a null `destLen` pointer in this translation; the scalar-pointer abstraction does
not model aliasing that pointer with caller buffers. No success or safety claim is built in. -/
def compress2_z (dest : C.BPtr) (capacity : Option UInt64) (source : C.BPtr)
    (sourceLen : UInt64) (level : Int32) (before : C.Heap) :
    Outcome C.Heap (Int32 × Option UInt64) :=
  execute (Zlib.Compress.compress2_z dest capacity source sourceLen level) before

/-- The concrete compatibility wrapper. Unlike `_z`, a null `destLen` is dereferenced by the
wrapper before `_z` can validate arguments, so the resulting fault must remain observable. -/
def compress2 (dest : C.BPtr) (capacity : Option UInt64) (source : C.BPtr)
    (sourceLen : UInt64) (level : Int32) (before : C.Heap) :
    Outcome C.Heap (Int32 × UInt64) :=
  execute (Zlib.Compress.compress2 dest capacity source sourceLen level) before

end ZlibF.Spec.Api.Concrete

namespace ZlibF.Spec.Api

/-- `compressBound` and `compressBound_z` on the default LP64 target equal the natural-number
formula, saturated to `2^64 - 1` on overflow, for every representable argument. This goal mentions
the actual translated functions. It assumes no compressor contract and no abstract `HeapApi`. -/
def Goal.compress_bound_value : Prop :=
  ∀ sourceLen : UInt64,
    (Zlib.Compress.compressBound sourceLen).toNat = compressBound sourceLen.toNat ∧
    (Zlib.Compress.compressBound_z sourceLen).toNat = compressBound sourceLen.toNat

/-- With valid pointer shapes, failure of the first default-allocator call in `compress2_z`
returns the memory error and stores zero. Automatic local storage does not consume that call.
No new block stays live after the failure. The caller's byte blocks are unchanged. The hypotheses
allow arbitrary input contents, sizes and static tables: this path returns before reading them.
This is a concrete error-path goal, not an assumed initialisation contract. -/
def Goal.compress2_z_first_alloc_failure : Prop :=
  ∀ (before : C.Heap) (dest source : C.BPtr) (capacity sourceLen : UInt64),
    C.Fresh before → before.allocOk before.nalloc = false →
    (0 < capacity → dest ≠ .null) → (0 < sourceLen → source ≠ .null) →
    ∃ after, C.run (Zlib.Compress.compress2_z dest (some capacity) source sourceLen
        C.Z_DEFAULT_COMPRESSION) before = .ok ((C.Z_MEM_ERROR, some 0), after) ∧
      after.nalloc = before.nalloc + 1 ∧ after.bytes = before.bytes ∧
      (∀ block, after.live block ↔ before.live block)

end ZlibF.Spec.Api
