import ZlibF.Spec.Public.Domains
import ZlibF.Spec.Public.Sequences

/-!
# Initialisation: one safety goal per inflate and deflate init function

Step 2 of `docs/design/safety-functional-split.md`. The domain is `InitDomain`: a fresh record
with the default allocator (or `NULL` allocator fields, which the call fills in), a readable
version string and a well-formed heap. No history is needed. The goals can fail: the call must
return without a fault, write only the stream record and fresh blocks, and on `Z_OK` leave a
reachable stream whose new blocks it owns; on any other code it must leave the live blocks as
they were. `Goal.inflate_initialisation_domain` and `Goal.deflate_initialisation_domain` show the
domain and the `Z_OK` branch are non-empty. A wrong version, a wrong `stream_size` and a `NULL`
stream are the refusal branches of the full contracts (`Goal.inflateInit2_`, `Goal.deflateInit2_`,
...), each of which returns with the heap unchanged.
-/

namespace ZlibF.Spec.Public
open C ZlibF.Spec

/-- The outcome of an init call on stream `r` from `h` to `after` with code `rc`: only the stream
record and fresh blocks are written; on `Z_OK` the stream is reachable and every new live block
is owned by it (no leak); on any other code the live blocks are unchanged. -/
def InitCallSafe (kind : StreamKind) (h after : Heap) (r : ZStreamRef) (rc : Int32) : Prop :=
  Frame h after (StreamRoot r) ∧
  ((rc = Z_OK ∧ StreamReachable kind after r ∧
      ∃ created : Nat → Prop, (∀ b, created b → StreamOwned after r b) ∧
        LiveChange h after created (fun _ => False)) ∨
   (rc ≠ Z_OK ∧ LiveChange h after (fun _ => False) (fun _ => False)))

/-- `int inflateInit2_(z_streamp strm, int windowBits, const char *version, int stream_size)`.
**Safety of `inflateInit2_`** (macro `inflateInit2`): for every `windowBits` and every allocation
outcome, on `InitDomain` the call is safe (`InitCallSafe`). -/
def Goal.inflateInit2__safety : Prop :=
  ∀ h r version wb, InitDomain h r version →
    ∃ rc after, C.run (Zlib.Inflate.inflateInit2_ (some r) wb version 112) h = .ok (rc, after) ∧
      InitCallSafe .inflate h after r rc

/-- `int inflateInit_(z_streamp strm, const char *version, int stream_size)`.
**Safety of `inflateInit_`** (macro `inflateInit`): as `Goal.inflateInit2__safety` at window
bits 15. -/
def Goal.inflateInit__safety : Prop :=
  ∀ h r version, InitDomain h r version →
    ∃ rc after, C.run (Zlib.Inflate.inflateInit_ (some r) version 112) h = .ok (rc, after) ∧
      InitCallSafe .inflate h after r rc

/-- `int deflateInit2_(z_streamp strm, int level, int method, int windowBits, int memLevel,
int strategy, const char *version, int stream_size)`.
**Safety of `deflateInit2_`** (macro `deflateInit2`): for every level, method, window, memory
level and strategy, and every allocation outcome, on `InitDomain` the call is safe
(`InitCallSafe`). -/
def Goal.deflateInit2__safety : Prop :=
  ∀ h r version level method wb mem strategy, InitDomain h r version →
    ∃ rc after, C.run (Zlib.Deflate.deflateInit2_ (some r) level method wb mem strategy version 112) h =
      .ok (rc, after) ∧ InitCallSafe .deflate h after r rc

/-- `int deflateInit_(z_streamp strm, int level, const char *version, int stream_size)`.
**Safety of `deflateInit_`** (macro `deflateInit`): as `Goal.deflateInit2__safety` with the
default method, window, memory level and strategy, for every level. -/
def Goal.deflateInit__safety : Prop :=
  ∀ h r version level, InitDomain h r version →
    ∃ rc after, C.run (Zlib.Deflate.deflateInit_ (some r) level version 112) h = .ok (rc, after) ∧
      InitCallSafe .deflate h after r rc

end ZlibF.Spec.Public
