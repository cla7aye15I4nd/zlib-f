import ZlibF.Proof.«deflate.c.universal-ops-prime»
import ZlibF.Spec.Public.Streams

/-!
# deflate.c: the destination of `deflateGetDictionary` is a plain byte block

The history's arguments of `deflateGetDictionary` (`StreamArguments`) give a writable caller range
that is no deflate state record. So the destination lies in a caller byte block. The case splits of
`operation_step` and `operation_header` use this in place of a premise.
-/

namespace Zlib.Deflate.Universal
open C ZlibF.Spec ZlibF.Spec.Public Zlib.Deflate Zlib.Deflate.Spec
set_option autoImplicit false

/-- The arguments of `deflateGetDictionary` place
its destination in a plain byte block. `CallerRange` asks for a writable range (so not a static
table) and the history's clause excludes every deflate state record. -/
theorem plain_dictionary_of_args {h : Heap} {r : ZStreamRef} {dictionary : BPtr} {hasDictLength : Bool}
    (args : StreamArguments h r (.deflateGetDictionary (some r) dictionary hasDictLength)) :
    ∀ q off, dictionary = .ref q off → ∃ x, q = .blk x := by
  intro q off e
  obtain ⟨_, _, _, _, _, _, range, outside⟩ := args
  rcases range with null | ⟨⟨xs, bytes⟩, writable, _⟩
  · rw [e] at null; cases null
  rcases bytes with ⟨null, _, _⟩ | ⟨q', i, a, ptr, get, _, _⟩
  · rw [e] at null; cases null
  rw [e] at ptr
  cases ptr
  cases q with
  | blk x => exact ⟨x, rfl⟩
  | dstate_depth x =>
    exfalso
    have none := outside x (by rw [e]; rfl)
    change (h.dstates x).map (·.depth) = some a at get
    rw [none] at get; cases get
  | _ =>
    exfalso
    rcases writable rfl with ⟨null, _⟩ | ⟨q2, i2, a2, eq2, _, ro2, _⟩
    · rw [e] at null; cases null
    · rw [e] at eq2; cases eq2; cases ro2

end Zlib.Deflate.Universal
