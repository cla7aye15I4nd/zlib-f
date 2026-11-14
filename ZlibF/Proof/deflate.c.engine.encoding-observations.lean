import ZlibF.Proof.«deflate.c.engine.encoded-state»
import ZlibF.Spec.Public.Sequences
import ZlibF.Spec.Functional.Api.Goals
import ZlibF.Spec.Functional.Api.InflateAccepted

/-! # Actual public observations identify execution input/output accounting -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- A readable byte range determines one exact list, including a null
empty range and every static, raw or embedded byte view. -/
theorem observed_bytes_unique {h : Heap} {p : BPtr} {n : Nat} {left right : List UInt8}
    (first : Bytes h p n left) (second : Bytes h p n right) : left = right := by
  rcases first with ⟨rfl, rfl, rfl⟩ | ⟨ref, off, array, rfl, get, _fit, value⟩
  · rcases second with ⟨_null, _empty, nil⟩ | ⟨_ref, _off, _array, impossible, _rest⟩
    · exact nil.symm
    · cases impossible
  · exact value.trans (checksum_bytes_slice rfl get second).symm

/-- A DataStep's observed return heap, result, accepted count and output
bytes are exactly those of a proved execution of the same actual C call.
No observed accounting or encoding correctness is assumed by DataStep. -/
theorem data_step_identify_actual {h observedAfter actualAfter : Heap} {r : ZStreamRef}
    {z z' : ZStream} {flush observedRC actualRC : Int32} {observedUsed used : Nat}
    {input observedOutput written : List UInt8}
    (step : DataStep .deflate h observedAfter r flush observedRC input observedOutput observedUsed)
    (before : r.get h = some z)
    (actual : deflate (some r) flush h = .ok (actualRC, actualAfter))
    (after : r.get actualAfter = some z')
    (account : StreamAccounting z z' used written.length)
    (bytes : Bytes actualAfter z.next_out written.length written) :
    observedAfter = actualAfter ∧ observedRC = actualRC ∧ observedUsed = used ∧ observedOutput = written := by
  obtain ⟨oldZ, nextZ, oldGet, nextGet, _buffers, _header, _input, usedEq, outputBytes, run⟩ := step
  have oldEq : oldZ = z := Option.some.inj (oldGet.symm.trans before)
  subst oldZ
  change deflate (some r) flush h = .ok (observedRC, observedAfter) at run
  have same := Prod.mk.inj (Except.ok.inj (run.symm.trans actual))
  have nextEq : nextZ = z' := by
    rw [same.2] at nextGet
    exact Option.some.inj (nextGet.symm.trans after)
  subst nextZ
  have inputCount := account.2.2.1
  have usedSame : observedUsed = used := by omega
  have outputCount := account.2.2.2.1
  have writtenCount : z.avail_out.toNat - z'.avail_out.toNat = written.length := by omega
  rw [same.2, writtenCount] at outputBytes
  exact ⟨same.2, same.1, usedSame, observed_bytes_unique outputBytes bytes⟩

end Zlib.Deflate.Engine.Proofs
