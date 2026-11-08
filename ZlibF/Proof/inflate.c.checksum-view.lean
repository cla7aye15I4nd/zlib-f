import ZlibF.Proof.«public-adler-update»
import ZlibF.Proof.«inflate.c.output-invariant»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The actual zlib-wrapper checksum update accepts every represented
readable byte view. Its value follows from the proved translated Adler
callee for every seed, including the one-byte special case. -/
theorem UPDATE_CHECK_zlib_view {h : Heap} {zs : Nat} {s : InflateState} {ref : BRef}
    {off : Nat} {array : Array UInt8} {len : UInt32}
    (state : h.istates zs = some s) (flags : s.flags = 0)
    (get : Space.get h ref = some array) (fit : off + len.toNat ≤ array.size) (check : UInt64) :
    UPDATE_CHECK (some (.tab zs)) check (.ref ref off) len h =
      .ok (adlerValue check ((array.toList.drop off).take len.toNat), h) := by
  have run := ZlibF.Spec.Public.AdlerUpdateProof.adler_z_any_public get check off len.toUInt64
    (by simpa only [UInt32.toNat_toUInt64] using fit)
  have update : Zlib.Adler32.adler32 check (.ref ref off) len h =
      .ok (adlerValue check ((array.toList.drop off).take len.toNat), h) := by
    simpa only [C.run, Zlib.Adler32.adler32, UInt32.toNat_toUInt64] using run
  unfold UPDATE_CHECK
  simp only [bind_app, rdS, ldInflateState_tab state, flags, pure_app]
  change Zlib.Adler32.adler32 check (.ref ref off) len h = _
  with_reducible exact update

/-- The dispatch output relation supplies the actual produced prefix and
validates the negative pointer addition used by CHECK and inf_leave. Empty
output and non-block byte views retain the same caller domain. -/
theorem UPDATE_CHECK_zlib_output {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (E : Env c h r zs z s) (good : Good h r zs z s)
    (output : OutputCursorInvariant h r l) (flags : s.flags = 0) (check : UInt64) :
    ∃ ref off array,
      l.put = .ref ref off ∧ Space.get h ref = some array ∧
      (l.out_ - l.left).toNat ≤ off ∧ off ≤ array.size ∧
      l.put.add (-((l.out_ - l.left).toNat : Int)) h =
        .ok (.ref ref (off - (l.out_ - l.left).toNat), h) ∧
      UPDATE_CHECK c.st check (.ref ref (off - (l.out_ - l.left).toNat)) (l.out_ - l.left) h =
        .ok (adlerValue check ((array.toList.drop (off - (l.out_ - l.left).toNat)).take
          (l.out_ - l.left).toNat), h) := by
  obtain ⟨ref, array, off, put, get, _, room, count, produced, _⟩ :=
    callerRange_slow_output good l output.range output.nonnull output.count output.produced
  have amount : (l.out_ - l.left).toNat = l.out_.toNat - l.left.toNat := UInt32.toNat_sub_of_le _ _ count
  have prefixBound : (l.out_ - l.left).toNat ≤ off := by rw [amount]; exact produced
  have endBound : off ≤ array.size := by omega
  refine ⟨ref, off, array, put, get, prefixBound, endBound, ?_, ?_⟩
  · rw [put]
    exact Ptr.sub_nat_ok get prefixBound endBound
  · rw [E.st]
    exact UPDATE_CHECK_zlib_view E.hs flags get (by omega) check

end Zlib.Inflate.Proofs
