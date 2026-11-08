import ZlibF.Proof.«inflate.c.dictionary-install-state»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The actual accepted dictionary prefix reaches its actual window run,
then writes precisely havedict or MEM. Checksums are real translated runs,
not assumed callee specifications. -/
theorem inflateSetDictionary_window_cut {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s state : InflateState} {ref : BRef} {off : Nat} {array : Array UInt8} {len : UInt32} {wr : Int32}
    (live : Live h r zs z s) (get : Space.get h ref = some array) (room : off + len.toNat ≤ array.size)
    (allowed : s.wrap = 0 ∨ s.mode = DICT)
    (check : s.mode = DICT → (ZlibF.Spec.adler32 (Zlib.Adler32.Proofs.seg array off len.toNat)).toUInt64 = s.check)
    (windowRun : updatewindow (some r) (.ref ref (off + len.toNat)) len h = .ok (wr, after))
    (stateGet : after.istates zs = some state) :
    C.run (inflateSetDictionary (some r) (.ref ref off) len) h =
      if wr = 0 then .ok (Z_OK, setI after zs { state with havedict := 1 })
      else .ok (Z_MEM_ERROR, setI after zs { state with mode := MEM }) := by
  have add : Ptr.add (Ptr.ref ref off) (len.toNat : Int) h =
      .ok (.ref ref (off + len.toNat), h) := Ptr.add_nat_ok get room
  have nonnull : (Ptr.ref ref off == (Ptr.null : BPtr)) = false := by simp
  change inflateSetDictionary (some r) (.ref ref off) len h = _
  unfold inflateSetDictionary
  simp only [bind_app, stateCheck_live live, ldZ_eq, ldI_eq, live.hz, live.zst, castI, live.hs,
    nonnull, bne_self_eq_false, Bool.or_self, Bool.false_eq_true, ite_false]
  by_cases dict : s.mode = DICT
  · have checksum := adler32_dict_any get len room
    have expected := check dict
    have test : (s.mode == DICT) = true := by simpa using dict
    simp only [test, adler32_init, checksum, expected, bne_self_eq_false, add, windowRun,
      ite_true, Bool.false_eq_true, ite_false, Bool.and_false, dict, beq_self_eq_true]
    simp only [bind_app, adler32_init, checksum, expected, bne_self_eq_false, add, windowRun,
      Bool.false_eq_true, ite_false, setMode, wrI_eq, stateGet]
    by_cases zero : wr = 0
    · simp only [zero, bne_self_eq_false, Bool.false_eq_true, ite_false, ite_true, bind_app, wrI_eq, stateGet, pure_app, setI]
    · have nonzero : (wr != 0) = true := by simpa using zero
      simp only [nonzero, ite_true, zero, ite_false, setMode, bind_app, wrI_eq, stateGet, pure_app, setI]
  · have raw : s.wrap = 0 := allowed.resolve_right dict
    have test : (s.mode == DICT) = false := by simpa using dict
    simp only [test, raw, add, windowRun, bne_self_eq_false, Bool.false_and,
      Bool.false_eq_true, ite_false, Bool.and_false]
    simp only [bind_app, add, windowRun, Bool.false_eq_true, ite_false, setMode, wrI_eq, stateGet]
    by_cases zero : wr = 0
    · simp only [zero, bne_self_eq_false, Bool.false_eq_true, ite_false, ite_true, bind_app, wrI_eq, stateGet, pure_app, setI]
    · have nonzero : (wr != 0) = true := by simpa using zero
      simp only [nonzero, ite_true, zero, ite_false, setMode, bind_app, wrI_eq, stateGet, pure_app, setI]

end Zlib.Inflate.Proofs
