import ZlibF.Proof.«inflate.c.fast-future-restore-entry-geometry»

namespace Zlib.Inflate.Proofs.FunctionalEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inftrees
set_option autoImplicit false

/-- Actual RESTORE installs the local byte and bit cursors before the
general fast prelude. The installed tables, retained window and already
written current-call bytes survive that source write. -/
theorem PayloadRepresentation.restore_fast_entry_future_geometry_v2
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState}
    {slow : IL} {bs : List UInt8}
    {L D : List Nat} {oldDict past current : List UInt8}
    {future tail : List Bool} {decoded : List UInt8}
    (E : Env c h r zs z s)
    (representation : PayloadRepresentation h r zs z s slow bs
      L D (oldDict ++ past))
    (mode : DataTableMode s.mode)
    (distanceFlags : ∀ (ref : CodeRef) (offset : Nat)
      (codes : Array Code), s.distcode = .ref ref offset →
      Space.get h ref = some codes →
      Zlib.Inftrees.Spec.FastTableFlags.QueryCompatible
        DISTS codes offset s.distbits.toNat)
    (historyView : ∀ dest oo output,
      slow.put = .ref dest oo → Space.get h dest = some output →
      ZlibF.Math.LZ77Copy.writtenBytes output oo
        (slow.out_.toNat - slow.left.toNat) = current)
    (parsed : Symbols L D oldDict (past ++ current)
      (stream slow bs ++ future) tail decoded)
    (fast : (slow.have_ >= 6 && slow.left >= 258 &&
      slow.bits < 8) = true) :
    let restored := setI (r.put h (leaveStream z slow)) zs
      (leaveState s slow)
    past <+: decoded ∧
    ∃ (ctx : FastLoopContext) (q : Zlib.Inffast.L),
      runX (RESTORE c.strm c.st) slow h =
        .ok ((.ok (), slow), restored) ∧
      C.run (fastEntryPrefix (some r) slow.out_) restored =
        .ok ((ctx.c, q), restored) ∧
      FastFutureReady ctx L D
        ((oldDict ++ past).drop
          ((oldDict ++ past).length - 32768))
        future tail (decoded.drop past.length) restored q ∧
      ctx.r = r ∧ ctx.zs = zs ∧ q.broke = false ∧
      slow.put = .ref ctx.dest ctx.oo ∧
      ctx.leftTotal = slow.left ∧ ctx.outTotal = slow.out_ ∧
      ctx.z = leaveStream z slow ∧ ctx.s = leaveState s slow ∧
      q.bits = slow.bits := by
  dsimp only
  obtain ⟨actualRestore, after⟩ := representation.restore E
  have restoredRep := after
  obtain ⟨origin, buffers, _bits, tables, dictionary⟩ := after
  have dataMode : DataTableMode (leaveState s slow).mode := by
    change DataTableMode s.mode
    exact mode
  have codeGet : (r.put h (leaveStream z slow)).istates zs = some s := by
    simpa using representation.1.good.live.hs
  have restoredFlags : ∀ (ref : CodeRef) (offset : Nat)
      (codes : Array Code),
      (leaveState s slow).distcode = .ref ref offset →
      Space.get (setI (r.put h (leaveStream z slow)) zs
        (leaveState s slow)) ref = some codes →
      Zlib.Inftrees.Spec.FastTableFlags.QueryCompatible
        DISTS codes offset (leaveState s slow).distbits.toNat := by
    intro ref offset codes pointer get
    have oldPointer : s.distcode = .ref ref offset := pointer
    have oldGet : Space.get h ref = some codes := by
      unfold leaveState at get
      rw [code_views_set_bits codeGet,
        code_views_put_stream] at get
      exact get
    exact distanceFlags ref offset codes oldPointer oldGet
  have restoredHistory : ∀ dest oo output,
      slow.put = .ref dest oo →
      Space.get (setI (r.put h (leaveStream z slow)) zs
        (leaveState s slow)) dest = some output →
      ZlibF.Math.LZ77Copy.writtenBytes output oo
        (slow.out_.toNat - slow.left.toNat) = current := by
    intro dest oo output ptr get
    have beforeGet : Space.get h dest = some output := by
      rw [byte_view_get_setI, byte_view_get_stream_put] at get
      exact get
    exact historyView dest oo output ptr beforeGet
  obtain ⟨prefixBytes, ctx, q, prefixRun, sameR, sameZs,
    sameZ, sameS, _lenWidth, _distWidth, _lcode,
    _dcode, put, _out, _input, bits, _hold, left,
    outTotal, notBroken, semantic⟩ :=
    PayloadRepresentation.fast_entry_future restoredRep dataMode rfl rfl rfl rfl
      rfl rfl restoredFlags restoredHistory parsed fast
  exact ⟨prefixBytes, ctx, q, actualRestore, prefixRun,
    semantic, sameR, sameZs, notBroken, put, left, outTotal, sameZ, sameS, bits⟩

#print axioms PayloadRepresentation.restore_fast_entry_future_geometry_v2
end Zlib.Inflate.Proofs.FunctionalEpoch
