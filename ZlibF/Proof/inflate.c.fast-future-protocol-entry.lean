import ZlibF.Proof.«inflate.c.fast-future-restore-entry»
import ZlibF.Proof.«inflate.c.protocol-window-history»

namespace Zlib.Inflate.Proofs.FunctionalEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inftrees
set_option autoImplicit false

/-- The admitted actual history supplies the retained physical ring for
an arbitrary active block. This establishes the dictionary clause of the
fast-entry representation from the real protocol, including prior output. -/
theorem PayloadRepresentation.of_protocol_window
    {r : ZStreamRef} {h : Heap} {log : DataLog}
    {zs : Nat} {z : ZStream} {s : InflateState}
    {regs : IL} {bs : List UInt8} {L D : List Nat}
    (allowed : AllowedInflateProtocol 15 r h log)
    (scope : ProtocolWindow.PlatformScope allowed.choose_spec)
    (origin : DefaultOriginState h r zs z s)
    (buffers : DispatchBuffers h r regs bs)
    (bits : regs.bits.toNat ≤ 39)
    (tables : InstalledTables h s L D)
    (active : s.mode < CHECK) :
    PayloadRepresentation h r zs z s regs bs L D
      (log.dictionary ++ log.output) := by
  obtain ⟨index, stream, state, current, _allocator,
    dictionary⟩ :=
    ProtocolWindow.allowed_saved_logical_exact allowed scope
  have sameZ : stream = z := Option.some.inj
    (current.good.live.hz.symm.trans origin.good.live.hz)
  subst stream
  have sameIndex : index = zs := by
    simpa using current.good.live.zst.symm.trans
      origin.good.live.zst
  subst index
  have sameS : state = s := Option.some.inj
    (current.good.live.hs.symm.trans origin.good.live.hs)
  subst state
  exact ⟨origin, buffers, bits, tables, dictionary active⟩

#print axioms PayloadRepresentation.of_protocol_window

/-- The admitted history, installed source tables and actual RESTORE give
one real fast prelude and a semantic Ready for a nonempty window and a
nonempty current-call output prefix. There is no zero-window hypothesis. -/
theorem PayloadRepresentation.protocol_restore_fast_entry_future
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {log : DataLog}
    {slow : IL} {bs : List UInt8} {L D : List Nat}
    {oldDict past current : List UInt8}
    {future tail : List Bool} {decoded : List UInt8}
    (allowed : AllowedInflateProtocol 15 r h log)
    (scope : ProtocolWindow.PlatformScope allowed.choose_spec)
    (E : Env c h r zs z s)
    (origin : DefaultOriginState h r zs z s)
    (buffers : DispatchBuffers h r slow bs)
    (bits : slow.bits.toNat ≤ 39)
    (tables : InstalledTables h s L D)
    (active : s.mode < CHECK)
    (mode : DataTableMode s.mode)
    (logical : log.dictionary ++ log.output = oldDict ++ past)
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
      ctx.r = r ∧ ctx.zs = zs ∧ q.broke = false := by
  have representation :=
    PayloadRepresentation.of_protocol_window allowed scope
      origin buffers bits tables active
  rw [logical] at representation
  exact representation.restore_fast_entry_future E mode
    distanceFlags historyView parsed fast

#print axioms PayloadRepresentation.protocol_restore_fast_entry_future
end Zlib.Inflate.Proofs.FunctionalEpoch
