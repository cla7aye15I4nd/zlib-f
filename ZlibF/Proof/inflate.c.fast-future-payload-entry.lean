import ZlibF.Proof.«inflate.c.fast-future-generic-entry-producer»
import ZlibF.Proof.«inflate.c.global-payload-representation»
import ZlibF.Proof.«inflate.c.symbols-retained-context»

namespace Zlib.Inflate.Proofs.FunctionalEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inftrees
set_option autoImplicit false

/-- The actual installed-table and retained-window representation enters
the translated fast prelude with an arbitrary previous output history and
arbitrary current-call output prefix. The independent parser is trimmed to
the real 32 KiB physical ring, using the default state's actual wbits=15. -/
theorem PayloadRepresentation.fast_entry_future
    {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState}
    {slow : IL} {bs : List UInt8}
    {L D : List Nat} {oldDict past current : List UInt8}
    {future tail : List Bool} {decoded : List UInt8}
    (representation : PayloadRepresentation h r zs z s slow bs
      L D (oldDict ++ past))
    (mode : DataTableMode s.mode)
    (inputCursor : z.next_in = slow.next)
    (inputCount : z.avail_in = slow.have_)
    (outputCursor : z.next_out = slow.put)
    (outputCount : z.avail_out = slow.left)
    (stateHold : s.hold = slow.hold)
    (stateBits : s.bits = slow.bits)
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
    past <+: decoded ∧
    ∃ (ctx : FastLoopContext) (q : Zlib.Inffast.L),
      C.run (fastEntryPrefix (some r) slow.out_) h =
        .ok ((ctx.c, q), h) ∧
      ctx.r = r ∧ ctx.zs = zs ∧ ctx.z = z ∧ ctx.s = s ∧
      ctx.rootWidth = s.lenbits.toNat ∧
      ctx.distWidth = s.distbits.toNat ∧
      ctx.c.lcode = s.lencode ∧ ctx.c.dcode = s.distcode ∧
      slow.put = .ref ctx.dest ctx.oo ∧ q.out = slow.put ∧
      q.in_ = slow.next ∧ q.bits = slow.bits ∧
      q.hold = slow.hold ∧ ctx.leftTotal = slow.left ∧
      ctx.outTotal = slow.out_ ∧ q.broke = false ∧
      FastFutureReady ctx L D
        ((oldDict ++ past).drop
          ((oldDict ++ past).length - 32768))
        future tail (decoded.drop past.length) h q := by
  obtain ⟨origin, buffers, _bits, tables, dictionary⟩ := representation
  have capacity : 2 ^ s.wbits.toNat = 32768 := by
    rw [origin.toDefaultStateJ.window]
    decide
  obtain ⟨outputPrefix, trimmed⟩ :=
    symbols_retained_target parsed
  have physical : InflateDictionary h s
      ((oldDict ++ past).drop
        ((oldDict ++ past).length - 32768)) := by
    simpa only [capacity] using dictionary
  have parser : ∀ dest oo output, slow.put = .ref dest oo →
      Space.get h dest = some output →
      Symbols L D
        ((oldDict ++ past).drop
          ((oldDict ++ past).length - 32768))
        (ZlibF.Math.LZ77Copy.writtenBytes output oo
          (slow.out_.toNat - slow.left.toNat))
        (stream slow bs ++ future) tail
        (decoded.drop past.length) := by
    intro dest oo output ptr get
    rw [historyView dest oo output ptr get]
    exact trimmed
  exact ⟨outputPrefix,
    fastEntryPrefix_future_general origin.toDefaultStateJ
      buffers mode inputCursor inputCount outputCursor outputCount
      stateHold stateBits tables distanceFlags physical parser fast⟩

#print axioms PayloadRepresentation.fast_entry_future
end Zlib.Inflate.Proofs.FunctionalEpoch
