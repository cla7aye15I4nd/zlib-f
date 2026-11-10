import ZlibF.Proof.«inflate.c.fast-arbitrary-body-result»
namespace Zlib.Inflate.Proofs.FastArbitraryBody
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inffast.Spec Zlib.Inftrees
open Zlib.Inftrees.Spec.DecodeTableInvariant Zlib.Inftrees.Spec.DecodeTableStability
open Zlib.Inffast.Proofs ZlibF.Math.LZ77Copy
set_option autoImplicit false
set_option maxRecDepth 8192
/-- All actual source-selected L leaves are classified without an independent
parser premise. Constructor flags justify base acceptance. Rejected length,
distance and too-far branches remain as actual BAD with unchanged output. -/
theorem BodyLengthCut.classify_result
    {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {c : Zlib.Inffast.Ctx} {ref dref : CodeRef} {codes dcodes : Array Code}
    {offset root extent doff droot dextent : Nat} {L D : List Nat}
    {slow : IL} {fast : Zlib.Inffast.L} {bs dict : List UInt8}
    (cut : BodyLengthCut h r c ref codes offset root slow fast bs)
    (invariant : DefaultStateJ h r zs z s) (get : Space.get h ref = some codes)
    (inv : Inv LENS codes offset root extent L)
    (flags : Zlib.Inftrees.Spec.FastTableFlags.QueryCompatible LENS codes offset root)
    (stable : StableQuery LENS codes offset root)
    (capacity : 48 ≤ (stream slow bs).length)
    (dptr : c.dcode = .ref dref doff) (dget : Space.get h dref = some dcodes)
    (dsafe : DistTableSafe dcodes doff droot) (dmask : c.dmask.toUInt64.toNat = 2 ^ droot - 1)
    (dinv : Inv DISTS dcodes doff droot dextent D)
    (dflags : Zlib.Inftrees.Spec.FastTableFlags.QueryCompatible DISTS dcodes doff droot)
    (streamPtr : c.strm = some r) (statePtr : c.state = some (.tab zs))
    (mode : DataTableMode s.mode)
    (left : slow.left ≠ 0) (avail : 258 ≤ slow.left.toNat)
    (whave : c.whave.toNat ≤ c.wsize.toNat) (wnext : c.wnext.toNat ≤ c.wsize.toNat) (wsize : c.wsize.toNat ≤ 32768)
    {dest : BRef} {output saved : Array UInt8} {oo bg j woff : Nat}
    (outPtr : fast.out = .ref dest j) (put : slow.put = .ref dest oo) (begPtr : c.beg = .ref dest bg)
    (endPtr : c.end_ = .ref dest (oo + slow.left.toNat - 257))
    (outputGet : Space.get h dest = some output) (write : Space.ro h dest = false)
    (size : oo + slow.left.toNat ≤ output.size) (current : oo ≤ j) (beginLe : bg ≤ j) (span : j - bg < 2 ^ 32)
    (guard : C.run (Ptr.lt fast.out c.end_) h = .ok (true, h))
    (windowData : c.whave ≠ 0 → ∃ window, window ≠ dest ∧ c.window = .ref window woff ∧
      Space.get h window = some saved ∧ woff + c.wsize.toNat ≤ saved.size)
    (dictionary : MatchHistory.saved saved c.wsize.toNat c.wnext.toNat c.whave.toNat woff = dict)
    (dictCount : dict.length = c.whave.toNat) :
    BodyResult h r zs z s c slow fast bs dict L D dest output j bg := by
  let entry := codes.getD cut.selection.index default
  by_cases literal : entry.op = 0
  · obtain ⟨result, after, finalSlow, byte, actual, input, out, heap, finalGet, packet, currentState, buffers, token⟩ :=
      cut.literal_source invariant get inv literal left avail outPtr put endPtr outputGet write size current beginLe guard dict
    exact ⟨cut.used, result, after, finalSlow, output.set! j byte, by have := cut.usedBound; omega, cut.usedInput, input,
      actual, packet, buffers, finalGet, Or.inl ⟨1, by omega, heap, out, currentState, token⟩⟩
  · by_cases base : entry.op &&& 16 ≠ 0
    · exact cut.base_result invariant get inv flags base capacity dptr dget dsafe dmask dinv dflags
        streamPtr statePtr left avail whave wnext wsize outPtr put begPtr endPtr outputGet write size
        current beginLe span guard windowData dictionary dictCount
    · have noBase : entry.op &&& 16 = 0 := Classical.not_not.mp base
      have terminal : entry.op &&& 64 ≠ 0 := by
        have shape := cut.selection.leaf.2
        rcases shape with ordinary | length | rejected
        · exact False.elim (literal ordinary)
        · exact False.elim (length.1 noBase)
        · exact rejected.2
      by_cases ending : entry.op &&& 32 ≠ 0
      · have accepted : Zlib.Inftrees.Spec.DecodeSoundness.LeafAccepted LENS entry := by
          simp only [Zlib.Inftrees.Spec.DecodeSoundness.LeafAccepted, ite_true]
          exact Or.inl (by simpa only [bne_iff_ne] using ending)
        obtain ⟨result, finalSlow, actual, input, broke, out, packet, currentState, buffers, token⟩ :=
          cut.eob_source invariant get statePtr mode inv accepted literal noBase dict (writtenBytes output j (j - bg))
        have finalGet : Space.get (setI h zs {s with mode := TYPE}) dest = some output := by
          rw [byte_view_get_setI]; exact outputGet
        exact ⟨cut.used, result, _, finalSlow, output, by have := cut.usedBound; omega, cut.usedInput, input,
          actual, packet, buffers, finalGet,
          Or.inr (Or.inl ⟨rfl, broke, out.trans outPtr, rfl, currentState, token⟩)⟩
      · have noEnd : entry.op &&& 32 = 0 := Classical.not_not.mp ending
        have rejected : ¬ Zlib.Inftrees.Spec.DecodeSoundness.LeafAccepted LENS entry := by
          simp only [Zlib.Inftrees.Spec.DecodeSoundness.LeafAccepted, ite_true]
          intro accepted
          rcases accepted with endCode | valid
          · have nz : entry.op &&& 32 ≠ 0 := by simpa only [bne_iff_ne] using endCode
            exact nz noEnd
          · exact terminal valid
        obtain ⟨i, result, after, finalSlow, actual, input, heap, broke, out, packet, currentState, buffers, views, _rejection⟩ :=
          cut.invalid_source (D := D) invariant get streamPtr statePtr inv stable rejected noBase dict (writtenBytes output j (j - bg))
        have finalGet : Space.get after dest = some output := by rw [views]; exact outputGet
        exact ⟨cut.used, result, after, finalSlow, output, by have := cut.usedBound; omega, cut.usedInput, input,
          actual, packet, buffers, finalGet,
          Or.inr (Or.inr ⟨i, heap, broke, out.trans outPtr, rfl, currentState⟩)⟩

#print axioms BodyLengthCut.classify_result
end Zlib.Inflate.Proofs.FastArbitraryBody
