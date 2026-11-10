import ZlibF.Proof.«inflate.c.slow-copy-fragment-public»
namespace Zlib.Inflate.Proofs.SlowInputFragment
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inffast.Proofs Zlib.Inffast.Spec ZlibF.Math.LZ77Copy
set_option autoImplicit false
/-- The actual protocol produces the real saved dictionary, allocator,
common J, sane/pending scalar facts and immutable library data. Installed
Huffman meaning stays an internal representation fact from its actual
constructor; no public contract or no-fast restriction is introduced. -/
theorem protocol_copy_fragment_public_prefix {L D : List Nat} {p : CopySyntax L D}
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {log : DataLog}
    {l : IL} {bs : List UInt8} {future residual : List Bool}
    {lref dref : CodeRef} {lo lextent doff dextent : Nat} {lca dca : Array Code}
    {dest : BRef} {off : Nat} {output : Array UInt8}
    (E : Env c h r zs z s) (good : Good h r zs z s)
    (allowed : AllowedInflateProtocol 15 r h log) (scope : ProtocolWindow.PlatformScope allowed.choose_spec)
    (lpointer : s.lencode = .ref lref lo) (lget : Space.get h lref = some lca)
    (lmeaning : Zlib.Inftrees.Spec.DecodeTableInvariant.Inv LENS lca lo s.lenbits.toNat lextent L)
    (lstable : Zlib.Inftrees.Spec.DecodeTableStability.StableQuery LENS lca lo s.lenbits.toNat)
    (dpointer : s.distcode = .ref dref doff) (dget : Space.get h dref = some dca)
    (dmeaning : Zlib.Inftrees.Spec.DecodeTableInvariant.Inv DISTS dca doff s.distbits.toNat dextent D)
    (dstable : Zlib.Inftrees.Spec.DecodeTableStability.StableQuery DISTS dca doff s.distbits.toNat)
    (buffers : DispatchBuffers h r l bs) (initialBits : l.bits.toNat ≤ 39) (phase : PendingSyntax p s residual) (source : FutureSource l bs future residual)
    (entry : ParserWaitingMode s ∨ s.mode = LEN_)
    (slow : s.mode = LEN ∨ s.mode = LEN_ → ¬ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true)
    (put : l.put = .ref dest off) (get : Space.get h dest = some output) (write : Space.ro h dest = false)
    (room : off + l.left.toNat ≤ output.size) (count : l.left.toNat ≤ l.out_.toNat)
    (produced : l.out_.toNat - l.left.toNat ≤ off)
    (privateWindow : ∀ w, s.window = .ref (.blk w) 0 → dest ≠ .blk w)
    (separate : Separate l.next l.have_.toNat l.put l.left.toNat)
    (available : distBases.getD p.distanceSymbol 0 + p.distanceValue ≤ log.dictionary.length + log.output.length + (l.out_.toNat - l.left.toNat)) :
    PublicCopyFragmentResult p c h s l bs
      ((log.dictionary ++ log.output).drop ((log.dictionary ++ log.output).length - 32768)) future r zs z dest off output := by
  have active : s.mode < CHECK := by
    cases phase with
    | len selected => rcases selected with mode | mode <;> rw [mode] <;> decide
    | lenext mode _ _ _ => rw [mode]; decide
    | dist mode _ _ _ => rw [mode]; decide
    | distext mode _ _ _ _ _ => rw [mode]; decide
    | matching mode _ _ _ _ => rw [mode]; decide
  obtain ⟨invariant, allocator, physical⟩ := protocol_saved_dictionary allowed scope good active
  let current := writtenBytes output off (l.out_.toNat - l.left.toNat)
  have currentLength : current.length = l.out_.toNat - l.left.toNat := by
    simp only [current, writtenBytes, List.length_take, List.length_drop, Array.length_toList]
    omega
  have validDistance : distBases.getD p.distanceSymbol 0 + p.distanceValue ≤ (log.dictionary ++ log.output ++ current).length := by
    simpa only [List.length_append, currentLength] using available
  obtain ⟨_dict, physicalAvailable, _logicalBytes⟩ := protocol_copy_history p allowed scope good active current 0 validDistance
  have statics : Zlib.Crc32.Proofs.StaticsOK h := by
    unfold Zlib.Crc32.Proofs.StaticsOK
    rw [invariant.globals]
    exact ⟨rfl, rfl⟩
  exact slow_copy_fragment_public_prefix E good (invariant.tables phase.data_mode) allocator.1 statics
    lpointer lget lmeaning lstable dpointer dget dmeaning dstable buffers invariant.pending initialBits
    phase source entry slow physical put get write room count produced privateWindow separate
    (by simpa only [currentLength] using physicalAvailable)

#print axioms protocol_copy_fragment_public_prefix
end Zlib.Inflate.Proofs.SlowInputFragment
