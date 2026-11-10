import ZlibF.Proof.«inflate.c.slow-protocol-fragment-public»
import ZlibF.Proof.«inflate.c.slow-pending-fragment-public»
namespace Zlib.Inflate.Proofs.SlowInputFragment
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inffast.Proofs Zlib.Inffast.Spec ZlibF.Math.LZ77Copy
open SlowMatchCompletion
set_option autoImplicit false
/-- A real MATCH mode identifies the retained independent residual even
when zero-width extras make two earlier bit-list values coincide. -/
theorem PendingSyntax.matching_residual {L D : List Nat} {p : CopySyntax L D}
    {s : InflateState} {residual : List Bool} (mode : s.mode = MATCH) (phase : PendingSyntax p s residual) :
    residual = p.rest := by
  cases phase with
  | len selected => rcases selected with selected | selected <;> rw [selected] at mode <;> contradiction
  | lenext selected _ _ _ => rw [selected] at mode; contradiction
  | dist selected _ _ _ => rw [selected] at mode; contradiction
  | distext selected _ _ _ _ _ => rw [selected] at mode; contradiction
  | matching _ _ _ _ _ => rfl

/-- One mode-selected source API covers fresh/partially parsed copy tokens
and partially emitted MATCH tokens. All capacities are allowed. Every wait
executes the real loop and public return suffix with produced buffers and
original scalar fields; completion supplies the real LEN prefix. -/
theorem protocol_slow_token_public_prefix {L D : List Nat} {p : CopySyntax L D}
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
    (entry : (ParserWaitingMode s ∨ s.mode = LEN_) ∨ s.mode = MATCH)
    (slow : s.mode = LEN ∨ s.mode = LEN_ → ¬ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true)
    (put : l.put = .ref dest off) (get : Space.get h dest = some output) (write : Space.ro h dest = false)
    (room : off + l.left.toNat ≤ output.size) (count : l.left.toNat ≤ l.out_.toNat)
    (produced : l.out_.toNat - l.left.toNat ≤ off)
    (privateWindow : ∀ w, s.window = .ref (.blk w) 0 → dest ≠ .blk w)
    (separate : Separate l.next l.have_.toNat l.put l.left.toNat)
    (available : distBases.getD p.distanceSymbol 0 + p.distanceValue ≤ log.dictionary.length + log.output.length + (l.out_.toNat - l.left.toNat)) :
    (PublicCopyFragmentResult p c h s l bs
      ((log.dictionary ++ log.output).drop ((log.dictionary ++ log.output).length - 32768)) future r zs z dest off output) ∨
    (PendingMatchFragmentResult p c h s l bs
      ((log.dictionary ++ log.output).drop ((log.dictionary ++ log.output).length - 32768)) future r zs z dest off output) := by
  rcases entry with parsing | matching
  · exact Or.inl (protocol_copy_fragment_public_prefix E good allowed scope lpointer lget lmeaning lstable
      dpointer dget dmeaning dstable buffers initialBits phase source parsing slow put get write room count produced privateWindow separate available)
  · have residualEq := PendingSyntax.matching_residual matching phase
    rw [residualEq] at phase source
    have active : s.mode < CHECK := by rw [matching]; decide
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
    have fields := pending_matching_fields matching phase
    exact Or.inr (pending_match_fragment_public_prefix E good (invariant.tables phase.data_mode) physical buffers matching
      phase source invariant.pending initialBits allocator.1 statics put get write room count produced privateWindow separate
      (by rw [fields.2.2.1]; simpa only [currentLength] using physicalAvailable))

#print axioms PendingSyntax.matching_residual
#print axioms protocol_slow_token_public_prefix
end Zlib.Inflate.Proofs.SlowInputFragment
