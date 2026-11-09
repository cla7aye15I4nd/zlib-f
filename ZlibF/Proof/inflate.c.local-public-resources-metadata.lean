import ZlibF.Proof.«inflate.c.local-public-state»
import ZlibF.Proof.«inflate.c.metadata-mode-output-frame»

namespace Zlib.Inflate.Local
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- These actual modes update metadata or inspect bits, without emitting
caller output. Their possible continuations are part of the same source run. -/
def MetadataMode (mode : UInt32) : Prop :=
  mode = DICTID ∨ mode = DICT ∨ mode = TYPE ∨ mode = TYPEDO ∨ mode = CHECK ∨ mode = LENGTH

/-- Every actual metadata dispatch writes only its stream/decoder records.
The checksum and fixed-table callees are proved about their actual bodies. -/
theorem inflate_dispatch_metadata_record_frame
    {c : Ctx} {l regs : IL} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {outcome : Except Ex Unit}
    (E : Env c h r zs z s) (mode : MetadataMode s.mode)
    (run : runX (inflate_dispatch c) l h = .ok ((outcome, regs), after)) :
    RecordFrame r c.st h after := by
  rcases mode with dictionaryId | dictionary | blockType | blockMore | check | length
  · exact recordFrameX_inflate_DICTID r c E.strm l h outcome regs after
      ((inflate_dispatch_DICTID E l dictionaryId).symm.trans run)
  · exact recordFrameX_inflate_DICT r c E.strm l h outcome regs after
      ((inflate_dispatch_DICT E l dictionary).symm.trans run)
  · have source := inflate_dispatch_block_type E l (Or.inl blockType)
    rw [ite_eq_left blockType] at source
    exact recordFrameX_inflate_TYPE r c E.strm l h outcome regs after (source.symm.trans run)
  · have source := inflate_dispatch_block_type E l (Or.inr blockMore)
    have notType : s.mode ≠ TYPE := by rw [blockMore]; decide
    rw [ite_eq_right notType] at source
    exact recordFrameX_inflate_TYPEDO r c E.strm l h outcome regs after (source.symm.trans run)
  · exact recordFrameX_inflate_CHECK r c E.strm l h outcome regs after
      ((inflate_dispatch_CHECK E l check).symm.trans run)
  · exact recordFrameX_inflate_LENGTH r c E.strm l h outcome regs after
      ((inflate_dispatch_LENGTH E l length).symm.trans run)

/-- The metadata-mode frame is tied to the same produced count and actual
cursor movement as the proved default execution, including direct DICT returns. -/
theorem inflate_dispatch_metadata_exact_frame
    {c : Ctx} {l : IL} {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : LocalStateJ h cutoff r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : MetadataMode s.mode) (incoming : l.bits.toNat ≤ 39) :
    ∃ outcome regs after stream state made,
      runX (inflate_dispatch c) l h = .ok ((outcome, regs), after) ∧
      LocalGood after cutoff r zs stream state ∧ regs.left.toNat + made = l.left.toNat ∧
      regs.put = inputAdvance l.put made ∧
      BufferFrame h after (fun b => StreamRoot r b ∨ b = zs) [⟨l.put, made⟩] := by
  obtain ⟨outcome, regs, after, stream, state, _, made, _, run, current, _, _, _, _, put, count, _⟩ :=
    inflate_dispatch_default_view_state_rank E invariant buffers incoming
  have frame := (inflate_dispatch_metadata_record_frame E mode run).buffer [⟨l.put, made⟩]
  refine ⟨outcome, regs, after, stream, state, made, run, current.good, count, put, ?_⟩
  simpa only [E.st, DecoderRecordRoot] using frame

#print axioms inflate_dispatch_metadata_record_frame
#print axioms inflate_dispatch_metadata_exact_frame
end Zlib.Inflate.Local
