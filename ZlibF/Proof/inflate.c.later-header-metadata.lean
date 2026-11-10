import ZlibF.Proof.«inflate.c.header-payload-progress»
import ZlibF.Proof.«inflate.c.wrapper-output-credit»
import ZlibF.Proof.«inflate.c.block-source-gate»
namespace Zlib.Inflate.Proofs.LaterHeader
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.WrapperGlue
set_option autoImplicit false

/-- The actual block/header constructors change only tag, count, length
and table metadata. Window contents and checksum credit remain live. -/
def HeaderFrame (before after : InflateState) : Prop :=
  after = {before with last := after.last, ncode := after.ncode, nlen := after.nlen, ndist := after.ndist, lens := after.lens, «have» := after.«have», work := after.work, codes := after.codes, next := after.next, lencode := after.lencode, distcode := after.distcode, lenbits := after.lenbits, distbits := after.distbits, mode := after.mode}

theorem HeaderFrame.trans {a b d : InflateState} (first : HeaderFrame a b) (second : HeaderFrame b d) : HeaderFrame a d := by
  unfold HeaderFrame at *
  rw [second, first]

theorem HeaderFrame.credit {z : ZStream} {s state : InflateState} {credited : List UInt8}
    (frame : HeaderFrame s state) (credit : AdlerCredit z s credited) : AdlerCredit z state credited := by
  rw [frame]
  exact credit

/-- Retained chronological history is transported across real private
header writes; no empty saved window or earlier output premise is used. -/
theorem HeaderFrame.dictionary {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {s state : InflateState} {history : List UInt8}
    (good : Good h r zs z s) (frame : HeaderFrame s state)
    (dictionary : InflateDictionary h s history) :
    InflateDictionary (setI h zs state) state history := by
  rcases dictionary with ⟨zero, empty⟩ | ⟨ref, off, a, window, get, bound, values⟩
  · exact Or.inl ⟨by rw [frame]; exact zero, empty⟩
  · rcases good.inv.win.block with null | ⟨b, bytes, ptr, _get, _ro, _size⟩
    · rw [null] at window
      cases window
    · rw [ptr] at window
      cases window
      refine Or.inr ⟨.blk b, 0, a, ?_, ?_, ?_, ?_⟩
      · rw [frame]; exact ptr
      · simpa only [Space.get, BRef.get_blk, setI] using get
      · rw [frame]; exact bound
      · rw [frame]; exact values

/-- The actual completed code-length reader and two table constructors
retain the incoming checksum and saved window, together with BFINAL.
The source stream is identical, hence its allocator callbacks are too. -/
theorem code_boundary_metadata
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8} {decoded : List Nat} {future rest : List Bool}
    {credited history : List UInt8}
    (before : DefaultOriginState h r zs z s)
    (b : PayloadPhaseView.CodeBoundary c h r zs z s l bs decoded future rest)
    (credit : AdlerCredit z s credited) (dictionary : InflateDictionary h s history) :
    HeaderFrame s b.state ∧ AdlerCredit z b.state credited ∧
      InflateDictionary (setI h zs b.state) b.state history ∧ b.state.last = s.last := by
  have frame : HeaderFrame s b.state := by
    unfold HeaderFrame
    rw [b.metadata, b.readFrame]
  exact ⟨frame, frame.credit credit, frame.dictionary before.good dictionary, by rw [b.metadata, b.readFrame]⟩

#print axioms HeaderFrame.trans
#print axioms HeaderFrame.credit
#print axioms HeaderFrame.dictionary
#print axioms code_boundary_metadata
end Zlib.Inflate.Proofs.LaterHeader
