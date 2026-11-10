import ZlibF.Proof.«inflate.c.payload-adler-source»
import ZlibF.Proof.«inflate.c.whole-payload-trip-source»
namespace Zlib.Inflate.Proofs.PayloadAdler
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs
set_option autoImplicit false

/-- Every real slow payload branch retains the public Adler field.
Only the diagnostic message is written by rejection; this proof observes
source effects independently of whether parsing succeeds. -/
theorem data_slow_frame
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l regs : IL} {outcome : Except Ex Unit}
    (E : Env c h r zs z s) (mode : DataTableMode s.mode)
    (slow : s.mode = LEN_ ∨ s.mode = LEN → ¬ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true)
    (actual : runX (inflate_dispatch c) l h = .ok ((outcome, regs), after)) :
    AdlerStreamFrame r h after := by
  rcases mode with selected | selected | selected | selected | selected | selected | selected
  · rw [inflate_dispatch_LEN_start E l selected] at actual
    unfold inflate_LEN_ at actual
    rw [runX_bind, runX_setMode E] at actual
    change runX (inflate_LEN c) l (setI h zs {s with mode := LEN}) = .ok ((outcome, regs), after) at actual
    rw [inflate_LEN_slow_cut (slow (Or.inl selected))] at actual
    have observed := adlerStreamX_lenSlow r c E.strm l _ outcome regs after actual
    simpa only [AdlerStreamFrame, ZStreamRef.get_setI] using observed
  · rw [inflate_dispatch_LEN E l selected, inflate_LEN_slow_cut (slow (Or.inr selected))] at actual
    exact adlerStreamX_lenSlow r c E.strm l h outcome regs after actual
  · rw [inflate_dispatch_LENEXT E l selected] at actual
    exact adlerStreamX_inflate_LENEXT r c E.strm l h outcome regs after actual
  · rw [inflate_dispatch_DIST E l selected] at actual
    exact adlerStreamX_inflate_DIST r c E.strm l h outcome regs after actual
  · rw [inflate_dispatch_DISTEXT E l selected] at actual
    exact adlerStreamX_inflate_DISTEXT r c E.strm l h outcome regs after actual
  · rw [inflate_dispatch_MATCH E l selected] at actual
    exact adlerStreamX_inflate_MATCH r c E.strm l h outcome regs after actual
  · rw [inflate_dispatch_LIT E l selected] at actual
    exact adlerStreamX_inflate_LIT r c E.strm l h outcome regs after actual

#print axioms data_slow_frame
end Zlib.Inflate.Proofs.PayloadAdler
namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs
set_option autoImplicit false

theorem PayloadTrip.slow_adler
    {c : Ctx} {entryHeap h after : Heap} {r : ZStreamRef} {zs : Nat}
    {entryZ z : ZStream} {s : InflateState} {l regs : IL} {base : DataLog} {raw : List UInt8}
    {outcome : Except Ex Unit} {before : EpochCallCut c entryHeap h r zs entryZ z s l base raw}
    (trip : PayloadTrip before after regs outcome) (mode : DataTableMode s.mode)
    (slow : s.mode = LEN_ ∨ s.mode = LEN → ¬ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    trip.stream.adler = z.adler := by
  have observed := PayloadAdler.data_slow_frame before.framed.cut.env mode slow trip.actual
  change (r.get after).map (·.adler) = (r.get h).map (·.adler) at observed
  rw [trip.origin.good.live.hz, before.framed.cut.origin.good.live.hz] at observed
  exact Option.some.inj observed

#print axioms PayloadTrip.slow_adler
end Zlib.Inflate.Proofs.WholeEpoch
