import ZlibF.Proof.«deflate.c.engine.generic-header-ready»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- Private header stores leave every embedded-depth byte view exact. -/
theorem generic_zlib_header_ready_foreign_view {h : Heap} {r : ZStreamRef} {ds pb owner : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8}
    (state : h.dstates ds = some d) :
    Space.get (levelHeaderReady h r ds pb z d buf) (BRef.dstate_depth owner) =
      Space.get h (BRef.dstate_depth owner) := by
  rw [levelHeaderReady, byte_view_setD_depth (d := d) (result := levelHeaderState d)
    (by simpa only [ZStreamRef.put_dstates] using state) rfl, byte_get_stream_put]
  rfl

/-- The actual four private trailer stores leave the foreign caller view exact. -/
theorem generic_zlib_trailer_ready_foreign_view {h : Heap} {ds pb owner : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8}
    (state : h.dstates ds = some d) :
    Space.get (setD (Zlib.Trees.Proofs.Out.setB h pb (zlibTrailerBuffer buf z.adler)) ds
      {d with pending := 4}) (BRef.dstate_depth owner) = Space.get h (BRef.dstate_depth owner) := by
  rw [byte_view_setD_depth (h := Zlib.Trees.Proofs.Out.setB h pb (zlibTrailerBuffer buf z.adler))
    (d := d) (result := {d with pending := 4}) state rfl]
  rfl

end Zlib.Deflate.Engine.Proofs
#print axioms Zlib.Deflate.Engine.Proofs.generic_zlib_header_ready_foreign_view
#print axioms Zlib.Deflate.Engine.Proofs.generic_zlib_trailer_ready_foreign_view
