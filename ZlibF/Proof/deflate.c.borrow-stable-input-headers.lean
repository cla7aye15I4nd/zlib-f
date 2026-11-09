import ZlibF.Proof.«deflate.c.borrow-stable-base»
import ZlibF.Proof.«deflate.c.engine.common-header-buffered»
import ZlibF.Proof.«deflate.c.engine.common-header-boundary»

/-! # Actual header heap updates retain borrowed libc text -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
set_option autoImplicit false

/-- The exact default header heap changes byte and stream/state records only. -/
theorem header_complete_borrow_eq (h : Heap) (r : ZStreamRef) (ds pb ob oo : Nat)
    (z : ZStream) (d : DeflateState) (buf output : Array UInt8) :
    (headerCompleteHeap h r ds pb ob oo z d buf output).libcErrorBorrow = h.libcErrorBorrow := by
  change (r.put (headerCompleteBytes h pb ob oo buf output) (headerCompleteStream z ob oo)).libcErrorBorrow = _
  rw [Zlib.Deflate.BorrowProofs.stream_put_borrow]
  rfl

/-- The exact level-dependent completed header has the same actual receipt. -/
theorem level_header_complete_borrow_eq (h : Heap) (r : ZStreamRef) (ds pb ob oo : Nat)
    (z : ZStream) (d : DeflateState) (buf output : Array UInt8) :
    (levelHeaderCompleteHeap h r ds pb ob oo z d buf output).libcErrorBorrow = h.libcErrorBorrow := by
  change (r.put (levelHeaderCompleteBytes d.level h pb ob oo buf output) (headerCompleteStream z ob oo)).libcErrorBorrow = _
  rw [Zlib.Deflate.BorrowProofs.stream_put_borrow]
  rfl

/-- The exact one-byte level header retains the live libc borrow epoch. -/
theorem level_header_one_borrow_eq (h : Heap) (r : ZStreamRef) (ds pb ob oo : Nat)
    (z : ZStream) (d : DeflateState) (buf output : Array UInt8) :
    (levelHeaderOneHeap h r ds pb ob oo z d buf output).libcErrorBorrow = h.libcErrorBorrow := by
  change (r.put (levelHeaderOneBytes d.level h pb ob oo buf output)
    (pendingStream z (.ref (.blk ob) (oo + 1)) 1)).libcErrorBorrow = _
  rw [Zlib.Deflate.BorrowProofs.stream_put_borrow]
  rfl

end Zlib.Deflate.Engine.Proofs
