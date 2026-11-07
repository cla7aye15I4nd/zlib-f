import ZlibF.Runtime.Monad

/-!
# Low address bits of byte pointers

CRC observes only an address modulo eight. Raw blocks retain the existing
aligned-origin convention. Every static or embedded byte array has an
arbitrary, stable origin residue in the heap. No ABI field alignment is
silently replaced by zero. These residues are metadata, not writable bytes.
This does not provide general record layout or pointer-to-integer semantics.
-/

namespace C

def ByteBaseRef.toBRef : C.ByteBaseRef → BRef
  | .str id => .str id
  | .dstate_depth id => .dstate_depth id
  | .st_dist_code => .st_dist_code
  | .st_length_code => .st_length_code

namespace ByteAddress

/-- Origin residue. Raw heap blocks have the pre-existing aligned origin. -/
def base (h : Heap) : BRef → Nat
  | .blk _ => 0
  | .str id => (h.byteBase (.str id)).val
  | .dstate_depth id => (h.byteBase (.dstate_depth id)).val
  | .st_dist_code => (h.byteBase .st_dist_code).val
  | .st_length_code => (h.byteBase .st_length_code).val

/-- A representative whose low three bits agree with the represented
address. Upper address bits are not observed by the CRC translation. -/
def value (h : Heap) : BPtr → UInt64
  | .null => 0
  | .ref (.blk _) off => UInt64.ofNat off
  | .ref r off => UInt64.ofNat (base h r + off)

/-- Reading address metadata has no memory effect. -/
def address (p : BPtr) : M UInt64 := fun h => .ok (value h p, h)

end ByteAddress
end C
