import ZlibF.Spec.Public.Streams

namespace ZlibF.Spec.Public
open C

def relocateCode (old fresh : Nat) : CodePtr → CodePtr
  | .ref (.istate_codes i) off => if i = old then .ref (.istate_codes fresh) off else .ref (.istate_codes i) off
  | p => p

def relocateByte (fresh old pointer : BPtr) : BPtr :=
  match fresh, old, pointer with
  | .ref r start, .ref _ base, .ref _ off => .ref r (start + off - base)
  | _, _, _ => .null

def SameBytePrefix (before after : Heap) (source dest : BPtr) (n : Nat) : Prop :=
  ∃ xs, Bytes before source n xs ∧ Bytes after dest n xs

def SameWordPrefix (before after : Heap) (source dest : WPtr) (n : Nat) : Prop :=
  ∃ r off a r' off' a', source = .ref r off ∧ dest = .ref r' off' ∧
    Space.get before r = some a ∧ Space.get after r' = some a' ∧
    off + n ≤ a.size ∧ off' + n ≤ a'.size ∧
    (a.toList.drop off).take n = (a'.toList.drop off').take n

def copiedDeflate (dest : ZStreamRef) (fresh : Nat) (old copied : DeflateState) : DeflateState :=
  { old with
    strm := some dest, window := copied.window, prev := copied.prev, head := copied.head
    pending_buf := copied.pending_buf
    pending_out := relocateByte copied.pending_buf old.pending_buf old.pending_out
    sym_buf := advance copied.pending_buf old.lit_bufsize.toNat
    l_desc := { old.l_desc with dyn_tree := .ref (.dstate_dyn_ltree fresh) 0 }
    d_desc := { old.d_desc with dyn_tree := .ref (.dstate_dyn_dtree fresh) 0 }
    bl_desc := { old.bl_desc with dyn_tree := .ref (.dstate_bl_tree fresh) 0 } }

end ZlibF.Spec.Public
