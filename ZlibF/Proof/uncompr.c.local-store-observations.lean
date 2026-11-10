import ZlibF.Proof.«uncompr.c.local-wrapper-stores»

namespace Zlib.Uncompr.Proof.LocalStoreObservations
open C ZlibF.Spec.Public Zlib.Inflate.Spec Zlib.Inflate.Proofs
open Zlib.Uncompr.Proof.Cells Zlib.Uncompr.Proof.Writeback
set_option autoImplicit false

/-- An exact eight-byte Store exposes its actual scalar value. -/
theorem store_cell {h after : Heap} {p : BPtr} {value : UInt64}
    (store : Store h p (lengthBytes value) after) : LengthCell after p value := by
  rcases store with ⟨empty, _⟩ | ⟨ref, off, a, ptr, get, write, room, same⟩
  · simp [lengthBytes] at empty
  · subst p
    have room8 : off + 8 ≤ a.size := by simpa [lengthBytes] using room
    subst after
    change LengthCell (Space.put h ref (scalarSlice a off value)) (.ref ref off) value
    have newGet := byte_view_get_put get write (scalarSlice a off value)
    have newWrite : Space.ro (Space.put h ref (scalarSlice a off value)) ref = false := by
      rw [byte_view_ro_write]; exact write
    have size := scalarSlice_size a off value room8
    constructor
    · exact Or.inr ⟨ref,off,scalarSlice a off value,rfl,newGet,by rw [size];exact room8,
        (scalarSlice_bytes a off value room8).symm⟩
    · exact Or.inr ⟨ref,off,scalarSlice a off value,rfl,newGet,newWrite,by rw [size];exact room8⟩

/-- A complete Frame preserves a real scalar cell; no table-function
extensionality is used. -/
theorem frame_cell {h after : Heap} {p : BPtr} {value : UInt64}
    (frame : Frame h after (fun _ => False)) (cell : LengthCell h p value) : LengthCell after p value := by
  rcases cell.1 with null | ⟨ref,off,a,ptr,get,room,values⟩
  · have impossible := cell.2
    rw [null.1] at impossible
    simp [Writable] at impossible
  · subst p
    have outside (b : Nat) (root : ByteRoot (.ref ref off) b) : h.live b ∧ ¬ (fun _ => False) b := by
      refine ⟨?_,by simp⟩
      cases ref with
      | blk i =>
        change b = i at root
        subst b
        exact Or.inl (by simp [show h.bytes i = some a from get])
      | dstate_depth i =>
        change b = i at root
        subst b
        cases hs : h.dstates i with
        | none => simp [Space.get,hs] at get
        | some s => simp [Heap.live,hs]
      | str i => cases root
      | st_dist_code => cases root
      | st_length_code => cases root
    have write : Space.ro h ref = false := by
      rcases cell.2 with impossible | ⟨ref',off',a',same,get',write,_⟩
      · cases impossible.1
      · cases same
        exact write
    have stable : C.LibcBorrow.BorrowStable h after ref := by
      cases ref with
      | str i => simp [Space.ro] at write
      | _ => trivial
    have views := frame.byte_view_eq outside stable
    exact ⟨Or.inr ⟨ref,off,a,rfl,views.1.symm ▸ get,room,values⟩,
      Or.inr ⟨ref,off,a,rfl,views.1.symm ▸ get,views.2.trans write,room⟩⟩

/-- On the same expected-store chain, the final actual heap contains the
two stored scalar values. Separate slices in one object are allowed. -/
theorem counted_cells {first second expected actual : Heap} {sourceLen destLen : BPtr}
    {consumed produced : UInt64}
    (sourceStore : Store first sourceLen (lengthBytes consumed) second)
    (destStore : Store second destLen (lengthBytes produced) expected)
    (frame : Frame expected actual (fun _ => False))
    (separate : Separate sourceLen 8 destLen 8) :
    LengthCell actual sourceLen consumed ∧ LengthCell actual destLen produced := by
  have source := store_cell sourceStore
  have finalSource : LengthCell expected sourceLen consumed :=
    ⟨store_length_keep_bytes destStore source.1 separate,
      store_length_keep_writable destStore source.2 separate⟩
  exact ⟨frame_cell frame finalSource,frame_cell frame (store_cell destStore)⟩

#print axioms store_cell
#print axioms frame_cell
#print axioms counted_cells
end Zlib.Uncompr.Proof.LocalStoreObservations
