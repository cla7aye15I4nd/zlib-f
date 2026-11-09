import ZlibF.Proof.«inflate.c.base»
import ZlibF.Proof.«borrowed-byte-frame»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate.Spec
set_option autoImplicit false

/-- Any admitted writable byte view can be replaced and then read back. -/
theorem byte_view_get_put {h : Heap} {ref : BRef} {old : Array UInt8}
    (get : Space.get h ref = some old) (write : Space.ro h ref = false) (array : Array UInt8) :
    Space.get (Space.put h ref array) ref = some array := by
  cases ref with
  | blk id => simp [Space.get, Space.put]
  | str id => simp [Space.ro] at write
  | dstate_depth id =>
    cases state : h.dstates id with
    | none => simp [Space.get, state] at get
    | some s => simp [Space.get, Space.put, state]
  | st_dist_code => simp [Space.ro] at write
  | st_length_code => simp [Space.ro] at write

/-- Replacing a byte array does not change whether its view is writable. -/
theorem byte_view_ro_put (h : Heap) (ref : BRef) (array : Array UInt8) :
    Space.ro (Space.put h ref array) ref = Space.ro h ref := by
  cases ref <;> simp [Space.put, Space.ro]

/-- Writes to one byte view leave a distinct byte view unchanged. -/
theorem byte_view_get_put_ne (h : Heap) {dest source : BRef} (different : source ≠ dest) (array : Array UInt8) :
    (Space.get (Space.put h dest array) source : Option (Array UInt8)) = Space.get h source :=
  ZlibF.Spec.Public.BorrowedViews.get_put_other h different array

/-- Successive replacements of a writable view collapse to the last one. -/
theorem byte_view_put_put {h : Heap} {ref : BRef} {old : Array UInt8}
    (get : Space.get h ref = some old) (write : Space.ro h ref = false) (first second : Array UInt8) :
    Space.put (Space.put h ref first) ref second = Space.put h ref second := by
  cases ref with
  | blk id => simp [Space.put, upd_upd]
  | str id => simp [Space.ro] at write
  | dstate_depth id =>
    cases state : h.dstates id with
    | none => simp [Space.get, state] at get
    | some s => simp [Space.put, state, upd_upd]
  | st_dist_code => simp [Space.ro] at write
  | st_length_code => simp [Space.ro] at write

/-- Writing an existing writable byte view back unchanged leaves the heap unchanged. -/
theorem byte_view_put_self {h : Heap} {ref : BRef} {old : Array UInt8}
    (get : Space.get h ref = some old) (write : Space.ro h ref = false) :
    Space.put h ref old = h := by
  cases ref with
  | blk id => simp only [Space.get] at get; simp [Space.put, upd_self _ _ _ get]
  | str id => simp [Space.ro] at write
  | dstate_depth id =>
    cases state : h.dstates id with
    | none => simp [Space.get, state] at get
    | some s =>
      have same : s.depth = old := by simpa [Space.get, state] using get
      rw [← same]
      simp [Space.put, state, upd_self _ _ _ state]
  | st_dist_code => simp [Space.ro] at write
  | st_length_code => simp [Space.ro] at write

/-- Inflate scalar records and byte views occupy different storage. -/
theorem byte_view_get_setI (h : Heap) (zs : Nat) (s : InflateState) (ref : BRef) :
    (Space.get (setI h zs s) ref : Option (Array UInt8)) = Space.get h ref := by
  cases ref <;> rfl

theorem byte_view_ro_setI (h : Heap) (zs : Nat) (s : InflateState) (ref : BRef) :
    Space.ro (setI h zs s) ref = Space.ro h ref := by
  cases ref <;> rfl

theorem byte_view_put_setI (h : Heap) (zs : Nat) (s : InflateState) (ref : BRef) (array : Array UInt8) :
    Space.put (setI h zs s) ref array = setI (Space.put h ref array) zs s := by
  cases ref <;> simp only [Space.put, setI]
  split <;> rfl

theorem byte_view_put_istates (h : Heap) (ref : BRef) (array : Array UInt8) :
    (Space.put h ref array).istates = h.istates := by
  cases ref <;> simp only [Space.put]
  split <;> rfl

theorem byte_view_put_stream (h : Heap) (ref : BRef) (array : Array UInt8) (r : ZStreamRef) :
    r.get (Space.put h ref array) = r.get h := by
  cases ref <;> cases r <;> simp only [Space.put, ZStreamRef.get]
  all_goals split <;> rfl

theorem byte_view_get_stream_put (h : Heap) (r : ZStreamRef) (z : ZStream) (ref : BRef) :
    (Space.get (r.put h z) ref : Option (Array UInt8)) = Space.get h ref := by
  cases ref <;> cases r <;> simp only [Space.get, ZStreamRef.put]
  all_goals split <;> rfl

theorem byte_view_ro_stream_put (h : Heap) (r : ZStreamRef) (z : ZStream) (ref : BRef) :
    Space.ro (r.put h z) ref = Space.ro h ref := by
  cases ref <;> cases r <;> simp only [Space.ro, ZStreamRef.put]
  all_goals split <;> rfl

end Zlib.Inflate.Proofs
