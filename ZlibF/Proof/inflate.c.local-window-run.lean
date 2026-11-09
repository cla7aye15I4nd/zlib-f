import ZlibF.Proof.«inflate.c.local-window-state»
import ZlibF.Proof.«inflate.c.local-window-platform»

/-! The allocation origin and exact executable heap for a fresh window.
These actual identities retain the stronger age needed to exclude local
reserved objects; no caller-wide uniqueness premise is added. -/
namespace Zlib.Inflate.Local
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

def localWindowSize (s : InflateState) : Nat := ((1 <<< s.wbits : UInt32) * 1).toNat

def localWindowArray (h : Heap) (s : InflateState) : Array UInt8 :=
  Array.ofFn (n := localWindowSize s) fun i => Junk.of (h.garbage h.nalloc i.val)

def localWindowPrior (h : Heap) (zs : Nat) (s : InflateState) : Heap :=
  setI (Zlib.Zutil.Proofs.allocHeap h (localWindowSize s)) zs (withWin s h.nextBlk)

def localWindowNewState (h : Heap) (s : InflateState) (bytes : Array UInt8)
    (eo : Nat) (copy : UInt32) : InflateState :=
  (uwPost (initWinS (withWin s h.nextBlk)) (localWindowArray h s) bytes eo copy).2

def localWindowNewHeap (h : Heap) (zs : Nat) (s : InflateState) (bytes : Array UInt8)
    (eo : Nat) (copy : UInt32) : Heap :=
  let prior := localWindowPrior h zs s
  setI {setI prior zs (initWinS (withWin s h.nextBlk)) with
    bytes := upd prior.bytes h.nextBlk
      (some (uwPost (initWinS (withWin s h.nextBlk)) (localWindowArray h s) bytes eo copy).1)}
    zs (localWindowNewState h s bytes eo copy)

/-- The actual allocator, all initial field writes and ring copy compute this
exact same final heap. Caller byte storage may collide in old typed tables. -/
theorem uw_new_local_exact {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {eo : Nat} {source : BRef} {bytes : Array UInt8} {copy : UInt32}
    (good : LocalGood h cutoff r zs z s) (allocator : z.zalloc = .fn "zcalloc")
    (window : s.window = .null) (allocated : h.allocOk h.nalloc = true)
    (get : Space.get h source = some bytes) (count : copy.toNat ≤ eo) (bound : eo ≤ bytes.size) :
    updatewindow (some r) (.ref source eo) copy h =
      .ok (0, localWindowNewHeap h zs s bytes eo copy) := by
  have sourceFresh : source ≠ .blk h.nextBlk := by
    intro he
    subst source
    have absent := Fresh.bytes good.fresh (Nat.le_refl h.nextBlk)
    change h.bytes h.nextBlk = some bytes at get
    rw [get] at absent
    contradiction
  have arraySize : (localWindowArray h s).size = 2 ^ s.wbits.toNat := by
    simp only [localWindowArray, Array.size_ofFn, localWindowSize, UInt32.mul_one]
    exact shl_toNat_aux good.inv.win.wbits
  have live : Live (localWindowPrior h zs s) r zs z (withWin s h.nextBlk) := by
    refine ⟨?_, by simp [localWindowPrior, setI], good.live.zst, good.live.back,
      good.live.mode, good.live.zalloc, good.live.zfree⟩
    cases r <;> simpa [ZStreamRef.get, localWindowPrior, setI, Zlib.Zutil.Proofs.allocHeap] using good.live.hz
  have arrayGet : (localWindowPrior h zs s).bytes h.nextBlk = some (localWindowArray h s) := by
    simp [localWindowPrior, localWindowArray, localWindowSize, Zlib.Zutil.Proofs.allocHeap, setI]
  have arrayRo : (localWindowPrior h zs s).ro h.nextBlk = false := by
    simp [localWindowPrior, Zlib.Zutil.Proofs.allocHeap, setI]
  have sourceGet : Space.get (localWindowPrior h zs s) source = some bytes := by
    cases source with
    | blk b =>
      have ne : b ≠ h.nextBlk := fun he => sourceFresh (by rw [he])
      simpa [localWindowPrior, Zlib.Zutil.Proofs.allocHeap, setI, upd_ne _ _ _ _ ne] using get
    | str b => exact get
    | st_dist_code => exact get
    | st_length_code => exact get
    | dstate_depth b => exact get
  have separate : Separate (.ref source (eo - copy.toNat)) copy.toNat
      (withWin s h.nextBlk).window (2 ^ (withWin s h.nextBlk).wbits.toNat) := by
    simp [Separate, withWin, sourceFresh]
  rw [uw_alloc_ok good.live allocator good.inv.win.wbits window allocated good.fresh]
  exact uw_main_public live rfl arrayGet arrayRo good.inv.win.wbits arraySize
    good.inv.win.ws good.inv.win.wn sourceGet count bound separate

/-- The exact origin is the pre-allocation next identity, not merely cutoff. -/
theorem localWindowNewState_origin (h : Heap) (s : InflateState) (bytes : Array UInt8)
    (eo : Nat) (copy : UInt32) :
    (localWindowNewState h s bytes eo copy).window = .ref (.blk h.nextBlk) 0 := by
  unfold localWindowNewState uwPost initWinS
  repeat' split
  all_goals rfl

theorem localWindowNewHeap_counts (h : Heap) (zs : Nat) (s : InflateState)
    (bytes : Array UInt8) (eo : Nat) (copy : UInt32) :
    (localWindowNewHeap h zs s bytes eo copy).nextBlk = h.nextBlk + 1 ∧
    (localWindowNewHeap h zs s bytes eo copy).nalloc = h.nalloc + 1 ∧
    (localWindowNewHeap h zs s bytes eo copy).allocOk = h.allocOk := by
  exact ⟨rfl, rfl, rfl⟩

/-- The new allocation's final shape is unchanged by all real ring writes. -/
theorem localWindowNewHeap_shape {h : Heap} {zs : Nat} {s : InflateState}
    (stored : h.istates zs = some s) (bytes : Array UInt8) (eo : Nat) (copy : UInt32) :
    Shape (Zlib.Zutil.Proofs.allocHeap h (localWindowSize s))
      (localWindowNewHeap h zs s bytes eo copy) := by
  let allocated := Zlib.Zutil.Proofs.allocHeap h (localWindowSize s)
  have start : allocated.istates zs = some s := stored
  have first := shape_setI start (withWin s h.nextBlk)
  have second := shape_setI (zs := zs) (h := localWindowPrior h zs s)
    (s0 := withWin s h.nextBlk) (by simp [localWindowPrior, setI]) (initWinS (withWin s h.nextBlk))
  have arrayGet : (setI (localWindowPrior h zs s) zs (initWinS (withWin s h.nextBlk))).bytes h.nextBlk =
      some (localWindowArray h s) := by
    simp [localWindowPrior, localWindowArray, localWindowSize, Zlib.Zutil.Proofs.allocHeap, setI]
  have third := shape_setB arrayGet
    (uwPost (initWinS (withWin s h.nextBlk)) (localWindowArray h s) bytes eo copy).1
  have fourth := shape_setI (zs := zs) (h := {setI (localWindowPrior h zs s) zs (initWinS (withWin s h.nextBlk)) with
      bytes := upd (localWindowPrior h zs s).bytes h.nextBlk
        (some (uwPost (initWinS (withWin s h.nextBlk)) (localWindowArray h s) bytes eo copy).1)})
    (s0 := initWinS (withWin s h.nextBlk)) (by simp [setI]) (localWindowNewState h s bytes eo copy)
  exact first.trans (second.trans (third.trans fourth))

/-- The actual fresh window creates exactly one malloc identity, regardless
of old caller typed collisions. -/
theorem localWindowNewHeap_live {h : Heap} {zs : Nat} {s : InflateState}
    (stored : h.istates zs = some s) (bytes : Array UInt8) (eo : Nat) (copy : UInt32) :
    LiveChange h (localWindowNewHeap h zs s bytes eo copy) (fun b => b = h.nextBlk) (fun _ => False) := by
  have allocated := (Zlib.Zutil.Proofs.allocHeap_frame h (localWindowSize s)).1
    h.live (fun _ => Iff.rfl)
  intro b
  rw [Shape.live (localWindowNewHeap_shape stored bytes eo copy) b]
  simpa [Heap.Owns] using allocated b

/-- Every old caller object outside the owned stream/state/window footprint
has the exact original bytes, object table entry and readonly metadata. -/
theorem localWindowNewHeap_frame {h : Heap} {r : ZStreamRef} {zs : Nat} {s : InflateState}
    (fresh : Fresh h) (bytes : Array UInt8) (eo : Nat) (copy : UInt32) :
    Frame h (localWindowNewHeap h zs s bytes eo copy)
      (fun b => StreamRoot r b ∨ InflateOwned zs s b) := by
  simpa only [localWindowNewHeap, localWindowPrior] using
    (uw_new_frame (r := r) (zs := zs) (st := s)
      (st0 := withWin s h.nextBlk) (st1 := initWinS (withWin s h.nextBlk))
      (st2 := localWindowNewState h s bytes eo copy)
      (n := localWindowSize s)
      (a := (uwPost (initWinS (withWin s h.nextBlk)) (localWindowArray h s) bytes eo copy).1) fresh)

#print axioms uw_new_local_exact
#print axioms localWindowNewState_origin
#print axioms localWindowNewHeap_counts
#print axioms localWindowNewHeap_shape
#print axioms localWindowNewHeap_live
#print axioms localWindowNewHeap_frame
end Zlib.Inflate.Local
