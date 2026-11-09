import ZlibF.Proof.«gzlib.c.open-mode-loop»

/-!
# gzlib.c: supplied-descriptor I/O for all parsed settings

The caller-supplied descriptor is retained even when an actual seek fails.
No descriptor validity, successful I/O, fixed level, or fixed strategy is assumed.
-/

namespace Zlib.Gzlib.Proofs
open C Zlib.GzFs Zlib.Gzguts Zlib.Gzlib.Spec ZlibF.Spec.Public.OffsetProof
open ZlibF.Math.GzModeParser

/-- Actual world after the read/append seek; ordinary writing has no seek. -/
def suppliedWorld (mode : ZlibF.Spec.Api.GzMode) (fd : Int32) (fs : Fs) : Fs :=
  match mode with
  | .read => (lseekRes fd 0 SEEK_CUR fs).2
  | .write => fs
  | .append => (lseekRes fd 0 SEEK_END fs).2

/-- Actual field writes before reset: read start normalization, or append's
mode transition. Other old fields, including inactive pointers, are preserved. -/
def suppliedRecord (s : GzState) (mode : ZlibF.Spec.Api.GzMode) (fd : Int32) (fs : Fs) : GzState :=
  { s with
    fd := fd
    mode := if mode = .append then GZ_WRITE else s.mode
    start := if mode = .read then
      (if (lseekRes fd 0 SEEK_CUR fs).1 = -1 then 0 else (lseekRes fd 0 SEEK_CUR fs).1)
      else s.start }

/-- Real supplied-fd post-copy source execution with arbitrary flag/exclusive
locals and arbitrary parsed level/strategy. Both fcntl calls are the actual
fixed-world operations; no contract for them is assumed. -/
theorem openAfterPath_supplied (h : Heap) (fs : Fs) (i : Nat) (s : GzState)
    (ml : ModeLoop) (path : BPtr) (fd : Int32) (mode : ZlibF.Spec.Api.GzMode)
    (hs : h.gzstates i = some s) (hm : s.mode = modeCode (some mode))
    (hmsg : s.msg = .null) (hfd : fd ≠ -1) :
    openAfterPath (some (.tab i)) path fd ml fs h =
      .ok ((some (.in_gzstate_x i), suppliedWorld mode fd fs),
        setS h i (resetRec (suppliedRecord s mode fd fs))) := by
  cases mode with
  | read =>
    let bits : Int32 := ml.oflag ||| O_LARGEFILE
    by_cases hnb : bits &&& O_NONBLOCK = 0 <;>
      by_cases hce : bits &&& O_CLOEXEC = 0 <;>
      by_cases he : (lseekRes fd 0 SEEK_CUR fs).1 = -1 <;>
      dsimp only [bits] at hnb hce <;>
      unfold openAfterPath <;>
      offsetsimp [hs, hm, hmsg, hfd, suppliedWorld, suppliedRecord, fsFcntl, hnb, hce, modeCode, gz_reset, gz_error, resetRec, setS, upd_upd, hnd, GZ_READ, GZ_WRITE, GZ_APPEND, he]
  | write =>
    let bits : Int32 := ml.oflag ||| (O_LARGEFILE ||| (O_WRONLY ||| O_CREAT ||| (if ml.exclusive = 0 then 0 else O_EXCL) ||| O_TRUNC))
    by_cases hnb : bits &&& O_NONBLOCK = 0 <;>
      by_cases hce : bits &&& O_CLOEXEC = 0 <;>
      dsimp only [bits] at hnb hce <;>
      unfold openAfterPath <;>
      offsetsimp [hs, hm, hmsg, hfd, suppliedWorld, suppliedRecord, fsFcntl, hnb, hce, modeCode, gz_reset, gz_error, resetRec, setS, upd_upd, hnd, GZ_READ, GZ_WRITE, GZ_APPEND]
  | append =>
    let bits : Int32 := ml.oflag ||| (O_LARGEFILE ||| (O_WRONLY ||| O_CREAT ||| (if ml.exclusive = 0 then 0 else O_EXCL) ||| O_APPEND))
    by_cases hnb : bits &&& O_NONBLOCK = 0 <;>
      by_cases hce : bits &&& O_CLOEXEC = 0 <;>
      dsimp only [bits] at hnb hce <;>
      unfold openAfterPath <;>
      offsetsimp [hs, hm, hmsg, hfd, suppliedWorld, suppliedRecord, fsFcntl, hnb, hce, modeCode, gz_reset, gz_error, resetRec, setS, upd_upd, hnd, GZ_READ, GZ_WRITE, GZ_APPEND]

/-- The actual supplied-fd execution establishes the public OS relation for
any original mode bytes; no syscall opens a second descriptor. -/
theorem suppliedWorld_OpenWorld (h : Heap) (fs : Fs) (fd : Int32) (s : GzState)
    (mode : ZlibF.Spec.Api.GzMode) (flags : List UInt8)
    (hm : s.mode = modeCode (some mode)) (hfd : fd ≠ -1) :
    ZlibF.Spec.Public.OpenWorld h fs (suppliedWorld mode fd fs) [] flags mode (some fd) fd
      (resetRec (suppliedRecord s mode fd fs)).start := by
  refine ⟨fs, ⟨rfl, rfl⟩, ?_⟩
  cases mode with
  | read =>
    simp only [hfd, ite_false, suppliedWorld]
    exact ⟨_, fsLseek_eq _ _ _ _ _, by simp [suppliedRecord, resetRec, hm, modeCode, GZ_READ, fsLseek_eq]⟩
  | write => simp [hfd, suppliedWorld]
  | append =>
    simp only [hfd, ite_false, suppliedWorld]
    exact ⟨_, fsLseek_eq _ _ _ _ _⟩

/-- Primitive fields established by real initialization/path allocation give
OpenState after the actual reset, for any parser level and strategy. -/
theorem suppliedHeap_OpenState (h : Heap) (i pb : Nat) (s : GzState) (fs : Fs)
    (mode : ZlibF.Spec.Api.GzMode) (level : Int) (strategy : Nat) (direct : Int)
    (fd : Int32) (name : List UInt8)
    (hs : h.gzstates i = some s) (hm : s.mode = modeCode (some mode))
    (hprivate : s.path = .ref (.blk pb) 0) (hsize : s.size = 0) (hwant : s.want = 8192)
    (hlevel : s.level.toInt = level) (hstrategy : s.strategy.toInt = (strategy : Int))
    (hdirect : s.direct.toInt = if mode = .read ∧ direct = 0 then 1 else direct)
    (hf : Fresh h) (hu : Uniq h) (hg : ZlibF.Spec.Public.LibraryGlobals h)
    (hpath : ZlibF.Spec.Public.CString h (.ref (.blk pb) 0) name)
    (hbuf : ZlibF.Spec.Public.MallocBuffer h (.ref (.blk pb) 0) (name.length + 1)) :
    ZlibF.Spec.Public.OpenState (setS h i (resetRec (suppliedRecord s mode fd fs))) i
      (resetRec (suppliedRecord s mode fd fs)) mode level strategy direct fd name := by
  let final := resetRec (suppliedRecord s mode fd fs)
  have hshape := shape_setS hs final
  have hpf := openCString_setS h i final (.ref (.blk pb) 0) name hpath
  have hbf := openMallocBuffer_setS h i final (.ref (.blk pb) 0) (name.length + 1) hbuf
  have hfinalPath : final.path = .ref (.blk pb) 0 := by
    cases mode <;> simp [final, suppliedRecord, resetRec, hm, hprivate, modeCode, GZ_READ, GZ_WRITE]
  have hv : ZlibF.Spec.Public.GzValid (setS h i final) i final := by
    refine ⟨by simp [setS], ?_, Shape.fresh hshape rfl hf, Shape.uniq hshape hu,
      hg, ⟨name, ?_, ?_⟩, Or.inl ?_, ?_, ?_, ?_, ?_, ?_⟩
    · cases mode <;> simp [final, suppliedRecord, resetRec, hm, modeCode, GZ_READ, GZ_WRITE]
    · simpa only [hfinalPath] using hpf
    · simpa only [hfinalPath] using hbf
    · cases mode <;> simp [final, suppliedRecord, resetRec, hm, modeCode, GZ_READ, GZ_WRITE]
    · intro _
      cases mode <;> simp [final, suppliedRecord, resetRec, hm, modeCode, GZ_READ, GZ_WRITE]
    · cases mode <;> simp [final, suppliedRecord, resetRec, hwant, hm, modeCode, GZ_READ, GZ_WRITE]
    · cases mode <;> simp [final, suppliedRecord, resetRec, hwant, hm, modeCode, GZ_READ, GZ_WRITE]
    · cases mode <;> simp [final, suppliedRecord, resetRec, hsize, hm, modeCode, GZ_READ, GZ_WRITE]
    · cases mode <;> simp [final, suppliedRecord, resetRec, hm, modeCode, GZ_READ, GZ_WRITE]
  refine ⟨hv, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (change ZlibF.Spec.Public.CString (setS h i final) final.path name
       rw [hfinalPath]
       exact hpf)
    | (cases mode <;> simp [resetRec, suppliedRecord, hm, hprivate, hsize, hwant,
        hlevel, hstrategy, hdirect, modeCode, GZ_READ, GZ_WRITE])

/-- Actual seeks/fcntl/reset allocate nothing and change only this existing
handle. The same heap has exact preservation of every live object kind. -/
theorem suppliedHeap_ledger (h : Heap) (i : Nat) (s : GzState) (fs : Fs)
    (mode : ZlibF.Spec.Api.GzMode) (fd : Int32) (hs : h.gzstates i = some s) :
    ZlibF.Spec.Public.Frame h (setS h i (resetRec (suppliedRecord s mode fd fs))) (fun b => b = i) ∧
    ZlibF.Spec.Public.LiveChange h (setS h i (resetRec (suppliedRecord s mode fd fs)))
      (fun _ => False) (fun _ => False) := by
  exact openModeLoop_frame h i s _ hs

#print axioms openAfterPath_supplied
#print axioms suppliedWorld_OpenWorld
#print axioms suppliedHeap_ledger
#print axioms suppliedHeap_OpenState
end Zlib.Gzlib.Proofs
