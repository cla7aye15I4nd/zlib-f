import ZlibF.Proof.«gzlib.c.error-message-replacement»
import ZlibF.Proof.«gzwrite.c.direct-errno-source»

/-! # Actual writer close suffix and direct cleanup

This is the exact source suffix after gz_comp. On the direct path it releases
input, old/new owned message, private path and handle even when close(fd)
reports EBADF. No compressor contract or output allocation is involved.
-/
namespace Zlib.Gzwrite.DirectClose
open C Zlib.GzFs Zlib.Gzguts Zlib.Gzlib Zlib.Gzwrite Zlib.Deflate
open Zlib.Gzlib.Spec Zlib.Gzlib.Proofs ZlibF.Spec.Public ZlibF.Spec.Public.OffsetProof
open Zlib.Gzlib.MessageHistory Zlib.Gzlib.MessagePrevious

def closeTail (state : GzStatePtr) (initial : Int32) : G Int32 := do
  let mut ret := initial
  let s ← ldS state
  if s.size != 0 then
    if s.direct == 0 then
      let _ ← deflateEnd (strmOf state)
      freeB s.out
    freeB s.«in»
  gz_error state Z_OK .null
  let s ← ldS state
  freeB s.path
  if (← fsClose s.fd) == -1 then ret := Z_ERRNO
  freeGzState state
  return ret

def closeFromComp (state : GzStatePtr) : G Int32 := do
  let mut ret := Z_OK
  if (← gz_comp state Z_FINISH) == -1 then ret := (← ldS state).err
  closeTail state ret

/-- Kernel source cut for the same actual full writer close after its entry
checks. The RHS still executes the real translated gz_comp and suffix. -/
theorem gzclose_w_source {h : Heap} {i : Nat} {s : GzState}
    (hs : h.gzstates i = some s) (hm : s.mode = GZ_WRITE) (hskip : s.skip = 0) (fs : Fs) :
    gzclose_w (hnd i) fs h = closeFromComp (some (.tab i)) fs h := by
  unfold gzclose_w closeFromComp closeTail
  offsetsimp [hs,hm,hskip]

private theorem fsClose_badfd (fs : Fs) (fd : Int32) (h : Heap)
    (hfd : fd < 0 ∨ (fs.fds.size : Int) ≤ fd.toInt) :
    fsClose fd fs h = .ok ((-1,{fs with errno := EBADF}),h) := by
  rcases hfd with neg | large
  · simp [fsClose,neg,pure_app]
  · simp [fsClose,large,pure_app]

def inputFreedHeap (h : Heap) (b : Nat) : Heap := {h with bytes := upd h.bytes b none}
def messageFreedHeap (h : Heap) (i : Nat) (s : GzState) (b : Nat) : Heap :=
  clearMessageHeap (inputFreedHeap h b) i s Z_OK

def closedDirectHeap (h : Heap) (i : Nat) (s : GzState) (b path : Nat) : Heap :=
  let cleared := messageFreedHeap h i s b
  let released := {cleared with bytes := upd cleared.bytes path none}
  {released with gzstates := upd released.gzstates i none}

/-- The exact direct close suffix, including final message cleanup and an
actual failed close syscall. Separation is supplied from actual fresh malloc
history by the caller proof; no public domain is changed. -/
theorem close_tail_badfd_run {h : Heap} {i b path : Nat} {s : GzState}
    {input pathBytes : Array UInt8} (hs : h.gzstates i = some s)
    (hsize : s.size ≠ 0) (hdir : s.direct ≠ 0)
    (hin : s.«in» = .ref (.blk b) 0) (hb : h.bytes b = some input) (hro : h.ro b = false)
    (hp : s.path = .ref (.blk path) 0) (hpath : h.bytes path = some pathBytes) (hpathRo : h.ro path = false)
    (hbp : b ≠ path) (hc : ClearableMessage h s) (him : s.«in» ≠ s.msg) (hpm : s.path ≠ s.msg)
    (fs : Fs) (hfd : s.fd < 0 ∨ (fs.fds.size : Int) ≤ s.fd.toInt) (initial : Int32) :
    closeTail (some (.tab i)) initial fs h =
      .ok ((Z_ERRNO,{fs with errno := EBADF}),closedDirectHeap h i s b path) := by
  let hIn := inputFreedHeap h b
  let hMsg := messageFreedHeap h i s b
  let hPath := {hMsg with bytes := upd hMsg.bytes path none}
  have freeInput : freeB s.«in» h = .ok ((),hIn) := by rw [hin]; exact C.freeB_ok hb hro
  have hsIn : hIn.gzstates i = some s := hs
  have hcIn : ClearableMessage hIn s := by
    rcases hc with hm | ⟨mb,ma,hm,hmb,hmro,he⟩
    · exact Or.inl hm
    · have sep : mb ≠ b := by intro eq; subst mb; exact him (hin.trans hm.symm)
      refine Or.inr ⟨mb,ma,hm,?_,hmro,he⟩
      simpa [hIn,inputFreedHeap,sep] using hmb
  have clear := gz_error_clear_code_run hsIn hcIn Z_OK
  have pathIn : hIn.bytes path = some pathBytes := by
    simpa [hIn,inputFreedHeap,Ne.symm hbp] using hpath
  have keepPath := clear_previous_keeps_block (i := i) hcIn pathIn
    (show .ref (.blk path) 0 ≠ s.msg from fun eq => hpm (hp.trans eq))
  have hsMsg : hMsg.gzstates i = some {s with msg := .null,err := Z_OK} := by
    simp [hMsg,messageFreedHeap,clearMessageHeap,setS]
  have pathMsg : hMsg.bytes path = some pathBytes := keepPath.1
  have pathRoMsg : hMsg.ro path = false := keepPath.2.trans hpathRo
  have freePath : freeB s.path hMsg = .ok ((),hPath) := by rw [hp]; exact C.freeB_ok pathMsg pathRoMsg
  have close := fsClose_badfd fs s.fd hPath hfd
  have hsPath : hPath.gzstates i = some {s with msg := .null,err := Z_OK} := hsMsg
  have freeState := C.freeGzState_tab hsPath
  dsimp only [hIn,hMsg,hPath,messageFreedHeap] at clear hsMsg freePath close freeState
  unfold closeTail
  offsetsimp [hs,hsize,hdir,freeInput,clear,hsMsg,freePath,close,freeState,
    hIn,hMsg,hPath,messageFreedHeap,closedDirectHeap]

#print axioms gzclose_w_source
#print axioms close_tail_badfd_run
end Zlib.Gzwrite.DirectClose
