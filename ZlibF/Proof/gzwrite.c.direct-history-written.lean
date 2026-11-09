import ZlibF.Proof.«gzwrite.c.direct-history-prefix»
import ZlibF.Proof.«gzwrite.c.direct-errno-owned»

/-! # Facts on the same real first-write result

The private path remains readable after the new input allocation and copy.
Freshness follows the real allocation ledger and existing-object updates.
These facts connect the first public history to the complete flush theorem;
none is a caller contract or a new global uniqueness premise.
-/
namespace Zlib.Gzwrite.DirectHistory
open C Zlib.GzFs Zlib.Gzguts Zlib.Gzlib Zlib.Gzwrite Zlib.Gzlib.Spec Zlib.Gzlib.Proofs
open ZlibF.Spec.Public Zlib.Gzwrite.Proofs

def firstWrittenState (h : Heap) (s : GzState) (n : UInt32) : GzState :=
  let base := directInitRec (configuredState s) h.nextBlk
  { base with strm := {base.strm with next_in := base.«in»,avail_in := n}
              x := {base.x with pos := Int64.ofInt (base.x.pos.toInt + (n.toNat : Int))} }

private theorem write_shape {h : Heap} {i b : Nat} {s : GzState} {a src : Array UInt8}
    (hs : h.gzstates i = some s) (hb : h.bytes b = some a) (off : Nat) (n : UInt32) :
    Shape h (writeEmptyHeap h i b s a src off n) := by
  let bytesHeap := {h with bytes := upd h.bytes b (some (copyRange a src 0 off n.toNat))}
  have before : Shape h bytesHeap := by
    intro j
    by_cases eq : j = b
    · subst j
      simp [bytesHeap,hb]
    · simp [bytesHeap,eq]
  unfold writeEmptyHeap
  apply Shape.trans before
  exact shape_setS (h := bytesHeap) hs _

/-- The exact returned record and buffered bytes come from the real write's
already frozen heap expression. -/
theorem first_written_observations (h : Heap) (i : Nat) (s : GzState) (src : Array UInt8)
    (off : Nat) (n : UInt32) :
    (firstWrittenHeap h i s src off n).gzstates i = some (firstWrittenState h s n) ∧
    (firstWrittenHeap h i s src off n).bytes h.nextBlk =
      some (copyRange (initBufferBytes h (configuredState s)) src 0 off n.toNat) ∧
    (firstWrittenHeap h i s src off n).nextBlk = h.nextBlk+1 ∧
    (firstWrittenHeap h i s src off n).nalloc = h.nalloc+1 := by
  simp [firstWrittenHeap,firstWrittenState,writeEmptyHeap,directInitHeap,directInitAlloc,
    directInitRec,configuredHeap,setS]

/-- No new live object exists beyond the real allocation cursor. Updating an
existing typed record and byte block cannot invalidate allocation freshness. -/
theorem first_written_fresh {h : Heap} {i : Nat} {s : GzState} {src : Array UInt8}
    (hs : h.gzstates i = some s) (hf : Fresh h) (off : Nat) (n : UInt32) :
    Fresh (firstWrittenHeap h i s src off n) := by
  let cfg := configuredHeap h i s
  let ready := directInitHeap cfg i (configuredState s)
  have hsCfg : cfg.gzstates i = some (configuredState s) := by simp [cfg,configuredHeap]
  have hfCfg : Fresh cfg := Shape.fresh (shape_setS hs (configuredState s)) rfl hf
  have ledger := (directInitHeap_ledger hsCfg hfCfg).2
  have hfReady : Fresh ready := by
    intro j hj hl
    have live := (ledger j).1 hl
    change h.nextBlk+1 ≤ j at hj
    rcases live with old | new
    · exact hfCfg j (by change h.nextBlk ≤ j; omega) old.1
    · change j = h.nextBlk at new
      omega
  have hsReady : ready.gzstates i = some (directInitRec (configuredState s) h.nextBlk) := by
    simp [ready,cfg,directInitHeap,configuredHeap]
  have hbReady : ready.bytes h.nextBlk = some (initBufferBytes h (configuredState s)) := by
    simp [ready,cfg,directInitHeap,directInitAlloc,configuredHeap,setS,initBufferBytes]
  have shape := write_shape (src := src) hsReady hbReady off n
  exact Shape.fresh shape rfl hfReady

private theorem CString_block_transport {h after : Heap} {p : BPtr} {xs : List UInt8} {b : Nat}
    (hp : p = .ref (.blk b) 0) (hc : CString h p xs) (hb : after.bytes b = h.bytes b) :
    CString after p xs := by
  subst p
  refine ⟨?_,hc.2⟩
  rcases hc.1 with hn | ⟨r,off,a,hptr,ha,hfit,htext⟩
  · cases hn.1
  · cases hptr
    exact Or.inr ⟨.blk b,0,a,rfl,hb.trans ha,hfit,htext⟩

/-- Actual malloc freshness separates the new input buffer from the existing
private path. This produces both its exact original CString and ownership on
that same written heap, with no new no-alias premise. -/
theorem first_written_private_path {h : Heap} {i : Nat} {s : GzState} {src : Array UInt8}
    {xs : List UInt8} (hp : CString h s.path xs)
    (hpath : MallocBuffer h s.path (xs.length+1)) (hf : Fresh h) (off : Nat) (n : UInt32) :
    CString (firstWrittenHeap h i s src off n) (firstWrittenState h s n).path xs ∧
    MallocBuffer (firstWrittenHeap h i s src off n) (firstWrittenState h s n).path (xs.length+1) := by
  obtain ⟨b,a,hptr,hbytes,hro,hfit⟩ := hpath
  have sep : b ≠ h.nextBlk := by
    intro eq
    subst b
    exact hf h.nextBlk (Nat.le_refl _) (Or.inl (by rw [hbytes]; simp))
  have bytes : (firstWrittenHeap h i s src off n).bytes b = h.bytes b := by
    simp [firstWrittenHeap,writeEmptyHeap,directInitHeap,directInitAlloc,configuredHeap,setS,sep]
  have readonly : (firstWrittenHeap h i s src off n).ro b = h.ro b := by
    simp [firstWrittenHeap,writeEmptyHeap,directInitHeap,directInitAlloc,configuredHeap,setS,sep]
  refine ⟨CString_block_transport hptr hp bytes,?_⟩
  exact ⟨b,a,hptr,bytes.trans hbytes,readonly.trans hro,hfit⟩

/-- The same actual written heap satisfies every flush entry condition,
including its fresh allocation cursor and original private path. Small path
length is an internal observation supplied by descriptor initialization. -/
theorem first_written_flush_badfd {h : Heap} {i off : Nat} {s : GzState} {src : Array UInt8}
    {name : List UInt8} {fd : Int32}
    (ho : OpenState h i s .write (-1) 0 1 fd name) (hsmall : name.length ≤ 15)
    (n : UInt32) (hn : n ≠ 0) (hn8 : n.toNat < 8) (fs : Fs)
    (hfd : fd < 0 ∨ (fs.fds.size : Int) ≤ fd.toInt) :
    let written := firstWrittenHeap h i s src off n
    gzflush (hnd i) Z_SYNC_FLUSH fs written =
      .ok ((DirectErrno.failedFlushCode written,{fs with errno := EBADF}),
        DirectErrno.failedFlushHeap written fs i (firstWrittenState h s n) name) := by
  dsimp only
  rcases ho with ⟨hv,hmode,hfdEq,hp,_,_,hdirect,_,_,he,hmsg,_,_,_,_,hskip,_⟩
  have pathBuffer := Zlib.Gzlib.InitializedErrorPath.valid_observed_path_malloc hv hp
  have privatePath := first_written_private_path (i := i) (src := src) hp pathBuffer hv.2.2.1 off n
  have fresh := first_written_fresh (src := src) hv.1 hv.2.2.1 off n
  have observations := first_written_observations h i s src off n
  have hdir : s.direct ≠ 0 := by
    have eq : s.direct.toInt = 1 := by simpa using hdirect
    intro zero
    rw [zero] at eq
    contradiction
  have hchunk : n ≤ 1073741824 := by
    apply UInt32.le_iff_toNat_le.mpr
    change n.toNat ≤ 1073741824
    omega
  have bufferFit : n.toNat ≤ (copyRange (initBufferBytes h (configuredState s)) src 0 off n.toNat).size := by
    rw [size_copyRange]
    change n.toNat ≤ 16
    omega
  have cap : name.length+(Zlib.Gzlib.ErrnoOwned.errnoCharacters EBADF).length+2 ≤ 2147483647 := by
    have text := C.LibcStrings.Proofs.errno_bytes_lt64 EBADF
    simp only [strBytes,Array.size_push,ByteArray.size_data] at text
    change (libcErrnoText EBADF).toUTF8.data.size+1 < 64 at text
    simp only [Zlib.Gzlib.ErrnoOwned.errnoCharacters,strerrorText,Array.length_toList]
    omega
  apply DirectErrno.gzflush_direct_badfd_owned_run observations.1
    (show (firstWrittenState h s n).mode = GZ_WRITE from hmode)
    (show (firstWrittenState h s n).err = Z_OK from he)
    (show (firstWrittenState h s n).msg = .null from hmsg)
    (show (firstWrittenState h s n).skip = 0 from hskip)
    (show (firstWrittenState h s n).size ≠ 0 by change (8 : UInt32) ≠ 0; decide)
    (show (firstWrittenState h s n).direct ≠ 0 from hdir)
    n rfl hn hchunk rfl observations.2.1 (by simpa only [Nat.zero_add] using bufferFit) fs
    (show (firstWrittenState h s n).fd < 0 ∨ (fs.fds.size : Int) ≤ (firstWrittenState h s n).fd.toInt by
      change s.fd < 0 ∨ (fs.fds.size : Int) ≤ s.fd.toInt
      rw [hfdEq]
      exact hfd)
    privatePath.1 privatePath.2 fresh (fun _ => cap)

#print axioms first_written_observations
#print axioms first_written_fresh
#print axioms first_written_private_path
#print axioms first_written_flush_badfd
end Zlib.Gzwrite.DirectHistory
