import ZlibF.Proof.«gzlib.c.initialized-error-path»
import ZlibF.Proof.«gzwrite.c.init-buffered»

/-! # Real descriptor-open and first short transparent write

The public initializer, public buffer choice and public writer use one actual
heap. Source storage is caller byte storage preserved by initialization. This
prefix accepts arbitrary positive inputs shorter than the chosen eight-byte
buffer. It does not yet assert a final flush or close result.
-/
namespace Zlib.Gzwrite.DirectHistory
open C Zlib.GzFs Zlib.Gzguts Zlib.Gzlib Zlib.Gzwrite Zlib.Gzlib.Spec Zlib.Gzlib.Proofs
open ZlibF.Spec.Public ZlibF.Spec.Public.OffsetProof Zlib.Gzwrite.Proofs

/-- The real public writer includes its entry checks and the same lazy buffer
allocation as the internal writer. This remains a conditional execution lemma;
its premises are discharged by the actual open witness below. -/
theorem gzwrite_direct_lazy_short {h : Heap} {i p off : Nat} {s : GzState}
    {src : Array UInt8} (hs : h.gzstates i = some s) (hsize : s.size = 0)
    (hm : s.mode = GZ_WRITE) (he : s.err = Z_OK) (hmsg : s.msg = .null)
    (hdir : s.direct ≠ 0) (hF : Fresh h) (hok : h.allocOk h.nalloc = true)
    (hskip : s.skip = 0) (havail : s.strm.avail_in = 0)
    (hp : h.bytes p = some src) (n : UInt32) (hn : n ≠ 0) (hshort : n < s.want)
    (hlen : ¬ n.toInt32 < 0) (hcap : n.toNat ≤ (s.want <<< 1).toNat)
    (hsrc : off + n.toNat ≤ src.size)
    (hpos : s.x.pos.toInt + (n.toNat : Int) < 9223372036854775808) (fs : Fs) :
    gzwrite (hnd i) (.ref (.blk p) off) n fs h =
      .ok ((n.toInt32, fs), writeEmptyHeap (directInitHeap h i s) i h.nextBlk
        (directInitRec s h.nextBlk) (initBufferBytes h s) src off n) := by
  have hc := gz_error_clear hs he hmsg
  have hw := gz_write_direct_lazy_short hs hsize hdir hF hok hskip havail hp n hn hshort hcap hsrc hpos fs
  unfold gzwrite
  offsetsimp [hs, hm, he, hc, hlen, hw]


def configuredState (s : GzState) : GzState := {s with want := 8}
def configuredHeap (h : Heap) (i : Nat) (s : GzState) : Heap := setS h i (configuredState s)
def firstWrittenHeap (h : Heap) (i : Nat) (s : GzState) (src : Array UInt8)
    (off : Nat) (n : UInt32) : Heap :=
  writeEmptyHeap (directInitHeap (configuredHeap h i s) i (configuredState s)) i h.nextBlk
    (directInitRec (configuredState s) h.nextBlk) (initBufferBytes h (configuredState s)) src off n

/-- The actual public buffer request changes only want on this open writer. -/
theorem buffer_eight_run {h : Heap} {i : Nat} {s : GzState}
    (hs : h.gzstates i = some s) (hm : s.mode = GZ_WRITE) (hz : s.size = 0) :
    gzbuffer (hnd i) 8 h = .ok (0,configuredHeap h i s) := by
  have shift : ¬ ((8 : UInt32) <<< 1) < 8 := by decide
  unfold gzbuffer
  offsetsimp [hs,hm,hz,shift,configuredHeap,configuredState]

/-- Public write executes its real lazy allocation and accepts the complete
short input on the exact post-gzbuffer heap. All initial fields come from the
same OpenState rather than from a callee contract. -/
theorem open_state_short_write {h : Heap} {i p off : Nat} {s : GzState} {src : Array UInt8}
    {name : List UInt8} {fd : Int32}
    (ho : OpenState h i s .write (-1) 0 1 fd name)
    (hp : h.bytes p = some src) (n : UInt32) (hn : n ≠ 0) (hn8 : n.toNat < 8)
    (hsrc : off + n.toNat ≤ src.size) (hok : h.allocOk h.nalloc = true) (fs : Fs) :
    gzwrite (hnd i) (.ref (.blk p) off) n fs (configuredHeap h i s) =
      .ok ((n.toInt32,fs),firstWrittenHeap h i s src off n) := by
  rcases ho with ⟨hv,hm,_,_,_,_,hdir,hzero,_,he,hmsg,_,hpos,_,_,hskip,havail,_⟩
  have hs : (configuredHeap h i s).gzstates i = some (configuredState s) := by simp [configuredHeap]
  have hf : Fresh (configuredHeap h i s) :=
    Shape.fresh (shape_setS hv.1 (configuredState s)) rfl hv.2.2.1
  have hd : s.direct ≠ 0 := by
    have hdir1 : s.direct.toInt = 1 := by simpa using hdir
    intro heq
    rw [heq] at hdir1
    contradiction
  have hlen : ¬n.toInt32 < 0 := by
    have cast : n.toInt32 = Int32.ofNat n.toNat := by
      simpa using (UInt32.toInt32_ofNat' (n := n.toNat))
    rw [cast]
    have hval := Int32.toInt_ofNat_of_lt (show n.toNat < 2^31 by omega)
    intro neg
    have bad := Int32.lt_iff_toInt_lt.mp neg
    change (Int32.ofNat n.toNat).toInt < 0 at bad
    rw [hval] at bad
    omega
  have hcap : n.toNat ≤ 16 := by omega
  have position : s.x.pos.toInt + (n.toNat : Int) < 9223372036854775808 := by
    rw [hpos]
    change (0 : Int) + n.toNat < 9223372036854775808
    omega
  simpa [firstWrittenHeap,configuredState,configuredHeap,initBufferBytes,setS] using
    gzwrite_direct_lazy_short hs hzero hm he hmsg hd hf hok hskip havail hp n hn
      (show n < (configuredState s).want from UInt32.lt_iff_toNat_lt.mpr hn8)
      hlen (show n.toNat ≤ ((configuredState s).want <<< 1).toNat by change n.toNat ≤ 16; exact hcap)
      hsrc position fs

def descriptorShortHistory (fd : Int32) (mode source : BPtr) (n : UInt32) : G (GzFilePtr × Int32 × Int32) := do
  let file ← gzdopen fd mode
  let buffered ← gzbuffer file 8
  let wrote ← gzwrite file source n
  return (file,buffered,wrote)

/-- Same actual public gzdopen→gzbuffer→gzwrite history, for arbitrary caller
source bytes and all positive n<8. Original init uniqueness is inherited; no
new global uniqueness premise is added. -/
theorem descriptor_short_history {h : Heap} {fs : Fs} {fd : Int32} {mode : BPtr}
    {p off : Nat} {src : Array UInt8}
    (hf : Fresh h) (hu : Uniq h) (hg : LibraryGlobals h) (hnfd : 0 ≤ fd.toInt)
    (hm : CString h mode [119,84]) (hp : h.bytes p = some src)
    (n : UInt32) (hn : n ≠ 0) (hn8 : n.toNat < 8) (hsrc : off + n.toNat ≤ src.size)
    (ha : h.allocOk h.nalloc = true) (ha1 : h.allocOk (h.nalloc+1) = true)
    (ha2 : h.allocOk (h.nalloc+2) = true)
    (hinput : h.allocOk (h.nalloc+3) = true) :
    let entry := descriptorEntryHeap h fd
    let opened := descriptorReleased (writerOpenHeap entry true (descriptorPath fd) fd) h.nextBlk
    let state := writerOpenState entry true fd
    descriptorShortHistory fd mode (.ref (.blk p) off) n fs h =
      .ok (((some (.in_gzstate_x entry.nextBlk),0,n.toInt32),fs),
        firstWrittenHeap opened entry.nextBlk state src off n) := by
  dsimp only
  obtain ⟨init,ho,frame,_⟩ := gzdopen_writer_accounted h fs fd mode true hf hu hg hnfd hm ha ha1 ha2
  have hpLive : h.live p := Or.inl (by rw [hp]; simp)
  have hpOpened := (frame.2.2.2.2.2 p hpLive (by simp)).1.trans hp
  have hmode : (writerOpenState (descriptorEntryHeap h fd) true fd).mode = GZ_WRITE := ho.2.1
  have hzero : (writerOpenState (descriptorEntryHeap h fd) true fd).size = 0 := ho.2.2.2.2.2.2.2.1
  have buffered := buffer_eight_run ho.1.1 hmode hzero
  have hfdne : fd ≠ -1 := by intro eq; rw [eq] at hnfd; contradiction
  have nonempty : (descriptorPath fd).toArray.isEmpty = false := by simp [descriptorPath]
  have hcount : (descriptorReleased
      (writerOpenHeap (descriptorEntryHeap h fd) true (descriptorPath fd) fd) h.nextBlk).nalloc = h.nalloc+3 := by
    simp [descriptorReleased,writerOpenHeap,writerFinishedHeap,writerEntryHeap,
      writerFormattedHeap,pathFormattedHeap,pathBytesHeap,pathAllocatedHeap,writerIoHeap,
      descriptorEntryHeap,descriptorFormattedHeap,descriptorAllocatedHeap,openFrontHeap,setS,
      hfdne,nonempty,Nat.add_assoc]
  have halloc : (descriptorReleased
      (writerOpenHeap (descriptorEntryHeap h fd) true (descriptorPath fd) fd) h.nextBlk).allocOk
      (descriptorReleased (writerOpenHeap (descriptorEntryHeap h fd) true (descriptorPath fd) fd) h.nextBlk).nalloc = true := by
    rw [hcount,←frame.2.1]
    exact hinput
  have wrote := open_state_short_write ho hpOpened n hn hn8 hsrc halloc fs
  dsimp only [hnd] at buffered wrote
  unfold descriptorShortHistory
  offsetsimp [init,buffered,wrote]

#print axioms buffer_eight_run
#print axioms open_state_short_write
#print axioms descriptor_short_history
end Zlib.Gzwrite.DirectHistory
