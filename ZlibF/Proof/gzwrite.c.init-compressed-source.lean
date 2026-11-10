import ZlibF.Proof.«public-gz-offset»
import ZlibF.Proof.«gzlib.c.base»

/-! # Actual compressed lazy-init entry

The compressor call uses window 31 (gzip), not window 15 (zlib). The source
cut below retains the real Init2 call and its cleanup; it does not assume or
claim the missing successful gzip compressor contract.
-/
namespace Zlib.Gzwrite.CompressedInit
open C Zlib.GzFs Zlib.Gzguts Zlib.Gzlib Zlib.Gzwrite
open Zlib.Gzlib.Spec Zlib.Gzlib.Proofs ZlibF.Spec.Public.OffsetProof
open Zlib.Deflate (deflateInit2_)

/-- Exact suffix after both real outer mallocs, with the real compressor call
and all error cleanup. The version pointer is produced by real strLit. -/
def compressedTail (state : GzStatePtr) : G Int32 := do
  let strm := strmOf state
  updZ strm fun z => { z with zalloc := .null, zfree := .null, «opaque» := .null }
  let s ← ldS state
  let ver ← strLit ZLIB_VERSION
  let ret ← deflateInit2_ strm s.level Z_DEFLATED 31 DEF_MEM_LEVEL s.strategy ver 112
  if ret != Z_OK then
    let s ← ldS state
    freeB s.out
    freeB s.«in»
    gz_error state Z_MEM_ERROR (← strLit "out of memory")
    return -1
  updZ strm fun z => { z with next_in := .null }
  updS state fun s => { s with size := s.want }
  let s ← ldS state
  if s.direct == 0 then
    updZ strm fun z => { z with avail_out := s.size, next_out := s.out }
    let z ← ldZ strm
    updX state fun x => { x with next := z.next_out }
  return 0

def inputBytes (h : Heap) (s : GzState) : Array UInt8 :=
  Array.ofFn (n := (s.want <<< 1).toNat) fun j => Junk.of (h.garbage h.nalloc j.val)
def outputBytes (h : Heap) (s : GzState) : Array UInt8 :=
  Array.ofFn (n := s.want.toNat) fun j => Junk.of (h.garbage (h.nalloc+1) j.val)
def inputHeap (h : Heap) (i : Nat) (s : GzState) : Heap :=
  setS {h with
    bytes := upd h.bytes h.nextBlk (some (inputBytes h s))
    ro := upd h.ro h.nextBlk false
    nextBlk := h.nextBlk+1
    nalloc := h.nalloc+1} i {s with «in» := .ref (.blk h.nextBlk) 0}
def buffersHeap (h : Heap) (i : Nat) (s : GzState) : Heap :=
  let first := inputHeap h i s
  setS {first with
    bytes := upd first.bytes (h.nextBlk+1) (some (outputBytes h s))
    ro := upd first.ro (h.nextBlk+1) false
    nextBlk := h.nextBlk+2
    nalloc := h.nalloc+2}
    i {s with «in» := .ref (.blk h.nextBlk) 0,out := .ref (.blk (h.nextBlk+1)) 0}

/-- `int gz_init(gz_statep state)` reaches its real gzip-31 compressor call
on the exact heap from both successful outer mallocs. No compressor outcome,
representation, termination or callee specification is a premise. This source
entry is not a successful-init or full gz_init contract. -/
theorem gz_init_compressed_source {h : Heap} {i : Nat} {s : GzState}
    (hs : h.gzstates i = some s) (hd : s.direct=0) (hf : Fresh h)
    (ha : h.allocOk h.nalloc=true) (ha1 : h.allocOk (h.nalloc+1)=true) (fs : Fs) :
    gz_init (some (.tab i)) fs h = compressedTail (some (.tab i)) fs (buffersHeap h i s) := by
  have below : i<h.nextBlk := by
    by_cases lt : i<h.nextBlk
    · exact lt
    · exact False.elim (hf i (by omega) (by simp [Heap.live,hs]))
  have nextEmpty := hf (h.nextBlk+1) (by omega)
  have nextSlot (a : Array UInt8) (st : GzState) :
      ({h with
        bytes := upd h.bytes h.nextBlk (some a)
        ro := upd h.ro h.nextBlk false
        gzstates := upd h.gzstates i (some st)
        nextBlk := h.nextBlk+1
        nalloc := h.nalloc+1} : Heap).slotUsed (h.nextBlk+1)=false := by
    apply Heap.slotUsed_eq_false.mpr
    simpa [Heap.live,show h.nextBlk+1 ≠ i by omega] using nextEmpty
  unfold gz_init
  offsetsimp [hs,hd,allocB,ha,ha1,Fresh.slotUsed_next hf,nextSlot,
    inputHeap,inputBytes,outputBytes,buffersHeap,setS,upd_upd,compressedTail,MAX_WBITS]
  rfl

#print axioms gz_init_compressed_source
end Zlib.Gzwrite.CompressedInit
