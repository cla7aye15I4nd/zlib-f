import ZlibF.Proof.«gzwrite.c.buffered»

/-!
# gzwrite.c: connecting transparent initialization to buffered writes

The actual lazy initializer allocates the input buffer. The first short write then
uses the same heap and the buffer that was just allocated. The initial handle
representation and reset fields remain explicit premises until open is connected.
-/

namespace Zlib.Gzwrite.Proofs
open C Zlib.GzFs Zlib.Gzguts Zlib.Gzlib Zlib.Gzlib.Spec Zlib.Gzlib.Proofs
open ZlibF.Spec.Public.OffsetProof

/-- Arbitrary initial contents supplied by the real allocation oracle. -/
def initBufferBytes (h : Heap) (s : GzState) : Array UInt8 :=
  Array.ofFn (n := (s.want <<< 1).toNat) fun i => Junk.of (h.garbage h.nalloc i.val)

/-- The single actual allocation in a successful transparent initializer. -/
def directInitAlloc (h : Heap) (s : GzState) : Heap :=
  { h with bytes := upd h.bytes h.nextBlk (some (initBufferBytes h s))
           ro := upd h.ro h.nextBlk false
           nextBlk := h.nextBlk + 1
           nalloc := h.nalloc + 1 }

/-- The record produced by the transparent branch of `gz_init`. -/
def directInitRec (s : GzState) (b : Nat) : GzState :=
  { s with «in» := .ref (.blk b) 0, size := s.want
           strm := { s.strm with next_in := .null } }

/-- The exact heap produced by the real lazy initializer. -/
def directInitHeap (h : Heap) (i : Nat) (s : GzState) : Heap :=
  setS (directInitAlloc h s) i (directInitRec s h.nextBlk)

/-- `int gz_init(gz_statep state)` allocates its real transparent input buffer,
sets the size and next-input field, and does not initialize a compressor. The heap
must be fresh and this allocation must succeed; buffer contents remain arbitrary. -/
theorem gz_init_direct {h : Heap} {i : Nat} {s : GzState}
    (hs : h.gzstates i = some s) (hdir : s.direct ≠ 0)
    (hF : Fresh h) (hok : h.allocOk h.nalloc = true) (fs : Fs) :
    gz_init (some (.tab i)) fs h = .ok ((0, fs), directInitHeap h i s) := by
  have hslot := Fresh.slotUsed_next hF
  unfold gz_init
  offsetsimp [hs, hdir, allocB, hok, hslot,
    directInitHeap, directInitAlloc, directInitRec, initBufferBytes, setS, upd_upd]
  rfl

/-- The allocation establishes the live writable buffer and nonzero size required
by buffered writes. `avail_in`, seek state and file position are inherited exactly
from the initial record rather than assumed as a callee contract. -/
theorem directInitHeap_buffer (h : Heap) (i : Nat) (s : GzState)
    (hwant : s.want ≠ 0) :
    (directInitHeap h i s).gzstates i = some (directInitRec s h.nextBlk) ∧
    (directInitRec s h.nextBlk).size ≠ 0 ∧
    (directInitRec s h.nextBlk).«in» = .ref (.blk h.nextBlk) 0 ∧
    (directInitHeap h i s).bytes h.nextBlk = some (initBufferBytes h s) ∧
    (directInitHeap h i s).ro h.nextBlk = false ∧
    (directInitRec s h.nextBlk).strm.avail_in = s.strm.avail_in ∧
    (directInitRec s h.nextBlk).skip = s.skip ∧
    (directInitRec s h.nextBlk).x.pos = s.x.pos ∧
    (directInitHeap h i s).nalloc = h.nalloc + 1 ∧
    (directInitHeap h i s).nextBlk = h.nextBlk + 1 := by
  simp [directInitHeap, directInitAlloc, directInitRec, hwant]

/-- Initialization preserves every unrelated existing allocation and accounts
for exactly its new input buffer. -/
theorem directInitHeap_ledger {h : Heap} {i : Nat} {s : GzState}
    (hs : h.gzstates i = some s) (hF : Fresh h) :
    ZlibF.Spec.Public.Frame h (directInitHeap h i s) (fun k => k = i) ∧
    ZlibF.Spec.Public.LiveChange h (directInitHeap h i s) (fun k => k = h.nextBlk) (fun _ => False) := by
  constructor
  · simp [ZlibF.Spec.Public.Frame, directInitHeap, directInitAlloc, setS, upd_apply]
    intro k hLive hki
    have hkn : k ≠ h.nextBlk := by
      have hk := Fresh.lt hF hLive
      omega
    simp_all
  · intro k
    by_cases hkn : k = h.nextBlk
    · subst k
      simp [directInitHeap, directInitAlloc, setS, Heap.live]
    · by_cases hki : k = i
      · subst k
        simp [directInitHeap, directInitAlloc, setS, Heap.live, hs, hkn]
      · simp [directInitHeap, directInitAlloc, setS, Heap.live, hkn, hki]

/-- A nonempty lazy transparent write continues on the exact heap returned by its
actual initializer. This is an execution equality, not a specification assumption. -/
theorem gz_write_direct_after_init {h : Heap} {i : Nat} {s : GzState}
    (hs : h.gzstates i = some s) (hsize : s.size = 0) (hdir : s.direct ≠ 0)
    (hF : Fresh h) (hok : h.allocOk h.nalloc = true) (hwant : s.want ≠ 0)
    (buf : BPtr) (len : UInt64) (hlen : len ≠ 0) (fs : Fs) :
    gz_write (some (.tab i)) buf len fs h =
      gz_write (some (.tab i)) buf len fs (directInitHeap h i s) := by
  have hi := gz_init_direct hs hdir hF hok fs
  unfold gz_write
  offsetsimp [hs, hsize, hi, hwant, hlen, directInitHeap, directInitAlloc, directInitRec]

/-- A first short transparent write allocates its own buffer and copies into that
same allocation in the same actual execution. Source-buffer separation follows
from heap freshness; it is not supplied as a new caller premise. The initial seek,
stream-input and position fields still need the real open/reset history. -/
theorem gz_write_direct_lazy_short {h : Heap} {i p off : Nat} {s : GzState}
    {src : Array UInt8} (hs : h.gzstates i = some s) (hsize : s.size = 0)
    (hdir : s.direct ≠ 0) (hF : Fresh h) (hok : h.allocOk h.nalloc = true)
    (hskip : s.skip = 0) (havail : s.strm.avail_in = 0)
    (hp : h.bytes p = some src) (n : UInt32) (hn : n ≠ 0) (hshort : n < s.want)
    (hcap : n.toNat ≤ (s.want <<< 1).toNat) (hsrc : off + n.toNat ≤ src.size)
    (hpos : s.x.pos.toInt + (n.toNat : Int) < 9223372036854775808) (fs : Fs) :
    gz_write (some (.tab i)) (.ref (.blk p) off) n.toUInt64 fs h =
      .ok ((n.toUInt64, fs), writeEmptyHeap (directInitHeap h i s) i h.nextBlk
        (directInitRec s h.nextBlk) (initBufferBytes h s) src off n) := by
  have hwant : s.want ≠ 0 := by
    intro hz
    rw [hz] at hshort
    have hh := UInt32.lt_iff_toNat_lt.mp hshort
    simp at hh
  have hn64 : n.toUInt64 ≠ 0 := by
    intro hz
    have hh := congrArg UInt64.toNat hz
    have hh' : n.toNat = (0 : UInt32).toNat := by simpa using hh
    exact hn (UInt32.toNat_inj.mp hh')
  have hbp : h.nextBlk ≠ p := by
    intro heq
    have hz := Fresh.bytes hF (b := p) (by omega)
    rw [hp] at hz
    contradiction
  have hpb : p ≠ h.nextBlk := Ne.symm hbp
  have hnew := directInitHeap_buffer h i s hwant
  have hsrc' : (directInitHeap h i s).bytes p = some src := by
    simp [directInitHeap, directInitAlloc, hpb, hp]
  rw [gz_write_direct_after_init hs hsize hdir hF hok hwant _ _ hn64 fs]
  exact gz_write_empty_buffer hnew.1 (by simpa [directInitRec] using hskip)
    (by simpa [directInitRec] using havail) rfl hnew.2.2.2.1 hsrc' hbp hnew.2.2.2.2.1
    n hn hshort (by simpa [initBufferBytes] using hcap) hsrc hpos fs

#print axioms gz_init_direct
#print axioms gz_write_direct_lazy_short


end Zlib.Gzwrite.Proofs
