import ZlibF.Proof.«public-gz-offset»
import ZlibF.Zlib.«gzwrite.c»

/-!
# gzwrite.c: initialized buffer execution

These are internal execution lemmas. Buffer ownership, available capacity and a
representable file position are explicit premises. They are not a proof that every
public history establishes those premises. No compressor contract is assumed.
-/

namespace Zlib.Gzwrite.Proofs
open C Zlib.GzFs Zlib.Gzguts Zlib.Gzlib Zlib.Gzlib.Spec Zlib.Gzlib.Proofs
open ZlibF.Spec.Public.OffsetProof

/-- The actual error-clear operation on an already clear message. -/
theorem gz_error_clear {h : Heap} {i : Nat} {s : GzState}
    (hs : h.gzstates i = some s) (he : s.err = Z_OK) (hm : s.msg = .null) :
    gz_error (some (.tab i)) Z_OK .null h = .ok ((), h) := by
  have hr : { s with err := Z_OK, msg := .null } = s := by cases s; simp_all
  have hh : setS h i s = h := by
    unfold setS
    congr 1
    exact upd_self _ _ _ hs
  simp [gz_error, bind_app, ldS_run hs, hm, updS_run hs, hr, hh, pure_app]

private theorem store8_block {h : Heap} {b k : Nat} {a : Array UInt8}
    (hb : h.bytes b = some a) (hr : h.ro b = false) (hk : k < a.size) (v : UInt8) :
    store8 (.ref (.blk b) k) v h =
      .ok ((), { h with bytes := upd h.bytes b (some (a.set! k v)) }) :=
  Ptr.store_ok hb hr hk

/-- The exact heap after appending the first buffered byte. -/
def putcEmptyHeap (h : Heap) (i b : Nat) (s : GzState) (a : Array UInt8) (c : Int32) : Heap :=
  setS { h with bytes := upd h.bytes b (some (a.set! 0 c.toUInt32.toUInt8)) } i
    { s with strm := { s.strm with next_in := s.«in», avail_in := 1 }
             x := { s.x with pos := Int64.ofInt (s.x.pos.toInt + 1) } }

/-- `int gzputc(gzFile file, int c)` stores the first byte in an initialized empty
buffer. This domain requires a clear error/message, no pending seek, a nonempty
writable input block and position headroom. It performs no file I/O or allocation.
The initialization/history proof that establishes these premises remains separate. -/
theorem gzputc_empty_buffer {h : Heap} {i b : Nat} {s : GzState} {a : Array UInt8}
    (hs : h.gzstates i = some s) (hm : s.mode = GZ_WRITE)
    (he : s.err = Z_OK) (hmsg : s.msg = .null) (hskip : s.skip = 0)
    (hsize : s.size ≠ 0) (havail : s.strm.avail_in = 0)
    (hin : s.«in» = .ref (.blk b) 0) (ha : h.bytes b = some a)
    (hro : h.ro b = false) (hne : 0 < a.size)
    (hpos : s.x.pos.toInt + 1 < 9223372036854775808) (c : Int32) (fs : Fs) :
    gzputc (hnd i) c fs h = .ok ((c &&& 0xff, fs), putcEmptyHeap h i b s a c) := by
  have hc := gz_error_clear hs he hmsg
  have hlo : -9223372036854775808 ≤ s.x.pos.toInt + 1 := by
    have := Int64.le_toInt s.x.pos
    change -9223372036854775808 ≤ s.x.pos.toInt at this
    omega
  have hsz : (0 : UInt32) < s.size := UInt32.pos_iff_ne_zero.mpr hsize
  have hz : (Int64.toUInt64 0).toUInt32 = (0 : UInt32) := by decide
  have hzn : (Int64.toUInt64 0).toNat = 0 := by decide
  unfold gzputc
  offsetsimp [hs, hm, he, hc, hskip, hsize, havail, hin, Ptr.add, Ptr.diff, ha,
    store8_block, hro, hne, i64add, i64chk, hpos, hlo, hz, hzn, hsz, putcEmptyHeap, setS, upd_upd]

/-- The exact buffer-copy result before a compressor call is needed. -/
def writeEmptyHeap (h : Heap) (i b : Nat) (s : GzState) (a src : Array UInt8)
    (off : Nat) (n : UInt32) : Heap :=
  setS { h with bytes := upd h.bytes b (some (copyRange a src 0 off n.toNat)) } i
    { s with strm := { s.strm with next_in := s.«in», avail_in := n }
             x := { s.x with pos := Int64.ofInt (s.x.pos.toInt + (n.toNat : Int)) } }

/-- `z_size_t gz_write(gz_statep state, voidpc buf, z_size_t len)` copies a short
nonempty input entirely into an initialized empty buffer. The caller supplies a
readable source in a different block and enough writable buffer and position space.
No compressor theorem is assumed and no compressor call is executed. Establishing
these internal premises from public histories remains a separate obligation. -/
theorem gz_write_empty_buffer {h : Heap} {i b p off : Nat} {s : GzState}
    {a src : Array UInt8} (hs : h.gzstates i = some s)
    (hskip : s.skip = 0) (havail : s.strm.avail_in = 0)
    (hin : s.«in» = .ref (.blk b) 0) (ha : h.bytes b = some a)
    (hp : h.bytes p = some src) (hbp : b ≠ p) (hro : h.ro b = false)
    (n : UInt32) (hn : n ≠ 0) (hshort : n < s.size)
    (hcap : n.toNat ≤ a.size) (hsrc : off + n.toNat ≤ src.size)
    (hpos : s.x.pos.toInt + (n.toNat : Int) < 9223372036854775808) (fs : Fs) :
    gz_write (some (.tab i)) (.ref (.blk p) off) n.toUInt64 fs h =
      .ok ((n.toUInt64, fs), writeEmptyHeap h i b s a src off n) := by
  have hsize : s.size ≠ 0 := by
    intro hz
    rw [hz] at hshort
    have := UInt32.lt_iff_toNat_lt.mp hshort
    simp at this
  have hn64 : n.toUInt64 ≠ 0 := by
    intro hz
    have hh := congrArg UInt64.toNat hz
    have hh' : n.toNat = (0 : UInt32).toNat := by simpa using hh
    exact hn (UInt32.toNat_inj.mp hh')
  have hshort64 : n.toUInt64 < s.size.toUInt64 := by
    simpa only [UInt64.lt_iff_toNat_lt, UInt32.toNat_toUInt64] using UInt32.lt_iff_toNat_lt.mp hshort
  have hlo : -9223372036854775808 ≤ s.x.pos.toInt + (n.toNat : Int) := by
    have hb := Int64.le_toInt s.x.pos
    change -9223372036854775808 ≤ s.x.pos.toInt at hb
    omega
  have hne : 0 < a.size := by
    have hn' : n.toNat ≠ 0 := fun hz => hn (UInt32.toNat_inj.mp hz)
    omega
  have hz64 : Int64.toUInt64 0 = (0 : UInt64) := by decide
  have hnint : (n.toNat : Int) % 4294967296 = n.toNat := by
    apply Int.emod_eq_of_lt (by omega)
    have := n.toNat_lt
    omega
  have hsmod : s.size.toUInt64 % 4294967296 = s.size.toUInt64 := by
    apply UInt64.mod_eq_of_lt
    simp only [UInt64.lt_iff_toNat_lt, UInt32.toNat_toUInt64]
    exact s.size.toNat_lt
  have hpb : p ≠ b := Ne.symm hbp
  have hnonneg : 0 ≤ (off : Int) + n.toNat := by omega
  have hsrcInt : (off : Int) + n.toNat ≤ src.size := by omega
  unfold gz_write
  offsetsimp [hs, hskip, hsize, havail, hn64, hshort64, hshort]
  rw [gwhile]
  rw [show fuel = 18446744073709551615 + 1 by decide, gwhile.go]
  offsetsimp [hs, havail, hin, Ptr.add, Ptr.diff, ha, hz64, hsmod, hnint, hshort64,
    memcpyB_blk_ok, hp, hbp, hpb, hro, hcap, hsrc, hsrcInt, hnonneg,
    i64add, i64chk, u32ToI64_toInt, hlo, hpos, writeEmptyHeap, setS, upd_upd]
  rw [gwhile.go.eq_def]
  offsetsimp []

/-- Only the handle record and the input buffer can change; allocation counters
and every unrelated live allocation are preserved exactly. -/
theorem writeEmptyHeap_frame (h : Heap) (i b : Nat) (s : GzState)
    (a src : Array UInt8) (off : Nat) (n : UInt32) :
    ZlibF.Spec.Public.Frame h (writeEmptyHeap h i b s a src off n)
      (fun k => k = i ∨ k = b) ∧
    (writeEmptyHeap h i b s a src off n).nalloc = h.nalloc ∧
    (writeEmptyHeap h i b s a src off n).nextBlk = h.nextBlk := by
  simp [ZlibF.Spec.Public.Frame, writeEmptyHeap, setS, upd_apply]
  intro k _ hk
  simp_all

/-- The single-byte fast path has the same exact two-allocation footprint. -/
theorem putcEmptyHeap_frame (h : Heap) (i b : Nat) (s : GzState)
    (a : Array UInt8) (c : Int32) :
    ZlibF.Spec.Public.Frame h (putcEmptyHeap h i b s a c)
      (fun k => k = i ∨ k = b) ∧
    (putcEmptyHeap h i b s a c).nalloc = h.nalloc ∧
    (putcEmptyHeap h i b s a c).nextBlk = h.nextBlk := by
  simp [ZlibF.Spec.Public.Frame, putcEmptyHeap, setS, upd_apply]
  intro k _ hk
  simp_all

/-- The source allocation survives the real copy unchanged when it is a different
block from the internal output buffer. -/
theorem writeEmptyHeap_source (h : Heap) (i b p : Nat) (s : GzState)
    (a src : Array UInt8) (off : Nat) (n : UInt32) (hpb : p ≠ b) :
    (writeEmptyHeap h i b s a src off n).bytes p = h.bytes p := by
  simp [writeEmptyHeap, hpb]

/-- `int gzwrite(gzFile file, voidpc buf, unsigned len)` reaches the actual short
buffer-copy execution. This internal domain additionally requires the public int
result length check, a writable mode, and an already clear error/message. -/
theorem gzwrite_empty_buffer {h : Heap} {i b p off : Nat} {s : GzState}
    {a src : Array UInt8} (hs : h.gzstates i = some s)
    (hm : s.mode = GZ_WRITE) (he : s.err = Z_OK) (hmsg : s.msg = .null)
    (hskip : s.skip = 0) (havail : s.strm.avail_in = 0)
    (hin : s.«in» = .ref (.blk b) 0) (ha : h.bytes b = some a)
    (hp : h.bytes p = some src) (hbp : b ≠ p) (hro : h.ro b = false)
    (n : UInt32) (hn : n ≠ 0) (hshort : n < s.size) (hlen : ¬ n.toInt32 < 0)
    (hcap : n.toNat ≤ a.size) (hsrc : off + n.toNat ≤ src.size)
    (hpos : s.x.pos.toInt + (n.toNat : Int) < 9223372036854775808) (fs : Fs) :
    gzwrite (hnd i) (.ref (.blk p) off) n fs h =
      .ok ((n.toInt32, fs), writeEmptyHeap h i b s a src off n) := by
  have hc := gz_error_clear hs he hmsg
  have hw := gz_write_empty_buffer hs hskip havail hin ha hp hbp hro n hn hshort hcap hsrc hpos fs
  unfold gzwrite
  offsetsimp [hs, hm, he, hc, hlen, hw]

#print axioms gzputc_empty_buffer
#print axioms gz_write_empty_buffer
#print axioms gzwrite_empty_buffer

end Zlib.Gzwrite.Proofs
