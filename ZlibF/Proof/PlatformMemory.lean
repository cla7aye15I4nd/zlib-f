import ZlibF.Spec.PlatformMemory
import ZlibF.Runtime.Libc
import ZlibF.Proof.LibcBorrow
import ZlibF.Zlib.«zutil.c»

/-!
# Consequences of the explicit byte-object platform bound

The environment premise is used as stated. It is not derived from the
unrestricted runtime allocator or from stream reachability.
-/

namespace ZlibF.PlatformMemory
open C
set_option autoImplicit false

/-- Retrieve the bound in the form required by existing decoder lemmas. -/
theorem ByteObjectsFit.size_lt {h : Heap} (fit : ByteObjectsFit h)
    {ref : BRef} {a : Array UInt8} (get : Space.get h ref = some a) :
    a.size < 2 ^ 63 := fit ref a get

/-- Raw byte blocks satisfy the same bound as static and embedded views. -/
theorem ByteObjectsFit.block_size_lt {h : Heap} (fit : ByteObjectsFit h)
    {block : Nat} {a : Array UInt8} (get : h.bytes block = some a) :
    a.size < 2 ^ 63 := fit.size_lt (ref := .blk block) get

/-- Both pointers may be one past the object. Their actual signed
difference is representable without a separate arithmetic premise. -/
theorem ByteObjectsFit.diff_ok {h : Heap} (fit : ByteObjectsFit h)
    {ref : BRef} {a : Array UInt8} {p q : Nat}
    (get : Space.get h ref = some a) (hp : p ≤ a.size) (hq : q ≤ a.size) :
    OkOn h (Ptr.diff (.ref ref p) (.ref ref q))
      (Int64.ofInt ((p : Int) - (q : Int))) := by
  have bound := fit.size_lt get
  exact Ptr.diff_ok get hp hq (by omega)

/-- Any transition which retains or decreases every live byte-view size
preserves the platform condition. No callee execution contract is assumed. -/
theorem ByteObjectsFit.of_sizes_le {before after : Heap}
    (fit : ByteObjectsFit before)
    (sizes : ∀ (ref : BRef) (a : Array UInt8), Space.get after ref = some a →
      ∃ old, Space.get before ref = some old ∧ a.size ≤ old.size) :
    ByteObjectsFit after := by
  intro ref a get
  obtain ⟨old, oldGet, le⟩ := sizes ref a get
  exact Nat.lt_of_le_of_lt le (fit ref old oldGet)

/-- Persistent byte views retain their sizes when storage is unchanged.
An active external errno view is independently bounded below64 bytes, even
when its borrow metadata changes. -/
theorem ByteObjectsFit.of_storage_eq {before after : Heap}
    (fit : ByteObjectsFit before) (bytes : after.bytes = before.bytes)
    (dstates : after.dstates = before.dstates) (statics : after.static = before.static) :
    ByteObjectsFit after := by
  intro ref a get
  cases ref with
  | str i =>
    by_cases source : i < strTable.size
    · have same := C.LibcBorrow.str_view_stable (before := before) (after := after)
        (i := i) (Or.inl source)
      rw [same] at get
      exact fit (.str i) a get
    · have bounded := C.LibcBorrow.external_view_size (by omega : strTable.size ≤ i) get
      unfold byteObjectLimit
      omega
  | blk b => exact fit (.blk b) a (by simpa only [Space.get, bytes] using get)
  | dstate_depth i => exact fit (.dstate_depth i) a (by simpa only [Space.get, dstates] using get)
  | st_dist_code => exact fit .st_dist_code a (by simpa only [Space.get, statics] using get)
  | st_length_code => exact fit .st_length_code a (by simpa only [Space.get, statics] using get)

/-- Writing a stream record, including an embedded gzip stream, leaves
every represented byte-view size unchanged. -/
theorem ByteObjectsFit.put_stream {h : Heap} (fit : ByteObjectsFit h)
    (ref : ZStreamRef) (z : ZStream) : ByteObjectsFit (ref.put h z) := by
  apply fit.of_storage_eq
  all_goals cases ref <;> simp only [ZStreamRef.put] <;> split <;> rfl

/-- Updating decoder state records leaves all represented byte views
unchanged. Byte arrays embedded in compressor records remain covered. -/
theorem ByteObjectsFit.with_istates {h : Heap} (fit : ByteObjectsFit h)
    (states : Tbl (Option InflateState)) : ByteObjectsFit { h with istates := states } :=
  fit.of_storage_eq rfl rfl rfl

/-- Installing a bounded raw byte block preserves every other byte view.
This also covers an allocation's fresh storage after its size is bounded. -/
theorem ByteObjectsFit.with_bytes {h : Heap} (fit : ByteObjectsFit h)
    {block : Nat} {a : Array UInt8} (bound : a.size < byteObjectLimit) :
    ByteObjectsFit { h with bytes := upd h.bytes block (some a) } := by
  intro ref xs get
  cases ref with
  | blk b =>
    change (upd h.bytes block (some a)) b = some xs at get
    by_cases eq : b = block
    · subst b
      rw [upd_same] at get
      cases get
      exact bound
    · rw [upd_ne _ _ _ _ eq] at get
      exact fit (.blk b) xs get
  | str i => exact fit (.str i) xs get
  | dstate_depth i => exact fit (.dstate_depth i) xs get
  | st_dist_code => exact fit .st_dist_code xs get
  | st_length_code => exact fit .st_length_code xs get

/-- `void *malloc(size_t n)`.
For an explicitly bounded request, every returning outcome of the actual
runtime allocator preserves the byte-object scope. Allocation failure is
included. This theorem does not change the unrestricted allocator or claim
that its oracle enforces the platform bound for oversized requests. -/
theorem ByteObjectsFit.allocB {h after : Heap} (fit : ByteObjectsFit h)
    {n : Nat} {pointer : BPtr} (bound : n < byteObjectLimit)
    (run : C.allocB n h = .ok (pointer, after)) : ByteObjectsFit after := by
  unfold C.allocB at run
  split at run
  · split at run
    · contradiction
    · cases run
      have arrayBound : (Array.ofFn (n := n)
          (fun i => Junk.of (h.garbage h.nalloc i.val) : Fin n → UInt8)).size < byteObjectLimit := by
        simpa only [Array.size_ofFn] using bound
      exact (fit.with_bytes (block := h.nextBlk) arrayBound)
  · cases run
    exact fit

/-- `voidpf zcalloc(voidpf opaque, unsigned items, unsigned size)`.
The translated default allocator computes the request with 32-bit unsigned
multiplication. Thus every returning byte allocation preserves the platform
size scope, including NULL returns, without an extra size premise. This
does not establish that a wrapped product provides the intended capacity. -/
theorem ByteObjectsFit.zcalloc {h after : Heap} (fit : ByteObjectsFit h)
    {context pointer : BPtr} {items size : UInt32}
    (run : Zlib.Zutil.zcalloc context items size h = .ok (pointer, after)) :
    ByteObjectsFit after := by
  have bound : (items * size).toNat < byteObjectLimit := by
    have := UInt32.toNat_lt (items * size)
    unfold byteObjectLimit
    omega
  exact fit.allocB bound run

end ZlibF.PlatformMemory
