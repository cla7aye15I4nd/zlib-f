import ZlibF.Proof.«compress.c.local-pending»
import ZlibF.Proof.«compress.c.local-header»
import ZlibF.Proof.«deflate.c.engine.fill-preserve»
import ZlibF.Proof.«deflate.c.engine.fill-caller»

/-! # Actual first window fill with local private representation

The real first input read, hash priming, source loop and padding execute
from live records and concrete storage. The local state permits old typed
collisions. It does not supply or assume a global DGood contract.
-/
namespace ZlibF.Spec.Public.Proofs.CompressLocalFill
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open Zlib.Deflate.Engine.Proofs ZlibF.Spec.Public
open ZlibF.Spec.Public.Proofs.CompressLocalInit
open ZlibF.Spec.Public.Proofs.CompressLocal
open ZlibF.Spec.Public.Proofs.CompressLocalPending
open Zlib.Deflate.Proofs.DefaultInit
set_option autoImplicit false
set_option maxRecDepth 100000

/-- Actual first source body from live records and the checked hash shift. -/
theorem local_fill_body_first_read {h : Heap} {r : ZStreamRef} {ds w io : Nat}
    {z : ZStream} {d : DeflateState} {ref : BRef} {ia wa : Array UInt8}
    (live : DLive h r ds z d) (shift : d.hash_shift < 32) (win : d.window = .ref (.blk w) 0)
    (get : h.bytes w = some wa) (writable : h.ro w = false) (size : wa.size = 65536)
    (ss : d.strstart = 0) (la : d.lookahead = 0) (ins : d.insert = 0)
    (ws : d.w_size = 32768) (wsz : d.window_size = 65536) (wrap : d.wrap = 1)
    (pointer : z.next_in = .ref ref io) (input : Space.get h ref = some ia)
    (inputBound : io + z.avail_in.toNat ≤ ia.size) (nonempty : z.avail_in ≠ 0)
    (separate : BRef.blk w ≠ ref ∨ (rbLen z.avail_in 65536).toNat ≤ io ∨
      io + (rbLen z.avail_in 65536).toNat ≤ 0) :
    fillBody (some (.tab ds)) 32768 false h =
      .ok (false, firstRead h r ds w z d ref io ia wa) := by
  let n := rbLen z.avail_in 65536
  let copied := copyRange wa ia 0 io n.toNat
  let z' := readStream z n ref io (adlerValue z.adler ((ia.toList.drop io).take n.toNat))
  let hr := r.put { h with bytes := upd h.bytes w (some copied) } z'
  let dr := { d with lookahead := n }
  let hl := setD hr ds dr
  have count : n.toNat = min z.avail_in.toNat 65536 := by simpa [n] using rbLen_nat z.avail_in 65536
  have npos : n ≠ 0 := by
    intro zero
    have pos : 0 < z.avail_in.toNat := by
      have ne : z.avail_in.toNat ≠ 0 := by intro eq; apply nonempty; exact UInt32.toNat_inj.mp eq
      omega
    have nz := UInt32.toNat_inj.mpr zero
    simp only [UInt32.toNat_zero] at nz
    omega
  have nle : n.toNat ≤ 65536 := by omega
  have nle' : (rbLen z.avail_in 65536).toNat ≤ 65536 := nle
  have bound : io + n.toNat ≤ ia.size := by omega
  have read := read_buf_zlib (bo := 0) live.hz live.zst live.hs wrap pointer input get writable
    65536 npos bound (by simpa [size] using nle') (by simpa only [Nat.zero_add] using separate)
  have add : padd d.window 0 h = .ok (d.window, h) := by
    rw [win]
    simpa only [OkOn, padd, Nat.zero_add] using Ptr.add_nat_ok
      (show Space.get h (BRef.blk w) = some wa from get) (by omega : 0 + 0 ≤ wa.size)
  have add' : padd (.ref (.blk w) 0 : BPtr) 0 h = .ok (.ref (.blk w) 0, h) := by
    simpa only [win] using add
  have hrState : hr.dstates ds = some d := by simpa [hr] using live.hs
  have update : wr (some (.tab ds)) (fun d => { d with lookahead := d.lookahead + n }) hr =
      .ok ((), hl) := by simp [wrD_eq, hrState, la, hl, dr]
  have headGet : hl.bytes w = some copied := by simp [hl, hr]
  have prime := fill_prime_initial (h := hl) (ds := ds) (w := w) (d := dr) (wa := copied)
    (by simp [hl]) (by simpa [dr] using win) headGet (by simpa [dr] using ss)
    (by simpa [dr] using ins) (by simpa [dr, copied, size_copyRange, size] using nle) shift
  unfold fillBody
  simp only [bind_app, ldDeflateState_tab live.hs]
  simp only [ss, ws, MIN_LOOKAHEAD_u, la, wsz]
  simp only [show ¬ ((0 : UInt32) ≥ 32768 + (32768 - 262)) from by decide, ite_false]
  simp only [rdD_eq, live.hs, bind_app, live.back, zrd_eq, live.hz]
  simp only [beq_eq_false_iff_ne.mpr nonempty, Bool.false_eq_true, ite_false]
  simp only [show ((65536 : UInt64) - (0 : UInt32).toUInt64 - (0 : UInt32).toUInt64).toUInt32 = 65536 from rfl,
    show (0 : UInt32).toNat = 0 from rfl, bind_app, ldDeflateState_tab live.hs,
    ss, la, win, add', read]
  change (do
    wr (some (.tab ds)) (fun d => { d with lookahead := d.lookahead + n })
    fillPrime (some (.tab ds))
    pure false) hr = _
  rw [bind_app, update]
  simp only []
  rw [bind_app, prime]
  simp only [pure_app, hl, setD_setD]
  rfl


/-- Complete first source call, including real loop exit and padding. -/
theorem local_fill_window_first_run {h : Heap} {r : ZStreamRef} {ds w io : Nat}
    {z : ZStream} {d : DeflateState} {ref : BRef} {ia wa : Array UInt8}
    (live : DLive h r ds z d) (shift : d.hash_shift < 32) (win : d.window = .ref (.blk w) 0)
    (get : h.bytes w = some wa) (writable : h.ro w = false) (size : wa.size = 65536)
    (ss : d.strstart = 0) (la : d.lookahead = 0) (ins : d.insert = 0) (hw : d.high_water = 0)
    (ws : d.w_size = 32768) (wsz : d.window_size = 65536) (wrap : d.wrap = 1)
    (pointer : z.next_in = .ref ref io) (input : Space.get h ref = some ia)
    (inputBound : io + z.avail_in.toNat ≤ ia.size) (nonempty : z.avail_in ≠ 0)
    (separate : BRef.blk w ≠ ref ∨ (rbLen z.avail_in 65536).toNat ≤ io ∨
      io + (rbLen z.avail_in 65536).toNat ≤ 0) :
    fill_window (some (.tab ds)) h =
      .ok ((), firstFillHeap h r ds w z d ref io ia wa) := by
  let n := rbLen z.avail_in 65536
  let copied := copyRange wa ia 0 io n.toNat
  let z' := readStream z n ref io (adlerValue z.adler ((ia.toList.drop io).take n.toNat))
  let dr := primeState { d with lookahead := n } copied
  let hr := firstRead h r ds w z d ref io ia wa
  have fields := primeState_fields { d with lookahead := n } copied
  have look : dr.lookahead = n := fields.2.2.1
  have state : hr.dstates ds = some dr := by simp [hr, firstRead, dr, n, copied]
  have stream : r.get hr = some z' := by
    simp only [hr, firstRead, ZStreamRef.get_setD]
    exact ZStreamRef.get_put_same (by simpa [stream_get_bytes] using live.hz) _
  have next : fillCond (some (.tab ds)) false hr = .ok ((false, false), hr) := by
    have back : dr.strm = some r := fields.1.trans live.back
    have exhausted : n < MIN_LOOKAHEAD_u → z'.avail_in = 0 := by
      intro small
      have smallNat : n.toNat < 262 := by simpa [UInt32.lt_iff_toNat_lt, MIN_LOOKAHEAD_u] using small
      have count : n.toNat = min z.avail_in.toNat 65536 := by simpa [n] using rbLen_nat z.avail_in 65536
      have eq : n = z.avail_in := UInt32.toNat_inj.mp (by omega)
      simp [z', readStream, eq]
    unfold fillCond
    simp only [bind_app, ldDeflateState_tab state, Bool.false_eq_true, ite_false, look, back]
    by_cases small : n < MIN_LOOKAHEAD_u
    · simp [small, zrd_eq, stream, exhausted small]
    · simp [small]
  have body := local_fill_body_first_read live shift win get writable size ss la ins ws wsz wrap pointer input
    inputBound nonempty separate
  have loop := do_once body next
  have count : n.toNat = min z.avail_in.toNat 65536 := by simpa [n] using rbLen_nat z.avail_in 65536
  have bound : n.toNat ≤ 65536 := by omega
  have nz : n ≠ 0 := by
    intro zero
    have zeroNat : n.toNat = 0 := by rw [zero]; rfl
    have ai : z.avail_in.toNat = 0 := by omega
    exact nonempty (UInt32.toNat_inj.mp ai)
  have bytes : hr.bytes w = some copied := by simp [hr, firstRead, n, copied]
  have ro : hr.ro w = false := by simpa [hr, firstRead] using writable
  have pad := fill_high_water_first state
    (fields.2.2.2.2.2.trans win) bytes ro (by simpa [copied, size_copyRange] using size)
    (fields.2.1.trans ss) (fields.2.2.2.1.trans hw) (fields.2.2.2.2.1.trans wsz)
    (by simpa only [look] using nz) (by simpa only [look] using bound)
  rw [fill_window_source]
  simp only [bind_app, rdD_eq, live.hs, ws, loop]
  rw [pad]
  simp only [look]
  simp only [hr, firstRead, setD_bytes, ZStreamRef.put_bytes, setD_bytes_commute,
    setD_setD, ← stream_put_bytes, upd_upd, firstFillHeap, firstFillState]
  dsimp only [dr, primeState]
  split <;> rfl



/-- The same actual copied/padded fill result retains LocalState. -/
theorem local_first_fill_state {h : Heap} {r : ZStreamRef} {cutoff ds w io : Nat}
    {z : ZStream} {d : DeflateState} {ref : BRef} {ia wa : Array UInt8}
    (state : LocalState h cutoff r ds z d) (get : h.bytes w = some wa) (wsz : d.window_size = 65536) :
    let n := rbLen z.avail_in 65536
    let copied := copyRange wa ia 0 io n.toNat
    let nextZ := readStream z n ref io (adlerValue z.adler ((ia.toList.drop io).take n.toNat))
    LocalState (firstFillHeap h r ds w z d ref io ia wa) cutoff r ds nextZ (firstFillState d n copied) := by
  let n := rbLen z.avail_in 65536
  let copied := copyRange wa ia 0 io n.toNat
  let padded := fillRange copied n.toNat (firstPadding n).toNat 0
  let hb := {h with bytes := upd h.bytes w (some padded)}
  let df := firstFillState d n copied
  have localB : LocalState hb cutoff r ds z d := ZlibF.Spec.Public.Proofs.CompressLocalHeader.local_state_bytes_set state w padded wa get
    (by simp only [padded,copied,size_fillRange,size_copyRange])
  have bound : n.toNat ≤ 65536 := by have count := rbLen_nat z.avail_in 65536;change n.toNat = min z.avail_in.toNat 65536 at count;omega
  have high : df.high_water.toNat ≤ d.window_size.toNat := by
    change (n.toUInt64+firstPadding n).toNat ≤ d.window_size.toNat
    rw [wsz]
    exact (firstFill_high_water n bound).2
  have keep := firstFillState_keep d n copied
  have inv : DStInv hb ds df := by
    unfold df firstFillState primeState
    split <;> exact { localB.inv with
      hw := high
      blocks := localB.inv.blocks_keys rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl}
  exact ZlibF.Spec.Public.Proofs.CompressLocalHeader.local_state_setZD localB rfl state.live.zalloc state.live.zfree keep.2.1
    (by rw [keep.2.2.1];exact state.live.status) inv keep.1

/-- Exact first-fill heap effects at each represented typed slot. A copy
and padding touch only the window byte table; stores touch only the live
stream and private state. Equal allocation numbers in old tables are kept. -/
theorem local_first_fill_storage {h : Heap} {r : ZStreamRef} {ds w io : Nat}
    {z : ZStream} {d : DeflateState} {ref : BRef} {ia wa : Array UInt8}
    (live : DLive h r ds z d) (get : h.bytes w = some wa) :
    let after := firstFillHeap h r ds w z d ref io ia wa
    Shape h after ∧ after.nextBlk = h.nextBlk ∧ after.nalloc = h.nalloc ∧
      Frame h after (fun b => StreamRoot r b ∨ b = ds ∨ b = w) ∧
      after.words = h.words ∧ after.gzheaders = h.gzheaders ∧ after.istates = h.istates ∧ after.ro = h.ro ∧
      (∀ b, b ≠ w → after.bytes b = h.bytes b) ∧
      (∀ b, b ≠ ds → after.dstates b = h.dstates b) ∧
      (∀ b, ¬StreamRoot r b → after.streams b = h.streams b ∧ after.gzstates b = h.gzstates b) := by
  let n := rbLen z.avail_in 65536
  let padded := fillRange (copyRange wa ia 0 io n.toNat) n.toNat (firstPadding n).toNat 0
  let copied := {h with bytes := upd h.bytes w (some padded)}
  let stream := readStream z n ref io (adlerValue z.adler ((ia.toList.drop io).take n.toNat))
  let result := firstFillState d n (copyRange wa ia 0 io n.toNat)
  have getC : r.get copied = some z := by simpa only [copied,stream_get_bytes] using live.hz
  have shape := ((shape_setB get padded).trans (shape_put getC stream)).trans
    (shape_setD (by simpa using live.hs) result)
  refine ⟨shape,by simp [firstFillHeap],by simp [firstFillHeap],?_,
    by simp [firstFillHeap],by simp [firstFillHeap],by simp [firstFillHeap],by simp [firstFillHeap],?_,?_,?_⟩
  · refine ⟨by simp [firstFillHeap],by simp [firstFillHeap],by simp [firstFillHeap],
      by simp [firstFillHeap],by simp [firstFillHeap],?_⟩
    intro b _ outside
    have root : ¬StreamRoot r b := fun same => outside (Or.inl same)
    have state : b ≠ ds := fun same => outside (Or.inr (Or.inl same))
    have byte : b ≠ w := fun same => outside (Or.inr (Or.inr same))
    have before : SlotSame h copied b := by simp [SlotSame,copied,upd_ne _ _ _ _ byte]
    exact before.trans ((slot_put_except copied r stream b root).trans
      (slot_setD_except (r.put copied stream) ds result b state))
  · intro b different
    simp [firstFillHeap,upd_ne _ _ _ _ different]
  · intro b different
    simp [firstFillHeap,setD,upd_ne _ _ _ _ different]
  · intro b outside
    have slot := slot_put_except copied r stream b outside
    exact ⟨slot.2.2.1,slot.2.2.2.2.2.2.1⟩

/-- Old caller identities keep every non-byte typed lookup and every byte
lookup outside the new window. No old cross-table occupancy is excluded. -/
theorem local_first_fill_old_typed {h : Heap} {r : ZStreamRef} {cutoff ds w io : Nat}
    {z : ZStream} {d : DeflateState} {ref : BRef} {ia wa : Array UInt8}
    (live : DLive h r ds z d) (get : h.bytes w = some wa)
    (stateNew : cutoff ≤ ds) (windowNew : cutoff ≤ w)
    (streamNew : ∀ b, StreamRoot r b → cutoff ≤ b) :
    let after := firstFillHeap h r ds w z d ref io ia wa
    ∀ b, b < cutoff → SlotSame h after b := by
  obtain ⟨_,_,_,_,words,headers,istates,ro,bytes,states,streams⟩ := local_first_fill_storage live get
  dsimp only
  intro b old
  have notState : b ≠ ds := by omega
  have notWindow : b ≠ w := by omega
  have notStream : ¬StreamRoot r b := fun root => by have bound := streamNew b root;omega
  obtain ⟨stream,gzstate⟩ := streams b notStream
  exact ⟨bytes b notWindow,(by rw [words]),stream,(by rw [headers]),states b notState,
    (by rw [istates]),gzstate,(by rw [ro])⟩


/-- Actual initialized first refill, on the exact heap named by its source
copy and padding. Counts, local representation, frame and dispatch controls
are provided together. The original input offer can have any uInt length. -/
theorem local_fill_window_first {h : Heap} {r : ZStreamRef} {cutoff ds w io : Nat}
    {z : ZStream} {d : DeflateState} {ref : BRef} {ia wa : Array UInt8}
    (state : LocalState h cutoff r ds z d) (win : d.window = .ref (.blk w) 0)
    (get : h.bytes w = some wa) (writable : h.ro w = false) (size : wa.size = 65536)
    (ss : d.strstart = 0) (la : d.lookahead = 0) (ins : d.insert = 0) (hw : d.high_water = 0)
    (ws : d.w_size = 32768) (wsz : d.window_size = 65536) (wrap : d.wrap = 1)
    (pointer : z.next_in = .ref ref io) (input : Space.get h ref = some ia)
    (inputBound : io+z.avail_in.toNat ≤ ia.size) (nonempty : z.avail_in ≠ 0)
    (separate : BRef.blk w ≠ ref ∨ (rbLen z.avail_in 65536).toNat ≤ io ∨
      io+(rbLen z.avail_in 65536).toNat ≤ 0) :
    let n := rbLen z.avail_in 65536
    let copied := copyRange wa ia 0 io n.toNat
    let nextZ := readStream z n ref io (adlerValue z.adler ((ia.toList.drop io).take n.toNat))
    let result := firstFillState d n copied
    let after := firstFillHeap h r ds w z d ref io ia wa
    fill_window (some (.tab ds)) h = .ok ((),after) ∧
      LocalState after cutoff r ds nextZ result ∧ StreamAccounting z nextZ n.toNat 0 ∧
      Frame h after (fun b => StreamRoot r b ∨ b = ds ∨ b = w) ∧ Shape h after ∧
      result.lookahead = n ∧ result.strstart = 0 ∧ result.status = d.status ∧
      result.level = d.level ∧ result.strategy = d.strategy ∧ result.last_flush = d.last_flush ∧
      after.bytes w = some (fillRange copied n.toNat (firstPadding n).toNat 0) := by
  have count := rbLen_nat z.avail_in 65536
  have shift : d.hash_shift < 32 := by
    rw [UInt32.lt_iff_toNat_lt]
    exact (hash_parameters state.inv).hsh_lt
  obtain ⟨shape,_,_,frame,_⟩ := local_first_fill_storage state.live get
  have keep := firstFillState_keep d (rbLen z.avail_in 65536) (copyRange wa ia 0 io (rbLen z.avail_in 65536).toNat)
  refine ⟨local_fill_window_first_run state.live shift win get writable size ss la ins hw ws wsz wrap pointer input
    inputBound nonempty separate,local_first_fill_state state get wsz,
    read_stream_accounting z _ ref io _ pointer (by omega),frame,shape,keep.2.2.2.1,
    keep.2.2.2.2.trans ss,keep.2.2.1,?_,?_,?_,by simp [firstFillHeap]⟩ <;>
    unfold firstFillState primeState <;> split <;> rfl

/-- The short-input consumer gets exact exhaustion of its original offer;
this fact is derived from the actual first-read minimum, not assumed of a
callee. No restriction is added to the full first-refill producer above. -/
theorem local_first_fill_short_account {z : ZStream} {ref : BRef} {io : Nat} {checksum : UInt64}
    (pointer : z.next_in = .ref ref io) (small : z.avail_in.toNat ≤ 261) :
    let n := rbLen z.avail_in 65536
    let nextZ := readStream z n ref io checksum
    n = z.avail_in ∧ nextZ.avail_in = 0 ∧ StreamAccounting z nextZ z.avail_in.toNat 0 := by
  have count := rbLen_nat z.avail_in 65536
  change (rbLen z.avail_in 65536).toNat = min z.avail_in.toNat 65536 at count
  have same : rbLen z.avail_in 65536 = z.avail_in := UInt32.toNat_inj.mp (by omega)
  refine ⟨same,?_,?_⟩
  · simp [same,readStream]
  · simpa only [same] using read_stream_accounting z (rbLen z.avail_in 65536) ref io checksum pointer (by omega)

end ZlibF.Spec.Public.Proofs.CompressLocalFill
