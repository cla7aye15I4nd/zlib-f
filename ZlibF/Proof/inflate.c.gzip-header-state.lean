import ZlibF.Proof.«inflate.c.gzip-header-frame»
import ZlibF.Proof.«inflate.c.stored-views»

/-!
# inflate.c: the invariant carried through one gzip header dispatch

`GzInv e l h z s used` relates the registers `l`, the heap `h`, the stream
record `z` and the state record `s` at a point inside one dispatch from a gzip
header mode to the entry `e` of that dispatch: the representation invariant
holds, `used` bytes of the unread input are consumed, the output registers are
those of the entry, and the heap differs from the entry heap only in the
footprint (`HeaderFoot`). Each kind of step of the header modes keeps it.
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The local `hbuf` is not the block of a caller region of the header record. -/
def HbufApart (c : Ctx) (h : Heap) (head : GzHeaderPtr) : Prop :=
  ∀ b, c.hbuf = .ref (.blk b) 0 → ∀ region ∈ HeaderRegions h head, ∀ ref off,
    region.pointer = .ref ref off → ref ≠ .blk b

/-- The `extra` buffer of the attached header record is separate from the unread
input: `zmemcpy` from the input into it must not overlap (C `memcpy`). -/
def ExtraApart (h : Heap) (head : GzHeaderPtr) (l : IL) : Prop :=
  ∀ i g, head = some (.tab i) → h.gzheaders i = some g →
    Separate g.extra g.extra_max.toNat l.next l.have_.toNat

theorem GzipHeaderStateFrame.refl (s : InflateState) : GzipHeaderStateFrame s s := by
  unfold GzipHeaderStateFrame; cases s; rfl

theorem GzipHeaderStateFrame.trans {a b c : InflateState} (first : GzipHeaderStateFrame a b)
    (second : GzipHeaderStateFrame b c) : GzipHeaderStateFrame a c := by
  unfold GzipHeaderStateFrame at *
  rw [second, first]

theorem HeaderStreamFrame.refl (z : ZStream) : HeaderStreamFrame z z := by
  unfold HeaderStreamFrame; cases z; rfl

theorem HeaderStreamFrame.trans {a b c : ZStream} (first : HeaderStreamFrame a b)
    (second : HeaderStreamFrame b c) : HeaderStreamFrame a c := by
  unfold HeaderStreamFrame at *
  rw [second, first]

/-! ## Heap facts -/

/-- Read-only flags of byte views depend on `ro` only. -/
theorem space_ro_of_ro {h h' : Heap} (e : h'.ro = h.ro) (ref : BRef) :
    Space.ro h' ref = Space.ro h ref := by
  cases ref <;> simp [Space.ro, e]

/-- A view write of the same size keeps the representation invariant, even if
the view is the stream's window (only the window's size matters). -/
theorem _root_.Zlib.Inflate.Spec.Good.byte_view_put_sized {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (good : Good h r zs z s) {dest : BRef} {old : Array UInt8}
    (get : Space.get h dest = some old) (write : Space.ro h dest = false)
    (array : Array UInt8) (size : array.size = old.size) :
    Good (Space.put h dest array) r zs z s := by
  have shape := byte_view_put_shape get write array
  refine ⟨⟨by rw [byte_view_put_stream]; exact good.live.hz,
      by rw [byte_view_put_istates]; exact good.live.hs,
      good.live.zst, good.live.back, good.live.mode, good.live.zalloc, good.live.zfree⟩,
    ⟨good.inv.wf, ?_, good.inv.reqbits, good.inv.bits, good.inv.ptr⟩,
    shape.uniq good.uniq, shape.fresh (byte_view_put_nextBlk h dest array) good.fresh⟩
  have win := good.inv.win
  refine ⟨win.wbits, ?_, win.nullws, win.ws, win.hv, win.wn, win.eq⟩
  rcases win.block with null | ⟨w, saved, ptr, savedGet, savedWrite, savedSize⟩
  · exact Or.inl null
  · refine Or.inr ?_
    by_cases same : dest = .blk w
    · subst same
      have eq : old = saved := Option.some.inj (get.symm.trans savedGet)
      subst eq
      refine ⟨w, array, ptr, ?_, by rw [byte_view_put_ro]; exact savedWrite, size.trans savedSize⟩
      change (Space.get (Space.put h (BRef.blk w) array) (BRef.blk w) : Option (Array UInt8)) = some array
      exact byte_view_get_put get write array
    · refine ⟨w, saved, ptr, ?_, by rw [byte_view_put_ro]; exact savedWrite, savedSize⟩
      have unchanged := byte_view_get_put_ne h (Ne.symm same) array
      change (Space.get (Space.put h dest array) (BRef.blk w) : Option (Array UInt8)) = some saved
      rw [unchanged]
      exact savedGet

theorem byte_view_get_headerPut (h : Heap) (i : Nat) (g : GzHeader) (ref : BRef) :
    (Space.get ((GzHeaderRef.tab i).put h g) ref : Option (Array UInt8)) = Space.get h ref := by
  cases ref <;> simp only [Space.get, GzHeaderRef.put] <;> split <;> rfl

theorem headerPut_dstates (h : Heap) (i : Nat) (g : GzHeader) :
    ((GzHeaderRef.tab i).put h g).dstates = h.dstates := by
  simp only [GzHeaderRef.put]; split <;> rfl

theorem headerPut_static (h : Heap) (i : Nat) (g : GzHeader) :
    ((GzHeaderRef.tab i).put h g).static = h.static := by
  simp only [GzHeaderRef.put]; split <;> rfl

/-- A `gz_header` record write keeps the representation invariant. -/
theorem _root_.Zlib.Inflate.Spec.Good.headerPut {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (good : Good h r zs z s) {i : Nat} {g0 : GzHeader}
    (current : h.gzheaders i = some g0) (g : GzHeader) :
    Good ((GzHeaderRef.tab i).put h g) r zs z s := by
  have shape := shape_putG (g := .tab i) current g
  refine ⟨⟨by rw [ZStreamRef.get_putG]; exact good.live.hz,
      by rw [GzHeaderRef.put_istates]; exact good.live.hs,
      good.live.zst, good.live.back, good.live.mode, good.live.zalloc, good.live.zfree⟩,
    StInv.congr (GzHeaderRef.put_bytes h _ g) (GzHeaderRef.put_ro h _ g) good.inv,
    shape.uniq good.uniq, shape.fresh (GzHeaderRef.put_nextBlk h _ g) good.fresh⟩

/-- The unread input keeps its length under a heap change that keeps sizes. -/
theorem BitInv.resync {h h' : Heap} {l : IL} {bs : List UInt8} (inv : BitInv h l bs)
    (sizes : ByteViewSizes h h') : ∃ bs', bs'.length = bs.length ∧ BitInv h' l bs' := by
  rcases inv.next with empty | ⟨ref, array, off, ptr, get, room, _⟩
  · exact ⟨bs, rfl, ⟨inv.have_eq, Or.inl empty, inv.hold_lt⟩⟩
  · obtain ⟨array', get', size'⟩ := sizes.view get
    refine ⟨(array'.toList.drop off).take bs.length, ?_, ?_, ?_, inv.hold_lt⟩
    · simp only [List.length_take, List.length_drop, Array.length_toList]
      omega
    · have : ((array'.toList.drop off).take bs.length).length = bs.length := by
        simp only [List.length_take, List.length_drop, Array.length_toList]
        omega
      rw [this]; exact inv.have_eq
    · have len : ((array'.toList.drop off).take bs.length).length = bs.length := by
        simp only [List.length_take, List.length_drop, Array.length_toList]
        omega
      refine Or.inr ⟨ref, array', off, ptr, get', by rw [len]; omega, by rw [len]⟩

/-! ## The entry of one dispatch -/

/-- The fixed data of one gzip header dispatch. -/
structure GzEntry where
  c : Ctx
  r : ZStreamRef
  zs : Nat
  h : Heap
  z : ZStream
  s : InflateState
  l : IL
  bs : List UInt8

namespace GzEntry

/-- The blocks whose records the dispatch may rewrite. -/
def changed (e : GzEntry) (b : Nat) : Prop :=
  StreamRoot e.r b ∨ b = e.zs ∨ e.c.hbuf = .ref (.blk b) 0 ∨ e.s.head = some (.tab b)

/-- The caller regions named by the entry header record. -/
def regions (e : GzEntry) : List Region := HeaderRegions e.h e.s.head

/-- The premises of the dispatch theorem, at the entry. -/
structure Valid (e : GzEntry) : Prop where
  env : Env e.c e.h e.r e.zs e.z e.s
  good : Good e.h e.r e.zs e.z e.s
  buffers : DispatchBuffers e.h e.r e.l e.bs
  hbuf : LocalHbuf e.c e.h
  apart : HbufApart e.c e.h e.s.head
  record : HeaderMemory e.h e.r e.s.head true
  globals : LibraryGlobals e.h
  extra : ExtraApart e.h e.s.head e.l
  incoming : e.l.bits.toNat ≤ 39

end GzEntry

/-- The current header record against the entry record: the maxima are kept,
each buffer pointer is kept or NULL. -/
def RecordLinks (e : GzEntry) (h : Heap) : Prop :=
  ∀ i, e.s.head = some (.tab i) → ∀ g0, e.h.gzheaders i = some g0 → ∃ g, h.gzheaders i = some g ∧
    g.extra_max = g0.extra_max ∧ g.name_max = g0.name_max ∧ g.comm_max = g0.comm_max ∧
    (g.extra = g0.extra ∨ g.extra = .null) ∧ (g.name = g0.name ∨ g.name = .null) ∧
    (g.comment = g0.comment ∨ g.comment = .null)

/-- The invariant at a point of one gzip header dispatch. -/
structure GzInv (e : GzEntry) (l : IL) (h : Heap) (z : ZStream) (s : InflateState) (used : Nat) : Prop where
  good : Good h e.r e.zs z s
  bits : ∃ rest, rest.length = e.bs.length - used ∧ BitInv h l rest
  usedLe : used ≤ e.bs.length
  next : l.next = inputAdvance e.l.next used
  count : l.have_.toNat + used = e.l.have_.toNat
  put : l.put = e.l.put
  left : l.left = e.l.left
  out : l.out_ = e.l.out_
  bound : l.bits.toNat ≤ 39
  mass : l.bits.toNat ≤ e.l.bits.toNat + 8 * used
  foot : HeaderFoot e.changed e.regions e.h h
  sizes : ByteViewSizes e.h h
  state : GzipHeaderStateFrame e.s s
  stream : HeaderStreamFrame e.z z
  links : RecordLinks e h

namespace GzInv

variable {e : GzEntry} {l : IL} {h : Heap} {z : ZStream} {s : InflateState} {used : Nat}

theorem refl (valid : e.Valid) : GzInv e e.l e.h e.z e.s 0 := by
  refine ⟨valid.good, ⟨e.bs, by simp, valid.buffers.bits⟩, Nat.zero_le _, (inputAdvance_zero _).symm,
    by simp, rfl, rfl, rfl, valid.incoming, by omega, HeaderFoot.refl _ _ _, ByteViewSizes.refl _,
    GzipHeaderStateFrame.refl _, HeaderStreamFrame.refl _, ?_⟩
  intro i _ g0 get
  exact ⟨g0, get, rfl, rfl, rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩

theorem env (inv : GzInv e l h z s used) (valid : e.Valid) : Env e.c h e.r e.zs z s :=
  ⟨valid.env.strm, valid.env.st, inv.good.live.hz, inv.good.live.hs⟩

theorem head (inv : GzInv e l h z s used) : s.head = e.s.head := by
  rw [inv.state]

theorem window (inv : GzInv e l h z s used) : s.window = e.s.window := by
  rw [inv.state]

theorem wrap (inv : GzInv e l h z s used) : s.wrap = e.s.wrap := by
  rw [inv.state]

theorem static (inv : GzInv e l h z s used) : h.static = e.h.static := inv.foot.static

theorem statics (inv : GzInv e l h z s used) (valid : e.Valid) : Zlib.Crc32.Proofs.StaticsOK h := by
  have ok := LibraryGlobals.statics valid.globals
  unfold Zlib.Crc32.Proofs.StaticsOK at ok ⊢
  rw [inv.static]
  exact ok

theorem readonly (inv : GzInv e l h z s used) (ref : BRef) : Space.ro h ref = Space.ro e.h ref :=
  space_ro_of_ro inv.foot.ro ref

/-- The local `hbuf` stays a writable four-byte block. -/
theorem hbuf (inv : GzInv e l h z s used) (valid : e.Valid) :
    ∃ b a, e.c.hbuf = .ref (.blk b) 0 ∧ h.bytes b = some a ∧ a.size = 4 ∧ h.ro b = false ∧
      e.changed b ∧ ¬ RegionRoot e.regions (.blk b) := by
  obtain ⟨b, a0, ptr, get0, size0, ro0⟩ := valid.hbuf
  obtain ⟨a, get, size⟩ := inv.sizes.view (ref := .blk b) get0
  refine ⟨b, a, ptr, get, size.trans size0, by rw [inv.foot.ro]; exact ro0,
    Or.inr (Or.inr (Or.inl ptr)), ?_⟩
  rintro ⟨region, member, off, rptr⟩
  exact valid.apart b ptr region member _ off rptr rfl

/-- A heap change that keeps the stream and state records, the header records
and every byte-view size, and keeps the footprint. -/
theorem withHeap (inv : GzInv e l h z s used) {h' : Heap} (good : Good h' e.r e.zs z s)
    (sizes : ByteViewSizes h h') (foot : HeaderFoot e.changed e.regions e.h h')
    (headers : h'.gzheaders = h.gzheaders) : GzInv e l h' z s used := by
  obtain ⟨rest, len, bits⟩ := inv.bits
  obtain ⟨rest', len', bits'⟩ := bits.resync sizes
  refine ⟨good, ⟨rest', len'.trans len, bits'⟩, inv.usedLe, inv.next, inv.count, inv.put, inv.left,
    inv.out, inv.bound, inv.mass, foot, inv.sizes.trans sizes, inv.state, inv.stream, ?_⟩
  intro i head g0 get0
  rw [headers]
  exact inv.links i head g0 get0

/-- A state record write of the gzip header fields. -/
theorem setState (inv : GzInv e l h z s used) {s' : InflateState} (frame : GzipHeaderStateFrame s s')
    (mode : HEAD ≤ s'.mode ∧ s'.mode ≤ SYNC) : GzInv e l (setI h e.zs s') z s' used := by
  have eq : s' = { s with mode := s'.mode, flags := s'.flags, check := s'.check, length := s'.length } := frame
  have good : Good (setI h e.zs s') e.r e.zs z s' := by
    apply good_state inv.good (by rw [eq]) mode
    apply inv.good.inv.of_fields <;> (try rw [eq]) <;> (try rfl)
    rw [eq]; exact inv.good.inv.bits
  obtain ⟨rest, len, bits⟩ := inv.bits
  refine ⟨good, ⟨rest, len, bits.byte_views (fun ref => byte_view_get_setI h e.zs s' ref)⟩, inv.usedLe,
    inv.next, inv.count, inv.put, inv.left, inv.out, inv.bound, inv.mass,
    inv.foot.setI (Or.inr (Or.inl rfl)) inv.good.live.hs s',
    inv.sizes.trans (byte_view_sizes_setI h e.zs s'), inv.state.trans frame, inv.stream, ?_⟩
  intro i head g0 get0
  exact inv.links i head g0 get0

/-- A stream record write of the gzip header fields (`adler`, `msg`). -/
theorem setStream (inv : GzInv e l h z s used) {z' : ZStream} (frame : HeaderStreamFrame z z') :
    GzInv e l (e.r.put h z') z' s used := by
  have eq : z' = { z with adler := z'.adler, msg := z'.msg } := frame
  have good0 : Good (setI (e.r.put h z') e.zs s) e.r e.zs z' s :=
    inv.good.setZI (by rw [eq]) (by rw [eq]; exact inv.good.live.zalloc) (by rw [eq]; exact inv.good.live.zfree)
      rfl inv.good.live.mode (StInv.congr (by simp) (by simp) inv.good.inv)
  have same : setI (e.r.put h z') e.zs s = e.r.put h z' := by
    apply tcSetI_same
    rw [ZStreamRef.put_istates]
    exact inv.good.live.hs
  rw [same] at good0
  obtain ⟨rest, len, bits⟩ := inv.bits
  refine ⟨good0, ⟨rest, len, bits.byte_views (fun ref => byte_view_get_stream_put h e.r z' ref)⟩, inv.usedLe,
    inv.next, inv.count, inv.put, inv.left, inv.out, inv.bound, inv.mass,
    inv.foot.streamPut (fun b root => Or.inl root) inv.good.live.hz z',
    inv.sizes.trans (byte_view_sizes_stream_put h e.r z'), inv.state, inv.stream.trans frame, ?_⟩
  intro i head g0 get0
  obtain ⟨g, get, rest⟩ := inv.links i head g0 get0
  refine ⟨g, ?_, rest⟩
  cases r : e.r with
  | tab j => rw [r] at *; simp only [ZStreamRef.put]; split <;> exact get
  | in_gzstate_strm j => rw [r] at *; simp only [ZStreamRef.put]; split <;> exact get

/-- `badMode`: the message pointer and mode `BAD`. -/
theorem bad (inv : GzInv e l h z s used) (i : Nat) :
    GzInv e l (tcBadHeap h e.r e.zs z s i) { z with msg := .ref (.str i) 0 } { s with mode := BAD } used := by
  have one := inv.setStream (z' := { z with msg := .ref (.str i) 0 }) rfl
  exact one.setState rfl (by change HEAD ≤ BAD ∧ BAD ≤ SYNC; decide)

/-- A write of the header record that keeps maxima and keeps or clears pointers. -/
theorem setHeader (inv : GzInv e l h z s used) {i : Nat} {g g' : GzHeader}
    (head : s.head = some (.tab i)) (current : h.gzheaders i = some g)
    (maxima : g'.extra_max = g.extra_max ∧ g'.name_max = g.name_max ∧ g'.comm_max = g.comm_max)
    (extra : g'.extra = g.extra ∨ g'.extra = .null) (name : g'.name = g.name ∨ g'.name = .null)
    (comment : g'.comment = g.comment ∨ g'.comment = .null) :
    GzInv e l ((GzHeaderRef.tab i).put h g') z s used := by
  have head0 : e.s.head = some (.tab i) := inv.head ▸ head
  obtain ⟨rest, len, bits⟩ := inv.bits
  refine ⟨inv.good.headerPut current g', ⟨rest, len, bits.byte_views (fun ref => byte_view_get_headerPut h i g' ref)⟩,
    inv.usedLe, inv.next, inv.count, inv.put, inv.left, inv.out, inv.bound, inv.mass,
    inv.foot.headerPut (Or.inr (Or.inr (Or.inr head0))) current g', ?_, inv.state, inv.stream, ?_⟩
  · exact inv.sizes.trans (fun ref => by rw [byte_view_get_headerPut])
  · intro j headj g0 get0
    have ij : j = i := by rw [head0] at headj; cases headj; rfl
    subst ij
    obtain ⟨g1, get1, m1, m2, m3, x1, n1, c1⟩ := inv.links j headj g0 get0
    rw [current] at get1
    cases get1
    refine ⟨g', by simp [GzHeaderRef.put, current], maxima.1.trans m1, maxima.2.1.trans m2,
      maxima.2.2.trans m3, ?_, ?_, ?_⟩
    · rcases extra with x | x <;> rw [x]
      · exact x1
      · exact Or.inr rfl
    · rcases name with x | x <;> rw [x]
      · exact n1
      · exact Or.inr rfl
    · rcases comment with x | x <;> rw [x]
      · exact c1
      · exact Or.inr rfl

/-- A store into the local `hbuf`. -/
theorem storeHbuf (inv : GzInv e l h z s used) (valid : e.Valid) {b : Nat} {a : Array UInt8}
    (ptr : e.c.hbuf = .ref (.blk b) 0) (get : h.bytes b = some a) (a' : Array UInt8)
    (size : a'.size = a.size) : GzInv e l (Space.put h (BRef.blk b) a') z s used := by
  obtain ⟨b', a1, ptr', get', _, ro, changed, outside⟩ := inv.hbuf valid
  rw [ptr] at ptr'
  have bb : b = b' := by cases ptr'; rfl
  subst bb
  have viewGet : Space.get h (BRef.blk b) = some a := get
  have write : Space.ro h (BRef.blk b) = false := ro
  refine inv.withHeap (inv.good.byte_view_put_sized viewGet write a' size)
    (byte_view_sizes_put viewGet write a' size) (inv.foot.privatePut changed outside get a') ?_
  rfl

/-- A write of a caller region's view that changes only covered bytes. -/
theorem storeRegion (inv : GzInv e l h z s used) {ref : BRef} {a : Array UInt8}
    (root : RegionRoot e.regions ref) (get : Space.get h ref = some a) (write : Space.ro h ref = false)
    (a' : Array UInt8) (size : a'.size = a.size)
    (covered : ∀ j, j < a.size → ¬ RegionCovers e.regions ref j → a'[j]? = a[j]?) :
    GzInv e l (Space.put h ref a') z s used := by
  refine inv.withHeap (inv.good.byte_view_put_sized get write a' size)
    (byte_view_sizes_put get write a' size) (inv.foot.regionPut root get write a' size covered) ?_
  cases ref <;> simp only [Space.put] <;> (try split) <;> rfl

/-- `INITBITS()`. -/
theorem initbits (inv : GzInv e l h z s used) : GzInv e { l with hold := 0, bits := 0 } h z s used := by
  obtain ⟨rest, len, bits⟩ := inv.bits
  exact ⟨inv.good, ⟨rest, len, (INITBITS_inv bits).1⟩, inv.usedLe, inv.next, inv.count, inv.put, inv.left,
    inv.out, by simp, by simp, inv.foot, inv.sizes, inv.state, inv.stream, inv.links⟩

/-- Registers that do not touch the input, output and bit buffer. -/
theorem scratch (inv : GzInv e l h z s used) {l' : IL}
    (same : l'.next = l.next ∧ l'.have_ = l.have_ ∧ l'.hold = l.hold ∧ l'.bits = l.bits ∧
      l'.put = l.put ∧ l'.left = l.left ∧ l'.out_ = l.out_) : GzInv e l' h z s used := by
  obtain ⟨n, hv, ho, bi, p, le, o⟩ := same
  obtain ⟨rest, len, bits⟩ := inv.bits
  refine ⟨inv.good, ⟨rest, len, ⟨by rw [hv]; exact bits.have_eq, by rw [n]; exact bits.next,
    by rw [ho, bi]; exact bits.hold_lt⟩⟩, inv.usedLe, by rw [n]; exact inv.next, by rw [hv]; exact inv.count,
    by rw [p]; exact inv.put, by rw [le]; exact inv.left, by rw [o]; exact inv.out,
    by rw [bi]; exact inv.bound, by rw [bi]; exact inv.mass, inv.foot, inv.sizes, inv.state, inv.stream,
    inv.links⟩

/-- Consuming `n` bytes of the input without touching the bit buffer. -/
theorem consume (inv : GzInv e l h z s used) {l' : IL} {n : Nat} (bound : n ≤ l.have_.toNat)
    (next : l'.next = inputAdvance l.next n) (count : l'.have_.toNat + n = l.have_.toNat)
    (same : l'.hold = l.hold ∧ l'.bits = l.bits ∧ l'.put = l.put ∧ l'.left = l.left ∧ l'.out_ = l.out_) :
    GzInv e l' h z s (used + n) := by
  obtain ⟨ho, bi, p, le, o⟩ := same
  obtain ⟨rest, len, bits⟩ := inv.bits
  have restBound : n ≤ rest.length := by rw [← bits.have_eq]; exact bound
  refine ⟨inv.good, ⟨rest.drop n, by rw [List.length_drop, len]; omega,
      bits.advance_bytes restBound next count ho bi⟩, ?_, ?_, ?_,
    by rw [p]; exact inv.put, by rw [le]; exact inv.left, by rw [o]; exact inv.out,
    by rw [bi]; exact inv.bound, by rw [bi]; have := inv.mass; omega, inv.foot, inv.sizes, inv.state,
    inv.stream, inv.links⟩
  · have := inv.count; have := bits.have_eq; have := inv.usedLe; omega
  · rw [next, inv.next, inputAdvance_add]
  · have := inv.count; omega

/-- `NEEDBITS(n)` for `n ≤ 32`: it either leaves with all input consumed or
holds at least `n` bits. -/
theorem needbits (inv : GzInv e l h z s used) (n : UInt32) (small : n.toNat ≤ 32) :
    ∃ r l' j, runX (NEEDBITS n) l h = .ok ((r, l'), h) ∧ GzInv e l' h z s (used + j) ∧
      (r = .ok () ∨ r = .error Ex.leave) ∧ (r = .ok () → n.toNat ≤ l'.bits.toNat) ∧
      l' = { l with next := l'.next, have_ := l'.have_, hold := l'.hold, bits := l'.bits } := by
  obtain ⟨rest, len, bits⟩ := inv.bits
  obtain ⟨r, l', j, run, jBound, bits', _, count, shape, bound, _, enough, _, kinds, cursor⟩ :=
    NEEDBITS_run_cursor bits n (by omega)
  refine ⟨r, l', j, run, ⟨inv.good, ⟨rest.drop j, by rw [List.length_drop, len]; omega, bits'⟩, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, inv.foot, inv.sizes, inv.state, inv.stream, inv.links⟩, kinds, enough, shape⟩
  · have u := inv.usedLe; rw [len] at jBound; omega
  · rw [cursor, inv.next, inputAdvance_add]
  · have one := bits'.have_eq
    have two := bits.have_eq
    rw [List.length_drop] at one
    have := inv.count
    omega
  · rw [shape]; exact inv.put
  · rw [shape]; exact inv.left
  · rw [shape]; exact inv.out
  · exact Nat.le_trans bound (Nat.max_le.mpr ⟨inv.bound, by omega⟩)
  · have := inv.mass; omega

end GzInv

end Zlib.Inflate.Proofs
