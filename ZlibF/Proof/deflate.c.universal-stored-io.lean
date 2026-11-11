import ZlibF.Proof.«deflate.c.universal-stored»

/-!
# deflate.c, universal engine: writes to the caller's output in `deflate_stored`

`deflate_stored` copies bytes to `next_out` directly: from the window (`zmemcpy`) and from the
input (`read_buf(strm, next_out, len)`). The caller's output may be a byte block or the `depth`
array of another deflate state (`StreamBuffers` allows every writable byte view). This module
describes one write into that view: the stream invariants and the caller ranges are kept, and the
private blocks of the stream are untouched.
-/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- The kinds of the caller's output view: a byte block outside the stream, or the `depth`
array of another deflate state. -/
def OutputKind (h : Heap) (r : ZStreamRef) (ds : Nat) (d : DeflateState) (dst : BRef) : Prop :=
  (∃ ob, dst = .blk ob ∧ ¬ (StreamRoot r ob ∨ DeflateOwned ds d ob)) ∨
  (∃ owner foreign, dst = .dstate_depth owner ∧ h.dstates owner = some foreign ∧ owner ≠ ds)

/-- The caller's output view, its array and its capacity. -/
theorem output_view {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (good : DGood h r ds z d) (buffers : StreamBuffers h r) (out : z.next_out ≠ .null) :
    ∃ dst oo old, z.next_out = .ref dst oo ∧ Space.get h dst = some old ∧ Space.ro h dst = false ∧
      oo + z.avail_out.toNat ≤ old.size ∧ OutputKind h r ds d dst := by
  obtain ⟨ob, pointer⟩ := Zlib.Deflate.Universal.output_reference good.live.hz buffers out
  rcases pointer with ⟨oo, pointer⟩ | ⟨oo, pointer⟩
  · obtain ⟨output, get, ro, bound, _⟩ := caller_raw_output good buffers pointer
    exact ⟨.blk ob, oo, output, pointer, get, ro, bound,
      Or.inl ⟨ob, rfl, caller_raw_output_outside good buffers pointer⟩⟩
  · obtain ⟨foreign, get, bound, different, _, _⟩ := caller_foreign_output good buffers pointer
    exact ⟨.dstate_depth ob, oo, foreign.depth, pointer, BRef.get_dstate_depth get, rfl, bound,
      Or.inr ⟨ob, foreign, rfl, get, different⟩⟩

/-- What a write of a same-size array into the caller's output view keeps. -/
structure OutputPut (h g : Heap) (r : ZStreamRef) (ds : Nat) (z : ZStream) (d : DeflateState) : Prop where
  good : DGood g r ds z d
  sizes : ByteSizes h g
  static : g.static = h.static
  words : g.words = h.words
  private_ : ∀ b, (StreamRoot r b ∨ DeflateOwned ds d b) → g.bytes b = h.bytes b
  state : g.dstates ds = h.dstates ds
  stream : r.get g = r.get h
  nalloc : g.nalloc = h.nalloc
  nextBlk : g.nextBlk = h.nextBlk
  borrow : g.libcErrorBorrow = h.libcErrorBorrow
  owned : ∀ b, StreamOwned g r b ↔ StreamOwned h r b

theorem output_put {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    {dst : BRef} {old new : Array UInt8}
    (good : DGood h r ds z d) (get : Space.get h dst = some old) (kind : OutputKind h r ds d dst)
    (size : new.size = old.size) :
    OutputPut h (Space.put h dst new) r ds z d ∧ Space.get (Space.put h dst new) dst = some new := by
  rcases kind with ⟨ob, rfl, outside⟩ | ⟨owner, foreign, rfl, getF, different⟩
  · have getB : h.bytes ob = some old := get
    have goodG : DGood (Space.put h (BRef.blk ob) new) r ds z d := good.bytes_set ob new old getB size
    refine ⟨⟨goodG, ⟨fun ref a g0 => byte_view_write_size g0 getB size, fun ref => by cases ref <;> rfl⟩,
      rfl, rfl, fun b mine => ?_, rfl, stream_get_bytes h r _, rfl, rfl, rfl,
      stream_owned_keys good goodG rfl rfl rfl rfl⟩, upd_same _ _ _⟩
    have ne : b ≠ ob := fun e => outside (e ▸ mine)
    show (upd h.bytes ob (some new)) b = h.bytes b
    exact upd_ne _ _ _ _ ne
  · have put : Space.put h (BRef.dstate_depth owner) new = setD h owner { foreign with depth := new } :=
      BRef.put_dstate_depth getF new
    have equal : old = foreign.depth := Option.some.inj (get.symm.trans (BRef.get_dstate_depth getF))
    subst old
    rw [put]
    have goodG := foreign_depth_write_good good getF (Ne.symm different) new
    refine ⟨⟨goodG, foreign_depth_write_sizes getF size, rfl, rfl, fun _ _ => rfl,
      setD_dstates_ne _ _ _ _ (Ne.symm different), by cases r <;> rfl, rfl, rfl, rfl,
      stream_owned_keys good goodG rfl rfl rfl rfl⟩, BRef.get_dstate_depth (setD_dstates_same _ _ _)⟩


/-! ## Writes through a byte view -/

theorem view_put_dstates (h : Heap) {dst : BRef} {ds : Nat} (a : Array UInt8)
    (ne : ∀ o, dst = .dstate_depth o → o ≠ ds) : (Space.put h dst a).dstates ds = h.dstates ds := by
  cases dst with
  | dstate_depth o =>
    have no := ne o rfl
    show (match h.dstates o with
      | some s => { h with dstates := upd h.dstates o (some { s with depth := a }) } | none => h).dstates ds = _
    split
    · exact upd_ne _ _ _ _ (Ne.symm no)
    · rfl
  | blk _ | str _ | st_dist_code | st_length_code => rfl

theorem view_put_static (h : Heap) (dst : BRef) (a : Array UInt8) : (Space.put h dst a).static = h.static := by
  cases dst with
  | dstate_depth o =>
    show (match h.dstates o with
      | some s => { h with dstates := upd h.dstates o (some { s with depth := a }) } | none => h).static = _
    split <;> rfl
  | blk _ | str _ | st_dist_code | st_length_code => rfl

theorem view_put_stream (h : Heap) (r : ZStreamRef) (dst : BRef) (a : Array UInt8) :
    r.get (Space.put h dst a) = r.get h := by
  cases dst with
  | dstate_depth o =>
    show r.get (match h.dstates o with
      | some s => { h with dstates := upd h.dstates o (some { s with depth := a }) } | none => h) = _
    split <;> cases r <;> rfl
  | blk _ => cases r <;> rfl
  | str _ | st_dist_code | st_length_code => rfl

theorem view_put_comm (h : Heap) (r : ZStreamRef) (z : ZStream) (dst : BRef) (a : Array UInt8) :
    r.put (Space.put h dst a) z = Space.put (r.put h z) dst a := by
  cases dst with
  | dstate_depth o =>
    show r.put (match h.dstates o with
      | some s => { h with dstates := upd h.dstates o (some { s with depth := a }) } | none => h) z =
      (match (r.put h z).dstates o with
      | some s => { r.put h z with dstates := upd (r.put h z).dstates o (some { s with depth := a }) }
      | none => r.put h z)
    rw [ZStreamRef.put_dstates]
    split
    · cases r <;> simp only [ZStreamRef.put] <;> split <;> rfl
    · rfl
  | blk b =>
    show r.put { h with bytes := upd h.bytes b (some a) } z = { r.put h z with bytes := upd (r.put h z).bytes b (some a) }
    rw [ZStreamRef.put_bytes]; exact stream_put_bytes h r z _
  | str _ | st_dist_code | st_length_code => rfl

theorem view_put_get {h : Heap} {dst : BRef} {old : Array UInt8} (get : Space.get h dst = some old)
    (ro : Space.ro h dst = false) (a : Array UInt8) : Space.get (Space.put h dst a) dst = some a := by
  cases dst with
  | blk b => exact upd_same _ _ _
  | dstate_depth o =>
    cases state : h.dstates o with
    | none => simp [Space.get, state] at get
    | some s => rw [BRef.put_dstate_depth state]; exact BRef.get_dstate_depth (s := { s with depth := a }) (upd_same h.dstates o _)
  | str _ | st_dist_code | st_length_code => cases ro

theorem view_put_sizes {h : Heap} {dst : BRef} {old new : Array UInt8} (get : Space.get h dst = some old)
    (size : new.size = old.size) : ByteSizes h (Space.put h dst new) := by
  cases dst with
  | blk b => exact ⟨fun ref a g0 => byte_view_write_size g0 get size, fun ref => by cases ref <;> rfl⟩
  | dstate_depth o =>
    cases state : h.dstates o with
    | none => simp [Space.get, state] at get
    | some s =>
      have equal : old = s.depth := Option.some.inj (get.symm.trans (BRef.get_dstate_depth state))
      subst old
      rw [BRef.put_dstate_depth state]
      exact foreign_depth_write_sizes state size
  | str _ | st_dist_code | st_length_code => exact ⟨fun ref a g0 => ⟨a, g0, rfl⟩, fun _ => rfl⟩

/-- `read_buf(strm, buf, size)` into any writable byte view other than the stream's own state:
the copy, the cursors and the checksum of the copied bytes. -/
theorem read_buf_view {h : Heap} {r : ZStreamRef} {ds io bo : Nat}
    {z : ZStream} {d : DeflateState} {dst ref : BRef} {ia wa : Array UInt8}
    (hz : r.get h = some z) (hs : z.state = some (.deflate ds)) (hd : h.dstates ds = some d)
    (globals : d.wrap = 2 → CrcGlobals h) (pointer : z.next_in = .ref ref io)
    (input : Space.get h ref = some ia) (output : Space.get h dst = some wa) (writable : Space.ro h dst = false)
    (notState : ∀ o, dst = .dstate_depth o → o ≠ ds)
    (size : UInt32) (nonzero : rbLen z.avail_in size ≠ 0)
    (inputBound : io + (rbLen z.avail_in size).toNat ≤ ia.size)
    (outputBound : bo + (rbLen z.avail_in size).toNat ≤ wa.size)
    (separate : dst ≠ ref ∨ bo + (rbLen z.avail_in size).toNat ≤ io ∨
      io + (rbLen z.avail_in size).toNat ≤ bo) :
    let n := rbLen z.avail_in size
    let a := checksumValue d.wrap z.adler ((ia.toList.drop io).take n.toNat)
    read_buf (some r) (.ref dst bo) size h = .ok (n,
      r.put (Space.put h dst (copyRange wa ia bo io n.toNat)) (readStream z n ref io a)) := by
  let n := rbLen z.avail_in size
  let z1 := rbDec n z
  let h1 := r.put h z1
  let wa' := copyRange wa ia bo io n.toNat
  let h2 := Space.put h1 dst wa'
  let a := checksumValue d.wrap z.adler ((ia.toList.drop io).take n.toNat)
  let z2 := { z1 with adler := a }
  let h3 := r.put h2 z2
  have hz1 : r.get h1 = some z1 := ZStreamRef.get_put_same hz _
  have hz2 : r.get h2 = some z1 := by rw [view_put_stream]; exact hz1
  have hz3 : r.get h3 = some z2 := ZStreamRef.get_put_same hz2 _
  have getW : Space.get h1 dst = some wa := by rw [byte_get_stream_put]; exact output
  have getI : Space.get h1 ref = some ia := by rw [byte_get_stream_put]; exact input
  have ro : Space.ro h1 dst = false := by
    show Space.ro (r.put h z1) dst = false
    cases dst <;> simp_all [Space.ro]
  have copy : memcpyB (.ref dst bo) (.ref ref io) n.toNat h1 = .ok ((), h2) := by
    exact Ptr.memcpy_ok getW getI ro outputBound inputBound separate
  have getW2 : Space.get h2 dst = some wa' := view_put_get getW ro wa'
  have hd2 : h2.dstates ds = some d := by
    rw [view_put_dstates _ _ notState, ZStreamRef.put_dstates]; exact hd
  have slices : (wa'.toList.drop bo).take n.toNat = (ia.toList.drop io).take n.toNat := by
    rw [← seg_eq_take_drop wa' bo n.toNat (by simpa [wa', size_copyRange] using outputBound),
      ← seg_eq_take_drop ia io n.toNat inputBound]
    exact seg_copyRange wa ia bo io n.toNat outputBound
  have sizes2 : ByteSizes h1 h2 := view_put_sizes getW (size_copyRange _ _ _ _ _)
  obtain ⟨input', getI2, inputSize⟩ := sizes2.get ref ia getI
  have getI3 : Space.get h3 ref = some input' := by
    simpa only [h3, byte_get_stream_put] using getI2
  have advance : padd (.ref ref io : BPtr) n.toNat h3 = .ok (.ref ref (io + n.toNat), h3) := by
    simpa only [OkOn, padd] using Ptr.add_nat_ok getI3
      (by rw [inputSize]; exact inputBound : io + n.toNat ≤ input'.size)
  have endHeap : r.put h3 (rbAdvF (.ref ref (io + n.toNat)) n z2) =
      r.put (Space.put h dst wa') (readStream z n ref io a) := by
    have h2eq : h2 = r.put (Space.put h dst wa') z1 := by
      dsimp only [h2, h1]
      exact (view_put_comm h r z1 dst wa').symm
    dsimp only [h3]
    rw [ZStreamRef.put_put, h2eq, ZStreamRef.put_put]
    rfl
  have dec : zwr (some r) (rbDec n) h = .ok ((), h1) := by simp [zwr_eq, hz, h1, z1]
  have read : zrd (some r) (·.next_in) h1 = .ok (.ref ref io, h1) := by
    simp [zrd_eq, hz1, z1, rbDec, pointer]
  have state : zrd (some r) (·.state) h2 = .ok (some (.deflate ds), h2) := by
    simp [zrd_eq, hz2, z1, rbDec, hs]
  have wrapper : rd (some (.tab ds)) (·.wrap) h2 = .ok (d.wrap, h2) := by simp [rdD_eq, hd2]
  have seed : zrd (some r) (·.adler) h2 = .ok (z.adler, h2) := by simp [zrd_eq, hz2, z1, rbDec]
  have setAdler : zwr (some r) (rbSetAd a) h2 = .ok ((), h3) := by
    simp [zwr_eq, hz2, h3, z2, rbSetAd]
  have readNext : zrd (some r) (·.next_in) h3 = .ok (.ref ref io, h3) := by
    simp [zrd_eq, hz3, z2, z1, rbDec, pointer]
  have writeNext : zwr (some r) (rbAdvF (.ref ref (io + n.toNat)) n) h3 =
      .ok ((), r.put (Space.put h dst wa') (readStream z n ref io a)) := by
    simp only [zwr_eq, hz3, endHeap]
  rw [read_buf_ref_eq hz]
  change rbCore (some r) (.ref dst bo) n h = _
  have nz : (n == 0) = false := by simp [n, nonzero]
  by_cases one : d.wrap = 1
  · have checksum : Zlib.Adler32.adler32 z.adler (.ref dst bo) n h2 = .ok (a, h2) := by
      have run := ZlibF.Spec.Public.AdlerUpdateProof.adler_z_any_public
        (h := h2) (ref := dst) getW2 z.adler bo n.toUInt64 (by simpa [wa', size_copyRange] using outputBound)
      simpa only [C.run, Zlib.Adler32.adler32, UInt32.toNat_toUInt64, slices, a, checksumValue,
        ite_eq_left one] using run
    simp only [rbCore, nz, Bool.false_eq_true, ite_false, bind_app, dec, read, copy, state,
      castDeflateState_ok, wrapper, (show (d.wrap == 1) = true by simp [one]), ite_true,
      seed, checksum, setAdler, readNext, advance, writeNext, pure_app]
    rfl
  · by_cases two : d.wrap = 2
    · have checksum : Zlib.Crc32.crc32 z.adler (.ref dst bo) n h2 = .ok (a, h2) := by
        have g2 : CrcGlobals h2 := by
          obtain ⟨t1, t2⟩ := globals two
          have st : h2.static = h.static := by
            rw [view_put_static, ZStreamRef.put_static]
          exact ⟨by rw [st]; exact t1, by rw [st]; exact t2⟩
        have run := ZlibF.Spec.Public.Proofs.crc32 h2 z.adler (.ref dst bo) n
          ((wa'.toList.drop bo).take n.toNat) g2
          (Or.inr ⟨dst, bo, wa', rfl, getW2, by simpa [wa', size_copyRange] using outputBound, rfl⟩)
        simpa only [C.run, reduceCtorEq, ite_false, slices, a, checksumValue, ite_eq_right one,
          ite_eq_left two] using run
      simp only [rbCore, nz, Bool.false_eq_true, ite_false, bind_app, dec, read, copy, state,
        castDeflateState_ok, wrapper, (show (d.wrap == 1) = false by simpa using one),
        (show (d.wrap == 2) = true by simp [two]), ite_true,
        seed, checksum, setAdler, readNext, advance, writeNext, pure_app]
      rfl
    · have same : a = z.adler := by simp [a, checksumValue, one, two]
      have keep : h3 = h2 := by
        dsimp only [h3]
        have : z2 = z1 := by simp [z2, same, z1, rbDec]
        rw [this]
        exact ZStreamRef.put_self hz2
      have n1 : (d.wrap == 1) = false := by simpa using one
      have n2 : (d.wrap == 2) = false := by simpa using two
      simp only [keep] at readNext advance writeNext
      simp only [rbCore, nz, Bool.false_eq_true, ite_false, bind_app, dec, read, copy, state,
        castDeflateState_ok, wrapper, n1, n2, readNext, advance, writeNext, pure_app]
      rfl


/-! ## One direct write to the caller's output -/

/-- The stream record after `next_out += n; avail_out -= n; total_out += n`. -/
def outStream (z : ZStream) (no : BPtr) (n : UInt32) : ZStream :=
  { z with next_out := no, avail_out := z.avail_out - n, total_out := z.total_out + n.toUInt64 }

theorem good_stream_put {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (good : DGood h r ds z d) (z' : ZStream) (state : z'.state = z.state) (alloc : z'.zalloc = z.zalloc)
    (free : z'.zfree = z.zfree) : DGood (r.put h z') r ds z' d := by
  have g := good.setZD (z' := z') (d' := d) state (by rw [alloc]; exact good.live.zalloc)
    (by rw [free]; exact good.live.zfree) rfl good.live.status good.inv (by trkeep)
  rwa [setD_self (by rw [ZStreamRef.put_dstates]; exact good.live.hs)] at g

theorem sizes_stream_put (h : Heap) (r : ZStreamRef) (z : ZStream) : ByteSizes h (r.put h z) :=
  ⟨fun ref a get => ⟨a, by rw [byte_get_stream_put]; exact get, rfl⟩,
    fun ref => by cases ref <;> simp [Space.ro]⟩

theorem ByteSizes.chain {h g j : Heap} (first : ByteSizes h g) (second : ByteSizes g j) : ByteSizes h j := by
  refine ⟨?_, fun ref => (second.ro ref).trans (first.ro ref)⟩
  intro ref a get
  obtain ⟨middle, getM, sizeM⟩ := first.get ref a get
  obtain ⟨next, getA, sizeA⟩ := second.get ref middle getM
  exact ⟨next, getA, sizeA.trans sizeM⟩

/-- What one direct output step keeps: the stream invariants with the new stream record and the
same state, the caller ranges, and every private block. -/
structure OutStep (h g : Heap) (r : ZStreamRef) (ds : Nat) (z' : ZStream) (d : DeflateState) : Prop where
  good : DGood g r ds z' d
  buffers : StreamBuffers g r
  static : g.static = h.static
  words : g.words = h.words
  private_ : ∀ b, (StreamRoot r b ∨ DeflateOwned ds d b) → g.bytes b = h.bytes b
  nalloc : g.nalloc = h.nalloc

theorem output_step_close {h g : Heap} {r : ZStreamRef} {ds : Nat} {z z' : ZStream} {d : DeflateState}
    {dst : BRef} {old new : Array UInt8} {used produced : Nat}
    (good : DGood h r ds z d) (buffers : StreamBuffers h r)
    (get : Space.get h dst = some old) (kind : OutputKind h r ds d dst) (size : new.size = old.size)
    (g1 : g = Space.put h dst new)
    (account : StreamAccounting z z' used produced) :
    OutStep h (r.put g z') r ds z' d := by
  subst g
  obtain ⟨put, _⟩ := output_put good get kind size
  have goodA := good_stream_put put.good z' account.2.2.2.2.2.2.1 account.2.2.2.2.2.2.2.1
    account.2.2.2.2.2.2.2.2.1
  have sizes := put.sizes.chain (sizes_stream_put _ r z')
  have owned : ∀ b, StreamOwned (r.put (Space.put h dst new) z') r b ↔ StreamOwned h r b :=
    stream_owned_keys good goodA rfl rfl rfl rfl
  refine ⟨goodA, stream_buffers_sizes good.live.hz goodA.live.hz buffers sizes owned account, ?_, ?_,
    fun b mine => ?_, ?_⟩
  · rw [ZStreamRef.put_static]; exact put.static
  · rw [show (r.put (Space.put h dst new) z').words = (Space.put h dst new).words by cases r <;> simp only [ZStreamRef.put] <;> split <;> rfl]
    exact put.words
  · rw [ZStreamRef.put_bytes]; exact put.private_ b mine
  · rw [show (r.put (Space.put h dst new) z').nalloc = (Space.put h dst new).nalloc by cases r <;> simp only [ZStreamRef.put] <;> split <;> rfl]
    exact put.nalloc

/-- `zmemcpy(s->strm->next_out, src, n); next_out += n; avail_out -= n; total_out += n;` from a
source outside the caller's output. -/
theorem output_copy {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    {dst src : BRef} {oo so : Nat} {old sa : Array UInt8}
    (good : DGood h r ds z d) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref dst oo) (get : Space.get h dst = some old) (ro : Space.ro h dst = false)
    (cap : oo + z.avail_out.toNat ≤ old.size) (kind : OutputKind h r ds d dst)
    (srcGet : Space.get h src = some sa) (apart : dst ≠ src) (n : UInt32)
    (room : n.toNat ≤ z.avail_out.toNat) (srcBound : so + n.toNat ≤ sa.size) :
    let g := Space.put h dst (copyRange old sa oo so n.toNat)
    let z' := outStream z (.ref dst (oo + n.toNat)) n
    (do memcpyB z.next_out (.ref src so) n.toNat
        let no ← padd z.next_out n.toNat
        zwr (some r) (fun z => { z with next_out := no, avail_out := z.avail_out - n, total_out := z.total_out + n.toUInt64 })) h = .ok ((), r.put g z') ∧
      OutStep h (r.put g z') r ds z' d ∧ StreamAccounting z z' 0 n.toNat := by
  intro g z'
  have copy : memcpyB z.next_out (.ref src so) n.toNat h = .ok ((), g) := by
    rw [pointer]; exact Ptr.memcpy_ok get srcGet ro (by omega) srcBound (Or.inl apart)
  have getG : Space.get g dst = some (copyRange old sa oo so n.toNat) := view_put_get get ro _
  have step : padd z.next_out n.toNat g = .ok (.ref dst (oo + n.toNat), g) := by
    rw [pointer]
    simpa only [OkOn, padd] using Ptr.add_nat_ok getG (by rw [size_copyRange]; omega)
  have hzG : r.get g = some z := by rw [view_put_stream]; exact good.live.hz
  have write : zwr (some r) (fun z => { z with next_out := .ref dst (oo + n.toNat), avail_out := z.avail_out - n, total_out := z.total_out + n.toUInt64 }) g = .ok ((), r.put g z') := by
    simp only [zwr_eq, hzG]; rfl
  have account : StreamAccounting z z' 0 n.toNat := by
    have sub : (z.avail_out - n).toNat = z.avail_out.toNat - n.toNat :=
      UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr room)
    refine ⟨Nat.zero_le _, room, by simp [z', outStream], ?_, (advance_zero _).symm, ?_,
      rfl, rfl, rfl, rfl, rfl⟩
    · show (z.avail_out - n).toNat + n.toNat = z.avail_out.toNat
      omega
    · show _ = advance z.next_out n.toNat
      rw [pointer]; rfl
  refine ⟨?_, output_step_close good buffers get kind (size_copyRange _ _ _ _ _) rfl account, account⟩
  simp only [bind_app, copy, step, write]

/-- `read_buf(s->strm, s->strm->next_out, n); next_out += n; avail_out -= n; total_out += n;`
with `n` at most `avail_in` and `avail_out`. -/
theorem output_read {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    {dst : BRef} {oo : Nat} {old : Array UInt8}
    (good : DGood h r ds z d) (buffers : StreamBuffers h r) (globals : LibraryGlobals h)
    (pointer : z.next_out = .ref dst oo) (get : Space.get h dst = some old) (ro : Space.ro h dst = false)
    (cap : oo + z.avail_out.toNat ≤ old.size) (kind : OutputKind h r ds d dst)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null) (n : UInt32) (nonzero : n ≠ 0)
    (room : n.toNat ≤ z.avail_out.toNat) (avail : n.toNat ≤ z.avail_in.toNat) :
    ∃ g z', (do
        let _ ← read_buf (some r) (← zrd (some r) (·.next_out)) n
        let no ← padd (← zrd (some r) (·.next_out)) n.toNat
        zwr (some r) (fun z => { z with next_out := no, avail_out := z.avail_out - n, total_out := z.total_out + n.toUInt64 })) h = .ok ((), g) ∧
      OutStep h g r ds z' d ∧ StreamAccounting z z' n.toNat n.toNat := by
  have inputNZ : z.avail_in ≠ 0 := by
    intro e; rw [e] at avail; have : n.toNat ≠ 0 := by
      intro e2; exact nonzero (UInt32.toNat_inj.mp (by rw [e2]; rfl))
    simp at avail; omega
  obtain ⟨ref, io, inPtr⟩ : ∃ ref io, z.next_in = .ref ref io := by
    cases e : z.next_in with
    | null => exact False.elim (inputValid inputNZ e)
    | ref ref io => exact ⟨ref, io, rfl⟩
  obtain ⟨ia, inGet, inBound⟩ := caller_input_array good buffers inPtr
  have count : rbLen z.avail_in n = n := by
    unfold rbLen; split
    · rfl
    · rename_i big
      have b2 : z.avail_in.toNat ≤ n.toNat := UInt32.le_iff_toNat_le.mp (by simpa using big)
      exact UInt32.toNat_inj.mp (by omega)
  have notState : ∀ o, dst = .dstate_depth o → o ≠ ds := by
    intro o e
    rcases kind with ⟨ob, e2, _⟩ | ⟨owner, _, e2, _, different⟩
    · rw [e] at e2; cases e2
    · rw [e] at e2; cases e2; exact different
  have separate : dst ≠ ref ∨ oo + n.toNat ≤ io ∨ io + n.toNat ≤ oo := by
    obtain ⟨z0, get0, _, _, sep⟩ := buffers
    have same : z0 = z := Option.some.inj (get0.symm.trans good.live.hz)
    subst z0
    rw [inPtr, pointer] at sep
    rcases sep with zero | zero | sep
    · omega
    · omega
    · rcases sep with ne | before | after
      · exact Or.inl (Ne.symm ne)
      · exact Or.inr (Or.inr (by omega))
      · exact Or.inr (Or.inl (by omega))
  have crc : good.live.hs = good.live.hs := rfl
  have run := read_buf_view (bo := oo) good.live.hz good.live.zst good.live.hs
    (fun _ => Zlib.Deflate.Universal.crc_globals_of_library globals) inPtr inGet get ro notState n
    (by rw [count]; exact nonzero) (by rw [count]; omega) (by rw [count]; omega) (by rw [count]; exact separate)
  rw [count] at run
  let a := checksumValue d.wrap z.adler ((ia.toList.drop io).take n.toNat)
  let g := Space.put h dst (copyRange old ia oo io n.toNat)
  let z1 := readStream z n ref io a
  let z' := outStream z1 (.ref dst (oo + n.toNat)) n
  have hz1 : r.get (r.put g z1) = some z1 := by
    apply ZStreamRef.get_put_same; rw [view_put_stream]; exact good.live.hz
  have getG : Space.get (r.put g z1) dst = some (copyRange old ia oo io n.toNat) := by
    rw [byte_get_stream_put]; exact view_put_get get ro _
  have nextOut : z1.next_out = z.next_out := rfl
  have readOut : zrd (some r) (·.next_out) h = .ok (z.next_out, h) := by simp [zrd_eq, good.live.hz]
  have readOut1 : zrd (some r) (·.next_out) (r.put g z1) = .ok (z.next_out, r.put g z1) := by
    simp [zrd_eq, hz1, nextOut]
  have step : padd z.next_out n.toNat (r.put g z1) = .ok (.ref dst (oo + n.toNat), r.put g z1) := by
    rw [pointer]
    simpa only [OkOn, padd] using Ptr.add_nat_ok getG (by rw [size_copyRange]; omega)
  have write : zwr (some r) (fun z => { z with next_out := .ref dst (oo + n.toNat), avail_out := z.avail_out - n, total_out := z.total_out + n.toUInt64 }) (r.put g z1) = .ok ((), r.put (r.put g z1) z') := by
    simp only [zwr_eq, hz1]; rfl
  have accRead : StreamAccounting z z1 n.toNat 0 := read_stream_accounting z n ref io a inPtr avail
  have account : StreamAccounting z z' n.toNat n.toNat := by
    have sub : (z.avail_out - n).toNat = z.avail_out.toNat - n.toNat :=
      UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr room)
    obtain ⟨u1, _, i1, o1, ip1, op1, st1, al1, fr1, op1', rs1⟩ := accRead
    refine ⟨avail, room, i1, ?_, ip1, ?_, st1, al1, fr1, op1', rs1⟩
    · show (z1.avail_out - n).toNat + n.toNat = z.avail_out.toNat
      have : z1.avail_out = z.avail_out := rfl
      rw [this]; omega
    · show _ = advance z.next_out n.toNat
      rw [pointer]; rfl
  refine ⟨r.put g z', z', ?_, ?_, account⟩
  · rw [ZStreamRef.put_put] at write
    rw [← pointer] at run
    dsimp only [g, z1, a, z'] at readOut1 step write ⊢
    simp only [bind_app, readOut, run, readOut1, step, write, pure_app]
  · exact output_step_close good buffers get kind (size_copyRange _ _ _ _ _) rfl account

end Zlib.Deflate.Engine.Proofs
