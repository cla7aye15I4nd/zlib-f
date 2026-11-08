import ZlibF.Proof.«deflate.c.default-core»
import ZlibF.Proof.«deflate.c.init.memory»
import ZlibF.Proof.«deflate.c.engine.full-storage»

/-! # Fresh one-byte caller output for ordinary default deflate histories -/

namespace ZlibF.Spec.Public.Proofs.DeflateCore
open C ZlibF.Spec ZlibF.Spec.Public
open Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open Zlib.Deflate.Engine.Proofs Zlib.Deflate.Proofs.DefaultInit
set_option autoImplicit false

/-- Successful actual default initialization retains the library tables. -/
theorem initialized_globals {h after : Heap} {r : ZStreamRef} {version : BPtr}
    (domain : InitDomain h r version)
    (actual : C.run (deflateInit_ (some r) Z_DEFAULT_COMPRESSION version 112) h = .ok (Z_OK, after)) :
    LibraryGlobals after := by
  obtain ⟨fresh, unique, globals, versionValue, z, getZ, allocators, _state⟩ := domain
  have allocation := default_init_success_allocations fresh unique globals getZ allocators versionValue actual
  obtain ⟨rc, computed, execution, properties⟩ :=
    (DeflateInit.deflateInit_proof Z_DEFAULT_COMPRESSION).2.2
      h r z version fresh unique globals getZ allocators versionValue
  obtain ⟨_code, heaps⟩ := Prod.mk.inj (Except.ok.inj (execution.symm.trans actual))
  rw [heaps] at properties
  have first : h.allocOk h.nalloc ≠ false := by
    have zero : h.allocOk h.nalloc = true := by simpa only [Nat.add_zero] using allocation 0 (by decide)
    rw [zero]
    decide
  have all : (List.range 5).all (fun j => h.allocOk (h.nalloc + j)) = true := by
    simpa only [List.all_eq_true, List.mem_range] using allocation
  simp only [ite_eq_right first, ite_eq_left all] at properties
  obtain ⟨zf, sf, _good, _alloc, _free, _level, _strategy, _bits, _hash, _wrap,
    _start, _look, _pending, _valid, _header, _inputTotal, _outputTotal, _msg,
    frame, _live, _owned⟩ := properties.2.2
  exact frame.1.symm.trans globals

/-- The public raw-output frame also retains all library tables. -/
theorem raw_frame_static {h after : Heap} {r : ZStreamRef} {ds : Nat} {d : DeflateState}
    {pointer : BPtr} {written : Nat}
    (raw : DeflateCore.Output pointer)
    (frame : BufferFrame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b)
      [⟨pointer, written⟩]) : h.static = after.static := by
  have static := frame.1.1
  rcases raw with null | ⟨block, offset, pointerEq⟩
  · simpa only [restoreRegions, List.foldl_cons, List.foldl_nil, null] using static
  · rw [pointerEq] at static
    cases contents : h.bytes block <;>
      simpa [restoreRegions, Space.get, Space.put, contents] using static

/-- Initial library tables are retained by every actual ordinary request,
including pointer and scalar refusals. They are not a new caller premise. -/
theorem calls_globals {h : Heap} {r : ZStreamRef}
    (history : DeflateCore.Calls r h) : LibraryGlobals h := by
  induction history with
  | init domain actual => exact initialized_globals domain actual
  | caller _ edit _ih => exact edit.2.2.1
  | step previous getZ buffers raw actual ih =>
      obtain ⟨ds, z, d, config, boundary⟩ := calls_boundary previous
      have same : z = _ := Option.some.inj (boundary.good.live.hz.symm.trans getZ)
      subst z
      obtain ⟨_used, written, _rc, computed, _z, _d, execution, _boundary,
        _buffers, _good, _account, _bytes, _in, _out, _allowed, _errors, _bad,
        _terminal, _shape, frame, _live, _count, _frontier⟩ :=
        boundary.all_scalar_request_contract _ buffers raw
      have heaps := (Prod.mk.inj (Except.ok.inj (execution.symm.trans actual))).2
      subst computed
      exact (raw_frame_static raw frame).symm.trans ih

/-- The stream record cannot alias any stream-owned state or array. -/
theorem stream_root_unowned {h : Heap} {r : ZStreamRef} {ds b : Nat}
    {z : ZStream} {d : DeflateState} (good : DGood h r ds z d)
    (root : StreamRoot r b) : ¬ StreamOwned h r b := by
  intro owned
  have ownership := (stream_owned_deflate good b).mp owned
  have absent : h.streams b = none ∧ h.gzstates b = none := by
    obtain ⟨w, p, q, pb, blocks⟩ := good.inv.blocks
    rcases ownership with same | win | prev | head | pending
    · subst b
      have slots := good.uniq.dstates_only good.live.hs
      exact ⟨slots.2.2.1, slots.2.2.2.2.2⟩
    · rw [blocks.win] at win
      cases win
      obtain ⟨a, get, _size⟩ := blocks.wa
      have slots := good.uniq.bytes_only get
      exact ⟨slots.2.1, slots.2.2.2.2.2⟩
    · rw [blocks.prev] at prev
      cases prev
      obtain ⟨a, get, _size⟩ := blocks.pa
      have slots := good.uniq.words_only get
      exact ⟨slots.2.1, slots.2.2.2.2.2⟩
    · rw [blocks.head] at head
      cases head
      obtain ⟨a, get, _size⟩ := blocks.qa
      have slots := good.uniq.words_only get
      exact ⟨slots.2.1, slots.2.2.2.2.2⟩
    · rw [blocks.pbuf] at pending
      cases pending
      obtain ⟨a, get, _size⟩ := blocks.ba
      have slots := good.uniq.bytes_only get
      exact ⟨slots.2.1, slots.2.2.2.2.2⟩
  have get := good.live.hz
  cases r with
  | tab i =>
      change b = i at root
      simp [ZStreamRef.get, ← root, absent.1] at get
  | in_gzstate_strm i =>
      change b = i at root
      simp [ZStreamRef.get, ← root, absent.2] at get

/-- A caller can add one fresh byte allocation and replace only the output
binding. This is an actual public Rebuffer witness, not a library allocation
call or an assumption about allocator success. Every original public input
view and its exact snapshot survive, including static and embedded views. -/
theorem rebuffer_one_byte_of_good {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState} {input : List UInt8}
    (good : DGood h r ds z d) (globals : LibraryGlobals h) (allocators : DefAlloc z)
    (header : d.gzhead = none) (buffers : StreamBuffers h r)
    (snapshot : Bytes h z.next_in z.avail_in.toNat input) :
    ∃ after z', Rebuffer h after r ∧ r.get after = some z' ∧
      z' = { z with next_out := .ref (.blk h.nextBlk) 0, avail_out := 1 } ∧
      Bytes after z'.next_in z'.avail_in.toNat input ∧ StreamBuffers after r ∧
      DGood after r ds z' d ∧ DefAlloc z' ∧
      after.nextBlk = h.nextBlk + 1 ∧ after.nalloc = h.nalloc + 1 ∧
      (∀ b, DeflateOwned ds d b → SlotSame h after b) := by
  let allocated := Zlib.Zutil.Proofs.allocHeap h 1
  let next : ZStream := { z with next_out := .ref (.blk h.nextBlk) 0, avail_out := 1 }
  let after := r.put allocated next
  have allocatedGet : r.get allocated = some z := by
    cases r <;> simpa only [ZStreamRef.get, allocated, Zlib.Zutil.Proofs.allocHeap] using good.live.hz
  have nextGet : r.get after = some next := ZStreamRef.get_put_same allocatedGet next
  have allocatedFresh : Fresh allocated := fresh_byteHeap good.fresh 1
  have allocatedUnique : Uniq allocated := uniq_byteHeap good.uniq good.fresh 1
  have afterShape := shape_put allocatedGet next
  have afterFresh : Fresh after := afterShape.fresh (by simp) allocatedFresh
  have afterUnique : Uniq after := afterShape.uniq allocatedUnique
  have afterGlobals : LibraryGlobals after := by simpa [LibraryGlobals, after, allocated,
    Zlib.Zutil.Proofs.allocHeap] using globals
  have allocatedFrame : Frame h allocated (StreamRoot r) := by
    refine frame_of_old r good.fresh rfl rfl rfl (by simp [allocated, Zlib.Zutil.Proofs.allocHeap])
      (by simp [allocated, Zlib.Zutil.Proofs.allocHeap]) ?_
    intro b below _root
    simp [SlotSame, allocated, Zlib.Zutil.Proofs.allocHeap,
      upd_ne _ _ _ _ (show b ≠ h.nextBlk by omega)]
  have afterFrame : Frame h after (fun b => ¬ StreamOwned h r b) := by
    exact full_frame_weaken
      (frame_trans r allocatedFrame (stream_store_full_frame allocated r next))
      (fun b root => stream_root_unowned good root)
  have edit : Rebuffer h after r := by
    refine ⟨afterFresh, ?_, afterGlobals, afterFrame, z, next, good.live.hz, nextGet, ?_⟩
    · exact afterUnique
    · rfl
  obtain ⟨sameZ, getSame, changes, afterGood⟩ := rebuffer_good_no_header good edit header
  have same : sameZ = next := Option.some.inj (getSame.symm.trans nextGet)
  subst sameZ
  have preserveGet {ref : BRef} {a : Array UInt8} (get : Space.get h ref = some a) :
      Space.get after ref = some a := by
    have first : Space.get allocated ref = some a := by
      cases ref with
      | blk b =>
          have different : b ≠ h.nextBlk := by
            intro equal
            subst b
            have present : h.bytes h.nextBlk = some a := get
            have live : h.live h.nextBlk := Or.inl (by rw [present]; simp)
            exact good.fresh _ (Nat.le_refl _) live
          simpa [Space.get, allocated, Zlib.Zutil.Proofs.allocHeap,
            upd_ne _ _ _ _ different] using get
      | dstate_depth b => exact get
      | str i => exact get
      | st_dist_code => exact get
      | st_length_code => exact get
    exact ((byte_frame_put allocated r next (fun _ => False)).get ref 0
      (by intro b _root impossible; exact impossible)).trans first
  have snapshotA : Bytes after next.next_in next.avail_in.toNat input := by
    rcases snapshot with null | ⟨ref, offset, a, pointer, get, room, contents⟩
    · exact Or.inl null
    · exact Or.inr ⟨ref, offset, a, pointer, preserveGet get, room, contents⟩
  have inputRange : CallerRange after r next.next_in next.avail_in.toNat false := by
    obtain ⟨beforeZ, beforeGet, original, _output, _separate⟩ := buffers
    have beforeEq : beforeZ = z := Option.some.inj (beforeGet.symm.trans good.live.hz)
    subst beforeZ
    rcases original with null | ⟨_bytes, _write, outside⟩
    · exact Or.inl null
    · refine Or.inr ⟨⟨input, snapshotA⟩, ?_, ?_⟩
      · intro impossible
        cases impossible
      · intro b root owned
        exact outside b root ((stream_owned_deflate good b).mpr
          ((stream_owned_deflate afterGood b).mp owned))
  let newBytes : Array UInt8 := Array.ofFn (n := 1) fun i => Junk.of (h.garbage h.nalloc i.val)
  have newGet : after.bytes h.nextBlk = some newBytes := by
    simp [after, allocated, Zlib.Zutil.Proofs.allocHeap, newBytes]
  have newSize : newBytes.size = 1 := by simp [newBytes]
  have newRw : after.ro h.nextBlk = false := by
    simp [after, allocated, Zlib.Zutil.Proofs.allocHeap]
  have outputRange : CallerRange after r next.next_out next.avail_out.toNat true := by
    right
    refine ⟨⟨newBytes.toList, Or.inr ⟨.blk h.nextBlk, 0, newBytes, rfl,
      newGet, by simp [next, newSize], ?_⟩⟩, ?_, ?_⟩
    · change newBytes.toList = newBytes.toList.take 1
      exact (List.take_of_length_le (by simp [newSize])).symm
    · intro _write
      exact Or.inr ⟨.blk h.nextBlk, 0, newBytes, rfl, newGet, newRw, by simp [next, newSize]⟩
    · intro b root owned
      have equal : b = h.nextBlk := root
      subst b
      have oldOwned := (stream_owned_deflate afterGood h.nextBlk).mp owned
      exact good.fresh _ (Nat.le_refl _) (owned_live good oldOwned)
  have separation : Separate next.next_in next.avail_in.toNat next.next_out next.avail_out.toNat := by
    rcases snapshot with null | ⟨ref, offset, a, pointer, get, _room, _contents⟩
    · exact Or.inl null.2.1
    · have different : ref ≠ .blk h.nextBlk := by
        intro equal
        subst ref
        have present : h.bytes h.nextBlk = some a := get
        have live : h.live h.nextBlk := Or.inl (by rw [present]; simp)
        exact good.fresh _ (Nat.le_refl _) live
      exact Or.inr (Or.inr (by simpa only [next, pointer] using Or.inl different))
  refine ⟨after, next, edit, nextGet, rfl, snapshotA,
    ⟨next, nextGet, inputRange, outputRange, separation⟩, afterGood, allocators,
    by simp [after, allocated, Zlib.Zutil.Proofs.allocHeap],
    by simp [after, allocated, Zlib.Zutil.Proofs.allocHeap], ?_⟩
  exact fun b owned => rebuffer_owned good edit owned

/-- Every actual pure default-call history supplies the representation,
allocator and library facts needed to create the next positive output chunk.
No new invariant or allocator-success premise is imposed on the caller. -/
theorem calls_rebuffer_one_byte {h : Heap} {r : ZStreamRef} {z : ZStream}
    {input : List UInt8} (history : DeflateCore.Calls r h)
    (get : r.get h = some z) (buffers : StreamBuffers h r)
    (snapshot : Bytes h z.next_in z.avail_in.toNat input) :
    ∃ after z', Rebuffer h after r ∧ DeflateCore.Calls r after ∧ r.get after = some z' ∧
      z'.next_in = z.next_in ∧ z'.avail_in = z.avail_in ∧
      z'.next_out = .ref (.blk h.nextBlk) 0 ∧ z'.avail_out = 1 ∧
      Bytes after z'.next_in z'.avail_in.toNat input ∧ StreamBuffers after r ∧
      DefAlloc z' ∧ after.nextBlk = h.nextBlk + 1 ∧ after.nalloc = h.nalloc + 1 := by
  obtain ⟨ds, current, d, config, boundary⟩ := calls_boundary history
  have same : current = z := Option.some.inj (boundary.good.live.hz.symm.trans get)
  subst current
  obtain ⟨allocated, getAllocated, allocators⟩ := calls_allocators history
  have same : allocated = z := Option.some.inj (getAllocated.symm.trans get)
  subst allocated
  obtain ⟨after, next, edit, nextGet, changed, inputA, buffersA, _goodA,
      allocatorsA, frontier, attempts, _privateStorage⟩ :=
    rebuffer_one_byte_of_good boundary.good (calls_globals history) allocators
      boundary.no_header buffers snapshot
  refine ⟨after, next, edit, .caller history edit, nextGet, ?_, ?_, ?_, ?_,
    inputA, buffersA, allocatorsA, frontier, attempts⟩ <;> rw [changed]
  all_goals rfl

/-- The same rebuffer preserves the exact observed log and remaining input.
It changes no input bytes and inserts no data into the compression history. -/
theorem trace_rebuffer_one_byte {h : Heap} {r : ZStreamRef} {log : DataLog}
    {z : ZStream} {input : List UInt8} (history : DeflateCore.Trace r h log)
    (get : r.get h = some z) (buffers : StreamBuffers h r)
    (snapshot : Bytes h z.next_in z.avail_in.toNat input) :
    ∃ after z', Rebuffer h after r ∧ DeflateCore.Trace r after log ∧ r.get after = some z' ∧
      z'.next_in = z.next_in ∧ z'.avail_in = z.avail_in ∧
      z'.next_out = .ref (.blk h.nextBlk) 0 ∧ z'.avail_out = 1 ∧
      Bytes after z'.next_in z'.avail_in.toNat input ∧ StreamBuffers after r ∧
      DefAlloc z' ∧ after.nextBlk = h.nextBlk + 1 ∧ after.nalloc = h.nalloc + 1 := by
  obtain ⟨after, next, edit, _callsA, nextGet, inputPointer, inputCount,
      outputPointer, outputCount, inputA, buffersA, allocatorsA, frontier, attempts⟩ :=
    calls_rebuffer_one_byte (trace_calls history) get buffers snapshot
  exact ⟨after, next, edit, .caller history edit, nextGet, inputPointer, inputCount,
    outputPointer, outputCount, inputA, buffersA, allocatorsA, frontier, attempts⟩

end ZlibF.Spec.Public.Proofs.DeflateCore
