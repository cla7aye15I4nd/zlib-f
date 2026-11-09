import ZlibF.Proof.«inflate.c.copy-source-origin»
import ZlibF.Proof.«inflate.c.default-history-public-contract»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- A live stream record cannot alias an owned inflate state or window.
This follows from the actual allocation type uniqueness, including embedded
stream records. It imposes no extra destination restriction. -/
theorem stream_root_not_inflate_owned {h : Heap} {source dest : ZStreamRef} {zs b : Nat}
    {z oldDest : ZStream} {s : InflateState} (good : Good h source zs z s)
    (get : dest.get h = some oldDest) (root : StreamRoot dest b) :
    ¬ InflateOwned zs s b := by
  have notRoot : ∀ (words : h.words b = none) (streams : h.streams b = none)
      (headers : h.gzheaders b = none) (deflates : h.dstates b = none)
      (gzstates : h.gzstates b = none), False := by
    intro _ streams _ _ gzstates
    cases dest with
    | tab i =>
      change b = i at root
      subst i
      change h.streams b = some oldDest at get
      rw [streams] at get
      cases get
    | in_gzstate_strm i =>
      change b = i at root
      subst i
      simp only [ZStreamRef.get, gzstates, Option.map_none] at get
      cases get
  rintro (state | window)
  · subst b
    obtain ⟨words, streams, headers, deflates, _bytes, gzstates⟩ := Uniq.istates_only good.uniq good.live.hs
    exact notRoot words streams headers deflates gzstates
  · rcases good.inv.win.block with null | ⟨w, a, pointer, bytes, _write, _size⟩
    · rw [null] at window
      cases window
    · have same : w = b := BRef.blk.inj (Ptr.ref.inj (pointer.symm.trans window)).1
      subst w
      obtain ⟨words, streams, headers, deflates, _states, gzstates⟩ := Uniq.bytes_only good.uniq bytes
      exact notRoot words streams headers deflates gzstates

/-- The exact actual copy frame is an admitted environment frame relative
to the unchanged source. This is a proved relation about the produced heap,
not a caller-supplied edit. The copy's allocations and destination writes
are outside the source's private objects. -/
theorem copy_source_rebuffer_of_resources
    {h after : Heap} {source dest : ZStreamRef} {zs : Nat}
    {z oldDest : ZStream} {s : InflateState}
    (before : DefaultOriginState h source zs z s)
    (current : DefaultOriginState after source zs z s)
    (get : dest.get h = some oldDest) (frame : Frame h after (StreamRoot dest)) :
    Rebuffer h after source := by
  refine ⟨current.good.fresh, current.good.uniq, current.globals, ?_,
    z, z, before.good.live.hz, current.good.live.hz, ?_⟩
  · apply inflate_frame_mono frame
    intro b root owned
    exact stream_root_not_inflate_owned before.good get root
      ((before.good.streamOwned_iff b).mp owned)
  · rfl

/-- Any actual Copy result, including both allocation failures, permits
continued calls on the source in the existing initialized history relation.
The actual heap satisfies the existing legal environment relation; no new
history constructor, invariant assumption or successful result is needed. -/
theorem DefaultOriginHistory.copy_source_of_run
    {h after : Heap} {source dest : ZStreamRef} {oldDest : ZStream} {rc : Int32}
    (history : DefaultOriginHistory h source) (different : source ≠ dest)
    (get : dest.get h = some oldDest)
    (actual : C.run (inflateCopy (some dest) (some source)) h = .ok (rc, after)) :
    DefaultOriginHistory after source := by
  obtain ⟨⟨zs, z, s, before, allocator⟩, _⟩ := history.sound
  obtain ⟨code, computed, run, result, _⟩ :=
    CopyResource.inflateCopy_default_origin_total before allocator get different
  have same := Except.ok.inj (run.symm.trans actual)
  cases same
  have current := inflateCopy_source_origin_of_run before allocator get different actual
  have edit := copy_source_rebuffer_of_resources before current get result.2.2.1
  exact .rebuffer history edit current.platform

/-- The total next Copy call supplies actual resources and source history
for every return. Successful calls additionally establish destination history.
All state premises are derived from the actual initialized source history. -/
theorem DefaultOriginHistory.copy_total_contract
    {h : Heap} {source dest : ZStreamRef} {oldDest : ZStream}
    (history : DefaultOriginHistory h source) (different : source ≠ dest)
    (get : dest.get h = some oldDest) :
    ∃ zs z s rc after, DefaultOriginState h source zs z s ∧ DefAlloc z ∧
      C.run (inflateCopy (some dest) (some source)) h = .ok (rc, after) ∧
      DefaultOriginState after source zs z s ∧ DefAlloc z ∧
      DefaultOriginHistory after source ∧ StreamInvariant .inflate after source ∧
      CopyResource.CopyResult h after source dest zs z oldDest s rc ∧
      (rc = Z_OK → DefaultOriginHistory after dest) ∧
      (rc = Z_OK → ∃ copied,
        DefaultOriginState after dest h.nextBlk {z with state := some (.inflate h.nextBlk)} copied ∧
        DefaultOriginState after source zs z s) := by
  obtain ⟨⟨zs, z, s, before, allocator⟩, _⟩ := history.sound
  obtain ⟨rc, after, run, result, origins⟩ :=
    CopyResource.inflateCopy_default_origin_total before allocator get different
  have current := inflateCopy_source_origin_of_run before allocator get different run
  have next := history.copy_source_of_run different get run
  refine ⟨zs, z, s, rc, after, before, allocator, run, current, allocator,
    next, ⟨zs, z, s, current.good, allocator⟩, result, ?_, origins⟩
  intro success
  exact .copy history different get (by simpa only [success] using run)

#print axioms stream_root_not_inflate_owned
#print axioms copy_source_rebuffer_of_resources
#print axioms DefaultOriginHistory.copy_source_of_run
#print axioms DefaultOriginHistory.copy_total_contract
end Zlib.Inflate.Proofs
