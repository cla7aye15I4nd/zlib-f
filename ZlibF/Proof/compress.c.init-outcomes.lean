import ZlibF.Proof.«compress.c.wrapper-safety»

/-! # Every default initializer outcome retains the automatic stream -/
namespace ZlibF.Spec.Public.Proofs.CompressTail
open C Zlib.Compress Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open Zlib.Deflate.Engine.Proofs Zlib.Deflate.Proofs.DefaultInit
open ZlibF.Spec.Public.Proofs.CompressCaller
set_option autoImplicit false
set_option maxRecDepth 100000

/-- Actual MEM_ERROR initialization preserves every object-presence entry.
This strengthens the existing failure ledger just enough for real automatic
stream cleanup. It does not assert structural equality of backing tables. -/
theorem memory_failure_shape {h after : Heap} {r : ZStreamRef} {z : ZStream} {version : BPtr}
    (fresh : Fresh h) (unique : Uniq h) (globals : LibraryGlobals h)
    (get : r.get h = some z) (allocators : DefaultOrNull z) (valid : VersionValue h version (some 49))
    (actual : C.run (deflateInit_ (some r) Z_DEFAULT_COMPRESSION version 112) h = .ok (Z_MEM_ERROR, after)) :
    Shape h after := by
  let zp := ZlibF.Spec.Public.preparedStream z
  let hp := r.put h zp
  have shape := shape_put get zp
  have freshP : Fresh hp := shape.fresh (by simp [hp]) fresh
  have uniqueP : Uniq hp := shape.uniq unique
  have getP : r.get hp = some zp := ZStreamRef.get_put_same get _
  have allocP : DefAlloc zp := prepared_allocators allocators
  have entry : deflateInit_ (some r) Z_DEFAULT_COMPRESSION version 112 h = allocate (some r) 6 hp := by
    simpa only [show levelValue Z_DEFAULT_COMPRESSION = (6 : Int32) from rfl,
      show ((6 : Int32) < 0 || (6 : Int32) > 9) = false from rfl, Bool.false_eq_true, ite_false] using
      entry_run get valid Z_DEFAULT_COMPRESSION
  change deflateInit_ (some r) Z_DEFAULT_COMPRESSION version 112 h = _ at actual
  rw [entry] at actual
  by_cases first : h.allocOk h.nalloc = false
  · have fail := allocate_state_fail getP allocP.1 (by simpa [hp] using first) 6
    have heaps : after = { hp with nalloc := hp.nalloc + 1 } :=
      (Prod.mk.inj (Except.ok.inj (actual.symm.trans fail))).2
    rw [heaps]
    exact shape
  · have firstT : h.allocOk h.nalloc = true := by cases e : h.allocOk h.nalloc <;> simp_all
    by_cases all : (List.range 5).all (fun j => h.allocOk (h.nalloc + j)) = true
    · have allok : ∀ j, j < 5 → hp.allocOk (hp.nalloc + j) = true := by
        simpa only [List.all_eq_true, List.mem_range, hp, ZStreamRef.put_allocOk, ZStreamRef.put_nalloc] using all
      obtain ⟨a, b, c, q, success, _good, _live⟩ :=
        ZlibF.Spec.Public.Proofs.DeflateInit.allocate_success freshP uniqueP getP allocP
          (by simpa [hp] using ZlibF.Spec.Public.Proofs.DeflateInit.globals_trees globals)
          allok 6 (by decide) (by decide)
      have impossible : Z_MEM_ERROR = Z_OK := (Prod.mk.inj (Except.ok.inj (actual.symm.trans success))).1
      cases impossible
    · let ph := publishedHeap hp r zp
      have failed : ((bufferPointers ph).1 == .null || (bufferPointers ph).2.1 == .null ||
          (bufferPointers ph).2.2.1 == .null || (bufferPointers ph).2.2.2 == .null) = true := by
        apply Classical.byContradiction
        intro notFailed
        have noFailure : ((bufferPointers ph).1 == .null || (bufferPointers ph).2.1 == .null ||
            (bufferPointers ph).2.2.1 == .null || (bufferPointers ph).2.2.2 == .null) = false := by
          cases e : ((bufferPointers ph).1 == .null || (bufferPointers ph).2.1 == .null ||
            (bufferPointers ph).2.2.1 == .null || (bufferPointers ph).2.2.2 == .null) <;> simp_all
        obtain ⟨a, b, c, d⟩ := (buffers_failed_iff ph).mp noFailure
        apply all
        rw [List.all_eq_true]
        intro j member
        have small := List.mem_range.mp member
        have index : ph.nalloc = h.nalloc + 1 := by simp [ph, publishedHeap, stateHeap, hp]
        have oracle : ph.allocOk = h.allocOk := by simp [ph, publishedHeap, stateHeap, hp]
        rw [oracle, index] at a b c d
        have cases5 : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by omega
        rcases cases5 with e | e | e | e | e <;> subst j <;>
          simpa only [Nat.add_assoc, Nat.add_zero] using (by assumption)
      obtain ⟨m, failure⟩ := finish_failure getP allocP 6 failed
      have canonical : allocate (some r) 6 hp = .ok (Z_MEM_ERROR, failureHeap hp r zp m) := by
        rw [allocate_to_finish freshP getP allocP.1 (by simpa [hp] using firstT)]
        exact failure
      have heaps : after = failureHeap hp r zp m :=
        (Prod.mk.inj (Except.ok.inj (actual.symm.trans canonical))).2
      rw [heaps]
      exact shape.trans (failure_shape getP freshP m)


/-- On actual default initialization failure, each old byte allocation
outside the stream root retains exactly its previous contents. -/
theorem memory_failure_bytes {h after : Heap} {r : ZStreamRef} {z : ZStream} {version : BPtr}
    (fresh : Fresh h) (unique : Uniq h) (globals : LibraryGlobals h)
    (get : r.get h = some z) (allocators : DefaultOrNull z) (valid : VersionValue h version (some 49))
    (actual : C.run (deflateInit_ (some r) Z_DEFAULT_COMPRESSION version 112) h = .ok (Z_MEM_ERROR, after))
    (b : Nat) (live : h.live b) (outside : ¬StreamRoot r b) : after.bytes b = h.bytes b := by
  obtain ⟨rc, computed, run, post⟩ :=
    (ZlibF.Spec.Public.Proofs.DeflateInit.deflateInit_proof Z_DEFAULT_COMPRESSION).2.2
      h r z version fresh unique globals get allocators valid
  have events := Prod.mk.inj (Except.ok.inj (run.symm.trans actual))
  rw [events.1, events.2] at post
  change (if h.allocOk h.nalloc = false then
      Z_MEM_ERROR = Z_MEM_ERROR ∧ after.nalloc = h.nalloc + 1 ∧ SameObjects (r.put h (ZlibF.Spec.Public.preparedStream z)) after
    else after.nalloc = h.nalloc + 5 ∧
      if (List.range 5).all (fun j => h.allocOk (h.nalloc + j)) then
        Z_MEM_ERROR = Z_OK ∧ DeflateInitial h after r (ZlibF.Spec.Public.Proofs.DeflateInit.settings 6)
      else Z_MEM_ERROR = Z_MEM_ERROR ∧ (∃ z', r.get after = some z' ∧ z'.state = none) ∧
        LiveChange h after (fun _ => False) (fun _ => False) ∧ Frame h after (StreamRoot r)) at post
  by_cases first : h.allocOk h.nalloc = false
  · simp only [first, ite_true] at post
    have unchanged : (r.put h (ZlibF.Spec.Public.preparedStream z)).bytes = h.bytes := by
      cases r <;> simp only [ZStreamRef.put] <;> split <;> rfl
    exact (congrArg (fun t => t b) post.2.2.1).trans (congrArg (fun t => t b) unchanged)
  · simp only [first, ite_false] at post
    by_cases all : (List.range 5).all (fun j => h.allocOk (h.nalloc + j)) = true
    · simp only [all, ite_true] at post
      cases post.2.1
    · simp only [all, Bool.false_eq_true, ite_false] at post
      have frame : Frame h after (StreamRoot r) := post.2.2.2.2
      exact (frame.2.2.2.2.2 b live outside).1

private theorem local_live (h : Heap) (b : Nat) :
    (localHeap h).live b ↔ h.live b ∨ b = h.nextBlk := by
  by_cases same : b = h.nextBlk
  · subst b
    simp [localHeap, Heap.live]
  · simp only [localHeap, Heap.live, upd_ne _ _ _ _ same]
    simp only [same, or_false]

/-- Every actual MEM_ERROR initializer outcome reaches the real early
free branch of compress2_z. Stored length is exactly zero and all original
live objects and the physical empty output range are retained. -/
theorem memory_failure_wrapper {h initialized : Heap} {dest source : BPtr} {ob oo : Nat}
    {capacity sourceLen : UInt64} {xs : List UInt8}
    (fresh : Fresh h) (unique : Uniq h) (globals : LibraryGlobals h)
    (bytes : Bytes h source sourceLen.toNat xs) (writable : Writable h dest capacity.toNat)
    (pointer : dest = .ref (.blk ob) oo)
    (actualInit : C.run (deflateInit_ (some (.tab h.nextBlk)) Z_DEFAULT_COMPRESSION
      (.ref (.str 57) 0) 112) (localHeap h) = .ok (Z_MEM_ERROR, initialized)) :
    ∃ after,
      C.run (compress2_z dest (some capacity) source sourceLen Z_DEFAULT_COMPRESSION) h =
        .ok ((Z_MEM_ERROR, some 0), after) ∧
      Bytes after dest 0 [] ∧ (∀ b, after.live b ↔ h.live b) ∧ after.streams h.nextBlk = none := by
  obtain ⟨f, u, g, v, old, oldGet, alloc, _null⟩ := automatic_stream_domain h fresh unique globals
  have shape := memory_failure_shape f u g oldGet alloc v actualInit
  have uniqueA := shape.uniq u
  have someStream : ∃ z, initialized.streams h.nextBlk = some z := by
    have present := (shape h.nextBlk).2.2.1
    change (initialized.streams h.nextBlk).isSome = ((localHeap h).streams h.nextBlk).isSome at present
    simp only [localHeap, upd_same, Option.isSome_some] at present
    cases eq : initialized.streams h.nextBlk with
    | none => simp only [eq, Option.isSome_none, Bool.false_eq_true] at present
    | some z => exact ⟨z, rfl⟩
  obtain ⟨z, get⟩ := someStream
  let after := releaseLocal initialized h.nextBlk
  have actualFree : freeZStream (some (.tab h.nextBlk)) initialized = .ok ((), after) := by
    simp [freeZStream, get, after, releaseLocal]
  have nonnull : dest ≠ .null := by rw [pointer]; intro e; cases e
  have guard : ((sourceLen > 0 && source == .null) || (capacity > 0 && dest == .null)) = false := by
    apply Bool.eq_false_iff.mpr
    intro bad
    have cases : (sourceLen > 0 ∧ source = .null) ∨ (capacity > 0 ∧ dest = .null) := by
      simpa only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] using bad
    rcases cases with ⟨positive, null⟩ | ⟨_, null⟩
    · rw [null] at bytes
      rcases bytes with ⟨_, zero, _⟩ | ⟨_, _, _, impossible, _⟩
      · have gt := UInt64.lt_iff_toNat_lt.mp positive
        change 0 < sourceLen.toNat at gt
        omega
      · cases impossible
    · exact nonnull null
  have automatic : preInit h = .ok ((some (.tab h.nextBlk), .ref (.str 57) 0), localHeap h) := automatic_stream_run h fresh
  have whole : C.run (compress2_z dest (some capacity) source sourceLen Z_DEFAULT_COMPRESSION) h =
      .ok ((Z_MEM_ERROR, some 0), after) := by
    rw [compress2_z_stages]
    change deflateInit_ (some (.tab h.nextBlk)) Z_DEFAULT_COMPRESSION (.ref (.str 57) 0) 112 (localHeap h) = _ at actualInit
    simp only [C.run, sizeof_z_stream, guard, Bool.false_eq_true, ite_false, bind_app, automatic, actualInit,
      show (Z_MEM_ERROR != Z_OK) = true from rfl, ite_true, actualFree, pure_app]
  have output : Bytes after dest 0 [] := by
    rw [pointer] at writable ⊢
    rcases writable with ⟨impossible, _⟩ | ⟨ref, off, a, equal, getOriginal, _ro, bound⟩
    · cases impossible
    · obtain ⟨rfl, rfl⟩ := Ptr.ref.inj equal
      change h.bytes ob = some a at getOriginal
      have live : h.live ob := Or.inl (by change h.bytes ob ≠ none; rw [getOriginal]; intro e; cases e)
      have different : ob ≠ h.nextBlk := by intro eq; subst ob; exact fresh _ (Nat.le_refl _) live
      have oldLive : (localHeap h).live ob := (local_live h ob).mpr (Or.inl live)
      have oldBytes := memory_failure_bytes f u g oldGet alloc v actualInit ob oldLive different
      have kept : after.bytes ob = some a := oldBytes.trans getOriginal
      exact Or.inr ⟨.blk ob, oo, a, rfl, kept, by omega, by simp⟩
  refine ⟨after, whole, output, ?_, by simp [after, releaseLocal]⟩
  intro b
  change (releaseLocal initialized h.nextBlk).live b ↔ h.live b
  rw [release_local_live uniqueA get, shape.live, local_live]
  constructor
  · intro live
    exact live.1.resolve_right live.2
  · intro live
    exact ⟨Or.inl live, fun eq => fresh _ (by omega) (eq ▸ live)⟩


/-- All allocation-oracle outcomes of the actual default initializer:
parameter checks cannot fail at the fixed default configuration. -/
theorem default_initialization_total {h : Heap} {r : ZStreamRef} {z : ZStream} {version : BPtr}
    (fresh : Fresh h) (unique : Uniq h) (globals : LibraryGlobals h)
    (get : r.get h = some z) (allocators : DefaultOrNull z) (valid : VersionValue h version (some 49)) :
    ∃ rc after, C.run (deflateInit_ (some r) Z_DEFAULT_COMPRESSION version 112) h = .ok (rc, after) ∧
      (rc = Z_OK ∨ rc = Z_MEM_ERROR) := by
  obtain ⟨rc, after, actual, post⟩ :=
    (ZlibF.Spec.Public.Proofs.DeflateInit.deflateInit_proof Z_DEFAULT_COMPRESSION).2.2
      h r z version fresh unique globals get allocators valid
  refine ⟨rc, after, actual, ?_⟩
  change (if h.allocOk h.nalloc = false then
      rc = Z_MEM_ERROR ∧ after.nalloc = h.nalloc + 1 ∧ SameObjects (r.put h (ZlibF.Spec.Public.preparedStream z)) after
    else after.nalloc = h.nalloc + 5 ∧
      if (List.range 5).all (fun j => h.allocOk (h.nalloc + j)) then
        rc = Z_OK ∧ DeflateInitial h after r (ZlibF.Spec.Public.Proofs.DeflateInit.settings 6)
      else rc = Z_MEM_ERROR ∧ (∃ z', r.get after = some z' ∧ z'.state = none) ∧
        LiveChange h after (fun _ => False) (fun _ => False) ∧ Frame h after (StreamRoot r)) at post
  by_cases first : h.allocOk h.nalloc = false
  · simp only [first, ite_true] at post
    exact Or.inr post.1
  · simp only [first, ite_false] at post
    by_cases all : (List.range 5).all (fun j => h.allocOk (h.nalloc + j)) = true
    · simp only [all, ite_true] at post
      exact Or.inl post.2.1
    · simp only [all, Bool.false_eq_true, ite_false] at post
      exact Or.inr post.2.1

/-- The actual default compressor terminates for every allocation oracle
and every capacity in this explicit internal domain. It returns exactly
the physical output length and restores the original live-object ledger.
Any OK result independently encodes the entire original source.

No initializer-success event, initialized invariant or callee contract is
assumed. Uniq, nonnull raw output and per-byte-object size below 2^63 are
internal restrictions; the full Fresh-only/generic-buffer public target and
compressBound sufficiency remain unchanged and open. -/
theorem default_wrapper_total {h : Heap} {dest source : BPtr} {ob oo : Nat}
    {capacity sourceLen : UInt64} {xs : List UInt8}
    (fresh : Fresh h) (unique : Uniq h) (globals : LibraryGlobals h)
    (objects : ZlibF.PlatformMemory.ByteObjectsFit h)
    (bytes : Bytes h source sourceLen.toNat xs) (writable : Writable h dest capacity.toNat)
    (separate : Separate source sourceLen.toNat dest capacity.toNat)
    (pointer : dest = .ref (.blk ob) oo) :
    ∃ rc output after,
      C.run (compress2_z dest (some capacity) source sourceLen Z_DEFAULT_COMPRESSION) h =
        .ok ((rc, some (UInt64.ofNat output.length)), after) ∧
      (UInt64.ofNat output.length).toNat = output.length ∧ output.length ≤ capacity.toNat ∧
      Bytes after dest output.length output ∧ (rc = Z_OK → ZlibF.Spec.Zlib.Valid xs output) ∧
      (∀ b, after.live b ↔ h.live b) ∧ after.streams h.nextBlk = none := by
  obtain ⟨f, u, g, v, old, get, alloc, _null⟩ := automatic_stream_domain h fresh unique globals
  obtain ⟨rc, initialized, actualInit, allowed⟩ := default_initialization_total f u g get alloc v
  rcases allowed with ok | memory
  · subst rc
    obtain ⟨rc, output, after, actual, length, fits, physical, valid, live, dead, _count, _next⟩ :=
      successful_wrapper fresh unique globals objects bytes writable separate pointer actualInit
    exact ⟨rc, output, after, actual, length, fits, physical, valid, live, dead⟩
  · subst rc
    obtain ⟨after, actual, physical, live, dead⟩ :=
      memory_failure_wrapper fresh unique globals bytes writable pointer actualInit
    exact ⟨Z_MEM_ERROR, [], after, actual, rfl, Nat.zero_le _, physical,
      fun bad => False.elim ((by decide : Z_MEM_ERROR ≠ Z_OK) bad), live, dead⟩


/-- The real LP64 compatibility wrapper writes back the exact z-size
result. This equation preserves the original dereference/call/store order. -/
theorem compatibility_run_of_z {h after : Heap} {dest source : BPtr}
    {capacity sourceLen written : UInt64} {level rc : Int32}
    (actual : C.run (compress2_z dest (some capacity) source sourceLen level) h =
      .ok ((rc, some written), after)) :
    C.run (compress2 dest (some capacity) source sourceLen level) h = .ok ((rc, written), after) := by
  change compress2_z dest (some capacity) source sourceLen level h = _ at actual
  simp only [C.run, compress2, bind_app, actual, Option.getD_some, pure_app]

/-- All four real utility entries share the same verified default run,
physical output and exact returned length. This is the same explicitly
restricted internal domain as default_wrapper_total, with every allocator
outcome included and without a compression-bound sufficiency claim. -/
theorem default_wrapper_family_total {h : Heap} {dest source : BPtr} {ob oo : Nat}
    {capacity sourceLen : UInt64} {xs : List UInt8}
    (fresh : Fresh h) (unique : Uniq h) (globals : LibraryGlobals h)
    (objects : ZlibF.PlatformMemory.ByteObjectsFit h)
    (bytes : Bytes h source sourceLen.toNat xs) (writable : Writable h dest capacity.toNat)
    (separate : Separate source sourceLen.toNat dest capacity.toNat)
    (pointer : dest = .ref (.blk ob) oo) :
    ∃ rc output after,
      C.run (compress2_z dest (some capacity) source sourceLen Z_DEFAULT_COMPRESSION) h =
        .ok ((rc, some (UInt64.ofNat output.length)), after) ∧
      C.run (compress_z dest (some capacity) source sourceLen) h =
        .ok ((rc, some (UInt64.ofNat output.length)), after) ∧
      C.run (compress2 dest (some capacity) source sourceLen Z_DEFAULT_COMPRESSION) h =
        .ok ((rc, UInt64.ofNat output.length), after) ∧
      C.run (compress dest (some capacity) source sourceLen) h =
        .ok ((rc, UInt64.ofNat output.length), after) ∧
      (UInt64.ofNat output.length).toNat = output.length ∧ output.length ≤ capacity.toNat ∧
      Bytes after dest output.length output ∧ (rc = Z_OK → ZlibF.Spec.Zlib.Valid xs output) ∧
      (∀ b, after.live b ↔ h.live b) ∧ after.streams h.nextBlk = none := by
  obtain ⟨rc, output, after, actual, length, fits, physical, valid, live, dead⟩ :=
    default_wrapper_total fresh unique globals objects bytes writable separate pointer
  have compat := compatibility_run_of_z actual
  exact ⟨rc, output, after, actual, actual, compat, compat, length, fits, physical, valid, live, dead⟩

end ZlibF.Spec.Public.Proofs.CompressTail
