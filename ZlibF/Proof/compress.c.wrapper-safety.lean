import ZlibF.Proof.«compress.c.setup-resources»

/-! # The same real compressor execution reaches and completes its tail

The internal default/Uniq/nonnull-raw domain is explicit. In particular
no D-4 NULL subtraction is used to justify nonnull C pointer arithmetic.
-/
namespace ZlibF.Spec.Public.Proofs.CompressTail
open C Zlib.Compress Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open Zlib.Deflate.Engine.Proofs Zlib.Deflate.Proofs.DefaultInit
open ZlibF.Spec.Public.Proofs.CompressLoop ZlibF.Spec.Public.Proofs.CompressCaller
open ZlibF.Spec.Public.Proofs.CompressPrefix
set_option autoImplicit false
set_option maxRecDepth 100000

/-- Exactly the real automatic stream preparation and version query. -/
def preInit : M (ZStreamPtr × BPtr) := do
  let strm ← allocLocalZ
  zwr strm (fun z => { z with zalloc := .null, zfree := .null, «opaque» := .null })
  let version ← Zlib.Zutil.zlibVersion
  pure (strm, version)

private theorem monad_assoc {α β γ : Type} (a : M α) (b : α → M β) (c : β → M γ) :
    ((a >>= b) >>= c) = (a >>= fun x => b x >>= c) := by
  funext h
  simp only [bind_app]
  cases a h <;> rfl

private theorem monad_pure_bind {α β : Type} (a : α) (f : α → M β) :
    ((pure a : M α) >>= f) = f a := rfl

/-- Unconditional extraction of the actual pre-init and tail programs.
All checks, failure cleanup, loop locals and call order remain unchanged. -/
theorem compress2_z_stages (dest : BPtr) (capacity : Option UInt64)
    (source : BPtr) (sourceLen : UInt64) (level : Int32) :
    compress2_z dest capacity source sourceLen level = (do
      let some amount := capacity | return (Z_STREAM_ERROR, none)
      if (sourceLen > 0 && source == .null) || (amount > 0 && dest == .null) then
        return (Z_STREAM_ERROR, capacity)
      let (strm, version) ← preInit
      let err ← deflateInit_ strm level version sizeof_z_stream
      if err != Z_OK then
        freeZStream strm
        return (err, some 0)
      zwr strm (fun z => bindings z dest source)
      let (err, _, _) ← loop strm (err, amount, sourceLen)
      CompressTail.tail strm dest err) := by
  rw [compress2_z_tail_unfold]
  simp only [preInit, monad_assoc, monad_pure_bind, bindings]
  all_goals rfl

private theorem argument_guard_false {h : Heap} {source dest : BPtr} {amount n : UInt64}
    {xs : List UInt8} (bytes : Bytes h source n.toNat xs)
    (nonnull : dest ≠ .null) :
    ((n > 0 && source == .null) || (amount > 0 && dest == .null)) = false := by
  apply Bool.eq_false_iff.mpr
  intro bad
  have cases : (n > 0 ∧ source = .null) ∨ (amount > 0 ∧ dest = .null) := by
    simpa only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] using bad
  rcases cases with ⟨positive, null⟩ | ⟨_, null⟩
  · rw [null] at bytes
    rcases bytes with ⟨_, zero, _⟩ | ⟨_, _, _, impossible, _⟩
    · have gt := UInt64.lt_iff_toNat_lt.mp positive
      change 0 < n.toNat at gt
      omega
    · cases impossible
  · exact nonnull null

/-- Composition refers only to actual primitive/callee execution events.
The pre-init event is established by automatic_stream_run itself. -/
theorem run_of_successful_stages {h initialized ready loopHeap final : Heap}
    {dest source : BPtr} {capacity sourceLen finalLeft finalSourceLen : UInt64}
    {xs : List UInt8} {err rc : Int32} {stored : Option UInt64}
    (fresh : Fresh h) (bytes : Bytes h source sourceLen.toNat xs) (nonnull : dest ≠ .null)
    (actualInit : C.run (deflateInit_ (some (.tab h.nextBlk)) Z_DEFAULT_COMPRESSION
      (.ref (.str 57) 0) 112) (localHeap h) = .ok (Z_OK, initialized))
    (setup : C.run (zwr (some (.tab h.nextBlk)) (fun z => bindings z dest source)) initialized = .ok ((), ready))
    (actualLoop : loop (some (.tab h.nextBlk)) (Z_OK, capacity, sourceLen) ready =
      .ok ((err, finalLeft, finalSourceLen), loopHeap))
    (actualTail : CompressTail.tail (some (.tab h.nextBlk)) dest err loopHeap = .ok ((rc, stored), final)) :
    C.run (compress2_z dest (some capacity) source sourceLen Z_DEFAULT_COMPRESSION) h =
      .ok ((rc, stored), final) := by
  have guard := argument_guard_false (amount := capacity) bytes nonnull
  have automatic : preInit h = .ok ((some (.tab h.nextBlk), .ref (.str 57) 0), localHeap h) := automatic_stream_run h fresh
  change deflateInit_ (some (.tab h.nextBlk)) Z_DEFAULT_COMPRESSION (.ref (.str 57) 0) 112 (localHeap h) = _ at actualInit
  change zwr (some (.tab h.nextBlk)) (fun z => bindings z dest source) initialized = _ at setup
  rw [compress2_z_stages]
  simp only [C.run, sizeof_z_stream, guard, Bool.false_eq_true, ite_false, bind_app, automatic, actualInit,
    show (Z_OK != Z_OK) = false from rfl, setup, actualLoop, actualTail]


private theorem local_heap_live (h : Heap) (b : Nat) :
    (localHeap h).live b ↔ h.live b ∨ b = h.nextBlk := by
  by_cases same : b = h.nextBlk
  · subst b
    simp [localHeap, Heap.live]
  · simp only [localHeap, Heap.live, upd_ne _ _ _ _ same]
    simp only [same, or_false]

private theorem writable_bound {h : Heap} {p : BPtr} {n : Nat}
    (objects : ZlibF.PlatformMemory.ByteObjectsFit h) (writable : Writable h p n) : n < 2 ^ 63 := by
  rcases writable with ⟨_, rfl⟩ | ⟨ref, off, a, _, get, _, bound⟩
  · decide
  · have size := objects ref a get
    change a.size < 2 ^ 63 at size
    omega

/-- After an actual successful default initialization, the whole real
compress2_z execution terminates without fault, returns exactly its physical
output length, and releases all six temporary objects. An OK result is an
independently valid encoding of the entire original source.

This is an internal Uniq/nonnull-raw-output/ByteObjectsFit result. It keeps
the actual successful initializer event explicit; allocator-failure branches,
Fresh-only generic public buffers, and compressBound sufficiency are separate.
The C order of pointer subtraction, length, end and local free is retained. -/
theorem successful_wrapper {h initialized : Heap} {dest source : BPtr} {ob oo : Nat}
    {capacity sourceLen : UInt64} {xs : List UInt8}
    (fresh : Fresh h) (unique : Zlib.Inflate.Spec.Uniq h) (globals : LibraryGlobals h)
    (objects : ZlibF.PlatformMemory.ByteObjectsFit h)
    (bytes : Bytes h source sourceLen.toNat xs) (writable : Writable h dest capacity.toNat)
    (separate : Separate source sourceLen.toNat dest capacity.toNat)
    (pointer : dest = .ref (.blk ob) oo)
    (actualInit : C.run (deflateInit_ (some (.tab h.nextBlk)) Z_DEFAULT_COMPRESSION
      (.ref (.str 57) 0) 112) (localHeap h) = .ok (Z_OK, initialized)) :
    ∃ rc output after,
      C.run (compress2_z dest (some capacity) source sourceLen Z_DEFAULT_COMPRESSION) h =
        .ok ((rc, some (UInt64.ofNat output.length)), after) ∧
      (UInt64.ofNat output.length).toNat = output.length ∧ output.length ≤ capacity.toNat ∧
      Bytes after dest output.length output ∧ (rc = Z_OK → ZlibF.Spec.Zlib.Valid xs output) ∧
      (∀ b, after.live b ↔ h.live b) ∧
      after.streams h.nextBlk = none ∧ after.nalloc = h.nalloc + 5 ∧ after.nextBlk = h.nextBlk + 6 := by
  obtain ⟨ready, last, loopHeap, setup, actualLoop, stopped, _valid⟩ :=
    original_buffers_loop_total fresh unique globals objects bytes writable separate pointer actualInit
  obtain ⟨ready0, first, setup0, history, get, ranges, out, _in, outAvail, inAvail⟩ :=
    successful_default_seed fresh unique globals bytes writable separate actualInit
  have readyEq : ready0 = ready := (Prod.mk.inj (Except.ok.inj (setup0.symm.trans setup))).2
  subst ready0
  obtain ⟨initialZ, initialD, initial, initLive, initOwned, initCount, initNext⟩ :=
    setup_resources (dest := dest) (source := source) fresh unique globals actualInit setup
  have firstEq : initialZ = first := Option.some.inj (initial.good.live.hz.symm.trans get)
  subst initialZ
  have raw := out.trans pointer
  obtain ⟨k, positive, _fuelBound, execution⟩ := loop_go_prefix (slot := h.nextBlk) rfl actualLoop
  obtain ⟨used, log, returned, sound⟩ := actual_prefix_sound history get ranges raw execution
  obtain ⟨endZ, endD, boundary, shape, count, next⟩ :=
    prefix_resources history initial ranges raw execution
  have sameZ : endZ = returned := Option.some.inj (boundary.good.live.hz.symm.trans sound.get)
  subst endZ
  obtain ⟨buffers, _input⟩ := ranges_current (r := .tab h.nextBlk) sound.get sound.remaining
  have cursor : returned.next_out = .ref (.blk ob) (oo + log.output.length) := by
    rw [sound.outputPtr, raw]
    rfl
  have actualBytes : Bytes loopHeap (.ref (.blk ob) oo) log.output.length log.output := by
    rw [← raw]
    exact sound.outputBytes
  have lengthBound : log.output.length ≤ capacity.toNat := by
    have total := sound.outputCount
    rw [outAvail] at total
    simp only [UInt32.toNat_zero, Nat.zero_add] at total
    omega
  have small : log.output.length < 2 ^ 63 := Nat.lt_of_le_of_lt lengthBound (writable_bound objects writable)
  obtain ⟨ds, d, after, good, actualTail, finalBytes, dead, tailLive, _frame, tailCount, tailNext, word⟩ :=
    tail_nonnull_exact sound.history sound.get buffers cursor actualBytes small last.1
  have dsEq : ds = (localHeap h).nextBlk := by
    have a := good.live.zst
    have b := boundary.good.live.zst
    exact StateRef.deflate.inj (Option.some.inj (a.symm.trans b))
  subst ds
  have stateEq : d = endD := Option.some.inj (good.live.hs.symm.trans boundary.good.live.hs)
  subst d
  have own : DeflateOwned (localHeap h).nextBlk endD = DeflateOwned (localHeap h).nextBlk initialD :=
    boundary_owned_config boundary
  let rc := if last.1 == Z_STREAM_END then Z_OK else last.1
  have nonnull : dest ≠ .null := by rw [pointer]; intro e; cases e
  have whole := run_of_successful_stages fresh bytes nonnull actualInit setup actualLoop
    (by rw [pointer]; exact actualTail)
  refine ⟨rc, log.output, after, whole, word, lengthBound, ?_, ?_, ?_, dead, ?_, ?_⟩
  · rw [pointer]
    exact finalBytes
  · intro okay
    have ended : last.1 = Z_STREAM_END := by
      unfold rc at okay
      by_cases eq : last.1 = Z_STREAM_END
      · exact eq
      · have bad : last.1 = Z_OK := by simpa only [beq_iff_eq, eq, ite_false] using okay
        exact False.elim (stopped bad)
    have consumed := sound.ended ended
    have size := caller_bytes_length bytes
    have consumedCount := sound.inputCount
    rw [consumed.1, consumed.2, inAvail] at consumedCount
    simp only [UInt64.toNat_zero, UInt32.toNat_zero, Nat.zero_add] at consumedCount
    have all : used = xs.length := by omega
    have input : log.input = xs := by rw [sound.input, all, List.take_length]
    obtain ⟨_ds, _z, _d, _config, _encoding, valid⟩ := sound.history.encoding
    have correct := valid ((sound.result positive).trans ended)
    rwa [input] at correct
  · intro b
    have initialLedger := initLive b
    have finalLedger := tailLive b
    change ready.live b ↔ ((localHeap h).live b ∧ ¬False) ∨ DeflateOwned (localHeap h).nextBlk initialD b at initialLedger
    change after.live b ↔ (loopHeap.live b ∧ ¬(DeflateOwned (localHeap h).nextBlk endD b ∨ b = h.nextBlk)) ∨ False at finalLedger
    rw [own, shape.live, initialLedger, local_heap_live] at finalLedger
    simp only [not_false_eq_true, and_true, or_false] at finalLedger
    have newKeys := initOwned b
    have oldDead : DeflateOwned (localHeap h).nextBlk initialD b → ¬h.live b := by
      intro owned
      have bound := (newKeys.mp owned).1
      exact fresh b (by change h.nextBlk + 1 ≤ b at bound; omega)
    have localDead : b = h.nextBlk → ¬h.live b := by
      intro same
      subst b
      exact fresh _ (Nat.le_refl _)
    constructor
    · intro live
      rcases finalLedger.mp live with ⟨(old | automaticKey) | created, outside⟩
      · exact old
      · exact False.elim (outside (Or.inr automaticKey))
      · exact False.elim (outside (Or.inl created))
    · intro live
      apply finalLedger.mpr
      exact ⟨Or.inl (Or.inl live), fun bad => bad.elim (fun owned => oldDead owned live) (fun same => localDead same live)⟩
  · omega
  · omega

end ZlibF.Spec.Public.Proofs.CompressTail
