import ZlibF.Proof.«gz.inv-model»

/-!
# gz file interface, safety: the history of a handle and the sequence goal

The definitions of sections 3 and 4 of the gz safety skeleton (`gz.skeleton-model.lean` on the branch
`skeleton/gz`), stated over the representation invariant `GzInv` and the call shape `GzCallSafe` of
`gz.inv-model`, and over `GzOperation`, `GzArguments` and `GzCallerFrame` of `GzState`.

1. `GzWorldStep`, `GzHistory`: every actual history of one handle, with an OS-world step between calls.
2. `GzCloseCall`, `CloseRefuses`, `GzReleased`, `GzCloseSafe`: safety of a close call.
3. `GzOpenSafe`, `GzDopenSafe`: safety of an open.
4. `Goal.gz_sequence_safety`: safety of every gz file history.

The goal is the skeleton's statement with the `GzInv` and `GzArguments` of this branch: `GzInv` with the corrected
clauses listed in `gz.inv-model` (`GzCommon.next` only with buffered output, `copyDirect` allows `direct = 0`, and
the added clauses `haveSkip` and `againEof`), and the `gzprintf` arguments that the handle does not own
(`GzArguments`).

Patches. The statements are for the patched source (`patches/`: 0002, 0003, 0004 for F-1 and W7, and 0005).
-/

namespace ZlibF.Spec.Public
open C Zlib.GzFs
set_option autoImplicit false

/-! ## 1. The history -/

/-- An OS-world step between calls: any well-formed file-system state, except that the handle's descriptor
stays open or stays closed (only the library closes it). It subsumes `GzReachable.append`; with the oracle fields
in `Fs` it also replaces the oracle arbitrarily. -/
def GzWorldStep (fs fs' : Fs) (fd : Int32) : Prop :=
  FileSystem fs' ∧ (0 ≤ fd.toInt → (GzOracle.FdOpen fs' fd.toInt.toNat ↔ GzOracle.FdOpen fs fd.toInt.toNat))

/-- **Every actual history of one handle** (safety; replaces `GzReachable`, with `ByteObjectsFit` at every point
where the caller supplies a heap). The caller may free its own buffers (`caller`), including the last `gzread`
buffer (R-4: `GzCommon.next` says nothing of `x.next` without buffered output). -/
inductive GzHistory : Heap → Fs → Nat → Prop
  | open {h after fs fs' path mode i name flags} :
      Fresh h → Zlib.Gzlib.Spec.Uniq h → LibraryGlobals h → ZlibF.PlatformMemory.ByteObjectsFit h →
      FileSystem fs → CString h path name → CString h mode flags →
      Zlib.Gzlib.gzopen path mode fs h = .ok ((some (.in_gzstate_x i), fs'), after) →
      GzHistory after fs' i
  | open64 {h after fs fs' path mode i name flags} :
      Fresh h → Zlib.Gzlib.Spec.Uniq h → LibraryGlobals h → ZlibF.PlatformMemory.ByteObjectsFit h →
      FileSystem fs → CString h path name → CString h mode flags →
      Zlib.Gzlib.gzopen64 path mode fs h = .ok ((some (.in_gzstate_x i), fs'), after) →
      GzHistory after fs' i
  | dopen {h after fs fs' fd mode i flags} :
      Fresh h → Zlib.Gzlib.Spec.Uniq h → LibraryGlobals h → ZlibF.PlatformMemory.ByteObjectsFit h →
      FileSystem fs → CString h mode flags →
      Zlib.Gzlib.gzdopen fd mode fs h = .ok ((some (.in_gzstate_x i), fs'), after) →
      GzHistory after fs' i
  | step {h after fs fs' i s call value} : GzHistory h fs i → h.gzstates i = some s →
      GzOperation i call → GzArguments h i s call →
      call.execute fs h = .ok ((value, fs'), after) → GzHistory after fs' i
  | caller {h after fs i s} : GzHistory h fs i → h.gzstates i = some s →
      GzCallerFrame h after i s → ZlibF.PlatformMemory.ByteObjectsFit after → GzHistory after fs i
  | world {h fs fs' i s} : GzHistory h fs i → h.gzstates i = some s → GzWorldStep fs fs' s.fd →
      GzHistory h fs' i

/-! ## 2. Close and open calls, and the goal -/

/-- The close calls of handle `i`. -/
def GzCloseCall (i : Nat) : Call → Prop
  | .gzclose p | .gzclose_r p | .gzclose_w p => p = some (.in_gzstate_x i)
  | _ => False

/-- A close call of the other mode refuses. -/
def CloseRefuses (s : GzState) : Call → Prop
  | .gzclose_r _ => s.mode ≠ GZ_READ
  | .gzclose_w _ => s.mode ≠ GZ_WRITE
  | _ => False

/-- The handle is gone: the record and every owned block freed, nothing else changed, and the descriptor
released also when `close` reports -1 (M4); no other descriptor changes. No return code is claimed
(`CloseContract` stays the functional contract of the regular-file instance). -/
def GzReleased (h after : Heap) (fs fs' : Fs) (i : Nat) (s : GzState) : Prop :=
  after.gzstates i = none ∧ Frame h after (GzOwned h i s) ∧
  LiveChange h after (fun _ => False) (GzOwned h i s) ∧ FileSystem fs' ∧
  (0 ≤ s.fd.toInt → ¬ GzOracle.FdOpen fs' s.fd.toInt.toNat) ∧
  (∀ j, (0 ≤ s.fd.toInt → j ≠ s.fd.toInt.toNat) → (GzOracle.FdOpen fs' j ↔ GzOracle.FdOpen fs j))

/-- **Safety of a close call**: it returns, and either refuses on the wrong mode (nothing changes) or
releases the handle. -/
def GzCloseSafe (i : Nat) (call : Call) : Prop :=
  ∀ h fs s, GzInv h i s → FileSystem fs →
    ∃ value fs' after, call.execute fs h = .ok ((value, fs'), after) ∧
      ((CloseRefuses s call ∧ after = h ∧ fs' = fs) ∨ (¬ CloseRefuses s call ∧ GzReleased h after fs fs' i s))

/-- **Safety of an open** (`gzopen`, `gzopen64`): it returns and frames the heap; NULL leaves no new block and
no new open descriptor; a handle is in `GzInv`, owns exactly the new blocks, and its descriptor is the only
newly opened one. -/
def GzOpenSafe (program : BPtr → BPtr → G GzFilePtr) : Prop :=
  ∀ h fs path mode name flags,
    Fresh h → Zlib.Gzlib.Spec.Uniq h → LibraryGlobals h → ZlibF.PlatformMemory.ByteObjectsFit h →
    FileSystem fs → (path ≠ .null → CString h path name) → (mode ≠ .null → CString h mode flags) →
    ∃ result fs' after, program path mode fs h = .ok ((result, fs'), after) ∧
      Frame h after (fun _ => False) ∧ FileSystem fs' ∧
      (match result with
       | none => LiveChange h after (fun _ => False) (fun _ => False) ∧ FdsKept fs fs'
       | some (.in_gzstate_x i) => ∃ s, GzInv after i s ∧
           LiveChange h after (GzOwned after i s) (fun _ => False) ∧
           0 ≤ s.fd.toInt ∧ ¬ GzOracle.FdOpen fs s.fd.toInt.toNat ∧
           ∀ j, j ≠ s.fd.toInt.toNat → (GzOracle.FdOpen fs' j ↔ GzOracle.FdOpen fs j))

/-- **Safety of `gzdopen`**: as `GzOpenSafe`, but no descriptor is opened or closed (a failure leaves the
caller's descriptor with the caller; a success takes it over, open or not). -/
def GzDopenSafe : Prop :=
  ∀ h fs fd mode flags,
    Fresh h → Zlib.Gzlib.Spec.Uniq h → LibraryGlobals h → ZlibF.PlatformMemory.ByteObjectsFit h →
    FileSystem fs → (mode ≠ .null → CString h mode flags) →
    ∃ result fs' after, Zlib.Gzlib.gzdopen fd mode fs h = .ok ((result, fs'), after) ∧
      Frame h after (fun _ => False) ∧ FileSystem fs' ∧ FdsKept fs fs' ∧
      (match result with
       | none => LiveChange h after (fun _ => False) (fun _ => False)
       | some (.in_gzstate_x i) => ∃ s, GzInv after i s ∧ s.fd = fd ∧
           LiveChange h after (GzOwned after i s) (fun _ => False))

/-- **Goal: safety of every gz file history.** Every history keeps the world well formed and the
handle in `GzInv`; `GzHistory` has no budget premise. For every next public call and every world (every
oracle): the run's result is not a fault, it is `.ok` or the out-of-fuel outcome, never `Fault.ub` or a memory
error (no premise); with `ReadsFinite` (only for the reading calls of `NeedsReadBound`) the result is `.ok`. The
first half is partial correctness up to `2^64` iterations of each loop, which no real execution reaches. A call
that returns keeps the open descriptors, keeps
`GzInv`, writes only the handle's blocks and the declared caller regions, and changes the live blocks exactly
by the handle's ledger. Every close returns and either refuses on the wrong mode or frees every owned block and
releases the descriptor. Every open returns; a failed open leaves no block and no open descriptor behind. -/
def Goal.gz_sequence_safety : Prop :=
  (∀ h fs i, GzHistory h fs i → FileSystem fs ∧ ∃ s, GzInv h i s) ∧
  (∀ h fs i s call, GzHistory h fs i → h.gzstates i = some s → GzOperation i call → GzArguments h i s call →
    (∀ e, call.execute fs h = .error e → e = .outOfFuel) ∧
    ((NeedsReadBound call → ReadsFinite fs s.fd) →
      ∃ value fs' after, call.execute fs h = .ok ((value, fs'), after)) ∧
    (∀ value fs' after, call.execute fs h = .ok ((value, fs'), after) →
      FdsKept fs fs' ∧ GzStepPost h i s call fs' after)) ∧
  (∀ h fs i s call, GzHistory h fs i → h.gzstates i = some s → GzCloseCall i call →
    ∃ value fs' after, call.execute fs h = .ok ((value, fs'), after) ∧
      ((CloseRefuses s call ∧ after = h ∧ fs' = fs) ∨ (¬ CloseRefuses s call ∧ GzReleased h after fs fs' i s))) ∧
  GzOpenSafe Zlib.Gzlib.gzopen ∧ GzOpenSafe Zlib.Gzlib.gzopen64 ∧ GzDopenSafe

end ZlibF.Spec.Public
