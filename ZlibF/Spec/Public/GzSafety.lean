import ZlibF.Proof.«gz.inv-model»

/-!
# gz file interface, safety: the history of a handle and the sequence goal

The definitions of sections 3 and 4 of the gz safety skeleton (`gz.skeleton-model.lean` on the branch
`skeleton/gz`), stated over the representation invariant `GzInv` and the call shape `GzCallSafe` of
`gz.inv-model`, and over `GzOperation`, `GzArguments` and `GzCallerFrame` of `GzState`.

1. `GzWorldStep`, `GzHistory`: every actual history of one handle, with an OS-world step between calls. A world
   step may change any descriptor, the handle's own included.
2. `GzCloseCall`, `CloseRefuses`, `GzReleased`, `GzCloseSafe`: safety of a close call.
3. `GzOpenSafe`, `GzDopenSafe`: safety of an open.
4. `Goal.gz_sequence_safety`: safety of every gz file history, and the string `gzerror` returns.
5. `Goal.gz_sequence_nonvacuity`: its premises hold on concrete reading and writing histories.

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

/-- An OS-world step between calls: any well-formed file-system state. Another party (the application, another
handle on the same descriptor) may close the handle's descriptor `fd` or open another file under its number: the
next read or write of the handle then gets an error (`EBADF`) or reaches the other file, as in C. It subsumes
`GzReachable.append`; with the oracle fields in `Fs` it also replaces the oracle arbitrarily. `fs` and `fd` say
from which world and for which handle the step is taken; they constrain nothing. -/
def GzWorldStep (_fs fs' : Fs) (_fd : Int32) : Prop :=
  FileSystem fs'

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
error (no premise); with `ReadsFinite` (a read budget below `2^61` bytes, only for the reading calls of `NeedsReadBound`) the result is `.ok`. `NeedsReadBound` goes by call name:
`gzread`, `gzfread`, `gzgetc`, `gzgetc_`, `gzgets` and `gzungetc`. For these the termination claim needs `ReadsFinite`, also
where the C returns at once (a call on a writer, a request of length 0); every other call terminates in every world. The
first half is partial correctness up to `2^64` iterations of each loop, which no real execution reaches. A call
that returns keeps the open descriptors, keeps
`GzInv`, writes only the handle's blocks and the declared caller regions, and changes the live blocks exactly
by the handle's ledger. The pointer `gzerror` returns is a readable NUL-terminated string in the heap after the
call: a literal or the handle's message. Every close returns and either refuses on the wrong mode or frees every owned block and
releases the descriptor. Every open returns; a failed open leaves no block and no open descriptor behind. -/
def Goal.gz_sequence_safety : Prop :=
  (∀ h fs i, GzHistory h fs i → FileSystem fs ∧ ∃ s, GzInv h i s) ∧
  (∀ h fs i s call, GzHistory h fs i → h.gzstates i = some s → GzOperation i call → GzArguments h i s call →
    (∀ e, call.execute fs h = .error e → e = .outOfFuel) ∧
    ((NeedsReadBound call → ReadsFinite fs s.fd) →
      ∃ value fs' after, call.execute fs h = .ok ((value, fs'), after)) ∧
    (∀ value fs' after, call.execute fs h = .ok ((value, fs'), after) →
      FdsKept fs fs' ∧ GzStepPost h i s call fs' after)) ∧
  (∀ h fs i s errnum, GzHistory h fs i → h.gzstates i = some s →
    GzArguments h i s (.gzerror (some (.in_gzstate_x i)) errnum) →
    ∀ (value : BPtr) fs' after,
      (Call.gzerror (some (.in_gzstate_x i)) errnum).execute fs h = .ok ((value, fs'), after) →
      ∃ t, CString after value t) ∧
  (∀ h fs i s call, GzHistory h fs i → h.gzstates i = some s → GzCloseCall i call →
    ∃ value fs' after, call.execute fs h = .ok ((value, fs'), after) ∧
      ((CloseRefuses s call ∧ after = h ∧ fs' = fs) ∨ (¬ CloseRefuses s call ∧ GzReleased h after fs fs' i s))) ∧
  GzOpenSafe Zlib.Gzlib.gzopen ∧ GzOpenSafe Zlib.Gzlib.gzopen64 ∧ GzDopenSafe

/-- **Goal: the premises of `gz_sequence_safety` are satisfiable** (non-vacuity). Two concrete histories, one per
entry point and mode, each from a caller heap and a world that satisfy every premise of the opening constructor of
`GzHistory`, with no allocation failure:

1. `gzopen` gives a reading handle in `GzInv` whose descriptor has a finite read budget (`ReadsFinite`, the premise
   of the termination half), and a one-byte `gzread` into a caller buffer satisfies `GzArguments`;
2. `gzdopen` on an open descriptor gives a writing handle in `GzInv` that keeps the descriptor, and a one-byte
   `gzwrite` from a caller buffer satisfies `GzArguments`.

So the call clause of `gz_sequence_safety`, and its termination half for a reading call, apply to a real call with a
nonzero length. -/
def Goal.gz_sequence_nonvacuity : Prop :=
  (∃ (h : Heap) (fs : Fs) (path mode : BPtr) (name flags : List UInt8) (after : Heap) (fs' : Fs) (i : Nat)
      (s : GzState) (buf : BPtr),
    Fresh h ∧ Zlib.Gzlib.Spec.Uniq h ∧ LibraryGlobals h ∧ ZlibF.PlatformMemory.ByteObjectsFit h ∧
    NoAllocationFailure h ∧ FileSystem fs ∧ CString h path name ∧ CString h mode flags ∧
    Zlib.Gzlib.gzopen path mode fs h = .ok ((some (.in_gzstate_x i), fs'), after) ∧
    GzHistory after fs' i ∧ after.gzstates i = some s ∧ s.mode = GZ_READ ∧ GzInv after i s ∧
    ReadsFinite fs' s.fd ∧
    GzOperation i (.gzread (some (.in_gzstate_x i)) buf 1) ∧
    NeedsReadBound (.gzread (some (.in_gzstate_x i)) buf 1) ∧
    GzArguments after i s (.gzread (some (.in_gzstate_x i)) buf 1)) ∧
  (∃ (h : Heap) (fs : Fs) (fd : Int32) (mode : BPtr) (flags : List UInt8) (after : Heap) (fs' : Fs) (i : Nat)
      (s : GzState) (buf : BPtr),
    Fresh h ∧ Zlib.Gzlib.Spec.Uniq h ∧ LibraryGlobals h ∧ ZlibF.PlatformMemory.ByteObjectsFit h ∧
    NoAllocationFailure h ∧ FileSystem fs ∧ 0 ≤ fd.toInt ∧ GzOracle.FdOpen fs fd.toInt.toNat ∧
    CString h mode flags ∧
    Zlib.Gzlib.gzdopen fd mode fs h = .ok ((some (.in_gzstate_x i), fs'), after) ∧
    GzHistory after fs' i ∧ after.gzstates i = some s ∧ s.mode = GZ_WRITE ∧ s.fd = fd ∧ GzInv after i s ∧
    GzOperation i (.gzwrite (some (.in_gzstate_x i)) buf 1) ∧
    GzArguments after i s (.gzwrite (some (.in_gzstate_x i)) buf 1))

end ZlibF.Spec.Public
