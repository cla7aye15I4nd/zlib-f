import ZlibF.Spec.Public.GzControl
import ZlibF.Spec.PlatformMemory

/-!
# gz file interface, safety skeleton: model, invariant, history and goal (skeleton)

Skeleton branch only (`skeleton/gz`): `sorry` marks an open lemma. Nothing here is a registered goal. On
merge, the definitions of sections 2 to 4 move to `ZlibF/Spec/Public/GzSafety.lean`.

1. The OS-call oracle is on `dev` (fields of `Fs`, `ZlibF/Zlib/gzfs.lean`). Every safety statement below
   quantifies over every `fs : Fs`, hence over every oracle. M7 is the premise `ReadsFinite` (a finite read budget
   of the handle's descriptor). Section 1 also states the partial-correctness loop rules the no-fault half needs.
2. `GzInv` (`GzCommon`, `GzReadInv`, `GzWriteInv`): the representation invariant of an open handle, with batch
   C's W1–W10 folded into the write part.
3. `GzHistory`: every actual history of one handle. It replaces `GzReachable` for safety, carries
   `ByteObjectsFit` (decision 4), and has an OS-world step.
4. `GzCallSafe`, `GzCloseSafe`, `GzOpenSafe`, `GzDopenSafe` and `Goal.gz_sequence_safety`.

Patches. The statements are for the patched source: patch 0002 (R-1, upstream #1361), patch 0003 (R-2, upstream
#1363) and the local patches 0004+ for F-1 (`gzread.c` `x.pos` overflow), W7 (`gzwrite.c` `x.pos` overflow), R-3
(`gz_reset` does not write `x.next`) and R-4 (`x.next` left in the caller's buffer). A lemma that needs one says
"relies on local patch for <finding>" or "relies on patch 0002/0003". Until those patches are on `dev`, those
lemmas are false against the translation of this branch (`gzseek64_cur_negpos_ub` and `gzseek64_dangling_next_ub`
are checked counterexamples).
-/

namespace ZlibF.Spec.Public
open C Zlib.GzFs
set_option autoImplicit false

/-! ## 1. The OS-call oracle, the read budget and partial-correctness loop rules

The OS-call oracle is on `dev` (`ZlibF/Zlib/gzfs.lean`, fields `nos` .. `readBudget` of `Fs`; trusted base,
`docs/trusted-base.md`). Every statement below quantifies over every `fs : Fs`, hence over every oracle. -/

namespace GzOracle

/-- The descriptor number `j` is open. -/
def FdOpen (fs : Fs) (j : Nat) : Prop := ∃ f, fs.fds[j]? = some (some f)

end GzOracle

/-- **M7, the finiteness premise.** The handle's descriptor is non-negative and has a finite read budget, so every
later read is cut to a bound. A premise of the termination half only, and only for the calls of `NeedsReadBound`;
`docs/deviations.md`, "Gz reading termination". -/
def ReadsFinite (fs : Fs) (fd : Int32) : Prop := 0 ≤ fd.toInt ∧ fs.readBudget fd.toInt.toNat ≠ none

/-- **Partial-correctness rule for `gwhile`** (planned, to move to a proof file): an invariant on the loop state,
world and heap that the condition and the body keep on every `.ok` result, and under which they never fault except
by running out of fuel, gives the same for the loop. The existing loop rules assume `.ok` or prove termination;
this one is what the no-fault half of the goal needs. -/
theorem gwhile_partial {σ : Type} (I : σ → Fs → Heap → Prop) (cond : σ → G (Bool × σ)) (body : σ → G σ)
    (hc : ∀ s fs h, I s fs h → (∀ e, cond s fs h = .error e → e = .outOfFuel) ∧
      ∀ c s' fs' h', cond s fs h = .ok (((c, s'), fs'), h') → I s' fs' h')
    (hb : ∀ s fs h, I s fs h → (∀ e, body s fs h = .error e → e = .outOfFuel) ∧
      ∀ s' fs' h', body s fs h = .ok ((s', fs'), h') → I s' fs' h') :
    ∀ s fs h, I s fs h → (∀ e, gwhile cond body s fs h = .error e → e = .outOfFuel) ∧
      ∀ s' fs' h', gwhile cond body s fs h = .ok ((s', fs'), h') → I s' fs' h' := by
  sorry

/-- The same rule for `gdoWhile`. -/
theorem gdoWhile_partial {σ : Type} (I : σ → Fs → Heap → Prop) (body : σ → G σ) (cond : σ → G (Bool × σ))
    (hb : ∀ s fs h, I s fs h → (∀ e, body s fs h = .error e → e = .outOfFuel) ∧
      ∀ s' fs' h', body s fs h = .ok ((s', fs'), h') → I s' fs' h')
    (hc : ∀ s fs h, I s fs h → (∀ e, cond s fs h = .error e → e = .outOfFuel) ∧
      ∀ c s' fs' h', cond s fs h = .ok (((c, s'), fs'), h') → I s' fs' h') :
    ∀ s fs h, I s fs h → (∀ e, gdoWhile body cond s fs h = .error e → e = .outOfFuel) ∧
      ∀ s' fs' h', gdoWhile body cond s fs h = .ok ((s', fs'), h') → I s' fs' h' := by
  sorry

/-- The calls whose termination needs M7: the loops of `gz_fetch` (over empty gzip members), `gz_skip` and
`gz_read` read until the input ends. `gzread`, `gzfread`, `gzgetc`, `gzgetc_`, `gzgets` reach them, `gzungetc`
through `gz_skip`. `gzdirect` (one `gz_look`, whose `gz_load` loop is bounded by the request), the write side
(M2) and `gzseek` (no reading loop: the skip is deferred) do not need it. -/
def NeedsReadBound : Call → Prop
  | .gzread _ _ _ | .gzfread _ _ _ _ | .gzgetc _ | .gzgetc_ _ | .gzgets _ _ _ | .gzungetc _ _ => True
  | _ => False

/-! ## 2. The invariant -/

/-- A pointer to the start of a live writable byte block of exactly `n` bytes (`gz_look` and `gz_init` allocate
exactly these sizes). -/
def ExactBuffer (h : Heap) (p : BPtr) (n : Nat) : Prop :=
  ∃ b a, p = .ref (.blk b) 0 ∧ h.bytes b = some a ∧ h.ro b = false ∧ a.size = n

/-- The block of a pointer into a heap block. -/
def blkOf : BPtr → Option Nat
  | .ref (.blk b) _ => some b
  | _ => none

/-- The pointer advanced by `n` bytes. -/
def padv : BPtr → Nat → BPtr
  | .null, _ => .null
  | .ref r o, n => .ref r (o + n)

/-- The pointer fields the record owns: path, message, and the buffers when they exist (`out` only for a
reader or a compressing writer). -/
def ownedPtrs (s : GzState) : List BPtr :=
  [s.path, s.msg] ++
    (if s.size ≠ 0 then s.«in» :: (if s.mode = GZ_READ ∨ s.direct = 0 then [s.out] else []) else [])

/-- The embedded stream `&state->strm`. -/
def gzStrm (i : Nat) : ZStreamRef := .in_gzstate_strm i

/-- The part of the invariant common to readers and writers. -/
structure GzCommon (h : Heap) (i : Nat) (s : GzState) : Prop where
  record : h.gzstates i = some s
  mode : s.mode = GZ_READ ∨ s.mode = GZ_WRITE
  fresh : Fresh h
  uniq : Zlib.Gzlib.Spec.Uniq h
  globals : LibraryGlobals h
  /-- needed by `StreamReachable .inflate` at each codec step -/
  fit : ZlibF.PlatformMemory.ByteObjectsFit h
  path : ∃ p, CString h s.path p ∧ MallocBuffer h s.path (p.length + 1)
  /-- W9 -/
  msg : s.msg = .null ∨ ∃ m, CString h s.msg m ∧ MallocBuffer h s.msg (m.length + 1)
  memerr : s.err = Z_MEM_ERROR → s.msg = .null
  /-- W1 (`gzbuffer` clamps to 8 and refuses a doubling overflow). The lower bound matters for the write side:
  zlib.h (`deflate`, around line 327) asks that "avail_out is greater than six when the flush marker begins", and
  `gzbuffer` (`gzlib.c`, line 345) raises a smaller size to 8, "needed to behave well with flushing". -/
  want : 8 ≤ s.want.toNat ∧ s.want.toNat < 2 ^ 31
  size : s.size = 0 ∨ s.size = s.want
  /-- the owned pointer blocks are distinct, differ from the record and from the codec's blocks -/
  distinct : ((ownedPtrs s).filterMap blkOf).Nodup ∧
    (∀ p, p ∈ ownedPtrs s → ∀ b, blkOf p = some b → b ≠ i ∧ ¬ StreamOwned h (gzStrm i) b)
  /-- every owned block is live -/
  live : ∀ b, GzOwned h i s b → h.live b
  /-- positions. Relies on local patches for F-1 and W7 (`x.pos + skip` never passes `GZ_OFF_MAX`) and on patch
  0002 (R-1). Lower bound: `x.pos + x.have`, the end of the buffered output, is never negative (`gzungetc` lowers
  `x.pos` and raises `x.have` by one); it implies `-(2·size) ≤ x.pos` (as on dev, `GzInv.pos_lower`). -/
  pos : 0 ≤ s.skip.toInt ∧ s.x.pos.toInt + s.skip.toInt ≤ 9223372036854775807 ∧
    0 ≤ s.x.pos.toInt + s.x.have.toNat
  /-- `x.next` is NULL, or inside an owned buffer other than the message block (which `gz_error` frees), with
  `x.have` bytes after it; as `NextOk` on `dev`. Relies on local patches for R-3 (`gz_reset` writes `x.next`) and
  R-4 (`x.next` is never left in the caller's buffer). -/
  next : s.x.next = .null ∨ ∃ b off a, s.x.next = .ref (.blk b) off ∧ b ≠ i ∧ blkOf s.msg ≠ some b ∧
    GzOwned h i s b ∧ h.bytes b = some a ∧ off + s.x.have.toNat ≤ a.size
  nullHave : s.x.next = .null → s.x.have = 0
  /-- The codec does not own the record block (a write of the record is then a rebuffer of the codec). The codec
  steps establish it with `gz.record-free` (from `DGood` / `Good`). -/
  recordFree : ¬ StreamOwned h (gzStrm i) i

/-- The reader part (`s.mode = GZ_READ`). The note's clause "past ≠ 0 → skip = 0" is not included: a forward
`gzseek` after a short read keeps `past` and sets `skip` (`Api.GzSeek`). -/
structure GzReadInv (h : Heap) (i : Nat) (s : GzState) : Prop where
  how : s.how = LOOK ∨ s.how = GZ_COPY ∨ s.how = GZIP
  copyDirect : s.how = GZ_COPY → s.direct = 1
  gzipDirect : s.how = GZIP → s.direct = 0
  direct : s.direct = -1 ∨ s.direct = 0 ∨ s.direct = 1
  junk : s.junk = -1 ∨ s.junk = 0 ∨ s.junk = 1
  flags : (s.eof = 0 ∨ s.eof = 1) ∧ (s.past = 0 ∨ s.past = 1) ∧ (s.again = 0 ∨ s.again = 1)
  unalloc : s.size = 0 → s.x.have = 0 ∧ s.strm.avail_in = 0 ∧ s.how = LOOK ∧ s.strm.state = none
  bufs : s.size ≠ 0 → ExactBuffer h s.«in» s.size.toNat ∧ ExactBuffer h s.out (2 * s.size.toNat)
  input : s.strm.avail_in = 0 ∨ ∃ a, s.strm.next_in = padv s.«in» a ∧ a + s.strm.avail_in.toNat ≤ s.size.toNat
  /-- relies on patch 0003 (R-2: `x.next` is set before a COPY load can fail) -/
  output : s.x.have ≠ 0 → ∃ c, s.x.next = padv s.out c ∧ c + s.x.have.toNat ≤ 2 * s.size.toNat
  /-- the inflate stream is in the inflate history, with no header record (`gz_look` never calls
  `inflateGetHeader`) -/
  codec : s.size ≠ 0 → StreamReachable .inflate h (gzStrm i) ∧
    ∃ z k st, (gzStrm i).get h = some z ∧ z.state = some (.inflate k) ∧ h.istates k = some st ∧ st.head = none

/-- The writer part (`s.mode = GZ_WRITE`): batch C's W1–W10. W1 and W9 are in `GzCommon`; W10 needs no fact;
W7 is the position clause of `GzCommon` (relies on the local patch for W7). -/
structure GzWriteInv (h : Heap) (i : Nat) (s : GzState) : Prop where
  /-- the `gzgetc` macro reads `x.have` on any handle -/
  have0 : s.x.have = 0
  direct : s.direct = 0 ∨ s.direct = 1
  reset : s.reset = 0 ∨ s.reset = 1
  /-- W2 -/
  unalloc : s.size = 0 → s.strm.state = none
  /-- W3 -/
  bufs : s.size ≠ 0 → ExactBuffer h s.«in» (2 * s.size.toNat) ∧ (s.direct = 0 → ExactBuffer h s.out s.size.toNat)
  /-- W4 -/
  input : s.strm.avail_in = 0 ∨ ∃ a, s.strm.next_in = padv s.«in» a ∧ a + s.strm.avail_in.toNat ≤ s.size.toNat
  /-- W5 -/
  output : s.direct = 0 → s.size ≠ 0 → ∃ b c, s.strm.next_out = padv s.out b ∧
    s.strm.avail_out.toNat = s.size.toNat - b ∧ s.x.next = padv s.out c ∧ c ≤ b ∧ b ≤ s.size.toNat
  /-- W6: the deflate stream is in the deflate history, with no gzip header record -/
  codec : s.direct = 0 → s.size ≠ 0 → StreamReachable .deflate h (gzStrm i) ∧
    ∃ z k d, (gzStrm i).get h = some z ∧ z.state = some (.deflate k) ∧ h.dstates k = some d ∧ d.gzhead = none
  /-- W8 -/
  transparent : s.direct ≠ 0 → s.strm.state = none

/-- **The gz representation invariant.** Other modules use its interface lemmas, not this definition. -/
def GzInv (h : Heap) (i : Nat) (s : GzState) : Prop :=
  GzCommon h i s ∧ (s.mode = GZ_READ → GzReadInv h i s) ∧ (s.mode = GZ_WRITE → GzWriteInv h i s)

/-! ## 3. The history -/

/-- An OS-world step between calls: any well-formed file-system state, except that the handle's descriptor
stays open or stays closed (only the library closes it). It subsumes `GzReachable.append`; with the oracle fields
in `Fs` it also replaces the oracle arbitrarily. -/
def GzWorldStep (fs fs' : Fs) (fd : Int32) : Prop :=
  FileSystem fs' ∧ (0 ≤ fd.toInt → (GzOracle.FdOpen fs' fd.toInt.toNat ↔ GzOracle.FdOpen fs fd.toInt.toNat))

/-- **Every actual history of one handle** (safety; replaces `GzReachable`, with `ByteObjectsFit` at every point
where the caller supplies a heap). The caller may free its own buffers (`caller`), including the last `gzread`
buffer (R-4, relies on the local patch). -/
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

/-! ## 4. Shapes of the call lemmas and the goal -/

/-- The caller regions a call may write. -/
def GzWriteRegions : Call → List Region
  | .gzread _ p n => if n.toNat < 2 ^ 31 then [⟨p, n.toNat⟩] else []
  | .gzfread p size n _ => if size.toNat * n.toNat < 2 ^ 64 then [⟨p, size.toNat * n.toNat⟩] else []
  | .gzgets _ p n => if 1 ≤ n.toInt then [⟨p, n.toInt.toNat⟩] else []
  | .gzerror _ p => [⟨p, 4⟩]
  | _ => []

/-- The set of open descriptors is unchanged. -/
def FdsKept (fs fs' : Fs) : Prop := ∀ j, GzOracle.FdOpen fs' j ↔ GzOracle.FdOpen fs j

/-- After a non-closing call that returned: a well-formed world, the invariant, mode and descriptor kept, only
the handle's blocks and the declared caller regions written, and an exact ledger. -/
def GzStepPost (h : Heap) (i : Nat) (s : GzState) (call : Call) (fs' : Fs) (after : Heap) : Prop :=
  FileSystem fs' ∧ ∃ s', GzInv after i s' ∧ s'.mode = s.mode ∧ s'.fd = s.fd ∧
    BufferFrame h after (GzOwned h i s) (GzWriteRegions call) ∧
    LiveChange h after
      (fun b => GzOwned after i s' b ∧ ¬ h.live b)
      (fun b => GzOwned h i s b ∧ ¬ GzOwned after i s' b)

/-- **Safety of one call** on a handle in `GzInv`, for every world (every oracle). Two halves, as decided:
(1) with no budget premise, the run never faults: it returns normally or runs out of fuel, never `Fault.ub` (a
memory error is `Fault.ub`); (2) under M7 (`ReadsFinite`, only for the calls of `NeedsReadBound`) it returns
normally. And when it returns, with no budget premise, the open descriptors are kept and `GzStepPost` holds.
Half (1): for every world, the run's result is not a fault: it is `.ok` or the out-of-fuel outcome, never `Fault.ub`
or a memory error. Half (2): with `ReadsFinite`, the result is `.ok`. The fuel is the runtime's fixed per-loop
bound `2^64`, not a parameter, so half (1) is partial correctness up to `2^64` iterations of each loop, which no
real execution reaches; undefined behaviour that grows with iterations (a signed 64-bit counter advancing at
least 1 per iteration) would occur within `2^63` iterations, inside the fuel, so no fault hides behind
`outOfFuel`. -/
def GzCallSafe (i : Nat) (call : Call) : Prop :=
  ∀ h fs s, GzInv h i s → FileSystem fs → GzArguments h i s call →
    (∀ e, call.execute fs h = .error e → e = .outOfFuel) ∧
    ((NeedsReadBound call → ReadsFinite fs s.fd) →
      ∃ value fs' after, call.execute fs h = .ok ((value, fs'), after)) ∧
    (∀ value fs' after, call.execute fs h = .ok ((value, fs'), after) →
      FdsKept fs fs' ∧ GzStepPost h i s call fs' after)

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

/-- **Goal (skeleton): safety of every gz file history.** Every history keeps the world well formed and the
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

/-! ## 5. Helper shapes and interface lemmas of `GzInv` -/

/-- The three parts of a run in `G` that a safety lemma states: no fault but `outOfFuel`; a result under the
premise `finite` (M7 where needed, `True` otherwise); and `post` of every result. -/
def RunSafe {α : Type} (m : G α) (fs : Fs) (h : Heap) (finite : Prop) (post : α → Fs → Heap → Prop) : Prop :=
  (∀ e, m fs h = .error e → e = .outOfFuel) ∧
  (finite → ∃ a fs' after, m fs h = .ok ((a, fs'), after)) ∧
  (∀ a fs' after, m fs h = .ok ((a, fs'), after) → post a fs' after)

/-- `GzStepPost` with explicit caller regions (for the internal helpers). -/
def GzPost (h : Heap) (i : Nat) (s : GzState) (regions : List Region) (fs' : Fs) (after : Heap)
    (inv : Heap → Nat → GzState → Prop) : Prop :=
  FileSystem fs' ∧ ∃ s', inv after i s' ∧ s'.mode = s.mode ∧ s'.fd = s.fd ∧
    BufferFrame h after (GzOwned h i s) regions ∧
    LiveChange h after
      (fun b => GzOwned after i s' b ∧ ¬ h.live b)
      (fun b => GzOwned h i s b ∧ ¬ GzOwned after i s' b)

/-- The record with no buffered output (`x.have = 0`, `x.next = NULL`). -/
def clearOut (s : GzState) : GzState := { s with x := { s.x with «have» := 0, next := .null } }

/-- **The invariant up to the buffered output**, for the inside of a reading call: `GzInv` of the record with no
buffered output. `gz_decomp` and `gz_load` into the caller's buffer leave `x.next` in that buffer until `gz_read`
resets it (the local patch for R-4); this is what holds in between. -/
def GzInvUpToOutput (h : Heap) (i : Nat) (s : GzState) : Prop :=
  h.gzstates i = some s ∧ GzInv (putGz h i (clearOut s)) i (clearOut s)

/-- The state pointer of handle `i`. -/
def gzSt (i : Nat) : GzStatePtr := some (.tab i)

/-- Interface: the common part. -/
theorem GzInv.common {h : Heap} {i : Nat} {s : GzState} (inv : GzInv h i s) : GzCommon h i s := And.left inv

/-- Interface: the reader part. -/
theorem GzInv.reader {h : Heap} {i : Nat} {s : GzState} (inv : GzInv h i s) (hm : s.mode = GZ_READ) :
    GzReadInv h i s := (And.right inv).1 hm

/-- Interface: the writer part. -/
theorem GzInv.writer {h : Heap} {i : Nat} {s : GzState} (inv : GzInv h i s) (hm : s.mode = GZ_WRITE) :
    GzWriteInv h i s := (And.right inv).2 hm

/-- Interface: the record determines the state. -/
theorem GzInv.state_eq {h : Heap} {i : Nat} {s t : GzState} (inv : GzInv h i s) (ht : h.gzstates i = some t) :
    s = t := by
  have hs := inv.common.record
  rw [ht] at hs
  exact (Option.some.inj hs).symm

/-- Interface: an edit of the caller's memory (anything the handle does not own) keeps the invariant. Uses
`StreamReachable.rebuffer` for the codec (the record is not edited, so the stream fields are unchanged) and,
for `next`, the local patch for R-4 (`x.next` never points into caller memory). -/
theorem GzInv.caller {h after : Heap} {i : Nat} {s : GzState} (inv : GzInv h i s)
    (hf : GzCallerFrame h after i s) (fit : ZlibF.PlatformMemory.ByteObjectsFit after) : GzInv after i s := by
  sorry

/-- Interface: `gz_error` keeps the invariant. The message is NULL or a string the handle does not own; the new
error is `err`, or `Z_MEM_ERROR` with no message when the copy cannot be allocated; the old message is freed and
a new one may be created. -/
theorem GzInv.gz_error {h : Heap} {i : Nat} {s : GzState} (inv : GzInv h i s) (err : Int32) (msg : BPtr)
    (hmsg : msg = .null ∨ ∃ t, CString h msg t ∧ ∀ b, ByteRoot msg b → ¬ GzOwned h i s b) :
    ∃ after s', C.run (Zlib.Gzlib.gz_error (gzSt i) err msg) h = .ok ((), after) ∧ GzInv after i s' ∧
      s' = { s with err := s'.err, msg := s'.msg } ∧ (s'.err = err ∨ (s'.err = Z_MEM_ERROR ∧ s'.msg = .null)) ∧
      Frame h after (fun b => b = i ∨ blkOf s.msg = some b) ∧
      LiveChange h after (fun b => blkOf s'.msg = some b ∧ ¬ h.live b) (fun b => blkOf s.msg = some b) := by
  sorry

/-- Interface: `gz_reset` keeps the invariant and clears the buffered output, the position and the skip.
Relies on the local patch for R-3 (`gz_reset` writes `x.next`). -/
theorem GzInv.gz_reset {h : Heap} {i : Nat} {s : GzState} (inv : GzInv h i s) :
    ∃ after s', C.run (Zlib.Gzlib.gz_reset (gzSt i)) h = .ok ((), after) ∧ GzInv after i s' ∧
      s'.x.have = 0 ∧ s'.x.pos = 0 ∧ s'.skip = 0 ∧ s'.err = Z_OK ∧ s'.msg = .null ∧
      Frame h after (fun b => b = i ∨ blkOf s.msg = some b) ∧
      LiveChange h after (fun _ => False) (fun b => blkOf s.msg = some b) := by
  sorry

/-- Interface: a write of scalar fields of the record that keeps every clause of the invariant over the new
values keeps it (the caller of this lemma proves the clause conditions for the fields it changes). -/
theorem GzInv.put_scalars {h : Heap} {i : Nat} {s s' : GzState} (inv : GzInv h i s)
    (same : s'.path = s.path ∧ s'.msg = s.msg ∧ s'.«in» = s.«in» ∧ s'.out = s.out ∧ s'.size = s.size ∧
      s'.mode = s.mode ∧ s'.direct = s.direct ∧ s'.strm = s.strm ∧ s'.x.next = s.x.next ∧ s'.err = s.err)
    (want : 8 ≤ s'.want.toNat ∧ s'.want.toNat < 2 ^ 31 ∧ (s.size = 0 ∨ s'.want = s.want))
    (pos : 0 ≤ s'.skip.toInt ∧ s'.x.pos.toInt + s'.skip.toInt ≤ 9223372036854775807 ∧
      0 ≤ s'.x.pos.toInt + s'.x.have.toNat)
    (have_le : s'.x.have.toNat ≤ s.x.have.toNat)
    (rd : s.mode = GZ_READ → (s'.how = LOOK ∨ s'.how = GZ_COPY ∨ s'.how = GZIP) ∧ (s'.how = GZ_COPY → s'.direct = 1) ∧
      (s'.how = GZIP → s'.direct = 0) ∧ (s'.junk = -1 ∨ s'.junk = 0 ∨ s'.junk = 1) ∧
      (s'.eof = 0 ∨ s'.eof = 1) ∧ (s'.past = 0 ∨ s'.past = 1) ∧ (s'.again = 0 ∨ s'.again = 1) ∧
      (s.size = 0 → s'.how = LOOK))
    (wr : s.mode = GZ_WRITE → s'.reset = 0 ∨ s'.reset = 1) :
    GzInv (putGz h i s') i s' := by
  sorry

/-! ## Decision (4): the three `Uniq` are one predicate -/

/-- `Zlib.Gzlib.Spec.Uniq` and `Zlib.Inflate.Spec.Uniq` have the same body (one object per block number over the
same seven tables), so the codec histories embed with no conversion. -/
theorem gz_uniq_iff_inflate (h : Heap) : Zlib.Gzlib.Spec.Uniq h ↔ Zlib.Inflate.Spec.Uniq h := Iff.rfl

/-- The same for `Zlib.Deflate.Spec.Uniq`. -/
theorem gz_uniq_iff_deflate (h : Heap) : Zlib.Gzlib.Spec.Uniq h ↔ Zlib.Deflate.Spec.Uniq h := Iff.rfl

end ZlibF.Spec.Public
