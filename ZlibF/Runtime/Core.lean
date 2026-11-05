/-!
# Runtime core: the C-in-Lean memory and control model

Trusted base of every translation in this repository; see `docs/trusted-base.md`.
-/

/-!
# C-in-Lean runtime (draft, LP64)

A shallow embedding of the C subset used by zlib 1.3.2, for the target
`x86_64` LP64 (`int` 32-bit, `long`/`size_t`/pointers 64-bit).

Translation conventions (shared by hand/LLM translations and the future
mechanical C2Lean translator, so their outputs can be compared):

* C unsigned types map to Lean `UInt8/16/32/64`; their arithmetic is modular,
  exactly as in C. Signed arithmetic is checked: overflow raises `Fault.ub`.
* Every undefined behavior the translation can reach (out-of-bounds access,
  null dereference, out-of-range pointer arithmetic, signed overflow, invalid
  shift) becomes `throw (.ub _)`. A theorem that a function returns `.ok`
  therefore includes absence of these behaviors.
* Loops are translated with `cwhile`/`cdoWhile` over an explicit tuple of the
  loop-carried locals. They are structurally recursive on a fuel bound, so
  translations are total and provable; running out of fuel is `.outOfFuel`,
  which a termination theorem must rule out.

The trusted base of this runtime is reviewed by hand. It is a draft: it covers
only what the translated functions use so far.
-/

namespace C

/-- Why a C computation did not produce a value. -/
inductive Fault where
  | ub (what : String)
  | outOfFuel
  deriving Repr, DecidableEq, Inhabited

/-- Tags for the cell-based object model. Pointer payloads encode null as none. -/
inductive Cell where
  | u8 (value : UInt8) | u16 (value : UInt16) | u32 (value : UInt32)
  | u64 (value : UInt64) | i32 (value : Int32) | i64 (value : Int64)
  | ptr (value : Option (Nat × Int)) | fnptr (name : String)
  deriving Repr, DecidableEq, Inhabited

structure TypedBlock where
  cells : Array (Option Cell)
  readonly : Bool := false
  layout : String := ""
  declared : Array Cell := #[]
  deriving Repr, Inhabited

/-- One allocated object: its bytes. Freed objects become `none`. -/
abbrev Block := Option ByteArray

/-- The heap: allocated objects indexed by block identifier. -/
structure Heap where
  blocks : Array Block := #[]
  typedBlocks : Array (Option TypedBlock) := #[]
  readonlyBytes : Array Nat := #[]
  allocCalls : Nat := 0
  allocOk : Nat → Bool := fun _ => true
  /-- Initial contents of uninitialized `malloc` memory: byte `i` of the
  `n`-th allocation. Proofs quantify over it, so no behavior may depend on
  indeterminate bytes beyond what C permits (an unspecified value). -/
  garbage : Nat → Nat → UInt8 := fun _ _ => 0
  deriving Inhabited

/-- A C object pointer: null, or a block and a byte offset into it. -/
inductive Ptr where
  | null
  | ref (blk : Nat) (off : Int)
  deriving Repr, DecidableEq, Inhabited

/-- C computations: heap state plus faults. -/
abbrev CM := StateT Heap (Except Fault)

def ub {α} (what : String) : CM α := throw (.ub what)

/-- Size of a live block, or UB for an invalid/freed one. -/
def blockSize (blk : Nat) : CM Nat := do
  match (← get).blocks[blk]? with
  | some (some bytes) => pure bytes.size
  | _ => ub "access to invalid or freed object"

/-- `p + k` for an object pointer; C permits offsets `0 .. size` (one past). -/
def Ptr.add (p : Ptr) (k : Int) : CM Ptr := do
  match p with
  | .null => if k = 0 then pure .null else ub "arithmetic on null pointer"
  | .ref blk off =>
    let size ← blockSize blk
    let off' := off + k
    if 0 ≤ off' ∧ off' ≤ size then pure (.ref blk off') else ub "pointer arithmetic out of object"

/-- Read one byte `*p`. -/
def load8 (p : Ptr) : CM UInt8 := do
  match p with
  | .null => ub "null dereference"
  | .ref blk off =>
    match (← get).blocks[blk]? with
    | some (some bytes) =>
      if h : 0 ≤ off ∧ off.toNat < bytes.size then
        pure bytes[off.toNat]
      else ub "read out of bounds"
    | _ => ub "read of invalid or freed object"

/-- Read `p[i]`, i.e. `*(p + i)`. -/
def index8 (p : Ptr) (i : Int) : CM UInt8 := do
  load8 (← p.add i)

/-- Loop fuel. Large enough that no zlib loop over in-memory data can exhaust it. -/
def fuel : Nat := 2 ^ 64

/-- `while (cond) body` over loop-carried state `σ`. The condition may update
the state (e.g. `while (len--)`); its update happens on every evaluation,
including the final false one, as in C. -/
def cwhile {σ} (cond : σ → CM (Bool × σ)) (body : σ → CM σ) (s : σ) : CM σ :=
  go fuel s
where
  go : Nat → σ → CM σ
    | 0, _ => throw .outOfFuel
    | n + 1, s => do
      let (c, s) ← cond s
      if c then go n (← body s) else pure s

/-- `do body while (cond)` over loop-carried state `σ`. -/
def cdoWhile {σ} (body : σ → CM σ) (cond : σ → CM (Bool × σ)) (s : σ) : CM σ :=
  go fuel s
where
  go : Nat → σ → CM σ
    | 0, _ => throw .outOfFuel
    | n + 1, s => do
      let s ← body s
      let (c, s) ← cond s
      if c then go n s else pure s

/-- Allocate a block holding `bytes` (used by harnesses and tests). -/
def alloc (bytes : ByteArray) : CM Ptr := do
  let h ← get
  set { h with blocks := h.blocks.push (some bytes) }
  pure (.ref h.blocks.size 0)

/-- Run a computation on a heap. -/
def run {α} (m : CM α) (h : Heap := {}) : Except Fault (α × Heap) := m.run h

end C
