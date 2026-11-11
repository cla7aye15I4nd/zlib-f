import ZlibF.Proof.«inflate.c.meaning»
import ZlibF.Proof.«inflate.c.main.macros»
import ZlibF.Proof.«inflate.c.input-cursor»
import ZlibF.Spec.Public.Memory

/-!
# inflate.c: the format meaning inside one `inflate` call (interface)

`ParseMeaning` describes the decoder between calls. Inside a call the bit
buffer, the input cursor and the output cursor are in the registers `IL`, and
the stream record is written back only at `inf_leave`. `LoopMatches` is the
same meaning at each trip of the mode loop, for the registers `l` and the heap
`h`. The per-mode lemmas (batch 1: body modes; batch 2: header, dictionary,
trailer modes) go from `LoopMatches` to `LoopMatches` of an extended position,
to `goto inf_leave` with `LoopMatches`, or to `BAD` with `LoopDoomed`. The
loop assembly composes them; `inf_leave` turns `LoopMatches` into
`ParseMeaning`.

Fixed for the call (`LoopFrame`): the configuration, the dictionary, the
input and output of the epoch before the call, the input bytes offered to the
call, and the output start `next_out`.

At each trip:

* the decoder state, seen with the registers' bit buffer (`loopState`: what
  `RESTORE()` would write), matches the stage as in `ParseMeaning`;
* the input read in this call is `inp.take k` with `k = in - have`, and the
  rest `inp.drop k` is at `next` (`BitInv`);
* the bytes `[start, put)` are this call's output `callOut`; the stage's
  output is the epoch's output before the call followed by `callOut`;
* the output room `[put, put + left)` is writable and separate from the unread
  input and from the window, and the written output is separate from the
  unread input, so a write in the room changes none of them;
* the window and the dictionary state are those of the output before the
  call: nothing in the loop writes the window;
* the return register is still `Z_OK` (only `DONE`, `BAD` and leaving set
  it) and the configuration of the trace is kept (`ConfigMatches`);
* `check` and `total` cover the stage's output up to the check base
  `put - (out - left)` (before `CHECK` runs, the output before the call).
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- What stays fixed during one call. -/
structure LoopFrame where
  wrap : Api.Wrap
  configured : Nat
  /-- The epoch's dictionary. -/
  dict : List UInt8
  /-- The epoch's input before the call. -/
  logIn : List UInt8
  /-- The epoch's output before the call. -/
  logOut : List UInt8
  /-- The input bytes offered to the call (`avail_in` bytes at `next_in`). -/
  inp : List UInt8
  /-- `next_out` at entry. -/
  start : BPtr

/-- The decoder state with the registers' bit buffer, as `RESTORE()` writes it. -/
def loopState (s : InflateState) (l : IL) : InflateState :=
  { s with hold := l.hold, bits := l.bits }

/-- Bytes of the call read so far. -/
def loopRead (l : IL) : Nat := l.in_.toNat - l.have_.toNat

/-- Bytes written in the call since the check base. -/
def loopPending (l : IL) : Nat := l.out_.toNat - l.left.toNat

/-- The stage facts inside a call. For a body or trailer stage the window and
the check value are those of the output before the call (the window) and of
the output up to the check base (`check`, `total`). After the body the window
is not used again in the call (`CHECK` moves the check base, and `inf_leave`
then updates the window with the bytes after it only), so the trailer and
end stages carry no window fact, as in `StageMatches`. -/
def LoopStageMatches (h : Heap) (s : InflateState) (f : LoopFrame) (checked : List UInt8) :
    WrapStage → Prop
  | .header _ => HEAD ≤ s.mode ∧ s.mode ≤ DICTID
  | .needDict _ => s.mode = DICT
  | .body header pos => BodyMatches h s pos ∧ WindowMeaning h s f.dict f.logOut ∧
      CheckMeaning s f.wrap header checked
  | .trailer header _ _ => (s.mode = CHECK ∨ s.mode = LENGTH) ∧ CheckMeaning s f.wrap header checked
  | .done _ => s.mode = DONE

/-- The format meaning at one trip of the mode loop of a call with context
`c`. `callOut` is this call's output so far, at `[f.start, put)`. -/
def LoopMatches (c : Ctx) (f : LoopFrame) (h : Heap) (l : IL) : Prop :=
  ∃ (zs : Nat) (s : InflateState) (callOut : List UInt8) (consumed held : List Bool)
    (stage : WrapStage),
    c.st = some (.tab zs) ∧ h.istates zs = some s ∧ l.ret = Z_OK ∧
    ConfigMatches (loopState s l) f.wrap f.configured ∧
    l.have_.toNat ≤ l.in_.toNat ∧ l.in_.toNat = f.inp.length ∧
    BitInv h l (f.inp.drop (loopRead l)) ∧
    l.left.toNat ≤ l.out_.toNat ∧ loopPending l ≤ callOut.length ∧
    l.put = inputAdvance f.start callOut.length ∧ Bytes h f.start callOut.length callOut ∧
    Writable h l.put l.left.toNat ∧ Separate l.put l.left.toNat l.next l.have_.toNat ∧
    Separate l.put l.left.toNat s.window s.wsize.toNat ∧
    Separate f.start callOut.length l.next l.have_.toNat ∧
    bytesToBits (f.logIn ++ f.inp.take (loopRead l)) = consumed ++ held ∧
    HeldBits (loopState s l) held ∧
    WrapParsed f.wrap f.configured f.dict consumed stage ∧
    LoopStageMatches h (loopState s l) f
      ((f.logOut ++ callOut).take ((f.logOut ++ callOut).length - loopPending l)) stage ∧
    WrapMatches h (loopState s l) f.wrap f.configured f.dict stage ∧
    stage.output = f.logOut ++ callOut

/-- The consumed input has no valid completion with a full window (the `BAD`
clause of `ParseMeaning`, for the input read so far in the call). -/
def LoopDoomed (f : LoopFrame) (l : IL) : Prop :=
  ∀ source decoded, Api.Layer.Decodes f.wrap f.configured f.dict source decoded →
    Api.FullWindow f.wrap f.configured source →
    ¬ (f.logIn ++ f.inp.take (loopRead l)) <+: source

/-- Doom is kept when more input is read. -/
theorem LoopDoomed.more {f : LoopFrame} {l l' : IL} (doomed : LoopDoomed f l)
    (more : loopRead l ≤ loopRead l') : LoopDoomed f l' := by
  intro source decoded valid full longer
  apply doomed source decoded valid full
  refine List.IsPrefix.trans ?_ longer
  rw [List.prefix_append_right_inj]
  have shorter : f.inp.take (loopRead l) = (f.inp.take (loopRead l')).take (loopRead l) := by
    rw [List.take_take, Nat.min_eq_left more]
  rw [shorter]
  exact List.take_prefix _ _

end Zlib.Inflate.Proofs
