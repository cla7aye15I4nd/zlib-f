import ZlibF.Proof.«inflate.c.header-source-trace»
import ZlibF.Proof.«inflate.c.header-source»

namespace Zlib.Inflate.Proofs.HeaderPhaseView
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.CumulativeParser
set_option autoImplicit false

structure BlockMeta where
  header : Nat
  last : Nat
  deriving DecidableEq
structure CountMeta extends BlockMeta where
  lit : Nat
  dist : Nat
  code : Nat
  deriving DecidableEq
structure AlphabetMeta extends CountMeta where
  alphabet : List Nat
  deriving DecidableEq

def readBlock (input : List Bool) : Option (BlockMeta × List Bool) := do
  let (header, r0) ← readBits 16 input
  let (last, r1) ← readBits 1 r0
  let (kind, r2) ← readBits 2 r1
  if kind = 2 then some (⟨header, last⟩, r2) else none

def readCounts (input : List Bool) : Option (CountMeta × List Bool) := do
  let (block, r0) ← readBlock input
  let (lit, r1) ← readBits 5 r0
  let (dist, r2) ← readBits 5 r1
  let (code, r3) ← readBits 4 r2
  some (⟨block, lit, dist, code⟩, r3)

def readAlphabet (input : List Bool) : Option (AlphabetMeta × List Bool) := do
  let (counts, r0) ← readCounts input
  let (alphabet, r1) ← readCodeLenLens (counts.code + 4) r0
  some (⟨counts, alphabet⟩, r1)

/-- The actual credited byte ledger is interpreted causally for every
future suffix. Unread physical caller-buffer bytes are not retained. -/
def View {α : Type} (parser : List Bool → Option (α × List Bool)) (record : α)
    (credited rest : List Bool) : Prop :=
  ∀ future, parser (credited ++ future) = some (record, rest ++ future)

theorem View.advance {α : Type} {parser : List Bool → Option (α × List Bool)} {record : α}
    {credited rest : List Bool} (view : View parser record credited rest) (delta : List Bool) :
    View parser record (credited ++ delta) (rest ++ delta) := by
  intro future
  simpa only [List.append_assoc] using view (delta ++ future)

theorem View.bind {α β : Type} {parser : List Bool → Option (α × List Bool)} {record : α}
    {next : α → List Bool → Option (β × List Bool)} {nextMeta : β} {credited middle rest : List Bool}
    (view : View parser record credited middle) (suffix : View (next record) nextMeta middle rest) :
    View (fun input => do let (value, remaining) ← parser input; next value remaining) nextMeta credited rest := by
  intro future
  dsimp only
  rw [view future]
  exact suffix future

inductive Phase where
  | head | block | table | lens | code
  deriving DecidableEq

/-- Pure state/format components interpreted from the original DataLog.
These are conclusions of phase induction, never source-trace premises. -/
def PhaseData (phase : Phase) (state : InflateState) (log : DataLog) : Prop :=
  match phase with
  | .head => state.mode = HEAD ∧ state.last = 0 ∧ state.wrap = 5 ∧
      state.bits.toNat < 16 ∧ state.bits.toNat = 8 * log.input.length ∧
      natBits state.bits.toNat state.hold.toNat = bytesBits log.input ∧ log.input.length ≤ 1
  | .block => (state.mode = TYPE ∨ state.mode = TYPEDO) ∧ state.last = 0 ∧ state.bits = 0 ∧ state.hold = 0 ∧
      ∃ header, View (readBits 16) header (bytesBits log.input) []
  | .table => state.mode = TABLE ∧ ∃ record : BlockMeta,
      record.last < 2 ∧ state.last.toInt = (record.last : Int) ∧
      View readBlock record (bytesBits log.input) (natBits state.bits.toNat state.hold.toNat)
  | .lens => state.mode = LENLENS ∧ ∃ (record : CountMeta) (received : List Bool),
      record.last < 2 ∧ state.last.toInt = (record.last : Int) ∧
      View readCounts record (bytesBits log.input) received ∧
      state.nlen.toNat = record.lit + 257 ∧ state.ndist.toNat = record.dist + 1 ∧ state.ncode.toNat = record.code + 4 ∧
      LenlensProgress state state.hold state.bits received
  | .code => state.mode = CODELENS ∧ ∃ (record : AlphabetMeta) (received : List Bool),
      record.last < 2 ∧ state.last.toInt = (record.last : Int) ∧
      View readAlphabet record (bytesBits log.input) received ∧
      state.nlen.toNat = record.lit + 257 ∧ state.ndist.toNat = record.dist + 1 ∧ state.ncode.toNat = record.code + 4 ∧
      Zlib.Inftrees.Proofs.CodeLengthContents state.codes 0 state.lenbits.toNat record.alphabet ∧
      (∀ index, index < 2 ^ state.lenbits.toNat → ∃ entry, state.codes[index]? = some entry ∧ entry.op = 0) ∧
      Progress record.alphabet (state.nlen.toNat + state.ndist.toNat) [] received state

def Meaning (phase : Phase) (h : Heap) (r : ZStreamRef) (zs : Nat) (log : DataLog) : Prop :=
  ∃ z state, DefaultOriginState h r zs z state ∧ DefAlloc z ∧ state.wsize = 0 ∧ log.output = [] ∧ PhaseData phase state log

/-- The original trace's actual init and selected real HEAD transitions
establish the first unified phase. No initialized relation is a premise. -/
theorem head_from_init {h : Heap} {r : ZStreamRef} {log : DataLog} {zs : Nat} {history : InflateDataTrace 15 r h log}
    (selected : HeaderDataTrace.HeadEpoch r zs history) : Meaning .head h r zs log := by
  obtain ⟨z, state, current, allocator, empty, mode, last, wrap, window, below, count, word, bound⟩ := selected.sound
  exact ⟨z, state, current, allocator, window, empty, mode, last, wrap, below, count, word, bound⟩

#print axioms View.advance
#print axioms View.bind
#print axioms head_from_init
end Zlib.Inflate.Proofs.HeaderPhaseView
