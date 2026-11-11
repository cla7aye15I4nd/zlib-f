import ZlibF.Proof.«inflate.c.meaning-stuck»
import ZlibF.Proof.«inflate.c.meaning-stream-length»
import ZlibF.Proof.«inflate.c.main.bits»

/-!
# inflate.c: why a mode step stops

Two facts the mode steps state beside `LoopMatches` and `LoopDoomed`, for
the per-call facts of the decompression utilities (`ConsumesWithinStream`:
`StopShort`, `FailWithin`).

* `LeaveShort`: a step that leaves for want of input (`have == 0`) holds
  bits that do not complete the field its mode waits for. The `NEEDBITS(n)`
  modes hold fewer than `n` bits; `TYPE`/`TYPEDO` fewer than 3 before a
  block that is not the last (the block header); `COPY` still has stored bytes to copy; the lookups hold no
  complete valid symbol of any table meaning of the installed table
  (`LEN`, `DIST`) and no complete code-length item of any code-length
  meaning of it (`CODELENS`). The header and trailer modes are listed for
  the steps of batch 2, with the conditions under which they wait at all
  (`HEAD` and `CHECK` only with a wrapper, `LENGTH` only for gzip).
* `LoopRefuted`: at a rejection (`BAD`), no valid full-window stream is
  comparable with the input read so far: the stream does not continue it
  (`LoopDoomed`), and it does not end inside it either. So a call that
  rejects did not read past the end of a valid stream its input is
  comparable with. Every body rejection stops at a position no
  specification parse continues (`LoopStuck`), and a valid stream that ends
  inside the bits read would continue it (`header_split`,
  `deflateParsed_resid`).

Both were checked on the real decoder first
(`tests/goals/inflate-meaning-body`, starved leaves and data errors on
corrupted sources).
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open HeldWithinBounds
set_option autoImplicit false

/-- The held bits `held` of the state `s` do not complete the field the
mode of `s` waits for, when it waits for input. -/
def ShortAt (h : Heap) (s : InflateState) (held : List Bool) : Prop :=
  ((s.mode = TYPE ∨ s.mode = TYPEDO) ∧ s.last = 0 ∧ held.length < 3) ∨
  (s.mode = STORED ∧ held.length < 32) ∨
  (s.mode = COPY ∧ s.length ≠ 0) ∨
  (s.mode = TABLE ∧ held.length < 14) ∨
  (s.mode = LENLENS ∧ held.length < 3) ∨
  (s.mode = CODELENS ∧ ∀ ref offset codes cl, s.lencode = .ref ref offset →
    Space.get h ref = some codes →
    Zlib.Inftrees.Proofs.CodeLengthMeaning codes offset s.lenbits.toNat cl →
    ¬ CodeLenItem cl held) ∨
  ((s.mode = LEN_ ∨ s.mode = LEN) ∧ ∀ L, TableMeaning h s.lencode s.lenbits LENS L →
    ∀ symbol rest, decodeSym L held = some (symbol, rest) → 285 < symbol) ∨
  (s.mode = LENEXT ∧ held.length < s.extra.toNat) ∨
  (s.mode = DIST ∧ ∀ D, TableMeaning h s.distcode s.distbits DISTS D →
    ∀ symbol rest, decodeSym D held = some (symbol, rest) → 29 < symbol) ∨
  (s.mode = DISTEXT ∧ held.length < s.extra.toNat) ∨
  (s.mode = HEAD ∧ s.wrap ≠ 0 ∧ held.length < 16) ∨
  ((s.mode = FLAGS ∨ s.mode = OS ∨ s.mode = EXLEN ∨ s.mode = HCRC) ∧ held.length < 16) ∨
  ((s.mode = TIME ∨ s.mode = DICTID) ∧ held.length < 32) ∨
  (s.mode = CHECK ∧ s.wrap ≠ 0 ∧ held.length < 32) ∨
  (s.mode = LENGTH ∧ s.wrap ≠ 0 ∧ s.flags ≠ 0 ∧ held.length < 32)

/-- At a leave for want of input with registers `l`: the decoder state with
the registers' bit buffer is short of its field. -/
def LeaveShort (c : Ctx) (h : Heap) (l : IL) : Prop :=
  ∀ zs s, c.st = some (.tab zs) → h.istates zs = some s →
    ShortAt h s (natBits l.bits.toNat l.hold.toNat)

section ShortAtIntro
variable {h : Heap} {s : InflateState} {held : List Bool}

theorem ShortAt.type (m : s.mode = TYPE ∨ s.mode = TYPEDO) (last : s.last = 0)
    (n : held.length < 3) : ShortAt h s held :=
  Or.inl ⟨m, last, n⟩
theorem ShortAt.stored (m : s.mode = STORED) (n : held.length < 32) : ShortAt h s held :=
  Or.inr (Or.inl ⟨m, n⟩)
theorem ShortAt.copy (m : s.mode = COPY) (n : s.length ≠ 0) : ShortAt h s held :=
  Or.inr (Or.inr (Or.inl ⟨m, n⟩))
theorem ShortAt.table (m : s.mode = TABLE) (n : held.length < 14) : ShortAt h s held :=
  Or.inr (Or.inr (Or.inr (Or.inl ⟨m, n⟩)))
theorem ShortAt.lenlens (m : s.mode = LENLENS) (n : held.length < 3) : ShortAt h s held :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨m, n⟩))))
theorem ShortAt.codelens (m : s.mode = CODELENS)
    (n : ∀ ref offset codes cl, s.lencode = .ref ref offset → Space.get h ref = some codes →
      Zlib.Inftrees.Proofs.CodeLengthMeaning codes offset s.lenbits.toNat cl →
      ¬ CodeLenItem cl held) : ShortAt h s held :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨m, n⟩)))))
theorem ShortAt.len (m : s.mode = LEN_ ∨ s.mode = LEN)
    (n : ∀ L, TableMeaning h s.lencode s.lenbits LENS L →
      ∀ symbol rest, decodeSym L held = some (symbol, rest) → 285 < symbol) : ShortAt h s held :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨m, n⟩))))))
theorem ShortAt.lenext (m : s.mode = LENEXT) (n : held.length < s.extra.toNat) : ShortAt h s held :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨m, n⟩)))))))
theorem ShortAt.dist (m : s.mode = DIST)
    (n : ∀ D, TableMeaning h s.distcode s.distbits DISTS D →
      ∀ symbol rest, decodeSym D held = some (symbol, rest) → 29 < symbol) : ShortAt h s held :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨m, n⟩))))))))
theorem ShortAt.distext (m : s.mode = DISTEXT) (n : held.length < s.extra.toNat) : ShortAt h s held :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨m, n⟩)))))))))

end ShortAtIntro

/-! ## Reading `ShortAt` at a known mode -/

section ShortAtElim
variable {h : Heap} {s : InflateState} {held : List Bool}

theorem ShortAt.of_type (sh : ShortAt h s held) (m : s.mode = TYPE ∨ s.mode = TYPEDO) :
    s.last = 0 ∧ held.length < 3 := by
  rcases sh with ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩
  all_goals first
    | (exfalso; rcases m with m | m <;> rw [m] at mm <;> revert mm <;> decide)
    | exact r

theorem ShortAt.of_stored (sh : ShortAt h s held) (m : s.mode = STORED) :
    held.length < 32 := by
  rcases sh with ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩
  all_goals first
    | (exfalso; rw [m] at mm; revert mm; decide)
    | exact r

theorem ShortAt.of_copy (sh : ShortAt h s held) (m : s.mode = COPY_ ∨ s.mode = COPY) :
    s.length ≠ 0 := by
  rcases sh with ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩
  all_goals first
    | (exfalso; rcases m with m | m <;> rw [m] at mm <;> revert mm <;> decide)
    | exact r

theorem ShortAt.of_table (sh : ShortAt h s held) (m : s.mode = TABLE) :
    held.length < 14 := by
  rcases sh with ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩
  all_goals first
    | (exfalso; rw [m] at mm; revert mm; decide)
    | exact r

theorem ShortAt.of_lenlens (sh : ShortAt h s held) (m : s.mode = LENLENS) :
    held.length < 3 := by
  rcases sh with ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩
  all_goals first
    | (exfalso; rw [m] at mm; revert mm; decide)
    | exact r

theorem ShortAt.of_codelens (sh : ShortAt h s held) (m : s.mode = CODELENS) :
    ∀ ref offset codes cl, s.lencode = .ref ref offset → Space.get h ref = some codes →
      Zlib.Inftrees.Proofs.CodeLengthMeaning codes offset s.lenbits.toNat cl →
      ¬ CodeLenItem cl held := by
  rcases sh with ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩
  all_goals first
    | (exfalso; rw [m] at mm; revert mm; decide)
    | exact r

theorem ShortAt.of_len (sh : ShortAt h s held) (m : s.mode = LEN_ ∨ s.mode = LEN) :
    ∀ L, TableMeaning h s.lencode s.lenbits LENS L →
      ∀ symbol rest, decodeSym L held = some (symbol, rest) → 285 < symbol := by
  rcases sh with ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩
  all_goals first
    | (exfalso; rcases m with m | m <;> rw [m] at mm <;> revert mm <;> decide)
    | exact r

theorem ShortAt.of_lenext (sh : ShortAt h s held) (m : s.mode = LENEXT) :
    held.length < s.extra.toNat := by
  rcases sh with ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩
  all_goals first
    | (exfalso; rw [m] at mm; revert mm; decide)
    | exact r

theorem ShortAt.of_dist (sh : ShortAt h s held) (m : s.mode = DIST) :
    ∀ D, TableMeaning h s.distcode s.distbits DISTS D →
      ∀ symbol rest, decodeSym D held = some (symbol, rest) → 29 < symbol := by
  rcases sh with ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩
  all_goals first
    | (exfalso; rw [m] at mm; revert mm; decide)
    | exact r

theorem ShortAt.of_distext (sh : ShortAt h s held) (m : s.mode = DISTEXT) :
    held.length < s.extra.toNat := by
  rcases sh with ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩
  all_goals first
    | (exfalso; rw [m] at mm; revert mm; decide)
    | exact r

theorem ShortAt.of_head (sh : ShortAt h s held) (m : s.mode = HEAD) :
    s.wrap ≠ 0 ∧ held.length < 16 := by
  rcases sh with ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩
  all_goals first
    | (exfalso; rw [m] at mm; revert mm; decide)
    | exact r

theorem ShortAt.of_flags (sh : ShortAt h s held) (m : s.mode = FLAGS) :
    held.length < 16 := by
  rcases sh with ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩
  all_goals first
    | (exfalso; rw [m] at mm; revert mm; decide)
    | exact r

theorem ShortAt.of_os (sh : ShortAt h s held) (m : s.mode = OS) :
    held.length < 16 := by
  rcases sh with ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩
  all_goals first
    | (exfalso; rw [m] at mm; revert mm; decide)
    | exact r

theorem ShortAt.of_exlen (sh : ShortAt h s held) (m : s.mode = EXLEN) :
    held.length < 16 := by
  rcases sh with ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩
  all_goals first
    | (exfalso; rw [m] at mm; revert mm; decide)
    | exact r

theorem ShortAt.of_hcrc (sh : ShortAt h s held) (m : s.mode = HCRC) :
    held.length < 16 := by
  rcases sh with ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩
  all_goals first
    | (exfalso; rw [m] at mm; revert mm; decide)
    | exact r

theorem ShortAt.of_time (sh : ShortAt h s held) (m : s.mode = TIME) :
    held.length < 32 := by
  rcases sh with ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩
  all_goals first
    | (exfalso; rw [m] at mm; revert mm; decide)
    | exact r

theorem ShortAt.of_dictid (sh : ShortAt h s held) (m : s.mode = DICTID) :
    held.length < 32 := by
  rcases sh with ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩
  all_goals first
    | (exfalso; rw [m] at mm; revert mm; decide)
    | exact r

theorem ShortAt.of_check (sh : ShortAt h s held) (m : s.mode = CHECK) :
    held.length < 32 := by
  rcases sh with ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩
  all_goals first
    | (exfalso; rw [m] at mm; revert mm; decide)
    | exact r.2

theorem ShortAt.of_length (sh : ShortAt h s held) (m : s.mode = LENGTH) :
    held.length < 32 := by
  rcases sh with ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩
  all_goals first
    | (exfalso; rw [m] at mm; revert mm; decide)
    | exact r.2.2

theorem ShortAt.not_lit (sh : ShortAt h s held) (m : s.mode = LIT) :
    False := by
  rcases sh with ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩
  all_goals first
    | (exfalso; rw [m] at mm; revert mm; decide)
    | exact absurd rfl id

theorem ShortAt.not_match (sh : ShortAt h s held) (m : s.mode = MATCH) :
    False := by
  rcases sh with ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩
  all_goals first
    | (exfalso; rw [m] at mm; revert mm; decide)
    | exact absurd rfl id

theorem ShortAt.not_done (sh : ShortAt h s held) (m : s.mode = DONE) :
    False := by
  rcases sh with ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩
  all_goals first
    | (exfalso; rw [m] at mm; revert mm; decide)
    | exact absurd rfl id

theorem ShortAt.not_dict (sh : ShortAt h s held) (m : s.mode = DICT) :
    False := by
  rcases sh with ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩
  all_goals first
    | (exfalso; rw [m] at mm; revert mm; decide)
    | exact absurd rfl id

theorem ShortAt.not_extra (sh : ShortAt h s held) (m : s.mode = EXTRA) :
    False := by
  rcases sh with ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩
  all_goals first
    | (exfalso; rw [m] at mm; revert mm; decide)
    | exact absurd rfl id

theorem ShortAt.not_name (sh : ShortAt h s held) (m : s.mode = NAME) :
    False := by
  rcases sh with ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩
  all_goals first
    | (exfalso; rw [m] at mm; revert mm; decide)
    | exact absurd rfl id

theorem ShortAt.not_comment (sh : ShortAt h s held) (m : s.mode = COMMENT) :
    False := by
  rcases sh with ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩ | ⟨mm, r⟩
  all_goals first
    | (exfalso; rw [m] at mm; revert mm; decide)
    | exact absurd rfl id

end ShortAtElim

theorem LeaveShort.of_state {c : Ctx} {h : Heap} {l : IL} {zs : Nat} {s : InflateState}
    (st : c.st = some (.tab zs)) (hs : h.istates zs = some s)
    (short : ShortAt h s (natBits l.bits.toNat l.hold.toNat)) : LeaveShort c h l := by
  intro zs' s' st' hs'
  rw [st] at st'
  cases st'
  rw [hs] at hs'
  cases hs'
  exact short

/-- The input read so far is comparable with no valid full-window stream. -/
def LoopRefuted (f : LoopFrame) (l : IL) : Prop :=
  ∀ source decoded, Api.Layer.Decodes f.wrap f.configured f.dict source decoded →
    Api.FullWindow f.wrap f.configured source →
    ¬ ((f.logIn ++ f.inp.take (loopRead l)) <+: source ∨
      source <+: (f.logIn ++ f.inp.take (loopRead l)))

theorem LoopRefuted.doomed {f : LoopFrame} {l : IL} (refuted : LoopRefuted f l) :
    LoopDoomed f l :=
  fun source decoded valid full started => refuted source decoded valid full (Or.inl started)

/-- Refutation is kept when more input is read. -/
theorem LoopRefuted.more {f : LoopFrame} {l l' : IL} (refuted : LoopRefuted f l)
    (more : loopRead l ≤ loopRead l') : LoopRefuted f l' := by
  intro source decoded valid full cmp
  have shorter : f.logIn ++ f.inp.take (loopRead l) <+: f.logIn ++ f.inp.take (loopRead l') := by
    rw [List.prefix_append_right_inj]
    have e : f.inp.take (loopRead l) = (f.inp.take (loopRead l')).take (loopRead l) := by
      rw [List.take_take, Nat.min_eq_left more]
    rw [e]
    exact List.take_prefix _ _
  apply refuted source decoded valid full
  rcases cmp with p | p
  · exact Or.inl (shorter.trans p)
  · exact List.prefix_or_prefix_of_prefix shorter p

/-- A complete header the input read begins is a beginning of every valid
stream comparable with that input. -/
theorem header_of_cmp {wrap : Api.Wrap} {configured : Nat}
    {dict header bodyDict read source decoded : List UInt8}
    (wrapHeader : WrapHeader wrap configured dict header bodyDict)
    (valid : Api.Layer.Decodes wrap configured dict source decoded)
    (bp : bytesToBits header <+: bytesToBits read) (cmp : read <+: source ∨ source <+: read) :
    header <+: source := by
  have hp := bytesToBits_prefix_iff.mp bp
  rcases cmp with p | p
  · exact hp.trans p
  · rcases List.prefix_or_prefix_of_prefix hp p with q | q
    · exact q
    · exact (not_prefix_header wrapHeader valid q).elim

/-- A valid stream that ends inside the bits read after a complete header:
its blocks run over the deflate bits read and stop inside them. -/
theorem ended_resid {f : LoopFrame} {l : IL} {header bodyDict source decoded : List UInt8}
    {dbits rest : List Bool} {pos : DeflatePos}
    (wrapHeader : WrapHeader f.wrap f.configured f.dict header bodyDict)
    (dparsed : DeflateParsed bodyDict dbits pos)
    (bits : bytesToBits (f.logIn ++ f.inp.take (loopRead l)) = bytesToBits header ++ dbits ++ rest)
    (valid : Api.Layer.Decodes f.wrap f.configured f.dict source decoded)
    (ended : source <+: f.logIn ++ f.inp.take (loopRead l)) :
    header <+: source ∧ (dbits ++ rest).length % 8 = 0 ∧
      ∃ tail, Resid bodyDict pos rest tail decoded := by
  obtain ⟨Q, eqQ⟩ := ended
  have eq : bytesToBits header ++ (dbits ++ rest) = bytesToBits source ++ bytesToBits Q := by
    rw [← bytesToBits_append', eqQ, bits, List.append_assoc]
  have headerPre : header <+: source := by
    rcases bytes_cmp eq with p | p
    · exact p
    · exact (not_prefix_header wrapHeader valid p).elim
  obtain ⟨rest', xAligned, blocks, _⟩ :=
    header_split wrapHeader valid eq (by rw [bytesToBits_length']; omega)
  exact ⟨headerPre, xAligned, rest' ++ bytesToBits Q,
    deflateParsed_resid dparsed rest (rest' ++ bytesToBits Q) decoded xAligned blocks⟩

/-- A stuck body position refutes the input read so far. -/
theorem LoopRefuted.of_stuck {f : LoopFrame} {l : IL} (stuck : LoopStuck f l) :
    LoopRefuted f l := by
  intro source decoded valid full cmp
  rcases cmp with started | ended
  · exact LoopDoomed.of_stuck stuck source decoded valid full started
  · obtain ⟨consumed, rest, header, pos, bits, parsed, never⟩ := stuck
    obtain ⟨bodyDict, dbits, wrapHeader, rfl, dparsed⟩ := parsed
    obtain ⟨_, _, tail, resid⟩ := ended_resid wrapHeader dparsed bits valid ended
    exact never source full bodyDict wrapHeader [] tail decoded (by simpa using resid)

/-- A position whose continuation, read on byte-aligned input, has no parse
refutes the input read so far (`doomed_of_aligned`). -/
theorem refuted_of_aligned {f : LoopFrame} {l : IL} {header bodyDict : List UInt8}
    {dbits rest : List Bool} {pos : DeflatePos}
    (wrapHeader : WrapHeader f.wrap f.configured f.dict header bodyDict)
    (dparsed : DeflateParsed bodyDict dbits pos)
    (bits : bytesToBits (f.logIn ++ f.inp.take (loopRead l)) = bytesToBits header ++ dbits ++ rest)
    (never : ∀ more tail outF, (dbits ++ (rest ++ more)).length % 8 = 0 →
      ¬ Resid bodyDict pos (rest ++ more) tail outF) :
    LoopRefuted f l := by
  intro source decoded valid full cmp
  rcases cmp with started | ended
  · obtain ⟨more, tail, aligned, sourceBits, blocks, _⟩ :=
      body_on_source wrapHeader valid started bits
    have whole := bytesToBits_prefix_iff.mpr started
    rw [bits, sourceBits] at whole
    have inner : rest <+: more := by
      have := (List.prefix_append_right_inj (bytesToBits header)).mp
        (by simpa only [List.append_assoc] using whole)
      exact (List.prefix_append_right_inj dbits).mp this
    obtain ⟨more', rfl⟩ := inner
    exact never more' tail decoded (by simpa only [List.append_assoc] using aligned)
      (deflateParsed_resid dparsed (rest ++ more') tail decoded
        (by simpa only [List.append_assoc] using aligned)
        (by simpa only [List.append_assoc] using blocks))
  · obtain ⟨_, aligned, tail, resid⟩ := ended_resid wrapHeader dparsed bits valid ended
    exact never [] tail decoded (by simpa using aligned) (by simpa using resid)

/-- `refuted_of_aligned`, where the rejection may use the full window and
the header of the source at hand (`doomed_of_aligned_full`). -/
theorem refuted_of_aligned_full {f : LoopFrame} {l : IL} {header bodyDict : List UInt8}
    {dbits rest : List Bool} {pos : DeflatePos}
    (wrapHeader : WrapHeader f.wrap f.configured f.dict header bodyDict)
    (dparsed : DeflateParsed bodyDict dbits pos)
    (bits : bytesToBits (f.logIn ++ f.inp.take (loopRead l)) = bytesToBits header ++ dbits ++ rest)
    (never : ∀ source, Api.FullWindow f.wrap f.configured source → header <+: source →
      ∀ more tail outF, ¬ Resid bodyDict pos (rest ++ more) tail outF) :
    LoopRefuted f l := by
  intro source decoded valid full cmp
  have pre : header <+: source := by
    rcases cmp with started | ended
    · have bp : bytesToBits header <+: bytesToBits (f.logIn ++ f.inp.take (loopRead l)) := by
        rw [bits]
        exact ⟨dbits ++ rest, by simp⟩
      exact (bytesToBits_prefix_iff.mp bp).trans started
    · exact (ended_resid wrapHeader dparsed bits valid ended).1
  exact refuted_of_aligned wrapHeader dparsed bits
    (fun more tail outF _ => never source full pre more tail outF) source decoded valid full cmp

/-- Two code-length meanings of one table decode alike. -/
theorem codeLengthMeaning_decode {codes : Array Code} {offset root : Nat} {cl cl' : List Nat}
    (m : Zlib.Inftrees.Proofs.CodeLengthMeaning codes offset root cl)
    (m' : Zlib.Inftrees.Proofs.CodeLengthMeaning codes offset root cl') (inp : List Bool) :
    decodeSym cl inp = decodeSym cl' inp := by
  have one : ∀ {a b : List Nat}, Zlib.Inftrees.Proofs.CodeLengthMeaning codes offset root a →
      Zlib.Inftrees.Proofs.CodeLengthMeaning codes offset root b →
      ∀ symbol rest, decodeSym a inp = some (symbol, rest) → decodeSym b inp = some (symbol, rest) := by
    intro a b ma mb symbol rest d
    obtain ⟨value, suffix, entry, rd, get, op, val, _, fits, restEq⟩ := ma.forward inp rest symbol d
    obtain ⟨symbol', _, val', _, d'⟩ := mb.sound inp suffix value entry rd get op fits
    rw [d', restEq, ← val, ← val']
  cases d : decodeSym cl inp with
  | some p =>
    obtain ⟨symbol, rest⟩ := p
    exact (one m m' symbol rest d).symm
  | none =>
    cases d' : decodeSym cl' inp with
    | none => rfl
    | some p =>
      obtain ⟨symbol, rest⟩ := p
      rw [one m' m symbol rest d'] at d
      cases d

/-- A code-length item is one of every code-length meaning of the table. -/
theorem codeLenItem_meaning {codes : Array Code} {offset root : Nat} {cl cl' : List Nat}
    (m : Zlib.Inftrees.Proofs.CodeLengthMeaning codes offset root cl)
    (m' : Zlib.Inftrees.Proofs.CodeLengthMeaning codes offset root cl') {held : List Bool}
    (item : CodeLenItem cl' held) : CodeLenItem cl held := by
  obtain ⟨symbol, r1, x, r2, d, rb⟩ := item
  exact ⟨symbol, r1, x, r2, by rw [codeLengthMeaning_decode m m']; exact d, rb⟩

end Zlib.Inflate.Proofs
