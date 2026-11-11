import ZlibF.Proof.«deflate.c.universal-call-extra»

/-!
# deflate.c: the gzip name and comment stages of one `deflate` call

Batch C (`call_frame`, `deflate_header_trailer`). `gz_string_loop` copies the name or comment of
the caller's header record into `pending_buf` byte by byte, through its NUL, flushing whenever
`pending_buf` is full. The string is a C string at the call (`HeaderMemory`) and lies apart from
the output range and the stream's storage (`DeflateHeaderApart`), so the flushes keep it.
-/

namespace Zlib.Deflate.Universal.Call
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Deflate.Engine.Proofs
open Zlib.Trees.Proofs.Out (TreesInvAt BitsDiff)
set_option autoImplicit false

/-! ## A `do ... while` rule with a measure -/

theorem cdoWhile_go_measure {σ : Type} {body : σ → M σ} {cond : σ → M (Bool × σ)}
    (I : σ → Heap → Prop) (Q : σ → Heap → Prop) (μ : σ → Heap → Nat)
    (step : ∀ s h, I s h → ∃ s1 h1 c s2 h2, body s h = .ok (s1, h1) ∧ cond s1 h1 = .ok ((c, s2), h2) ∧
      (c = true → I s2 h2 ∧ μ s2 h2 < μ s h) ∧ (c = false → Q s2 h2)) :
    ∀ n s h, I s h → μ s h < n → ∃ s' h', cdoWhile.go body cond n s h = .ok (s', h') ∧ Q s' h' := by
  intro n
  induction n with
  | zero => intro s h _ bound; omega
  | succ n ih =>
    intro s h inv bound
    obtain ⟨s1, h1, c, s2, h2, runB, runC, more, stop⟩ := step s h inv
    cases c with
    | false => exact ⟨s2, h2, by simp [cdoWhile.go, runB, runC], stop rfl⟩
    | true =>
      obtain ⟨inv2, less⟩ := more rfl
      obtain ⟨s', h', go, q⟩ := ih s2 h2 inv2 (by omega)
      exact ⟨s', h', by simp [cdoWhile.go, runB, runC, go], q⟩

theorem cdoWhile_measure {σ : Type} {body : σ → M σ} {cond : σ → M (Bool × σ)}
    (I : σ → Heap → Prop) (Q : σ → Heap → Prop) (μ : σ → Heap → Nat)
    (step : ∀ s h, I s h → ∃ s1 h1 c s2 h2, body s h = .ok (s1, h1) ∧ cond s1 h1 = .ok ((c, s2), h2) ∧
      (c = true → I s2 h2 ∧ μ s2 h2 < μ s h) ∧ (c = false → Q s2 h2))
    {s : σ} {h : Heap} (inv : I s h) (bound : μ s h < fuel) :
    ∃ s' h', cdoWhile body cond s h = .ok (s', h') ∧ Q s' h' :=
  cdoWhile_go_measure I Q μ step fuel s h inv bound

/-! ## Ranges -/

theorem advance_advance (p : BPtr) (a b : Nat) : advance (advance p a) b = advance p (a + b) := by
  cases p <;> simp [advance, Nat.add_assoc]

theorem byteRoot_advance {p : BPtr} {k b : Nat} : ByteRoot (advance p k) b ↔ ByteRoot p b := by
  cases p with
  | null => simp [advance, ByteRoot]
  | ref r i => cases r <;> simp [advance, ByteRoot]

/-- A later part of a range is separate from whatever the whole range is separate from. -/
theorem separate_later {p q : BPtr} {n m k : Nat} (sep : Separate p n q m) (le : k ≤ n) :
    Separate (advance p k) (n - k) q m := by
  cases p with
  | null => simp [Separate, advance]
  | ref r i =>
    cases q with
    | null => simp [Separate, advance]
    | ref s j =>
      simp only [Separate, advance] at sep ⊢
      rcases sep with e | e | e | e | e
      · exact Or.inl (by omega)
      · exact Or.inr (Or.inl e)
      · exact Or.inr (Or.inr (Or.inl e))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (by omega))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (by omega))))

/-- A range separate from the output stays separate from what is left of the output. -/
theorem separate_advance {p q : BPtr} {n m produced m' : Nat} (sep : Separate p n q m)
    (left : m' + produced = m) : Separate p n (advance q produced) m' := by
  cases p with
  | null => simp [Separate]
  | ref r i =>
    cases q with
    | null => simp [Separate, advance]
    | ref s j =>
      simp only [Separate, advance] at sep ⊢
      rcases sep with e | e | e | e | e
      · exact Or.inl e
      · exact Or.inr (Or.inl (by omega))
      · exact Or.inr (Or.inr (Or.inl e))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (by omega))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (by omega))))

/-! ## The parts of `gz_string_loop` -/

/-- Read the next string byte into `pending_buf`. -/
def strRead (s : DeflateStatePtr) (sel : GzHeader → BPtr) (st : StrS) : M StrS := do
  let d ← ldDeflateState s
  let gh ← ldGzHeader d.gzhead
  let b ← index8 (sel gh) d.gzindex.toNat
  wr s (fun d => { d with gzindex := d.gzindex + 1 })
  put_byte s b
  pure { st with val := b.toUInt32.toInt32 }

/-- One iteration: flush a full `pending_buf` (with its early return), then read a byte. -/
def strBody (strm : ZStreamPtr) (s : DeflateStatePtr) (sel : GzHeader → BPtr) (st : StrS) : M StrS := do
  let d ← ldDeflateState s
  if d.pending == d.pending_buf_size then
    HCRC_UPDATE strm s st.beg
    flush_pending strm
    if (← rd s (·.pending)) != 0 then
      wr s (fun d => { d with last_flush := -1 })
      return { st with ret := true }
    strRead s sel { st with beg := 0 }
  else
    strRead s sel st

def strCond (st : StrS) : M (Bool × StrS) := pure (!st.ret && st.val != 0, st)

theorem string_loop_split (strm : ZStreamPtr) (s : DeflateStatePtr) (sel : GzHeader → BPtr) :
    gz_string_loop strm s sel = (do
      let beg ← rd s (·.pending)
      let st ← cdoWhile (strBody strm s sel) strCond { beg, val := 0, ret := false }
      if st.ret then return true
      HCRC_UPDATE strm s st.beg
      return false) := by
  delta gz_string_loop strBody strRead strCond
  exact rfl

end Zlib.Deflate.Universal.Call
