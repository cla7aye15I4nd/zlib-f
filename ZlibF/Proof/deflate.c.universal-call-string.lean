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

theorem slice_head {a : Array UInt8} {i n : Nat} {ys : List UInt8} (fits : i + n ≤ a.size) (pos : 1 ≤ n)
    (slice : ys = (a.toList.drop i).take n) : ys[0]? = a[i]? := by
  subst slice
  simp only [List.getElem?_take, List.getElem?_drop, Array.getElem?_toList]
  simp [show 0 < n by omega]

/-- **One string byte.** `strRead` copies the byte at `gzindex` into `pending_buf`. -/
theorem str_read {h : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream} {d : DeflateState}
    {buf : Array UInt8} (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) (cursor : d.pending_out = d.pending_buf)
    {i : Nat} {g : GzHeader} (record : d.gzhead = some (.tab i)) (getg : h.gzheaders i = some g)
    (sel : GzHeader → BPtr) {xs : List UInt8} (gzLe : d.gzindex.toNat ≤ xs.length)
    (unread : Bytes h (advance (sel g) d.gzindex.toNat) (xs.length + 1 - d.gzindex.toNat)
      ((xs ++ [0]).drop d.gzindex.toNat))
    (room : d.pending.toNat < buf.size) (st : StrS) :
    ∃ (c : UInt8) (after : Heap) (next : Array UInt8),
      (xs ++ [0])[d.gzindex.toNat]? = some c ∧
      strRead (some (.tab ds)) sel st h = .ok ({ st with val := c.toUInt32.toInt32 }, after) ∧
      DGood after r ds z { d with gzindex := d.gzindex + 1, pending := d.pending + 1 } ∧
      TreesInvAt after ds { d with gzindex := d.gzindex + 1, pending := d.pending + 1 } pb next ∧
      next.size = buf.size ∧ StreamBuffers after r ∧ HeaderFrame h after pb ∧
      (d.pending + 1).toNat = d.pending.toNat + 1 := by
  have ldg : ldGzHeader d.gzhead h = .ok (g, h) := by
    rw [record]; simp only [ldGzHeader, GzHeaderRef.get, getg]
  rcases unread with ⟨e, _, _⟩ | ⟨rp, ip, a, ptr, get, fits, slice⟩
  · exfalso; simp at *; omega
  have ptr' : ∃ so, sel g = .ref rp so ∧ ip = so + d.gzindex.toNat := by
    cases hs : sel g with
    | null => rw [hs] at ptr; simp [advance] at ptr
    | ref r0 so =>
      rw [hs] at ptr; simp only [advance, Ptr.ref.injEq] at ptr
      exact ⟨so, by rw [ptr.1], ptr.2.symm⟩
  obtain ⟨so, selEq, ipEq⟩ := ptr'
  have lt : so + d.gzindex.toNat < a.size := by omega
  have head := slice_head fits (by omega) slice
  rw [List.getElem?_drop, Nat.add_zero] at head
  have readOk := Ptr.index_ok (r := rp) (off := so) (i := d.gzindex.toNat) get lt
  unfold OkOn at readOk
  obtain ⟨goodW, treesW, buffersW, frameW⟩ := gzindex_engine good trees buffers (d.gzindex + 1)
  obtain ⟨runB, goodB, treesB, buffersB, _, _, countB, sizeB, _⟩ :=
    header_byte (ob := 0) goodW treesW buffersW cursor room a[so + d.gzindex.toNat]
  refine ⟨a[so + d.gzindex.toNat], _, _, ?_, ?_, goodB, treesB, sizeB, buffersB,
    frameW.trans (HeaderFrame.byte pb goodW.live.hs buf _), countB⟩
  · rw [head, ipEq]; exact Array.getElem?_eq_getElem lt
  · unfold strRead
    simp only [bind_app, ldDeflateState_tab good.live.hs, ldg, selEq, readOk, wrD_eq, good.live.hs]
    rw [runB]
    rfl

end Zlib.Deflate.Universal.Call
