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

/-- **One iteration of the string loop.** -/
theorem str_body {h : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream} {d : DeflateState}
    {buf : Array UInt8} (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) (cursor : d.pending_out = d.pending_buf) (low : d.bi_valid.toInt < 8)
    (out : z.next_out ≠ .null) (globals : LibraryGlobals h)
    {i : Nat} {g : GzHeader} (record : d.gzhead = some (.tab i)) (getg : h.gzheaders i = some g)
    (sel : GzHeader → BPtr) {xs : List UInt8} (gzLe : d.gzindex.toNat ≤ xs.length)
    (unread : Bytes h (advance (sel g) d.gzindex.toNat) (xs.length + 1 - d.gzindex.toNat)
      ((xs ++ [0]).drop d.gzindex.toNat))
    (apart : Separate (advance (sel g) d.gzindex.toNat) (xs.length + 1 - d.gzindex.toNat)
      z.next_out z.avail_out.toNat)
    (notOwned : ∀ b, ByteRoot (sel g) b → ¬ StreamOwned h r b)
    (st : StrS) (notRet : st.ret = false) (begLe : st.beg.toNat ≤ d.pending.toNat)
    (pendLe : d.pending.toNat ≤ buf.size) :
    ∃ (st1 : StrS) (after : Heap) (z1 : ZStream) (d1 : DeflateState) (produced : Nat),
      strBody (some r) (some (.tab ds)) sel st h = .ok (st1, after) ∧
      DGood after r ds z1 d1 ∧ StreamBuffers after r ∧ StreamAccounting z z1 0 produced ∧
      (∃ buf', TreesInvAt after ds d1 pb buf' ∧ buf'.size = buf.size) ∧
      after.gzheaders i = some g ∧ after.static = h.static ∧
      d1.status = d.status ∧ d1.gzhead = d.gzhead ∧ d1.bi_valid = d.bi_valid ∧
      d1.pending_buf = d.pending_buf ∧ d1.pending_buf_size = d.pending_buf_size ∧ z1.next_out ≠ .null ∧
      (st1.ret = true → d1.pending ≠ 0 ∧ d1.last_flush = -1 ∧ (1 ≤ produced ∨ z.avail_out.toNat = 0)) ∧
      (st1.ret = false → ∃ c, (xs ++ [0])[d.gzindex.toNat]? = some c ∧ st1.val = c.toUInt32.toInt32 ∧
        d1.gzindex = d.gzindex + 1 ∧ d1.pending_out = d1.pending_buf ∧ st1.beg.toNat ≤ d1.pending.toNat ∧
        d1.pending.toNat ≤ buf.size ∧ d1.last_flush = d.last_flush ∧
        (produced = 0 → d1.pending.toNat = d.pending.toNat + 1) ∧
        Bytes after (advance (sel g) d.gzindex.toNat) (xs.length + 1 - d.gzindex.toNat)
          ((xs ++ [0]).drop d.gzindex.toNat) ∧
        Separate (advance (sel g) d.gzindex.toNat) (xs.length + 1 - d.gzindex.toNat)
          z1.next_out z1.avail_out.toNat ∧
        (∀ b, ByteRoot (sel g) b → ¬ StreamOwned after r b)) := by
  have psize := trees.base.psize
  have bufLo : 512 ≤ buf.size := by have := trees.base.size; have := trees.base.lit_lo; omega
  have rootNotPb : ∀ rs so, advance (sel g) d.gzindex.toNat = .ref rs so → rs ≠ .blk pb := by
    intro rs so e same
    subst same
    have root : ByteRoot (sel g) pb := by
      have : ByteRoot (advance (sel g) d.gzindex.toNat) pb := by rw [e]; rfl
      exact byteRoot_advance.mp this
    exact notOwned pb root (owned_pending good trees).1
  -- the frame of a read step for the unread bytes
  have keepRead : ∀ {H H' : Heap}, HeaderFrame H H' pb →
      Bytes H (advance (sel g) d.gzindex.toNat) (xs.length + 1 - d.gzindex.toNat)
        ((xs ++ [0]).drop d.gzindex.toNat) →
      Bytes H' (advance (sel g) d.gzindex.toNat) (xs.length + 1 - d.gzindex.toNat)
        ((xs ++ [0]).drop d.gzindex.toNat) := by
    intro H H' frame bytes
    rcases bytes with ⟨e1, e2, e3⟩ | ⟨rp, ip, a, ptr, get, fits, slice⟩
    · exact Or.inl ⟨e1, e2, e3⟩
    · exact Or.inr ⟨rp, ip, a, ptr, by rw [frame.views rp (rootNotPb rp ip ptr)]; exact get, fits, slice⟩
  by_cases full : d.pending = d.pending_buf_size
  · have fullN : d.pending.toNat = buf.size := by rw [full, psize]
    obtain ⟨H2, z2, good2, trees2, buffers2, account2, frame2, run2⟩ :=
      hcrc_update good trees buffers globals record getg st.beg begLe
    have next2 : z2.next_out = z.next_out := by
      rw [account2.2.2.2.2.2.1]; cases z.next_out <;> rfl
    have avail2 : z2.avail_out.toNat = z.avail_out.toNat := by have := account2.2.2.2.1; omega
    have out2 : z2.next_out ≠ .null := by rw [next2]; exact out
    obtain ⟨produced, H3, z3, d3, run3, good3, trees3, buffers3, account3, copied, left, fields3, empty3,
      _adler3, gz3, static3, _sizes3⟩ := header_flush good2 trees2 buffers2 low cursor out2
    have owned2 := stream_owned_keys good good2 rfl rfl rfl rfl
    have unread2 := keepRead frame2 unread
    have unread3 := flush_keeps_bytes good2 trees2 buffers2 low cursor out2 run3 good3.live.hz account3 unread2
      (by rw [next2, show z2.avail_out = z.avail_out from UInt32.toNat_inj.mp avail2]; exact apart)
      (fun b root => by rw [owned2]; exact (byteRoot_advance.mp root) |> notOwned b)
    have owned3 := stream_owned_keys good2 good3 (by rw [fields3]) (by rw [fields3]) (by rw [fields3]) (by rw [fields3])
    have accountT : StreamAccounting z z3 0 produced := by
      simpa only [Nat.zero_add] using stream_accounting_trans account2 account3
    have producedEq : produced = min buf.size z.avail_out.toNat := by
      rw [copied, avail2, fullN]
    have pendingEq : d3.pending.toNat + produced = buf.size := by rw [left, fullN]
    have keys3 : d3.status = d.status ∧ d3.gzhead = d.gzhead ∧ d3.bi_valid = d.bi_valid ∧
        d3.pending_buf = d.pending_buf ∧ d3.pending_buf_size = d.pending_buf_size ∧ d3.gzindex = d.gzindex ∧
        d3.last_flush = d.last_flush := by
      rw [fields3]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    obtain ⟨buf3, trees3', size3⟩ := trees3
    have flushEq : ∀ K : M StrS, (do
        HCRC_UPDATE (some r) (some (.tab ds)) st.beg
        flush_pending (some r)
        K) h = K H3 := by
      intro K; simp only [bind_app, run2, run3]
    by_cases zero : d3.pending = 0
    · have room3 : d3.pending.toNat < buf3.size := by rw [zero, size3]; simp; omega
      have record3 : d3.gzhead = some (.tab i) := by rw [keys3.2.1, record]
      have gzLe3 : d3.gzindex.toNat ≤ xs.length := by rw [keys3.2.2.2.2.2.1]; exact gzLe
      obtain ⟨c, after, next, cEq, run, goodA, treesA, sizeA, buffersA, frameA, countA⟩ :=
        str_read good3 trees3' buffers3 (empty3 zero) record3 (gz3 i g (by rw [frame2.gzheaders, getg])) sel
          gzLe3 (by rw [keys3.2.2.2.2.2.1]; exact unread3) room3 { st with beg := 0 }
      have ownedA := stream_owned_keys good3 goodA rfl rfl rfl rfl
      refine ⟨{ st with beg := 0, val := c.toUInt32.toInt32 }, after, z3, _, produced, ?_, goodA, buffersA,
        accountT, ⟨next, treesA, sizeA.trans size3⟩, ?_, ?_, keys3.1, keys3.2.1, keys3.2.2.1,
        keys3.2.2.2.1, keys3.2.2.2.2.1, ?_, fun e => Bool.noConfusion (notRet.symm.trans e), fun _ => ?_⟩
      · unfold strBody
        simp only [bind_app, ldDeflateState_tab good.live.hs, full, beq_self_eq_true, ite_true]
        rw [run2]; simp only []
        rw [run3]
        simp only [rdD_eq, good3.live.hs, zero, bne_self_eq_false, Bool.false_eq_true, ite_false]
        exact run
      · rw [frameA.gzheaders]; exact gz3 i g (by rw [frame2.gzheaders, getg])
      · rw [frameA.static, static3, frame2.static]
      · rw [account3.2.2.2.2.2.1]; exact advance_ne_null out2 _
      · refine ⟨c, by rw [keys3.2.2.2.2.2.1] at cEq; exact cEq, rfl, by rw [keys3.2.2.2.2.2.1], empty3 zero,
          by simp, ?_, by rw [keys3.2.2.2.2.2.2], fun none => ?_, ?_, ?_, ?_⟩
        · change (d3.pending + 1).toNat ≤ buf.size; rw [countA, zero]; simp; omega
        · exfalso; rw [zero] at pendingEq; simp at pendingEq; omega
        · exact keepRead frameA unread3
        · rw [account3.2.2.2.2.2.1]
          apply separate_advance _ account3.2.2.2.1
          rw [next2, show z2.avail_out = z.avail_out from UInt32.toNat_inj.mp avail2]; exact apart
        · intro b root; rw [ownedA, owned3, owned2]; exact notOwned b root
    · obtain ⟨good5, buffers5, frame5⟩ := last_flush_frame (pb := pb) good3 trees3' buffers3 (-1)
      refine ⟨{ st with ret := true }, _, z3, _, produced, ?_, good5, buffers5, accountT,
        ⟨buf3, trees_at_buffer good5 trees3'.base.pbuf trees3'.base.bytes, size3⟩, ?_, ?_,
        keys3.1, keys3.2.1, keys3.2.2.1, keys3.2.2.2.1, keys3.2.2.2.2.1, ?_,
        fun _ => ⟨zero, rfl, ?_⟩, fun e => Bool.noConfusion e⟩
      · unfold strBody
        simp only [bind_app, ldDeflateState_tab good.live.hs, full, beq_self_eq_true, ite_true]
        rw [run2]; simp only []
        rw [run3]
        simp [rdD_eq, good3.live.hs, zero, wrD_eq]
      · rw [frame5.gzheaders]; exact gz3 i g (by rw [frame2.gzheaders, getg])
      · rw [frame5.static, static3, frame2.static]
      · rw [account3.2.2.2.2.2.1]; exact advance_ne_null out2 _
      · by_cases a0 : z.avail_out.toNat = 0
        · exact Or.inr a0
        · left; rw [producedEq]; omega
  · have room : d.pending.toNat < buf.size := by
      have : d.pending.toNat ≠ d.pending_buf_size.toNat := fun e => full (UInt64.toNat_inj.mp e)
      omega
    obtain ⟨c, after, next, cEq, run, goodA, treesA, sizeA, buffersA, frameA, countA⟩ :=
      str_read good trees buffers cursor record getg sel gzLe unread room st
    have owned := stream_owned_keys good goodA rfl rfl rfl rfl
    refine ⟨{ st with val := c.toUInt32.toInt32 }, after, z, _, 0, ?_, goodA, buffersA, stream_accounting_zero z,
      ⟨next, treesA, sizeA⟩, by rw [frameA.gzheaders, getg], frameA.static, rfl, rfl, rfl, rfl, rfl, out,
      fun e => Bool.noConfusion (notRet.symm.trans e), fun _ => ⟨c, cEq, rfl, rfl, cursor, ?_, ?_, rfl, fun _ => countA,
        keepRead frameA unread, apart, fun b root => by rw [owned]; exact notOwned b root⟩⟩
    · unfold strBody
      simp only [bind_app, ldDeflateState_tab good.live.hs, beq_eq_false_iff_ne.mpr full, Bool.false_eq_true,
        ite_false]
      exact run
    · change st.beg.toNat ≤ (d.pending + 1).toNat; omega
    · change (d.pending + 1).toNat ≤ buf.size; omega

end Zlib.Deflate.Universal.Call
