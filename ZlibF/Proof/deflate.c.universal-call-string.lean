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
    (keys : ∀ b, ByteRoot (sel g) b → b ≠ pb ∧ b ≠ ds)
    (st : StrS) (notRet : st.ret = false) (begLe : st.beg.toNat ≤ d.pending.toNat)
    (pendLe : d.pending.toNat ≤ buf.size) :
    ∃ (st1 : StrS) (after : Heap) (z1 : ZStream) (d1 : DeflateState) (produced : Nat),
      strBody (some r) (some (.tab ds)) sel st h = .ok (st1, after) ∧
      DGood after r ds z1 d1 ∧ StreamBuffers after r ∧ StreamAccounting z z1 0 produced ∧
      (∃ buf', TreesInvAt after ds d1 pb buf' ∧ buf'.size = buf.size) ∧
      after.gzheaders i = some g ∧ after.static = h.static ∧
      d1.status = d.status ∧ d1.gzhead = d.gzhead ∧ d1.bi_valid = d.bi_valid ∧
      d1.pending_buf = d.pending_buf ∧ d1.pending_buf_size = d.pending_buf_size ∧ z1.next_out ≠ .null ∧
      CallerKeep h after z ds pb ∧
      (st1.ret = true → d1.pending ≠ 0 ∧ d1.last_flush = -1 ∧ (1 ≤ produced ∨ z.avail_out.toNat = 0)) ∧
      (st1.ret = false → ∃ c, (xs ++ [0])[d.gzindex.toNat]? = some c ∧ st1.val = c.toUInt32.toInt32 ∧
        d1.gzindex = d.gzindex + 1 ∧ d1.pending_out = d1.pending_buf ∧ st1.beg.toNat ≤ d1.pending.toNat ∧
        d1.pending.toNat ≤ buf.size ∧ d1.last_flush = d.last_flush ∧
        (produced = 0 → d1.pending.toNat = d.pending.toNat + 1) ∧
        Bytes after (advance (sel g) d.gzindex.toNat) (xs.length + 1 - d.gzindex.toNat)
          ((xs ++ [0]).drop d.gzindex.toNat) ∧
        Separate (advance (sel g) d.gzindex.toNat) (xs.length + 1 - d.gzindex.toNat)
          z1.next_out z1.avail_out.toNat) := by
  have psize := trees.base.psize
  have bufLo : 512 ≤ buf.size := by have := trees.base.size; have := trees.base.lit_lo; omega
  have rootNotPb : ∀ rs so, advance (sel g) d.gzindex.toNat = .ref rs so → rs ≠ .blk pb := by
    intro rs so e same
    subst same
    have root : ByteRoot (sel g) pb := by
      have : ByteRoot (advance (sel g) d.gzindex.toNat) pb := by rw [e]; rfl
      exact byteRoot_advance.mp this
    exact (keys pb root).1 rfl
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
      (fun b root => keys b (byteRoot_advance.mp root))
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
    have keepF : CallerKeep h H3 z ds pb :=
      (CallerKeep.of_frame frame2).trans (CallerKeep.of_flush good2 trees2 buffers2 low cursor out2 run3
        good3.live.hz account3) account2
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
        keys3.2.2.2.1, keys3.2.2.2.2.1, ?_, keepF.trans (CallerKeep.of_frame frameA) accountT,
        fun e => Bool.noConfusion (notRet.symm.trans e), fun _ => ?_⟩
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
          by simp, ?_, by rw [keys3.2.2.2.2.2.2], fun none => ?_, ?_, ?_⟩
        · change (d3.pending + 1).toNat ≤ buf.size; rw [countA, zero]; simp; omega
        · exfalso; rw [zero] at pendingEq; simp at pendingEq; omega
        · exact keepRead frameA unread3
        · rw [account3.2.2.2.2.2.1]
          apply separate_advance _ account3.2.2.2.1
          rw [next2, show z2.avail_out = z.avail_out from UInt32.toNat_inj.mp avail2]; exact apart
    · obtain ⟨good5, buffers5, frame5⟩ := last_flush_frame (pb := pb) good3 trees3' buffers3 (-1)
      refine ⟨{ st with ret := true }, _, z3, _, produced, ?_, good5, buffers5, accountT,
        ⟨buf3, trees_at_buffer good5 trees3'.base.pbuf trees3'.base.bytes, size3⟩, ?_, ?_,
        keys3.1, keys3.2.1, keys3.2.2.1, keys3.2.2.2.1, keys3.2.2.2.2.1, ?_,
        keepF.trans (CallerKeep.of_frame frame5) accountT,
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
      CallerKeep.of_frame frameA, fun e => Bool.noConfusion (notRet.symm.trans e), fun _ => ⟨c, cEq, rfl, rfl, cursor, ?_, ?_, rfl, fun _ => countA,
        keepRead frameA unread, apart⟩⟩
    · unfold strBody
      simp only [bind_app, ldDeflateState_tab good.live.hs, beq_eq_false_iff_ne.mpr full, Bool.false_eq_true,
        ite_false]
      exact run
    · change st.beg.toNat ≤ (d.pending + 1).toNat; omega
    · change (d.pending + 1).toNat ≤ buf.size; omega

theorem bytes_later {h : Heap} {p : BPtr} {n k : Nat} {ys : List UInt8} (bytes : Bytes h p n ys) (le : k ≤ n) :
    Bytes h (advance p k) (n - k) (ys.drop k) := by
  rcases bytes with ⟨rfl, rfl, rfl⟩ | ⟨rp, ip, a, rfl, get, fits, rfl⟩
  · left; simp [advance]
  · right
    refine ⟨rp, ip + k, a, rfl, get, by omega, ?_⟩
    rw [List.drop_take, List.drop_drop]

theorem toInt32_eq_zero {c : UInt8} : c.toUInt32.toInt32 = 0 ↔ c = 0 := by
  constructor
  · intro e
    have u := congrArg Int32.toUInt32 e
    simp only [UInt32.toUInt32_toInt32] at u
    have v : c.toUInt32.toNat = 0 := by rw [u]; rfl
    rw [UInt8.toNat_toUInt32] at v
    exact UInt8.toNat_inj.mp (by rw [v]; rfl)
  · intro e; subst e; rfl

/-- The facts the string loop keeps relative to its entry (`z`, `d` on `H0`). -/
def StrBase (H0 : Heap) (r : ZStreamRef) (ds pb : Nat) (z : ZStream) (d : DeflateState)
    (buf : Array UInt8) (i : Nat) (g : GzHeader) (H : Heap) (z1 : ZStream) (d1 : DeflateState)
    (produced : Nat) : Prop :=
  DGood H r ds z1 d1 ∧ (∃ buf1, TreesInvAt H ds d1 pb buf1 ∧ buf1.size = buf.size) ∧ StreamBuffers H r ∧
  StreamAccounting z z1 0 produced ∧ H.gzheaders i = some g ∧ H.static = H0.static ∧
  d1.status = d.status ∧ d1.gzhead = d.gzhead ∧ d1.bi_valid = d.bi_valid ∧
  d1.pending_buf = d.pending_buf ∧ d1.pending_buf_size = d.pending_buf_size ∧ z1.next_out ≠ .null ∧
  CallerKeep H0 H z ds pb

/-- The head of the string loop: the next byte to read is at `gzindex`. -/
def StrHead (H0 : Heap) (r : ZStreamRef) (ds pb : Nat) (z : ZStream) (d : DeflateState)
    (buf : Array UInt8) (i : Nat) (g : GzHeader) (sel : GzHeader → BPtr) (xs : List UInt8)
    (st : StrS) (H : Heap) : Prop :=
  st.ret = false ∧ ∃ z1 d1 produced, StrBase H0 r ds pb z d buf i g H z1 d1 produced ∧
    d1.pending_out = d1.pending_buf ∧ st.beg.toNat ≤ d1.pending.toNat ∧ d1.pending.toNat ≤ buf.size ∧
    d1.last_flush = d.last_flush ∧ d1.gzindex.toNat ≤ xs.length ∧
    Bytes H (advance (sel g) d1.gzindex.toNat) (xs.length + 1 - d1.gzindex.toNat)
      ((xs ++ [0]).drop d1.gzindex.toNat) ∧
    Separate (advance (sel g) d1.gzindex.toNat) (xs.length + 1 - d1.gzindex.toNat)
      z1.next_out z1.avail_out.toNat ∧
    (produced = 0 → d.pending.toNat ≤ d1.pending.toNat)

/-- The end of the string loop. -/
def StrEnd (H0 : Heap) (r : ZStreamRef) (ds pb : Nat) (z : ZStream) (d : DeflateState)
    (buf : Array UInt8) (i : Nat) (g : GzHeader) (st : StrS) (H : Heap) : Prop :=
  ∃ z1 d1 produced, StrBase H0 r ds pb z d buf i g H z1 d1 produced ∧
    (st.ret = true → d1.pending ≠ 0 ∧ d1.last_flush = -1 ∧ (1 ≤ produced ∨ z.avail_out.toNat = 0)) ∧
    (st.ret = false → d1.pending_out = d1.pending_buf ∧ st.beg.toNat ≤ d1.pending.toNat ∧
      d1.pending.toNat ≤ buf.size ∧ d1.last_flush = d.last_flush ∧
      (produced = 0 → d.pending.toNat + 1 ≤ d1.pending.toNat))

/-- **The string loop** ends, after the NUL or with an early return. -/
theorem string_loop {H0 H : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream} {d : DeflateState}
    {buf : Array UInt8} {i : Nat} {g : GzHeader} (sel : GzHeader → BPtr) {xs : List UInt8}
    (cstring : 0 ∉ xs ∧ xs.length < 2 ^ 64) (globals : LibraryGlobals H0) (low : d.bi_valid.toInt < 8)
    (record : d.gzhead = some (.tab i)) (keys : ∀ b, ByteRoot (sel g) b → b ≠ pb ∧ b ≠ ds) (st : StrS) (head : StrHead H0 r ds pb z d buf i g sel xs st H) :
    ∃ st' H', cdoWhile (strBody (some r) (some (.tab ds)) sel) strCond st H = .ok (st', H') ∧
      StrEnd H0 r ds pb z d buf i g st' H' := by
  refine cdoWhile_measure (StrHead H0 r ds pb z d buf i g sel xs) (StrEnd H0 r ds pb z d buf i g)
    (fun _ H => match H.dstates ds with | some e => xs.length - e.gzindex.toNat | none => 0) ?_ head ?_
  · intro st H inv
    obtain ⟨notRet, z1, d1, p1, ⟨good1, ⟨buf1, trees1, size1⟩, buffers1, account1, gz1, static1, status1,
      gzhead1, bits1, pbuf1, pbs1, out1, keep1⟩, cursor1, beg1, pend1, last1, gzLe1, unread1, apart1, zero1⟩ := inv
    have globals1 : LibraryGlobals H := by unfold LibraryGlobals at globals ⊢; rw [static1, globals]
    obtain ⟨st2, H2, z2, d2, p2, run2, good2, buffers2, account2, trees2, gz2, static2, status2, gzhead2, bits2,
      pbuf2, pbs2, out2, keepB, ret2, cont2⟩ :=
      str_body good1 trees1 buffers1 cursor1 (by rw [bits1]; exact low) out1 globals1
        (by rw [gzhead1]; exact record) gz1 sel gzLe1 unread1 apart1 keys st notRet beg1 (by omega)
    have base2 : StrBase H0 r ds pb z d buf i g H2 z2 d2 (p1 + p2) := by
      obtain ⟨b2, t2, s2⟩ := trees2
      exact ⟨good2, ⟨b2, t2, s2.trans size1⟩, buffers2, stream_accounting_trans account1 account2, gz2,
        static2.trans static1, status2.trans status1, gzhead2.trans gzhead1, bits2.trans bits1,
        pbuf2.trans pbuf1, pbs2.trans pbs1, out2, keep1.trans keepB account1⟩
    have avail1 : z1.avail_out.toNat + p1 = z.avail_out.toNat := account1.2.2.2.1
    cases eRet : st2.ret
    · obtain ⟨c, cEq, val2, idx2, cursor2, beg2, pend2, last2, zero2, unread2, apart2⟩ := cont2 eRet
      by_cases atEnd : d1.gzindex.toNat = xs.length
      · have c0 : c = 0 := by
          rw [atEnd] at cEq; simp at cEq; exact cEq.symm
        refine ⟨st2, H2, false, st2, H2, run2, ?_, fun e => Bool.noConfusion e, fun _ => ?_⟩
        · unfold strCond; simp [eRet, val2, c0, pure_app]
        · refine ⟨z2, d2, p1 + p2, base2, fun e => Bool.noConfusion (eRet.symm.trans e), fun _ =>
            ⟨cursor2, beg2, by rw [← size1]; exact pend2, last2.trans last1, fun none => ?_⟩⟩
          have q1 : p1 = 0 := by omega
          have q2 : p2 = 0 := by omega
          have := zero2 q2; have := zero1 q1; omega
      · have lt : d1.gzindex.toNat < xs.length := by omega
        have cNe : c ≠ 0 := by
          intro c0
          rw [List.getElem?_append_left lt] at cEq
          exact cstring.1 (c0 ▸ List.mem_of_getElem? cEq)
        have idxN : d2.gzindex.toNat = d1.gzindex.toNat + 1 := by
          rw [idx2, UInt64.toNat_add]; simp; omega
        refine ⟨st2, H2, true, st2, H2, run2, ?_, fun _ => ⟨⟨eRet, z2, d2, p1 + p2, base2, cursor2, beg2,
          by rw [← size1]; exact pend2,
          last2.trans last1, by omega, ?_, ?_, fun none => ?_⟩, ?_⟩, fun e => Bool.noConfusion e⟩
        · unfold strCond
          have : (st2.val != 0) = true := by
            rw [val2]; exact bne_iff_ne.mpr (fun e => cNe (toInt32_eq_zero.mp e))
          simp [eRet, this, pure_app]
        · rw [idxN]
          have := bytes_later unread2 (k := 1) (by omega)
          rw [advance_advance, List.drop_drop] at this
          simpa [Nat.add_comm, Nat.sub_sub] using this
        · rw [idxN, ← advance_advance]
          have := separate_later apart2 (k := 1) (by omega)
          simpa [Nat.sub_sub] using this
        · have q1 : p1 = 0 := by omega
          have q2 : p2 = 0 := by omega
          have := zero2 q2; have := zero1 q1; omega
        · simp only [good1.live.hs, good2.live.hs]
          omega
    · obtain ⟨pend2, lf2, del2⟩ := ret2 eRet
      refine ⟨st2, H2, false, st2, H2, run2, ?_, fun e => Bool.noConfusion e, fun _ => ?_⟩
      · unfold strCond; simp [eRet, pure_app]
      · refine ⟨z2, d2, p1 + p2, base2, fun _ => ⟨pend2, lf2, ?_⟩, fun e => Bool.noConfusion (eRet.symm.trans e)⟩
        rcases del2 with d | d
        · left; omega
        · by_cases a0 : z.avail_out.toNat = 0
          · exact Or.inr a0
          · left
            have := account2.2.1
            omega
  · obtain ⟨_, z1, d1, p1, ⟨good1, _⟩, _⟩ := head
    simp only [good1.live.hs]
    unfold fuel
    omega

/-- **`gz_string_loop`**: copy the name or comment through its NUL, with the header CRC. It returns
`true` exactly at an early return, with bytes pending (a byte delivered, or no output room). -/
theorem string_copy {h : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream} {d : DeflateState}
    {buf : Array UInt8} (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) (cursor : d.pending_out = d.pending_buf) (low : d.bi_valid.toInt < 8)
    (out : z.next_out ≠ .null) (globals : LibraryGlobals h)
    {i : Nat} {g : GzHeader} (record : d.gzhead = some (.tab i)) (getg : h.gzheaders i = some g)
    (sel : GzHeader → BPtr) {xs : List UInt8} (cstring : 0 ∉ xs ∧ xs.length < 2 ^ 64)
    (gzLe : d.gzindex.toNat ≤ xs.length)
    (unread : Bytes h (advance (sel g) d.gzindex.toNat) (xs.length + 1 - d.gzindex.toNat)
      ((xs ++ [0]).drop d.gzindex.toNat))
    (apart : Separate (advance (sel g) d.gzindex.toNat) (xs.length + 1 - d.gzindex.toNat)
      z.next_out z.avail_out.toNat)
    (keys : ∀ b, ByteRoot (sel g) b → b ≠ pb ∧ b ≠ ds) (pendLe : d.pending.toNat ≤ buf.size) :
    ∃ (early : Bool) (after : Heap) (z1 : ZStream) (d1 : DeflateState) (produced : Nat),
      gz_string_loop (some r) (some (.tab ds)) sel h = .ok (early, after) ∧
      StrBase h r ds pb z d buf i g after z1 d1 produced ∧
      (early = true → d1.pending ≠ 0 ∧ d1.last_flush = -1 ∧ (1 ≤ produced ∨ z.avail_out.toNat = 0)) ∧
      (early = false → d1.pending_out = d1.pending_buf ∧ d1.pending.toNat ≤ buf.size ∧
        d1.last_flush = d.last_flush ∧ (produced = 0 → d.pending.toNat + 1 ≤ d1.pending.toNat)) := by
  let st0 : StrS := { beg := d.pending, val := 0, ret := false }
  have head : StrHead h r ds pb z d buf i g sel xs st0 h :=
    ⟨rfl, z, d, 0, ⟨good, ⟨buf, trees, rfl⟩, buffers, stream_accounting_zero z, getg, rfl, rfl, rfl, rfl, rfl, rfl,
      out, CallerKeep.refl h z ds pb⟩, cursor, Nat.le_refl _, pendLe, rfl, gzLe, unread, apart, fun _ => Nat.le_refl _⟩
  obtain ⟨st1, H1, runL, z1, d1, p1, base1, ret1, cont1⟩ :=
    string_loop sel cstring globals low record keys st0 head
  obtain ⟨good1, ⟨buf1, trees1, size1⟩, buffers1, account1, gz1, static1, status1, gzhead1, bits1, pbuf1,
    pbs1, out1, keep1⟩ := base1
  have split : gz_string_loop (some r) (some (.tab ds)) sel h =
      (do
        let st ← cdoWhile (strBody (some r) (some (.tab ds)) sel) strCond st0
        if st.ret then return true
        HCRC_UPDATE (some r) (some (.tab ds)) st.beg
        return false) h := by
    rw [string_loop_split]
    simp only [bind_app, rdD_eq, good.live.hs]
    rfl
  cases e : st1.ret
  · obtain ⟨cursor1, beg1, pend1, last1, zero1⟩ := cont1 e
    have globals1 : LibraryGlobals H1 := by unfold LibraryGlobals at globals ⊢; rw [static1, globals]
    obtain ⟨H2, z2, good2, trees2, buffers2, account2, frame2, run2⟩ :=
      hcrc_update good1 trees1 buffers1 globals1 (by rw [gzhead1]; exact record) gz1 st1.beg beg1
    refine ⟨false, H2, z2, d1, p1, ?_, ⟨good2, ⟨buf1, trees2, size1⟩, buffers2, ?_, ?_, ?_, status1, gzhead1,
      bits1, pbuf1, pbs1, ?_, keep1.trans (CallerKeep.of_frame frame2) account1⟩, fun e => Bool.noConfusion e,
      fun _ => ⟨cursor1, pend1, last1, zero1⟩⟩
    · rw [split]; simp only [bind_app, runL, e, Bool.false_eq_true, ite_false, run2, pure_app]
    · simpa only [Nat.add_zero] using stream_accounting_trans account1 account2
    · rw [frame2.gzheaders]; exact gz1
    · rw [frame2.static]; exact static1
    · rw [account2.2.2.2.2.2.1]; exact advance_ne_null out1 _
  · refine ⟨true, H1, z1, d1, p1, ?_, ⟨good1, ⟨buf1, trees1, size1⟩, buffers1, account1, gz1, static1, status1,
      gzhead1, bits1, pbuf1, pbs1, out1, keep1⟩, fun _ => ret1 e, fun e => Bool.noConfusion e⟩
    rw [split]; simp only [bind_app, runL, e, ite_true, pure_app]

/-- The facts a header stage keeps relative to its entry (`z`, `d` on `H0`); the status moves on. -/
def StageBase (H0 : Heap) (r : ZStreamRef) (ds pb : Nat) (z : ZStream) (d : DeflateState)
    (buf : Array UInt8) (i : Nat) (g : GzHeader) (H : Heap) (z1 : ZStream) (d1 : DeflateState)
    (produced : Nat) : Prop :=
  DGood H r ds z1 d1 ∧ (∃ buf1, TreesInvAt H ds d1 pb buf1 ∧ buf1.size = buf.size) ∧ StreamBuffers H r ∧
  StreamAccounting z z1 0 produced ∧ H.gzheaders i = some g ∧ H.static = H0.static ∧
  d1.gzhead = d.gzhead ∧ d1.bi_valid = d.bi_valid ∧
  d1.pending_buf = d.pending_buf ∧ d1.pending_buf_size = d.pending_buf_size ∧ z1.next_out ≠ .null

/-- What a header stage leaves, with its two outcomes. -/
def StageOut (H0 : Heap) (r : ZStreamRef) (ds pb : Nat) (z : ZStream) (d : DeflateState)
    (buf : Array UInt8) (i : Nat) (g : GzHeader) (next : Int32) (run : Except Fault (Int32 × Heap))
    (k : M Int32) : Prop :=
  ∃ (after : Heap) (z1 : ZStream) (d1 : DeflateState) (produced : Nat),
    StageBase H0 r ds pb z d buf i g after z1 d1 produced ∧ CallerKeep H0 after z ds pb ∧
    ((run = .ok (Z_OK, after) ∧ (1 ≤ produced ∨ z.avail_out.toNat = 0)) ∨
     (run = k after ∧ d1.status = next ∧ d1.pending_out = d1.pending_buf ∧ d1.pending.toNat ≤ buf.size ∧
       (produced = 0 → d.pending.toNat ≤ d1.pending.toNat) ∧
       (d.gzindex = 0 → next = COMMENT_STATE → d1.gzindex = 0)))

/-- The facts a string stage needs of the caller's name or comment. -/
def StringReady (h : Heap) (z : ZStream) (d : DeflateState) (ds pb : Nat) (p : BPtr) : Prop :=
  p ≠ .null → ∃ xs, CString h p xs ∧ d.gzindex.toNat ≤ xs.length ∧
    Separate p (xs.length + 1) z.next_out z.avail_out.toNat ∧ (∀ b, ByteRoot p b → b ≠ pb ∧ b ≠ ds)

theorem string_ready_copy {h : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream} {d : DeflateState}
    {buf : Array UInt8} (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) (cursor : d.pending_out = d.pending_buf) (low : d.bi_valid.toInt < 8)
    (out : z.next_out ≠ .null) (globals : LibraryGlobals h)
    {i : Nat} {g : GzHeader} (record : d.gzhead = some (.tab i)) (getg : h.gzheaders i = some g)
    (sel : GzHeader → BPtr) (ready : StringReady h z d ds pb (sel g)) (present : sel g ≠ .null)
    (pendLe : d.pending.toNat ≤ buf.size) :
    ∃ (early : Bool) (after : Heap) (z1 : ZStream) (d1 : DeflateState) (produced : Nat),
      gz_string_loop (some r) (some (.tab ds)) sel h = .ok (early, after) ∧
      StrBase h r ds pb z d buf i g after z1 d1 produced ∧
      (early = true → d1.pending ≠ 0 ∧ d1.last_flush = -1 ∧ (1 ≤ produced ∨ z.avail_out.toNat = 0)) ∧
      (early = false → d1.pending_out = d1.pending_buf ∧ d1.pending.toNat ≤ buf.size ∧
        d1.last_flush = d.last_flush ∧ (produced = 0 → d.pending.toNat + 1 ≤ d1.pending.toNat)) := by
  obtain ⟨xs, cs, gzLe, apart, keys⟩ := ready present
  exact string_copy good trees buffers cursor low out globals record getg sel ⟨cs.2.1, cs.2.2⟩ gzLe
    (bytes_later cs.1 (k := d.gzindex.toNat) (by omega)) (separate_later apart (by omega)) keys pendLe

/-- **The gzip name stage.** -/
theorem name_stage {h : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream} {d : DeflateState}
    {buf : Array UInt8} (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) (cursor : d.pending_out = d.pending_buf) (low : d.bi_valid.toInt < 8)
    (out : z.next_out ≠ .null) (globals : LibraryGlobals h) (status : d.status = NAME_STATE)
    {i : Nat} {g : GzHeader} (record : d.gzhead = some (.tab i)) (getg : h.gzheaders i = some g)
    (ready : StringReady h z d ds pb g.name) (pendLe : d.pending.toNat ≤ buf.size) (k : M Int32) :
    StageOut h r ds pb z d buf i g COMMENT_STATE (nameStage (some r) (some (.tab ds)) k h) k := by
  have ldg : ldGzHeader d.gzhead h = .ok (g, h) := by
    rw [record]; simp only [ldGzHeader, GzHeaderRef.get, getg]
  have st : (d.status == NAME_STATE) = true := by rw [status]; rfl
  by_cases present : g.name = .null
  · obtain ⟨good1, trees1, buffers1⟩ := status_engine good trees buffers COMMENT_STATE (by simp [GoodStatus])
    refine ⟨_, z, _, 0, ⟨good1, ⟨buf, trees1, rfl⟩, buffers1, stream_accounting_zero z, getg, rfl, rfl, rfl,
      rfl, rfl, out⟩, CallerKeep.of_frame (HeaderFrame.state pb good.live.hs _ rfl),
      Or.inr ⟨?_, rfl, cursor, pendLe, fun _ => Nat.le_refl _, fun z0 _ => z0⟩⟩
    unfold nameStage
    simp only [bind_app, rdD_eq, good.live.hs, st, ite_true, ldDeflateState_tab good.live.hs, ldg, present,
      bne_self_eq_false, Bool.false_eq_true, ite_false, wrD_eq]
  · obtain ⟨early, H1, z1, d1, p1, run1, base1, ret1, cont1⟩ :=
      string_ready_copy good trees buffers cursor low out globals record getg (·.name) ready present pendLe
    obtain ⟨good1, ⟨buf1, trees1, size1⟩, buffers1, account1, gz1, static1, status1, gzhead1, bits1, pbuf1,
      pbs1, out1, keep1⟩ := base1
    cases early
    · obtain ⟨cursor1, pend1, last1, zero1⟩ := cont1 rfl
      obtain ⟨good2, trees2, buffers2, frame2⟩ := gzindex_engine good1 trees1 buffers1 0
      obtain ⟨good3, trees3, buffers3⟩ := status_engine good2 trees2 buffers2 COMMENT_STATE (by simp [GoodStatus])
      refine ⟨_, z1, _, p1, ⟨good3, ⟨buf1, trees3, size1⟩, buffers3, account1, gz1, static1, gzhead1, bits1,
        pbuf1, pbs1, out1⟩, keep1.trans (CallerKeep.of_frame (frame2.trans
          (HeaderFrame.state pb good2.live.hs _ rfl))) account1, Or.inr ⟨?_, rfl, cursor1, pend1,
        fun none => (by have := zero1 none; change d.pending.toNat ≤ d1.pending.toNat; omega), fun _ _ => rfl⟩⟩
      unfold nameStage
      simp only [bind_app, rdD_eq, good.live.hs, st, ite_true, ldDeflateState_tab good.live.hs, ldg,
        show (g.name != .null) = true from bne_iff_ne.mpr present]
      rw [run1]
      simp [wrD_eq, good1.live.hs]
    · refine ⟨H1, z1, d1, p1, ⟨good1, ⟨buf1, trees1, size1⟩, buffers1, account1, gz1, static1, gzhead1, bits1,
        pbuf1, pbs1, out1⟩, keep1, Or.inl ⟨?_, (ret1 rfl).2.2⟩⟩
      unfold nameStage
      simp only [bind_app, rdD_eq, good.live.hs, st, ite_true, ldDeflateState_tab good.live.hs, ldg,
        show (g.name != .null) = true from bne_iff_ne.mpr present]
      rw [run1]
      simp [pure_app]

/-- **The gzip comment stage.** -/
theorem comment_stage {h : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream} {d : DeflateState}
    {buf : Array UInt8} (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) (cursor : d.pending_out = d.pending_buf) (low : d.bi_valid.toInt < 8)
    (out : z.next_out ≠ .null) (globals : LibraryGlobals h) (status : d.status = COMMENT_STATE)
    {i : Nat} {g : GzHeader} (record : d.gzhead = some (.tab i)) (getg : h.gzheaders i = some g)
    (ready : StringReady h z d ds pb g.comment) (pendLe : d.pending.toNat ≤ buf.size) (k : M Int32) :
    StageOut h r ds pb z d buf i g HCRC_STATE (commentStage (some r) (some (.tab ds)) k h) k := by
  have ldg : ldGzHeader d.gzhead h = .ok (g, h) := by
    rw [record]; simp only [ldGzHeader, GzHeaderRef.get, getg]
  have st : (d.status == COMMENT_STATE) = true := by rw [status]; rfl
  by_cases present : g.comment = .null
  · obtain ⟨good1, trees1, buffers1⟩ := status_engine good trees buffers HCRC_STATE (by simp [GoodStatus])
    refine ⟨_, z, _, 0, ⟨good1, ⟨buf, trees1, rfl⟩, buffers1, stream_accounting_zero z, getg, rfl, rfl, rfl,
      rfl, rfl, out⟩, CallerKeep.of_frame (HeaderFrame.state pb good.live.hs _ rfl),
      Or.inr ⟨?_, rfl, cursor, pendLe, fun _ => Nat.le_refl _, fun _ e => absurd e (by decide)⟩⟩
    unfold commentStage
    simp only [bind_app, rdD_eq, good.live.hs, st, ite_true, ldDeflateState_tab good.live.hs, ldg, present,
      bne_self_eq_false, Bool.false_eq_true, ite_false, wrD_eq]
  · obtain ⟨early, H1, z1, d1, p1, run1, base1, ret1, cont1⟩ :=
      string_ready_copy good trees buffers cursor low out globals record getg (·.comment) ready present pendLe
    obtain ⟨good1, ⟨buf1, trees1, size1⟩, buffers1, account1, gz1, static1, status1, gzhead1, bits1, pbuf1,
      pbs1, out1, keep1⟩ := base1
    cases early
    · obtain ⟨cursor1, pend1, last1, zero1⟩ := cont1 rfl
      obtain ⟨good3, trees3, buffers3⟩ := status_engine good1 trees1 buffers1 HCRC_STATE (by simp [GoodStatus])
      refine ⟨_, z1, _, p1, ⟨good3, ⟨buf1, trees3, size1⟩, buffers3, account1, gz1, static1, gzhead1, bits1,
        pbuf1, pbs1, out1⟩, keep1.trans (CallerKeep.of_frame
          (HeaderFrame.state pb good1.live.hs _ rfl)) account1, Or.inr ⟨?_, rfl, cursor1, pend1,
        fun none => (by have := zero1 none; change d.pending.toNat ≤ d1.pending.toNat; omega),
        fun _ e => absurd e (by decide)⟩⟩
      unfold commentStage
      simp only [bind_app, rdD_eq, good.live.hs, st, ite_true, ldDeflateState_tab good.live.hs, ldg,
        show (g.comment != .null) = true from bne_iff_ne.mpr present]
      rw [run1]
      simp [wrD_eq, good1.live.hs]
    · refine ⟨H1, z1, d1, p1, ⟨good1, ⟨buf1, trees1, size1⟩, buffers1, account1, gz1, static1, gzhead1, bits1,
        pbuf1, pbs1, out1⟩, keep1, Or.inl ⟨?_, (ret1 rfl).2.2⟩⟩
      unfold commentStage
      simp only [bind_app, rdD_eq, good.live.hs, st, ite_true, ldDeflateState_tab good.live.hs, ldg,
        show (g.comment != .null) = true from bne_iff_ne.mpr present]
      rw [run1]
      simp [pure_app]

end Zlib.Deflate.Universal.Call
