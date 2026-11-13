import ZlibF.Proof.«deflate.c.universal-call-headerphase»
import ZlibF.Proof.«deflate.c.universal-call-lift»

/-!
# deflate.c: the header phase's entry facts from the caller's domain

Batch C (`deflate_header_trailer`). `ActiveHeader` gives, at the call, the caller's gzip header
record (`HeaderMemory`) and the separation of its regions from the output (`DeflateHeaderApart`).
This file turns them into the facts of `HeaderEntry` at a later heap of the same call.
-/

namespace Zlib.Deflate.Universal.Call
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Deflate.Engine.Proofs
open Zlib.Trees.Proofs.Out (TreesInvAt BitsDiff)
set_option autoImplicit false

theorem separate_comm {p q : BPtr} {n m : Nat} (sep : Separate p n q m) : Separate q m p n := by
  cases p with
  | null => simp [Separate]
  | ref r i =>
    cases q with
    | null => simp [Separate]
    | ref s j =>
      simp only [Separate] at sep ⊢
      rcases sep with e | e | e | e | e
      · exact Or.inr (Or.inl e)
      · exact Or.inl e
      · exact Or.inr (Or.inr (Or.inl (Ne.symm e)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr e)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl e)))

theorem bytes_prefix {h : Heap} {p : BPtr} {n m : Nat} {xs : List UInt8} (bytes : Bytes h p n xs) (le : m ≤ n) :
    Bytes h p m (xs.take m) := by
  rcases bytes with ⟨rfl, rfl, rfl⟩ | ⟨rp, ip, a, rfl, get, fits, rfl⟩
  · left; exact ⟨rfl, by omega, List.take_nil⟩
  · right; refine ⟨rp, ip, a, rfl, get, by omega, ?_⟩
    rw [List.take_take, Nat.min_eq_left le]

/-- A caller range outside the stream's storage is rooted outside `pending_buf` and the state. -/
theorem keys_of_not_owned {h : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream} {d : DeflateState}
    {buf : Array UInt8} (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) {p : BPtr}
    (notOwned : ∀ b, ByteRoot p b → ¬ StreamOwned h r b) : ∀ b, ByteRoot p b → b ≠ pb ∧ b ≠ ds := by
  intro b root
  have own := owned_pending good trees
  exact ⟨fun e => notOwned b root (e ▸ own.1), fun e => notOwned b root (e ▸ own.2)⟩

/-- **The gzip stage's entry facts** at a later heap of the call, from the caller's domain at the
call: the header record, the extra field, and the name and comment as later strings. -/
theorem gzip_entry_facts {h0 h1 : Heap} {r : ZStreamRef} {ds pb produced : Nat} {z0 z1 : ZStream}
    {d0 : DeflateState} {buf0 : Array UInt8} (good0 : DGood h0 r ds z0 d0) (trees0 : TreesInvAt h0 ds d0 pb buf0)
    (writing : DeflateHeaderWriting d0) {i : Nat} (record : d0.gzhead = some (.tab i))
    (memory : HeaderMemory h0 r d0.gzhead false) (apart : DeflateHeaderApart h0 r z0 d0)
    (keep : CallerKeep h0 h1 z0 ds pb) (account : StreamAccounting z0 z1 0 produced)
    (records : h1.gzheaders = h0.gzheaders) :
    ∃ g, h1.gzheaders i = some g ∧
      (g.extra ≠ .null → ∃ rs eo ea, g.extra = .ref rs eo ∧ Space.get h1 rs = some ea ∧
        eo + g.extra_len.toNat % 2 ^ 16 ≤ ea.size ∧ rs ≠ .blk pb) ∧
      StringLater h1 z1 ds pb g.name ∧ StringLater h1 z1 ds pb g.comment := by
  rcases memory with none | ⟨i', g, ptr, getg, _, extraM, nameM, commentM⟩
  · rw [record] at none; cases none
  rw [record] at ptr
  simp only [Option.some.injEq, GzHeaderRef.tab.injEq] at ptr
  subst ptr
  simp only [Bool.false_eq_true, ite_false] at nameM commentM
  -- strings at the call
  have nameXs : ∃ xs, g.name ≠ .null → CString h0 g.name xs := by
    by_cases n : g.name = .null
    · exact ⟨[], fun e => absurd n e⟩
    · obtain ⟨xs, cs⟩ := nameM n; exact ⟨xs, fun _ => cs⟩
  have commentXs : ∃ xs, g.comment ≠ .null → CString h0 g.comment xs := by
    by_cases n : g.comment = .null
    · exact ⟨[], fun e => absurd n e⟩
    · obtain ⟨xs, cs⟩ := commentM n; exact ⟨xs, fun _ => cs⟩
  obtain ⟨nxs, ncs⟩ := nameXs
  obtain ⟨cxs, ccs⟩ := commentXs
  obtain ⟨pw, owned⟩ := apart writing i g record getg nxs cxs ncs ccs
  simp only [headerSpans, List.pairwise_cons, List.mem_cons, List.mem_singleton, List.not_mem_nil,
    forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true, implies_true] at pw
  obtain ⟨_, ⟨outExtra, outName, outComment, _⟩, _⟩ := pw
  have keysOf : ∀ p, p = g.extra ∨ p = g.name ∨ p = g.comment → ∀ b, ByteRoot p b → b ≠ pb ∧ b ≠ ds := by
    intro p mem
    apply keys_of_not_owned good0 trees0
    rcases mem with rfl | rfl | rfl
    · exact owned g.extra (by simp)
    · exact owned g.name (by simp)
    · exact owned g.comment (by simp)
  refine ⟨g, by rw [records]; exact getg, ?_, ?_, ?_⟩
  · intro present
    rcases extraM present with e | ⟨⟨xs, bytes⟩, _, _⟩
    · exact absurd e present
    have bytesL := bytes_prefix bytes (Nat.mod_le g.extra_len.toNat (2 ^ 16))
    have kept := keep _ _ _ bytesL (by simpa [present] using separate_comm outExtra) (keysOf _ (Or.inl rfl))
    rcases kept with ⟨e, _, _⟩ | ⟨rs, eo, ea, ptr, get, fits, _⟩
    · exact absurd e present
    exact ⟨rs, eo, ea, ptr, get, fits, fun same => (keysOf _ (Or.inl rfl) pb (by rw [ptr, same]; rfl)).1 rfl⟩
  · intro present
    have cs := ncs present
    refine ⟨nxs, ⟨keep _ _ _ cs.1 (by simpa [present] using separate_comm outName) (keysOf _ (Or.inr (Or.inl rfl))),
      cs.2.1, cs.2.2⟩, ?_, keysOf _ (Or.inr (Or.inl rfl))⟩
    rw [account.2.2.2.2.2.1]
    exact separate_advance (by simpa [present] using separate_comm outName) account.2.2.2.1
  · intro present
    have cs := ccs present
    refine ⟨cxs, ⟨keep _ _ _ cs.1 (by simpa [present] using separate_comm outComment)
      (keysOf _ (Or.inr (Or.inr rfl))), cs.2.1, cs.2.2⟩, ?_, keysOf _ (Or.inr (Or.inr rfl))⟩
    rw [account.2.2.2.2.2.1]
    exact separate_advance (by simpa [present] using separate_comm outComment) account.2.2.2.1

/-- The entry phase keeps the caller bytes: the `last_flush` write and the flush of pending output. -/
theorem entry_keep {h after : Heap} {r : ZStreamRef} {ds pb produced : Nat} {z z' : ZStream}
    {d : DeflateState} {buf : Array UInt8} (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) (cursor : d.pending_out = d.pending_buf) (low : d.bi_valid.toInt < 8)
    (out : z.next_out ≠ .null) (flush : Int32)
    (run : flush_pending (some r) (setD h ds { d with last_flush := flush }) = .ok ((), after))
    (live : r.get after = some z') (account : StreamAccounting z z' 0 produced) :
    CallerKeep h after z ds pb := by
  obtain ⟨good0, trees0, buffers0⟩ := last_flush_engine (pb := pb) (buf := buf) flush good trees buffers
  exact (CallerKeep.of_frame (HeaderFrame.state (r := r) pb good.live.hs { d with last_flush := flush } rfl)).trans
    (CallerKeep.of_flush good0 trees0 buffers0 low cursor out run live account) (stream_accounting_zero z)

/-- **`HeaderEntry` for a fresh header** (`INIT_STATE` or `GZIP_STATE`), at a later heap of the
call with nothing pending and output room, from `ActiveHeader` at the call. -/
theorem fresh_header_entry {h0 h1 : Heap} {r : ZStreamRef} {ds pb produced : Nat} {z0 z1 : ZStream}
    {d0 d1 : DeflateState} {buf0 buf1 : Array UInt8}
    (good0 : DGood h0 r ds z0 d0) (trees0 : TreesInvAt h0 ds d0 pb buf0) (active : ActiveHeader h0 r)
    (keep : CallerKeep h0 h1 z0 ds pb) (account : StreamAccounting z0 z1 0 produced)
    (records : h1.gzheaders = h0.gzheaders)
    (status : d1.status = d0.status) (gzhead : d1.gzhead = d0.gzhead)
    (fresh : d0.status = INIT_STATE ∨ d0.status = GZIP_STATE) (pending : d1.pending = 0)
    (avail : z1.avail_out ≠ 0) :
    HeaderEntry h1 z1 d1 ds pb buf1 := by
  obtain ⟨z, get, _, deflateHeader⟩ := active
  have same : z = z0 := Option.some.inj (get.symm.trans good0.live.hz)
  subst same
  obtain ⟨memory, _, apart⟩ := deflateHeader ds d0 good0.live.zst good0.live.hs
  refine ⟨fun _ => ⟨pending, avail⟩, fun gz => ?_, fun w => ?_, fun _ => pending⟩
  · have writing : DeflateHeaderWriting d0 := Or.inl (by rw [← status]; exact gz)
    refine ⟨?_, fun i record => ?_⟩
    · cases e : d1.gzhead with
      | none => exact Or.inl rfl
      | some ref => cases ref with | tab i => exact Or.inr ⟨i, rfl⟩
    · rw [gzhead] at record
      exact gzip_entry_facts good0 trees0 writing record (memory writing) apart keep account records
  · exfalso
    rw [status] at w
    rcases fresh with e | e <;> rw [e] at w <;> exact absurd w (by decide)



/-- **`HeaderEntry` for a resumed header** (`EXTRA_STATE` .. `HCRC_STATE`), at a later heap of the
call with nothing pending, from `ActiveHeader` at the call and the header facts `HeaderInv`
(the record is attached). The part written so far comes from `DeflateHeaderProgress`. -/
theorem resumed_header_entry {h0 h1 : Heap} {r : ZStreamRef} {ds pb produced : Nat} {z0 z1 : ZStream}
    {d0 d1 : DeflateState} {buf0 buf1 : Array UInt8}
    (good0 : DGood h0 r ds z0 d0) (trees0 : TreesInvAt h0 ds d0 pb buf0) (active : ActiveHeader h0 r)
    (header : HeaderInv d0) (keep : CallerKeep h0 h1 z0 ds pb) (account : StreamAccounting z0 z1 0 produced)
    (records : h1.gzheaders = h0.gzheaders)
    (status : d1.status = d0.status) (gzhead : d1.gzhead = d0.gzhead) (gzindex : d1.gzindex = d0.gzindex)
    (resumed : d0.status = EXTRA_STATE ∨ d0.status = NAME_STATE ∨ d0.status = COMMENT_STATE ∨
      d0.status = HCRC_STATE)
    (pending : d1.pending = 0) (room : 0 < buf1.size) :
    HeaderEntry h1 z1 d1 ds pb buf1 := by
  obtain ⟨z, get, _, deflateHeader⟩ := active
  have same : z = z0 := Option.some.inj (get.symm.trans good0.live.hz)
  subst same
  obtain ⟨memory, progress, apart⟩ := deflateHeader ds d0 good0.live.zst good0.live.hs
  have writing : DeflateHeaderWriting d0 := Or.inr resumed
  have notFresh : ¬ (d1.status = INIT_STATE ∨ d1.status = GZIP_STATE) := by
    rw [status]; intro e
    rcases resumed with x | x | x | x <;> rw [x] at e <;> rcases e with e | e <;> exact absurd e (by decide)
  have notBusy : ¬ (d1.status = BUSY_STATE ∨ d1.status = FINISH_STATE) := by
    rw [status]; intro e
    rcases resumed with x | x | x | x <;> rw [x] at e <;> rcases e with e | e <;> exact absurd e (by decide)
  refine ⟨fun e => absurd e notFresh, fun e => absurd (Or.inr e) notFresh, fun _ => ?_,
    fun e => absurd e notBusy⟩
  obtain ⟨i, record⟩ : ∃ i, d0.gzhead = some (.tab i) := by
    have attached := header.record resumed
    cases e : d0.gzhead with
    | none => exact absurd e attached
    | some ref => cases ref with | tab i => exact ⟨i, rfl⟩
  obtain ⟨g, getg1, extraMem, nameLater, commentLater⟩ :=
    gzip_entry_facts good0 trees0 writing record (memory writing) apart keep account records
  have getg0 : h0.gzheaders i = some g := by rw [← records]; exact getg1
  obtain ⟨pExtra, pName, pComment, aExtra, aName, aComment⟩ := progress i g record getg0
  have pend : d1.pending.toNat = 0 := by rw [pending]; rfl
  -- a string being written: its bytes at the call, kept to `h1`, and its range apart from the output
  have readyOf : ∀ (p : BPtr), (p ≠ .null → ∃ ys, CString h0 p ys ∧ d0.gzindex.toNat ≤ ys.length ∧
      Separate p (ys.length + 1) z.next_out z.avail_out.toNat ∧ (∀ b, ByteRoot p b → b ≠ pb ∧ b ≠ ds)) →
      StringReady h1 z1 d1 ds pb p := by
    intro p prog present
    obtain ⟨ys, cs0, le, sep, keys⟩ := prog present
    refine ⟨ys, ⟨keep p _ _ cs0.1 sep keys, cs0.2.1, cs0.2.2⟩, by rw [gzindex]; exact le, ?_, keys⟩
    rw [account.2.2.2.2.2.1]
    exact separate_advance sep account.2.2.2.1
  -- the strings of the record at the call
  have strings : (∃ nxs, g.name ≠ .null → CString h0 g.name nxs) ∧
      (∃ cxs, g.comment ≠ .null → CString h0 g.comment cxs) := by
    rcases memory writing with none | ⟨i', g', ptr, getg', _, _, nameM, commentM⟩
    · rw [record] at none; cases none
    rw [record] at ptr
    simp only [Option.some.injEq, GzHeaderRef.tab.injEq] at ptr
    subst ptr
    have gg : g' = g := Option.some.inj (getg'.symm.trans getg0)
    subst gg
    simp only [Bool.false_eq_true, ite_false] at nameM commentM
    refine ⟨?_, ?_⟩
    · by_cases n : g'.name = .null
      · exact ⟨[], fun e => absurd n e⟩
      · obtain ⟨xs, cs⟩ := nameM n; exact ⟨xs, fun _ => cs⟩
    · by_cases n : g'.comment = .null
      · exact ⟨[], fun e => absurd n e⟩
      · obtain ⟨xs, cs⟩ := commentM n; exact ⟨xs, fun _ => cs⟩
  obtain ⟨⟨nxs, ncs⟩, ⟨cxs, ccs⟩⟩ := strings
  have nameReady : d0.status = NAME_STATE → StringReady h1 z1 d1 ds pb g.name := by
    intro e
    apply readyOf
    intro present
    obtain ⟨ys, cs0, le⟩ := pName e present
    obtain ⟨pw, _⟩ := apart writing i g record getg0 ys cxs (fun _ => cs0) ccs
    simp only [headerSpans, List.pairwise_cons, List.mem_cons, List.mem_singleton, List.not_mem_nil,
      forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true, implies_true] at pw
    obtain ⟨_, ⟨_, outName, _, _⟩, _⟩ := pw
    obtain ⟨_, _, _, keys⟩ := nameLater present
    exact ⟨ys, cs0, le, by simpa [present] using separate_comm outName, keys⟩
  have commentReady : d0.status = COMMENT_STATE → StringReady h1 z1 d1 ds pb g.comment := by
    intro e
    apply readyOf
    intro present
    obtain ⟨ys, cs0, le⟩ := pComment e present
    obtain ⟨pw, _⟩ := apart writing i g record getg0 nxs ys ncs (fun _ => cs0)
    simp only [headerSpans, List.pairwise_cons, List.mem_cons, List.mem_singleton, List.not_mem_nil,
      forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true, implies_true] at pw
    obtain ⟨_, ⟨_, _, outComment, _⟩, _⟩ := pw
    obtain ⟨_, _, _, keys⟩ := commentLater present
    exact ⟨ys, cs0, le, by simpa [present] using separate_comm outComment, keys⟩
  exact ⟨i, g, by rw [gzhead]; exact record, getg1, by omega,
    fun e => ⟨extraMem, fun n => by rw [gzindex]; exact pExtra (by rw [← status]; exact e) n,
      fun n => by rw [gzindex]; exact aExtra (by rw [← status]; exact e) n, nameLater, commentLater, by omega⟩,
    fun e => ⟨nameReady (by rw [← status]; exact e),
      fun n => by rw [gzindex]; exact aName (by rw [← status]; exact e) n, commentLater⟩,
    fun e => commentReady (by rw [← status]; exact e)⟩

/-- The record shape of the header stages is one of batch 2's `HeaderFields` (with `wrap` kept). -/
theorem HeaderShape.fields {d d' : DeflateState} (shape : HeaderShape d d') : HeaderFields d d' := by
  obtain ⟨_, _, _, _, _, _, _, _, rfl⟩ := shape
  rfl

end Zlib.Deflate.Universal.Call
