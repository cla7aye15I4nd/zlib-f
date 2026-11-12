import ZlibF.Proof.«deflate.c.universal-call-headerphase»

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
  exact (CallerKeep.of_frame (HeaderFrame.state pb good.live.hs { d with last_flush := flush } rfl)).trans
    (CallerKeep.of_flush good0 trees0 buffers0 low cursor out run live account) (stream_accounting_zero z)

end Zlib.Deflate.Universal.Call
