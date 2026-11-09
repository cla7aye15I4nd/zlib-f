import ZlibF.Proof.«compress.c.capacity-contract»

/-! # Local type uniqueness from the real utility allocations

These proof-local facts do not replace DGood or change any public goal.
An arbitrary Fresh heap may contain old typed-table collisions. Fresh
allocations still have unique new identities; the real End execution and
its five-object live ledger require uniqueness only at those identities.
The ordinary engine's global DGood dependency remains a separate task.
-/
namespace ZlibF.Spec.Public.Proofs.CompressLocal
open C Zlib.Compress Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open Zlib.Deflate.Proofs.DefaultInit ZlibF.Spec.Public.Proofs.CompressCaller
set_option autoImplicit false
set_option maxRecDepth 100000

/-- Proof-local occupancy at one identity, rather than global Uniq. -/
def UniqueAt (h : Heap) (b : Nat) : Prop :=
  cnt (h.bytes b) + cnt (h.words b) + cnt (h.streams b) + cnt (h.gzheaders b) +
    cnt (h.dstates b) + cnt (h.istates b) + cnt (h.gzstates b) ≤ 1

/-- Only identities allocated since this cutoff are constrained. -/
def UniqueFrom (h : Heap) (cutoff : Nat) : Prop := ∀ b, cutoff ≤ b → UniqueAt h b

/-- Freshness establishes empty new identities without constraining old ones. -/
theorem fresh_unique_from {h : Heap} (fresh : Fresh h) : UniqueFrom h h.nextBlk := by
  intro b bound
  obtain ⟨a,c,d,e,f,g,j⟩ := Heap.not_live.mp (fresh b bound)
  simp only [UniqueAt,a,c,d,e,f,g,j,cnt_none,Nat.zero_add]
  decide

/-- Replacing values in already live typed slots preserves local occupancy. -/
theorem UniqueAt.shape {h g : Heap} {b : Nat} (unique : UniqueAt h b) (shape : Shape h g) : UniqueAt g b := by
  obtain ⟨a,c,d,e,f,j,k⟩ := shape b
  simp only [UniqueAt,cnt,a,c,d,e,f,j,k] at unique ⊢
  exact unique

theorem UniqueFrom.shape {h g : Heap} {cutoff : Nat} (unique : UniqueFrom h cutoff) (shape : Shape h g) : UniqueFrom g cutoff :=
  fun b bound => (unique b bound).shape shape

theorem UniqueAt.bytes_only {h : Heap} {b : Nat} (hU : UniqueAt h b) {a : Array UInt8} (hb : h.bytes b = some a) :
    h.words b = none ∧ h.streams b = none ∧ h.gzheaders b = none ∧ h.dstates b = none ∧ h.istates b = none ∧
    h.gzstates b = none := by
  have : cnt (h.bytes b) + cnt (h.words b) + cnt (h.streams b) + cnt (h.gzheaders b) + cnt (h.dstates b) + cnt (h.istates b) + cnt (h.gzstates b) ≤ 1 := hU
  simp only [hb, cnt_some] at this
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · cases hx : h.words b with
    | none => rfl
    | some _ => simp only [hx, cnt_some] at this <;> omega
  · cases hx : h.streams b with
    | none => rfl
    | some _ => simp only [hx, cnt_some] at this <;> omega
  · cases hx : h.gzheaders b with
    | none => rfl
    | some _ => simp only [hx, cnt_some] at this <;> omega
  · cases hx : h.dstates b with
    | none => rfl
    | some _ => simp only [hx, cnt_some] at this <;> omega
  · cases hx : h.istates b with
    | none => rfl
    | some _ => simp only [hx, cnt_some] at this <;> omega
  · cases hx : h.gzstates b with
    | none => rfl
    | some _ => simp only [hx, cnt_some] at this <;> omega

theorem UniqueAt.words_only {h : Heap} {b : Nat} (hU : UniqueAt h b) {a : Array UInt16} (hb : h.words b = some a) :
    h.bytes b = none ∧ h.streams b = none ∧ h.gzheaders b = none ∧ h.dstates b = none ∧ h.istates b = none ∧
    h.gzstates b = none := by
  have : cnt (h.bytes b) + cnt (h.words b) + cnt (h.streams b) + cnt (h.gzheaders b) + cnt (h.dstates b) + cnt (h.istates b) + cnt (h.gzstates b) ≤ 1 := hU
  simp only [hb, cnt_some] at this
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · cases hx : h.bytes b with
    | none => rfl
    | some _ => simp only [hx, cnt_some] at this <;> omega
  · cases hx : h.streams b with
    | none => rfl
    | some _ => simp only [hx, cnt_some] at this <;> omega
  · cases hx : h.gzheaders b with
    | none => rfl
    | some _ => simp only [hx, cnt_some] at this <;> omega
  · cases hx : h.dstates b with
    | none => rfl
    | some _ => simp only [hx, cnt_some] at this <;> omega
  · cases hx : h.istates b with
    | none => rfl
    | some _ => simp only [hx, cnt_some] at this <;> omega
  · cases hx : h.gzstates b with
    | none => rfl
    | some _ => simp only [hx, cnt_some] at this <;> omega

theorem UniqueAt.dstates_only {h : Heap} {b : Nat} (hU : UniqueAt h b) {a : DeflateState} (hb : h.dstates b = some a) :
    h.bytes b = none ∧ h.words b = none ∧ h.streams b = none ∧ h.gzheaders b = none ∧ h.istates b = none ∧
    h.gzstates b = none := by
  have : cnt (h.bytes b) + cnt (h.words b) + cnt (h.streams b) + cnt (h.gzheaders b) + cnt (h.dstates b) + cnt (h.istates b) + cnt (h.gzstates b) ≤ 1 := hU
  simp only [hb, cnt_some] at this
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · cases hx : h.bytes b with
    | none => rfl
    | some _ => simp only [hx, cnt_some] at this <;> omega
  · cases hx : h.words b with
    | none => rfl
    | some _ => simp only [hx, cnt_some] at this <;> omega
  · cases hx : h.streams b with
    | none => rfl
    | some _ => simp only [hx, cnt_some] at this <;> omega
  · cases hx : h.gzheaders b with
    | none => rfl
    | some _ => simp only [hx, cnt_some] at this <;> omega
  · cases hx : h.istates b with
    | none => rfl
    | some _ => simp only [hx, cnt_some] at this <;> omega
  · cases hx : h.gzstates b with
    | none => rfl
    | some _ => simp only [hx, cnt_some] at this <;> omega

/-- A real fresh state allocation establishes uniqueness at its new key;
all old keys retain precisely their previous local occupancy. -/
theorem UniqueFrom.state {h : Heap} {cutoff : Nat} (unique : UniqueFrom h cutoff) (fresh : Fresh h) (d : DeflateState) :
    UniqueFrom (stateHeap h d) cutoff := by
  intro x bound
  by_cases same : x = h.nextBlk
  · subst x
    obtain ⟨a,b,c,e,f,g,j⟩ := Heap.not_live.mp (fresh _ (Nat.le_refl _))
    simp [UniqueAt,stateHeap,a,b,c,e,g,j]
  · simpa only [UniqueAt,stateHeap,upd_ne _ _ _ _ same] using unique x bound

theorem UniqueFrom.word {h : Heap} {cutoff : Nat} (unique : UniqueFrom h cutoff) (fresh : Fresh h) (n : Nat) :
    UniqueFrom (wordHeap h n) cutoff := by
  intro x bound
  by_cases same : x = h.nextBlk
  · subst x
    obtain ⟨a,b,c,e,f,g,j⟩ := Heap.not_live.mp (fresh _ (Nat.le_refl _))
    simp [UniqueAt,wordHeap,a,c,e,f,g,j]
  · simpa only [UniqueAt,wordHeap,upd_ne _ _ _ _ same] using unique x bound

theorem UniqueFrom.byte {h : Heap} {cutoff : Nat} (unique : UniqueFrom h cutoff) (fresh : Fresh h) (n : Nat) :
    UniqueFrom (byteHeap h n) cutoff := by
  intro x bound
  by_cases same : x = h.nextBlk
  · subst x
    obtain ⟨a,b,c,e,f,g,j⟩ := Heap.not_live.mp (fresh _ (Nat.le_refl _))
    simp [UniqueAt,byteHeap,Zlib.Zutil.Proofs.allocHeap,b,c,e,f,g,j]
  · simpa only [UniqueAt,byteHeap,Zlib.Zutil.Proofs.allocHeap,upd_ne _ _ _ _ same] using unique x bound

theorem UniqueFrom.byte_result {h : Heap} {cutoff : Nat} (unique : UniqueFrom h cutoff) (fresh : Fresh h) (n : Nat) :
    UniqueFrom (byteResult h n) cutoff := by
  unfold byteResult
  split
  · exact unique.byte fresh n
  · exact unique

theorem UniqueFrom.word_result {h : Heap} {cutoff : Nat} (unique : UniqueFrom h cutoff) (fresh : Fresh h) (n : Nat) :
    UniqueFrom (wordResult h n) cutoff := by
  unfold wordResult
  split
  · exact unique.word fresh n
  · exact unique

/-- The four actual oracle-dependent requests preserve uniqueness only at
new identities, including every partial allocation-failure combination. -/
theorem UniqueFrom.buffers {h : Heap} {cutoff : Nat} (unique : UniqueFrom h cutoff) (fresh : Fresh h) :
    UniqueFrom (buffersHeap h) cutoff :=
  (((unique.byte_result fresh 65536).word_result (fresh_byteResult fresh 65536) 32768).word_result
    (fresh_wordResult (fresh_byteResult fresh 65536) 32768) 32768).byte_result
    (fresh_wordResult (fresh_wordResult (fresh_byteResult fresh 65536) 32768) 32768) 65536

/-- Actual automatic-stream creation is fresh and locally unique even if
unrelated old identities occur in several typed tables. -/
theorem automatic_stream_local {h : Heap} (fresh : Fresh h) :
    Fresh (localHeap h) ∧ UniqueFrom (localHeap h) h.nextBlk := by
  constructor
  · intro b bound live
    have different : b ≠ h.nextBlk := by change h.nextBlk+1 ≤ b at bound;omega
    apply fresh b (by change h.nextBlk+1 ≤ b at bound;omega)
    simpa only [localHeap,Heap.live,upd_ne _ _ _ _ different] using live
  · intro b bound
    by_cases same : b = h.nextBlk
    · subst b
      obtain ⟨a,c,d,e,f,g,j⟩ := Heap.not_live.mp (fresh _ (Nat.le_refl _))
      simp [UniqueAt,localHeap,a,c,e,f,g,j]
    · simpa only [UniqueAt,localHeap,upd_ne _ _ _ _ same] using fresh_unique_from fresh b bound

/-- The real allocation suffix reaches its real finish/cleanup decision
with Fresh and locally unique private storage. No global Uniq premise is
used, and all four later allocator outcomes remain arbitrary. -/
theorem allocate_local_cut {h : Heap} {r : ZStreamRef} {z : ZStream} {cutoff : Nat}
    (fresh : Fresh h) (unique : UniqueFrom h cutoff) (get : r.get h = some z)
    (allocator : z.zalloc = .fn "zcalloc") (stateSuccess : h.allocOk h.nalloc = true) (level : Int32) :
    let ph := publishedHeap h r z
    let after := setD (buffersHeap ph) h.nextBlk (bufferState ph (baseState r))
    allocate (some r) level h = finish (some r) (some (.tab h.nextBlk)) level (bufferPointers ph) after ∧
    Fresh after ∧ UniqueFrom after cutoff := by
  let ph := publishedHeap h r z
  have controls := shape_put get (stateStream z h.nextBlk)
  have freshControls : Fresh (r.put h (stateStream z h.nextBlk)) := controls.fresh (by simp) fresh
  have freshP : Fresh ph := fresh_stateHeap freshControls _
  have uniqueP : UniqueFrom ph cutoff := (unique.shape controls).state freshControls _
  have stateP : ph.dstates h.nextBlk = some (baseState r) := by simp [ph,publishedHeap,stateHeap]
  have stateB : (buffersHeap ph).dstates h.nextBlk = some (baseState r) := by rw [buffers_dstates];exact stateP
  have replace := shape_setD stateB (bufferState ph (baseState r))
  exact ⟨allocate_to_finish fresh get allocator stateSuccess level,
    replace.fresh (by simp) (buffers_fresh freshP),(uniqueP.buffers freshP).shape replace⟩

/-- The real default initializer's pre-reset decision is connected to the
automatic stream and its actual prepared allocator fields. Fresh alone
produces all new private-slot uniqueness; old collisions remain admitted. -/
theorem real_default_local_cut {h : Heap} (fresh : Fresh h)
    (stateSuccess : h.allocOk h.nalloc = true) :
    let root := ZStreamRef.tab h.nextBlk
    let prepared := root.put (localHeap h) (ZlibF.Spec.Public.preparedStream (localStream h))
    let ph := publishedHeap prepared root (ZlibF.Spec.Public.preparedStream (localStream h))
    let after := setD (buffersHeap ph) prepared.nextBlk (bufferState ph (baseState root))
    C.run (deflateInit_ (some root) Z_DEFAULT_COMPRESSION (.ref (.str 57) 0) 112) (localHeap h) =
      finish (some root) (some (.tab prepared.nextBlk)) 6 (bufferPointers ph) after ∧
      Fresh after ∧ UniqueFrom after h.nextBlk := by
  let root := ZStreamRef.tab h.nextBlk
  let z := ZlibF.Spec.Public.preparedStream (localStream h)
  let prepared := root.put (localHeap h) z
  have get : root.get (localHeap h) = some (localStream h) := by simp [root,localHeap,ZStreamRef.get]
  have version : ZlibF.Spec.Public.VersionValue (localHeap h) (.ref (.str 57) 0) (some 49) :=
    Or.inr ⟨49,rfl,Or.inr ⟨.str 57,0,strBytes ZLIB_VERSION,rfl,rfl,by decide +kernel,by decide +kernel⟩⟩
  have actual := entry_run get version Z_DEFAULT_COMPRESSION
  have normalize : levelValue Z_DEFAULT_COMPRESSION = 6 := by decide +kernel
  rw [normalize] at actual
  have test : ((6 : Int32) < 0 || (6 : Int32) > 9) = false := by decide +kernel
  rw [test] at actual
  obtain ⟨freshA,uniqueA⟩ := automatic_stream_local fresh
  have controls := shape_put get z
  have freshP : Fresh prepared := controls.fresh (by simp) freshA
  have uniqueP : UniqueFrom prepared h.nextBlk := uniqueA.shape controls
  have getP : root.get prepared = some z := ZStreamRef.get_put_same get _
  have allocator : z.zalloc = .fn "zcalloc" := by simp [z,ZlibF.Spec.Public.preparedStream,localStream]
  have stateP : prepared.allocOk prepared.nalloc = true := by simpa [prepared,localHeap] using stateSuccess
  obtain ⟨cut,freshCut,uniqueCut⟩ := allocate_local_cut freshP uniqueP getP allocator stateP 6
  exact ⟨actual.trans cut,freshCut,uniqueCut⟩

/-- End's exact live ledger uses uniqueness at its own five private keys.
No uniqueness fact about unrelated caller identities is consulted. -/
theorem end_heap_live_local {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState} {w p q b : Nat}
    (hB : DBlocks h d w p q b) (localUnique : ∀ x, (x = ds ∨ x = w ∨ x = p ∨ x = q ∨ x = b) → UniqueAt h x) (hz : r.get h = some z) (hs : h.dstates ds = some d) (x : Nat) :
    (endHeap h r ds z d).live x ↔ h.live x ∧ ¬ (x = ds ∨ x = w ∨ x = p ∨ x = q ∨ x = b) := by
  obtain ⟨wa, hwa, -⟩ := hB.wa
  obtain ⟨pa, hpa, -⟩ := hB.pa
  obtain ⟨qa, hqa, -⟩ := hB.qa
  obtain ⟨ba, hba, -⟩ := hB.ba
  obtain ⟨t1, t2, t3, t4, t5, t6, t7⟩ := endHeap_tables (ds := ds) hB hz x
  have key : (endHeap h r ds z d).live x ↔
      ((endHeap h r ds z d).bytes x ≠ none ∨ (endHeap h r ds z d).words x ≠ none ∨ (h.streams x).isSome ∨
        h.gzheaders x ≠ none ∨ (endHeap h r ds z d).dstates x ≠ none ∨ h.istates x ≠ none ∨ (h.gzstates x).isSome) := by
    unfold Heap.live
    rw [t6, t7, ← Option.isSome_iff_ne_none (o := (endHeap h r ds z d).streams x), t4,
      ← Option.isSome_iff_ne_none (o := (endHeap h r ds z d).gzstates x), t5]
  rw [key]
  unfold Heap.live
  rw [t1, t2, t3]
  by_cases hx : x = ds ∨ x = w ∨ x = p ∨ x = q ∨ x = b
  · simp only [hx, not_true_eq_false, and_false, iff_false]
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · obtain ⟨e1, e2, e3, e4, e5, e6⟩ := (localUnique x (Or.inl rfl)).dstates_only hs
      simp [e1, e2, e3, e4, e5, e6]
    · obtain ⟨e1, e2, e3, e4, e5, e6⟩ := (localUnique x (Or.inr (Or.inl rfl))).bytes_only hwa
      simp [e1, e2, e3, e4, e5, e6, Option.isSome_none]
    · obtain ⟨e1, e2, e3, e4, e5, e6⟩ := (localUnique x (Or.inr (Or.inr (Or.inl rfl)))).words_only hpa
      simp [e1, e2, e3, e4, e5, e6, Option.isSome_none]
    · obtain ⟨e1, e2, e3, e4, e5, e6⟩ := (localUnique x (Or.inr (Or.inr (Or.inr (Or.inl rfl))))).words_only hqa
      simp [e1, e2, e3, e4, e5, e6, Option.isSome_none]
    · obtain ⟨e1, e2, e3, e4, e5, e6⟩ := (localUnique x (Or.inr (Or.inr (Or.inr (Or.inr rfl))))).bytes_only hba
      simp [e1, e2, e3, e4, e5, e6, Option.isSome_none]
  · have hx1 : ¬ (x = w ∨ x = b) := fun e => hx (by rcases e with e | e <;> simp [e])
    have hx2 : ¬ (x = p ∨ x = q) := fun e => hx (by rcases e with e | e <;> simp [e])
    have hx3 : ¬ x = ds := fun e => hx (Or.inl e)
    have hn : ¬ (x = w ∨ x = p ∨ x = q ∨ x = b) := fun e => hx (Or.inr e)
    simp only [hx1, hx2, hx3, ite_false]
    simp [hn, Option.isSome_iff_ne_none]

/-- The real End execution, cleanup ledger and freshness are available
from local typed uniqueness. This theorem deliberately does not manufacture
the old DGood invariant or claim the ordinary engine's Fresh-only result. -/
theorem real_end_local {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState} {w p q b : Nat}
    (live : DLive h r ds z d) (allocator : z.zfree = .fn "zcfree") (blocks : DBlocks h d w p q b)
    (fresh : Fresh h) (localUnique : ∀ x, DOwned d ds x → UniqueAt h x) :
    C.run (deflateEnd (some r)) h =
      .ok ((if d.status == BUSY_STATE then Z_DATA_ERROR else Z_OK),endHeap h r ds z d) ∧
    ZlibF.Spec.Public.LiveChange h (endHeap h r ds z d) (fun _ => False) (DOwned d ds) ∧
    Fresh (endHeap h r ds z d) := by
  have ledger := end_heap_live_local blocks (fun x owned => localUnique x ((DOwned_iff blocks x).mpr owned)) live.hz live.hs
  have exactLedger : ∀ x, (endHeap h r ds z d).live x ↔ h.live x ∧ ¬DOwned d ds x := by
    intro x
    rw [DOwned_iff blocks x]
    exact ledger x
  refine ⟨deflateEnd_run live allocator blocks,?_,?_⟩
  · intro x
    simpa only [or_false] using exactLedger x
  · intro x bound remaining
    have next : (endHeap h r ds z d).nextBlk = h.nextBlk := by rw [endHeap_eq blocks];simp
    rw [next] at bound
    exact fresh x bound ((exactLedger x).mp remaining).1


/-- Every original readable dynamic byte view has an old identity. This
separates it from the automatic stream and later private allocations,
without requiring uniqueness of unrelated old typed objects. -/
theorem original_byte_root_below {h : Heap} {ref : BRef} {off b : Nat} {array : Array UInt8}
    (fresh : Fresh h) (get : Space.get h ref = some array) (root : ZlibF.Spec.Public.ByteRoot (.ref ref off) b) :
    b < h.nextBlk := by
  cases ref with
  | blk i =>
    change b = i at root
    subst b
    apply fresh.lt
    simp [Heap.live,show h.bytes i = some array from get]
  | dstate_depth i =>
    change b = i at root
    subst b
    cases state : h.dstates i with
    | none => simp [Space.get,state] at get
    | some d => apply fresh.lt;simp [Heap.live,state]
  | str i => cases root
  | st_dist_code => cases root
  | st_length_code => cases root

theorem UniqueAt.after_end {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState} {w p q b : Nat}
    {x : Nat} (unique : UniqueAt h x) (hB : DBlocks h d w p q b) (hz : r.get h = some z) : UniqueAt (endHeap h r ds z d) x := by
  obtain ⟨t1, t2, t3, t4, t5, t6, t7⟩ := endHeap_tables (ds := ds) hB hz x
  have : cnt (h.bytes x) + cnt (h.words x) + cnt (h.streams x) + cnt (h.gzheaders x) + cnt (h.dstates x) + cnt (h.istates x) + cnt (h.gzstates x) ≤ 1 := unique
  have c1 : cnt ((endHeap h r ds z d).bytes x) ≤ cnt (h.bytes x) := by
    rw [t1]; split <;> simp [cnt]
  have c2 : cnt ((endHeap h r ds z d).words x) ≤ cnt (h.words x) := by
    rw [t2]; split <;> simp [cnt]
  have c3 : cnt ((endHeap h r ds z d).dstates x) ≤ cnt (h.dstates x) := by
    rw [t3]; split <;> simp [cnt]
  have c4 : cnt ((endHeap h r ds z d).streams x) = cnt (h.streams x) := by simp only [cnt, t4]
  have c5 : cnt ((endHeap h r ds z d).gzstates x) = cnt (h.gzstates x) := by simp only [cnt, t5]
  change cnt ((endHeap h r ds z d).bytes x) + cnt ((endHeap h r ds z d).words x) + cnt ((endHeap h r ds z d).streams x) + cnt ((endHeap h r ds z d).gzheaders x) + cnt ((endHeap h r ds z d).dstates x) + cnt ((endHeap h r ds z d).istates x) + cnt ((endHeap h r ds z d).gzstates x) ≤ 1
  rw [t6, t7]
  omega

private theorem count_zero_none {α : Type} {value : Option α} (zero : cnt value = 0) : value = none := by
  cases value <;>simp_all only [cnt_some,cnt_none,reduceCtorEq]

/-- The automatic stream's free removes exactly its one identity. Only
that slot's occupancy is relevant; unrelated old collisions are admitted. -/
theorem release_stream_local {h : Heap} {slot : Nat} {z : ZStream}
    (unique : UniqueAt h slot) (get : h.streams slot = some z) (b : Nat) :
    (ZlibF.Spec.Public.Proofs.CompressTail.releaseLocal h slot).live b ↔ h.live b ∧ b ≠ slot := by
  by_cases same : b = slot
  · subst b
    have counts : cnt (h.bytes slot) + cnt (h.words slot) + cnt (h.streams slot) + cnt (h.gzheaders slot) + cnt (h.dstates slot) + cnt (h.istates slot) + cnt (h.gzstates slot) ≤ 1 := unique
    simp only [get,cnt_some] at counts
    have bytes := count_zero_none (value := h.bytes slot) (by omega)
    have words := count_zero_none (value := h.words slot) (by omega)
    have headers := count_zero_none (value := h.gzheaders slot) (by omega)
    have states := count_zero_none (value := h.dstates slot) (by omega)
    have inflates := count_zero_none (value := h.istates slot) (by omega)
    have gzip := count_zero_none (value := h.gzstates slot) (by omega)
    simp [ZlibF.Spec.Public.Proofs.CompressTail.releaseLocal,Heap.live,bytes,words,headers,states,inflates,gzip]
  · have live : (ZlibF.Spec.Public.Proofs.CompressTail.releaseLocal h slot).live b ↔ h.live b := by
      simp only [ZlibF.Spec.Public.Proofs.CompressTail.releaseLocal,Heap.live,upd_ne _ _ _ _ same]
    exact live.trans ⟨fun yes => ⟨yes,same⟩,And.left⟩

/-- Actual End followed by the real automatic-stream free restores the
live ledger outside exactly those six private identities. This is a full
cleanup execution theorem with only local type-uniqueness premises. -/
theorem real_cleanup_local {h : Heap} {slot ds : Nat} {z : ZStream} {d : DeflateState} {w p q b : Nat}
    (live : DLive h (.tab slot) ds z d) (allocator : z.zfree = .fn "zcfree") (blocks : DBlocks h d w p q b)
    (unique : UniqueAt h slot) (ownedUnique : ∀ x, DOwned d ds x → UniqueAt h x) (fresh : Fresh h) :
    let ended := endHeap h (.tab slot) ds z d
    let after := ZlibF.Spec.Public.Proofs.CompressTail.releaseLocal ended slot
    C.run (do let rc ← deflateEnd (some (.tab slot));freeZStream (some (.tab slot));pure rc) h =
      .ok ((if d.status == BUSY_STATE then Z_DATA_ERROR else Z_OK),after) ∧
    ZlibF.Spec.Public.LiveChange h after (fun _ => False) (fun x => DOwned d ds x ∨ x = slot) ∧
    Fresh after := by
  obtain ⟨actual,ledger,freshEnd⟩ := real_end_local live allocator blocks fresh ownedUnique
  let ended := endHeap h (.tab slot) ds z d
  have getEnd : ended.streams slot = some {z with state := none} := by
    dsimp only [ended]
    rw [endHeap_eq blocks]
    simp [ZStreamRef.put,show h.streams slot = some z from live.hz]
  have free := freeZStream_tab getEnd
  have uniqueEnd := unique.after_end (ds := ds) blocks live.hz
  have liveFree := release_stream_local uniqueEnd getEnd
  change deflateEnd (some (.tab slot)) h = .ok ((if d.status == BUSY_STATE then Z_DATA_ERROR else Z_OK),ended) at actual
  refine ⟨?_,?_,?_⟩
  · simp only [C.run,bind_app,actual,free,pure_app]
    rfl
  · intro x
    rw [liveFree,ledger]
    simp only [or_false,not_or]
    exact and_assoc
  · intro x bound remaining
    have next : (ZlibF.Spec.Public.Proofs.CompressTail.releaseLocal ended slot).nextBlk = ended.nextBlk := rfl
    rw [next] at bound
    exact freshEnd x bound ((liveFree x).mp remaining).1


/-- The same real cleanup heap preserves every typed caller slot outside
its six private identities. This exact frame does not infer typed contents
from global uniqueness or merely from unchanged table presence. -/
theorem cleanup_local_frame {h : Heap} {slot ds : Nat} {z : ZStream} {d : DeflateState} {w p q b : Nat}
    (get : h.streams slot = some z) (blocks : DBlocks h d w p q b) :
    ZlibF.Spec.Public.Frame h
      (ZlibF.Spec.Public.Proofs.CompressTail.releaseLocal (endHeap h (.tab slot) ds z d) slot)
      (fun x => DOwned d ds x ∨ x = slot) := by
  rw [endHeap_eq blocks]
  simp only [ZlibF.Spec.Public.Proofs.CompressTail.releaseLocal,ZStreamRef.put,get]
  refine ⟨rfl,rfl,rfl,Nat.le_refl _,Nat.le_refl _,?_⟩
  intro x _live outside
  have unowned : ¬(x = ds ∨ x = w ∨ x = p ∨ x = q ∨ x = b) :=
    fun owned => outside (Or.inl ((DOwned_iff blocks x).mpr owned))
  have notStream : x ≠ slot := fun same => outside (Or.inr same)
  have notD : x ≠ ds := fun same => unowned (Or.inl same)
  have notW : x ≠ w := fun same => unowned (Or.inr (Or.inl same))
  have notP : x ≠ p := fun same => unowned (Or.inr (Or.inr (Or.inl same)))
  have notQ : x ≠ q := fun same => unowned (Or.inr (Or.inr (Or.inr (Or.inl same))))
  have notB : x ≠ b := fun same => unowned (Or.inr (Or.inr (Or.inr (Or.inr same))))
  simp [SlotSame,ZlibF.Spec.Public.Proofs.CompressTail.releaseLocal,ZStreamRef.put,get,
    upd_ne _ _ _ _ notStream,upd_ne _ _ _ _ notD,upd_ne _ _ _ _ notW,upd_ne _ _ _ _ notP,
    upd_ne _ _ _ _ notQ,upd_ne _ _ _ _ notB]

end ZlibF.Spec.Public.Proofs.CompressLocal
