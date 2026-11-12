import ZlibF.Proof.«deflate.c.universal-history»
import ZlibF.Proof.«deflate.c.life.check»
import ZlibF.Proof.«deflate.c.life.bound»
import ZlibF.Proof.«deflate.c.life.getdict»
import ZlibF.Spec.Public.Sequences

/-!
# deflate.c: the stream operations keep the invariant (batch A, `operation_step`)

One lemma per operation of `StreamOperation .deflate`, each in the form of `operation_step`: the
call returns, `DInv` holds afterwards, and the buffer frame and the allocation ledger of
`StreamSequenceSafety` hold. This file starts with the operations that leave the heap unchanged
or change only fields of the state record that the invariant does not read.
-/

namespace Zlib.Deflate.Universal
open C ZlibF.Spec ZlibF.Spec.Public Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Engine.Proofs
open Zlib.Deflate.Proofs
set_option autoImplicit false

/-- The conclusion of `operation_step` for one call. -/
def StepOk (h : Heap) (r : ZStreamRef) (call : Call) : Prop :=
  ∃ value after, call.execute default h = .ok ((value, default), after) ∧
    (∃ ds' z' d', DInv after r ds' z' d') ∧
    BufferFrame h after
      (fun b => StreamRoot r b ∨ StreamOwned h r b ∨ StreamHeaderRecord h r call b)
      (StreamWriteRegions h r call) ∧
    LiveChange h after
      (fun b => StreamOwned after r b ∧ ¬ h.live b)
      (fun b => StreamOwned h r b ∧ ¬ StreamOwned after r b)

theorem heapCall_run {α : Type} {program : M α} {h after : Heap} {value : α}
    (run : program h = .ok (value, after)) : heapCall program default h = .ok ((value, default), after) := by
  unfold heapCall; rw [run]

/-- A call that leaves the heap unchanged and writes no caller region. -/
theorem step_unchanged {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    {call : Call} (inv : DInv h r ds z d) (value : call.Result)
    (run : call.execute default h = .ok ((value, default), h))
    (regions : StreamWriteRegions h r call = []) : StepOk h r call := by
  refine ⟨value, h, run, ⟨ds, z, d, inv⟩, ?_, ?_⟩
  · rw [regions]
    refine ⟨⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _, fun b _ _ => ?_⟩, fun _ mem => by cases mem⟩
    simp [restoreRegions]
  · intro b
    constructor
    · intro live; exact Or.inl ⟨live, fun ⟨_, not⟩ => not ‹_›⟩
    · rintro (⟨live, _⟩ | ⟨owned, _⟩)
      · exact live
      · exact owned_live inv.good ((inv.owned b).1 owned)

/-- `deflateUsed` reads the state. -/
theorem step_used {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv h r ds z d) (hasBits : Bool) : StepOk h r (.deflateUsed (some r) hasBits) :=
  step_unchanged inv _ (heapCall_run (deflateUsed_run inv.good.live hasBits)) rfl

/-- `deflatePending` reads the state. -/
theorem step_pending {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv h r ds z d) (hasPending hasBits : Bool) :
    StepOk h r (.deflatePending (some r) hasPending hasBits) :=
  step_unchanged inv _ (heapCall_run (deflatePending_run inv.good.live hasPending hasBits)) rfl

/-- A call that writes only the state record and no caller region. -/
theorem step_setD {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d d' : DeflateState}
    {call : Call} (inv : DInv h r ds z d) (value : call.Result)
    (run : call.execute default h = .ok ((value, default), setD h ds d'))
    (regions : StreamWriteRegions h r call = []) (inv' : DInv (setD h ds d') r ds z d')
    (sameOwned : ∀ b, DeflateOwned ds d b ↔ DeflateOwned ds d' b) :
    StepOk h r call := by
  refine ⟨value, setD h ds d', run, ⟨ds, z, d', inv'⟩, ?_, ?_⟩
  · rw [regions]
    refine ⟨⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _, fun b _ unchanged => ?_⟩, fun _ mem => by cases mem⟩
    have ne : b ≠ ds := by
      rintro rfl
      exact unchanged (Or.inr (Or.inl ((inv.owned b).2 (Or.inl rfl))))
    simp only [restoreRegions, List.foldl]
    exact ⟨rfl, rfl, rfl, rfl, setD_dstates_ne h ds b d' ne, rfl, rfl, rfl⟩
  · have shape := shape_setD inv.good.live.hs d'
    intro b
    rw [shape.live b]
    constructor
    · intro live
      refine Or.inl ⟨live, fun ⟨owned, not⟩ => not ?_⟩
      exact (inv'.owned b).2 ((sameOwned b).1 ((inv.owned b).1 owned))
    · rintro (⟨live, _⟩ | ⟨owned, _⟩)
      · exact live
      · exact owned_live inv.good ((sameOwned b).2 ((inv'.owned b).1 owned))

/-- `deflateTune` writes the four tuning fields, which the invariant does not read. -/
theorem step_tune {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv h r ds z d) (g m n c : Int32) : StepOk h r (.deflateTune (some r) g m n c) := by
  obtain ⟨_, run, rfl, good, _⟩ := deflateTune_safe inv.good g m n c
  refine step_setD inv _ (heapCall_run run) rfl ⟨good, inv.alloc, inv.globals, ?_, ?_, ?_⟩
    (fun b => by simp [DeflateOwned, tuneD])
  · have shape := inv.shape
    cases shape
    constructor <;> assumption
  · have hashing := inv.hashing
    cases hashing
    constructor <;> assumption
  · obtain ⟨⟨xs, ⟨b, a, pbuf, bytes, ledger⟩, near⟩, clear, below⟩ := inv.symbols
    exact ⟨⟨xs, ⟨b, a, pbuf, bytes, ledger.keep rfl rfl rfl rfl⟩, near⟩,
      ⟨clear.bl, clear.opt, clear.fixed⟩, below⟩

/-- Every header pointer has the form `GzOk` asks for. -/
theorem gzOk_any (h : Heap) (head : GzHeaderPtr) : GzOk h head := by
  rcases head with _ | ⟨i⟩
  · exact Or.inl rfl
  · cases i with
    | tab i => exact Or.inr ⟨i, rfl⟩

/-- A state update that keeps every field the invariant reads (besides `DGood`) keeps it. -/
theorem DInv.of_fields {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d d' : DeflateState}
    (inv : DInv h r ds z d) (good : DGood (setD h ds d') r ds z d')
    (shape : Shape d → Shape d') (hashing : Hashing h d → Hashing (setD h ds d') d')
    (symbols : Symbols h d → Symbols (setD h ds d') d') : DInv (setD h ds d') r ds z d' :=
  ⟨good, inv.alloc, inv.globals, shape inv.shape, hashing inv.hashing, symbols inv.symbols⟩

/-- `deflateSetHeader` stores the header pointer (gzip) or refuses; the invariant does not read
`gzhead` beyond its pointer form. -/
theorem step_setHeader {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv h r ds z d) (head : GzHeaderPtr) : StepOk h r (.deflateSetHeader (some r) head) := by
  by_cases wrap : d.wrap = 2
  · obtain ⟨_, run, rfl, good, _⟩ := deflateSetHeader_safe inv.good wrap head (gzOk_any h head)
    refine step_setD inv _ (heapCall_run run) rfl (inv.of_fields good ?_ ?_ ?_)
      (fun b => by simp [DeflateOwned, setHeaderD])
    · intro shape; cases shape; constructor <;> assumption
    · intro hashing; cases hashing; constructor <;> assumption
    · rintro ⟨⟨xs, ⟨b, a, pbuf, bytes, ledger⟩, near⟩, clear, below⟩
      exact ⟨⟨xs, ⟨b, a, pbuf, bytes, ledger.keep rfl rfl rfl rfl⟩, near⟩,
        ⟨clear.bl, clear.opt, clear.fixed⟩, below⟩
  · exact step_unchanged inv _ (heapCall_run (deflateSetHeader_run_other inv.good.live wrap head)) rfl

/-- A C string of the public history is a string `deflateBound` can measure. -/
theorem cstring_gzStr {h : Heap} {p : BPtr} {xs : List UInt8} (c : CString h p xs) :
    GzStr h p xs.length := by
  obtain ⟨bytes, nz, lt⟩ := c
  rcases bytes with ⟨_, n0, _⟩ | ⟨r, i, a, rfl, get, fit, eq⟩
  · simp at n0
  · refine ⟨r, i, a, rfl, get, by omega, ?_, ?_, lt⟩
    · have last := congrArg (fun l => l[xs.length]?) eq
      simp only [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero,
        List.getElem?_take, List.getElem?_drop] at last
      simp only [Nat.lt_add_one, if_true] at last
      rw [← Array.getElem?_toList]
      exact last.symm
    · intro k below
      have at_k := congrArg (fun l => l[k]?) eq
      simp only [List.getElem?_append_left below, List.getElem?_take, List.getElem?_drop] at at_k
      simp only [show k < xs.length + 1 by omega, if_true] at at_k
      rw [← Array.getElem?_toList, ← at_k]
      intro zero
      exact nz (List.mem_of_getElem? zero)

/-- A live header (the history's premise of `deflateBound`) gives the strings it measures. -/
theorem hdrStrOk_of_live {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv h r ds z d) (live : DeflateHeaderLive h r) : HdrStrOk h d := by
  obtain ⟨z', get, all⟩ := live
  have same : z' = z := Option.some.inj (get.symm.trans inv.good.live.hz)
  subst same
  rcases all ds d inv.good.live.zst inv.good.live.hs with none | ⟨i, g, head, gh, _, _, name, comment⟩
  · exact Or.inl none
  · refine Or.inr ⟨i, g, head, gh, ?_, ?_⟩
    · by_cases null : g.name = .null
      · exact Or.inl null
      · obtain ⟨xs, c⟩ := name null
        exact Or.inr ⟨xs.length, cstring_gzStr c⟩
    · by_cases null : g.comment = .null
      · exact Or.inl null
      · obtain ⟨xs, c⟩ := comment null
        exact Or.inr ⟨xs.length, cstring_gzStr c⟩

/-- `deflateBound` and `deflateBound_z` read the state and the live header. -/
theorem step_bound {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv h r ds z d) (live : DeflateHeaderLive h r) (n : UInt64) :
    StepOk h r (.deflateBound (some r) n) := by
  obtain ⟨wl, -, run⟩ := deflateBound_safe inv.good (hdrStrOk_of_live inv live) n
  exact step_unchanged inv _ (heapCall_run run) rfl

theorem step_bound_z {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv h r ds z d) (live : DeflateHeaderLive h r) (n : UInt64) :
    StepOk h r (.deflateBound_z (some r) n) := by
  obtain ⟨wl, -, run⟩ := deflateBound_z_safe inv.good (hdrStrOk_of_live inv live) n
  exact step_unchanged inv _ (heapCall_run run) rfl

/-- The invariant moves to a heap that keeps the bytes and words of the five owned blocks and the
static tables, when `DGood` is already known there. -/
theorem DInv.transfer {h h' : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv h r ds z d) (good' : DGood h' r ds z d) (static : h'.static = h.static)
    (bytes : ∀ b, DeflateOwned ds d b → h'.bytes b = h.bytes b)
    (words : ∀ b, DeflateOwned ds d b → h'.words b = h.words b) : DInv h' r ds z d := by
  have win : ∀ w, d.window = .ref (.blk w) 0 → h'.bytes w = h.bytes w :=
    fun w e => bytes w (Or.inr (Or.inl e))
  have prv : ∀ p, d.prev = .ref (.blk p) 0 → h'.words p = h.words p :=
    fun p e => words p (Or.inr (Or.inr (Or.inl e)))
  have hd : ∀ q, d.head = .ref (.blk q) 0 → h'.words q = h.words q :=
    fun q e => words q (Or.inr (Or.inr (Or.inr (Or.inl e))))
  have pb : ∀ b, d.pending_buf = .ref (.blk b) 0 → h'.bytes b = h.bytes b :=
    fun b e => bytes b (Or.inr (Or.inr (Or.inr (Or.inr e))))
  refine ⟨good', inv.alloc, ?_, inv.shape, ⟨fun zero => ?_, fun one => ?_⟩, ?_⟩
  · unfold LibraryGlobals at *; rw [static]; exact inv.globals
  · obtain ⟨w, p, q, wa, pa, qa, ew, ep, eq, hw, hp, hq, H⟩ := inv.hashing.chains zero
    exact ⟨w, p, q, wa, pa, qa, ew, ep, eq, (win w ew).trans hw, (prv p ep).trans hp, (hd q eq).trans hq, H⟩
  · obtain ⟨w, p, q, wa, pa, qa, ew, ep, eq, hw, hp, hq, H⟩ := inv.hashing.slid one
    exact ⟨w, p, q, wa, pa, qa, ew, ep, eq, (win w ew).trans hw, (prv p ep).trans hp, (hd q eq).trans hq, H⟩
  · obtain ⟨⟨xs, ⟨b, a, pbuf, hb, ledger⟩, near⟩, clear, below⟩ := inv.symbols
    exact ⟨⟨xs, ⟨b, a, pbuf, (pb b pbuf).trans hb, ledger⟩, near⟩, clear, below⟩

/-- `deflateGetDictionary` copies the last `min (strstart + lookahead) w_size` window bytes into
the caller's buffer. `plain`: the buffer is a caller byte block, not memory inside another
stream's state (the owner's rule on caller regions; to be supplied by the history's separation
clause, `docs/deviations.md`). -/
theorem step_getDictionary {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv h r ds z d) (dictionary : BPtr) (hasDictLength : Bool)
    (args : CallerRange h r dictionary (min d.w_size.toNat (d.strstart.toNat + d.lookahead.toNat)) true)
    (plain : ∀ q off, dictionary = .ref q off → ∃ x, q = .blk x) :
    StepOk h r (.deflateGetDictionary (some r) dictionary hasDictLength) := by
  have hI := inv.good.inv
  obtain ⟨w, p, q, b, hB⟩ := hI.blocks
  have hws : d.w_size.toNat ≤ 32768 := by
    have := hI.wsize; have := hI.wbits_hi
    have : 2 ^ d.w_bits.toNat ≤ 2 ^ 15 := Nat.pow_le_pow_right (by omega) hI.wbits_hi
    omega
  have hfill := inv.shape.room
  have hlen := dictLen_toNat hI.wsz hws hfill
  have notOwnedBlk : ∀ x off, dictionary = .ref (.blk x) off → ¬ DeflateOwned ds d x := by
    intro x off eq owned
    rcases args with null | ⟨_, _, notOwned⟩
    · rw [eq] at null; cases null
    · exact notOwned x (by rw [eq]; rfl) ((inv.owned x).2 owned)
  have hdict : dictionary ≠ .null → dictLen d ≠ 0 →
      DictDest h d (d.strstart.toNat + d.lookahead.toNat - (dictLen d).toNat) (dictLen d).toNat dictionary := by
    intro nn _
    rcases args with null | ⟨⟨xs, bytes⟩, writable, _⟩
    · exact absurd null nn
    rcases bytes with ⟨null, _, _⟩ | ⟨q', i, a, eq, get, fit, _⟩
    · exact absurd null nn
    obtain ⟨x, rfl⟩ := plain q' i eq
    rcases writable rfl with ⟨null, _⟩ | ⟨q2, i2, a2, eq2, get2, ro2, _⟩
    · exact absurd null nn
    rw [eq] at eq2
    cases eq2
    refine ⟨x, i, a, eq, get, ro2, by omega, fun w' ew => Or.inl ?_⟩
    rintro rfl
    exact notOwnedBlk x i eq (Or.inr (Or.inl ew))
  obtain ⟨h', run, good', -, dst, str, gzs, wrd, ro, gzh, ist, nb, na, st, ao, gb, outside, inside⟩ :=
    deflateGetDictionary_safe inv.good hfill dictionary hasDictLength hdict
  have bytesOwned : ∀ y, DeflateOwned ds d y → h'.bytes y = h.bytes y := by
    intro y owned
    exact outside y (fun off eq => notOwnedBlk y off eq owned)
  have inv' := inv.transfer good' st bytesOwned (fun y _ => by rw [wrd])
  refine ⟨_, h', heapCall_run run, ⟨ds, z, d, inv'⟩, ⟨?_, ?_⟩, ?_⟩
  · -- the frame after restoring the caller's buffer
    have restored : ∀ y, (restoreRegions h h' [⟨dictionary, 32768⟩]).bytes y = h.bytes y := by
      intro y
      by_cases blk : ∃ off, dictionary = .ref (.blk y) off
      · obtain ⟨off, eq⟩ := blk
        cases hy : h.bytes y with
        | none =>
          simp only [restoreRegions, List.foldl, eq]
          change (match h.bytes y with | none => h' | some a => _).bytes y = _
          rw [hy]; simp only
          rcases args with null | ⟨⟨xs, bytes⟩, _, _⟩
          · rw [eq] at null; cases null
          · rcases bytes with ⟨null, _, _⟩ | ⟨q', i, a, eq', get, _, _⟩
            · rw [eq] at null; cases null
            · rw [eq] at eq'; cases eq'; change h.bytes y = some a at get; rw [hy] at get; cases get
        | some a =>
          simp only [restoreRegions, List.foldl, eq]
          change (match h.bytes y with | none => h' | some a => Space.put h' (BRef.blk y) a).bytes y = _
          rw [hy]
          show (upd h'.bytes y (some a)) y = some a
          exact upd_same _ _ _
      · have other : ∀ off, dictionary ≠ .ref (.blk y) off := fun off eq => blk ⟨off, eq⟩
        rcases hd : dictionary with _ | ⟨q', off⟩
        · simp only [restoreRegions, List.foldl]
          exact outside y other
        · simp only [restoreRegions, List.foldl]
          obtain ⟨x, rfl⟩ := plain q' off hd
          have xy : x ≠ y := fun e => other off (by rw [hd, e])
          change (match h.bytes x with | none => h' | some a => Space.put h' (BRef.blk x) a).bytes y = _
          cases h.bytes x with
          | none => exact outside y other
          | some a =>
            show (upd h'.bytes x (some a)) y = h.bytes y
            rw [upd_ne _ _ _ _ (Ne.symm xy)]
            exact outside y other
    have restoreEq : ∃ bs, restoreRegions h h' [⟨dictionary, 32768⟩] = { h' with bytes := bs } := by
      rcases hd : dictionary with _ | ⟨q', off⟩
      · exact ⟨h'.bytes, by simp only [restoreRegions, List.foldl]⟩
      · obtain ⟨x, rfl⟩ := plain q' off hd
        simp only [restoreRegions, List.foldl]
        change ∃ bs, (match h.bytes x with | none => h' | some a => Space.put h' (BRef.blk x) a) = _
        cases h.bytes x with
        | none => exact ⟨h'.bytes, rfl⟩
        | some a => exact ⟨upd h'.bytes x (some a), rfl⟩
    obtain ⟨bs, eq⟩ := restoreEq
    have rb : ∀ y, bs y = h.bytes y := by
      intro y; have := restored y; rw [eq] at this; exact this
    change Frame h (restoreRegions h h' [⟨dictionary, 32768⟩]) _
    rw [eq]
    refine ⟨st.symm, ao.symm, gb.symm, Nat.le_of_eq nb.symm, Nat.le_of_eq na.symm, fun y _ _ => ?_⟩
    exact ⟨rb y, by rw [wrd], by rw [str], by rw [gzh], by rw [dst], by rw [ist], by rw [gzs], by rw [ro]⟩
  · intro region mem q' off a ptr get
    have mem' := List.mem_singleton.mp mem
    subst mem'
    obtain ⟨x, rfl⟩ := plain q' off ptr
    obtain ⟨wa, hwa, -⟩ := hB.wa
    obtain ⟨a', get', size, -, keep⟩ := inside w wa hB.win hwa x off a ptr get
    refine ⟨a', get', size, fun j hj notCovered => ?_⟩
    have away : j < off ∨ off + (dictLen d).toNat ≤ j := by
      rcases Nat.lt_or_ge j off with lt | ge
      · exact Or.inl lt
      · rcases Nat.lt_or_ge j (off + (dictLen d).toNat) with lt2 | ge2
        · have bound : (dictLen d).toNat ≤ 32768 := by omega
          have below : j < off + 32768 := by omega
          exact absurd ⟨⟨dictionary, 32768⟩, List.mem_singleton.mpr rfl, off, ptr, ge, below⟩ notCovered
        · exact Or.inr ge2
    have kept := keep j away
    rw [Array.getElem?_eq_getElem (by omega), Array.getElem?_eq_getElem hj]
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (show j < a'.size by omega),
      Array.getElem?_eq_getElem hj, Option.getD_some] at kept
    rw [kept]
  · have liveSame : ∀ y, h'.live y ↔ h.live y := by
      intro y
      have bytesNone : h'.bytes y = none ↔ h.bytes y = none := by
        by_cases blk : ∃ off, dictionary = .ref (.blk y) off
        · obtain ⟨off, ptr⟩ := blk
          cases hy : h.bytes y with
          | none =>
            rcases args with null | ⟨⟨xs, bytes⟩, _, _⟩
            · rw [ptr] at null; cases null
            · rcases bytes with ⟨null, _, _⟩ | ⟨q', i, a, eq', get, _, _⟩
              · rw [ptr] at null; cases null
              · rw [ptr] at eq'; cases eq'; change h.bytes y = some a at get; rw [hy] at get; cases get
          | some a =>
            obtain ⟨wa, hwa, -⟩ := hB.wa
            obtain ⟨a', get', -⟩ := inside w wa hB.win hwa y off a ptr hy
            simp [get']
        · rw [outside y (fun off e => blk ⟨off, e⟩)]
      unfold Heap.live
      rw [wrd, str, gzh, dst, ist, gzs]
      constructor
      · rintro (b' | rest)
        · exact Or.inl (fun e => b' (bytesNone.2 e))
        · exact Or.inr rest
      · rintro (b' | rest)
        · exact Or.inl (fun e => b' (bytesNone.1 e))
        · exact Or.inr rest
    intro y
    rw [liveSame y]
    constructor
    · intro live
      refine Or.inl ⟨live, fun ⟨owned, not⟩ => not ?_⟩
      exact (inv'.owned y).2 ((inv.owned y).1 owned)
    · rintro (⟨live, _⟩ | ⟨owned, _⟩)
      · exact live
      · exact owned_live inv.good ((inv'.owned y).1 owned)

end Zlib.Deflate.Universal
