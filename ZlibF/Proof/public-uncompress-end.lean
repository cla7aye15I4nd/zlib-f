import ZlibF.Proof.«public-uncompress-init»

/-!
# uncompr.c: storing the counts, ending the stream and freeing the automatic objects

After the loop `uncompress2_z` stores the consumed and produced lengths in the
caller cells, calls `inflateEnd`, and frees `stream.reserved` and the automatic
`z_stream`. The final heap equals, entry by entry, the caller heap with the output and
both cells written.
-/

namespace ZlibF.Spec.Public.Proofs.Uncompress
open C ZlibF.Spec ZlibF.Spec.Public Zlib.Gzguts Zlib.Inflate.Proofs Zlib.Inflate.Spec Zlib.Uncompr
open Zlib.Inflate (inflate inflateEnd)
set_option autoImplicit false

/-- A store of a nonempty list is a `writeOut`. -/
theorem store_eq_writeOut {h h' : Heap} {p : BPtr} {xs : List UInt8} (st : Store h p xs h') (ne : xs ≠ []) :
    h' = writeOut h p xs := by
  rcases st with ⟨e, -⟩ | ⟨r, i, a, rfl, g, -, -, rfl⟩
  · exact absurd e ne
  · simp [writeOut, g, ne]

/-- The same write on two heaps that agree on the written view keeps them in agreement. -/
theorem Agree.writeOut_both {keep : Nat → Prop} {E H : Heap} (agree : Agree keep E H) {p : BPtr}
    {xs : List UInt8} (kept : ∀ r i, p = .ref r i → ∀ c, BRef.block r = some c → keep c) :
    Agree keep (writeOut E p xs) (writeOut H p xs) := by
  cases p with
  | null => exact agree
  | ref r i =>
    have g := (agree.get (kept r i rfl)).1
    unfold writeOut
    simp only []
    rw [g]
    cases Space.get E r with
    | none => exact agree
    | some a =>
      simp only []
      split
      · exact agree
      · obtain ⟨eS, eA, eG, eB⟩ := put_globals E r (a.extract 0 i ++ xs.toArray ++ a.extract (i + xs.length) a.size)
        obtain ⟨hS, hA, hG, hB⟩ := put_globals H r (a.extract 0 i ++ xs.toArray ++ a.extract (i + xs.length) a.size)
        refine ⟨fun b kb => SameAt.put _ (agree.blocks b kb) (fun c hc => agree.blocks c (kept r i rfl c hc)),
          ?_, ?_, ?_, ?_⟩
        · rw [hS, eS]; exact agree.static
        · rw [hA, eA]; exact agree.allocOk
        · rw [hG, eG]; exact agree.garbage
        · rw [hB, eB]; exact agree.borrow

/-- What a write through a byte view changes: at most the view's own block. -/
theorem writeOut_same_other {H : Heap} {p : BPtr} {xs : List UInt8} (b : Nat)
    (other : ∀ r i, p = .ref r i → BRef.block r ≠ some b) : SameAt H (writeOut H p xs) b := by
  unfold writeOut
  split
  · rename_i r i
    split
    · split
      · exact SameAt.refl H b
      · exact SameAt.put_other H _ (other r i rfl)
    · exact SameAt.refl H b
  · exact SameAt.refl H b

theorem writeOut_streams (H : Heap) (p : BPtr) (xs : List UInt8) : (writeOut H p xs).streams = H.streams := by
  unfold writeOut
  split
  · split
    · split
      · rfl
      · rename_i r _ _ _ _ _
        cases r with
        | dstate_depth c => simp only [Space.put]; split <;> rfl
        | _ => rfl
    · rfl
  · rfl

theorem writeOut_istates (H : Heap) (p : BPtr) (xs : List UInt8) : (writeOut H p xs).istates = H.istates := by
  unfold writeOut
  split
  · split
    · split
      · rfl
      · rename_i r _ _ _ _ _
        cases r with
        | dstate_depth c => simp only [Space.put]; split <;> rfl
        | _ => rfl
    · rfl
  · rfl

theorem writeOut_globals (H : Heap) (p : BPtr) (xs : List UInt8) :
    (writeOut H p xs).static = H.static ∧ (writeOut H p xs).allocOk = H.allocOk ∧
    (writeOut H p xs).garbage = H.garbage ∧ (writeOut H p xs).nextBlk = H.nextBlk ∧
    (writeOut H p xs).nalloc = H.nalloc ∧ (writeOut H p xs).libcErrorBorrow = H.libcErrorBorrow := by
  unfold writeOut
  split
  · split
    · split
      · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
      · rename_i r _ _ _ _ _
        cases r with
        | dstate_depth c => simp only [Space.put]; split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
        | _ => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem writeOut_uniq {H : Heap} {p : BPtr} {xs : List UInt8} (u : Uniq H) : Uniq (writeOut H p xs) := by
  intro b
  have ub := u b
  cases p with
  | null => exact ub
  | ref r i =>
    simp only [writeOut]
    cases g : Space.get H r with
    | none => exact ub
    | some a =>
      simp only []
      split
      · exact ub
      · cases r with
        | blk c =>
          simp only [Space.get] at g
          simp only [Space.put, upd_apply]
          by_cases e : b = c
          · subst e; simpa [g] using ub
          · simpa [e] using ub
        | dstate_depth c =>
          simp only [Space.get] at g
          cases ds : H.dstates c with
          | none => rw [ds] at g; cases g
          | some st =>
            simp only [Space.put, ds, upd_apply]
            by_cases e : b = c
            · subst e; simpa [ds] using ub
            · simpa [e] using ub
        | _ => exact ub

/-- A caller write to a block that the stream neither is nor owns is a rebuffer. -/
theorem writeOut_rebuffer {H : Heap} {k : Nat} {i : Nat} {z : ZStream} {s : InflateState}
    (good : Good H (.tab k) i z s) (globals : LibraryGlobals H) {p : BPtr} {xs : List UInt8}
    (away : ∀ rr j, p = .ref rr j → ∀ c, BRef.block rr = some c → ¬ StreamOwned H (.tab k) c) :
    Rebuffer H (writeOut H p xs) (.tab k) := by
  obtain ⟨gS, gA, gG, gN, gNa, -⟩ := writeOut_globals H p xs
  refine ⟨?_, writeOut_uniq good.uniq, ?_, ?_, z, z, good.live.hz, ?_, rfl⟩
  · intro b hb live
    rw [writeOut_live] at live
    exact good.fresh b (by rw [gN] at hb; exact hb) live
  · simp only [LibraryGlobals] at globals ⊢; rw [gS]; exact globals
  · refine ⟨gS.symm, gA.symm, gG.symm, by rw [gN]; exact Nat.le_refl _, by rw [gNa]; exact Nat.le_refl _, ?_⟩
    intro b _ notChanged
    have owned : StreamOwned H (.tab k) b := Classical.byContradiction notChanged
    have same := writeOut_same_other (H := H) (p := p) (xs := xs) b (fun rr j hp hb => by
      exact away rr j hp b hb owned)
    obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8⟩ := same
    exact ⟨s1, s2, s3, s4, s5, s6, s7, s8⟩
  · have := good.live.hz
    simp only [ZStreamRef.get] at this ⊢
    rw [writeOut_streams]; exact this

theorem writeOut_fit {H : Heap} {p : BPtr} {xs : List UInt8} (fit : ZlibF.PlatformMemory.ByteObjectsFit H)
    (w : Writable H p xs.length) : ZlibF.PlatformMemory.ByteObjectsFit (writeOut H p xs) := by
  intro rr a g
  by_cases same : ∃ j, p = .ref rr j
  · obtain ⟨j, rfl⟩ := same
    rcases w with ⟨h0, -⟩ | ⟨r', j', a', hq, g', ro, fitw⟩
    · cases h0
    cases hq
    rcases writeOut_same (xs := xs) (i := j) g' ro with e | ⟨-, e⟩
    · have ea := Option.some.inj (e.symm.trans g)
      rw [← ea, written_size _ j xs (by omega)]
      exact fit rr _ g'
    · have ea := Option.some.inj (e.symm.trans g)
      rw [← ea]; exact fit rr _ g'
  · have same' : ∀ j, p ≠ .ref rr j := fun j e => same ⟨j, e⟩
    rw [writeOut_other same'] at g
    exact fit rr a g

/-- The caller's length cells for the run. -/
structure Cells (e : Env) (sourceLen destLen : BPtr) (n64 cap64 : UInt64) : Prop where
  scell : LengthCell e.h₀ sourceLen n64
  dcell : LengthCell e.h₀ destLen cap64
  hn : n64.toNat = e.n
  hcap : cap64.toNat = e.cap
  sepS : Separate sourceLen 8 e.out0 e.cap
  sepD : Separate destLen 8 e.out0 e.cap
  sepSD : Separate destLen 8 sourceLen 8

theorem cell_blocks {h : Heap} {p : BPtr} {v : UInt64} (c : LengthCell h p v) :
    ∀ r j, p = .ref r j → ∀ b, BRef.block r = some b → h.live b := by
  intro r j hp b hb
  rcases c.1 with ⟨-, h8, -⟩ | ⟨r', j', a, hq, g, -, -⟩
  · cases h8
  · rw [hq] at hp; cases hp; exact view_block_live g b hb

/-- A cell is still a cell after a write to a separate range. -/
theorem cell_writeOut_sep {h : Heap} {p q : BPtr} {v : UInt64} {c : Nat} {xs : List UInt8}
    (cell : LengthCell h p v) (sep : Separate p 8 q c) (len : xs.length ≤ c) (w : Writable h q c) :
    LengthCell (writeOut h q xs) p v :=
  ⟨bytes_writeOut_sep cell.1 sep len w, writable_writeOut cell.2 len w⟩

/-- A cell of the caller heap is a cell of the heap after the output was written. -/
theorem cell_after_output {e : Env} {p : BPtr} {v : UInt64} {out : List UInt8} (ok : EnvOK e)
    (cell : LengthCell e.h₀ p v) (sep : Separate p 8 e.out0 e.cap) (len : out.length ≤ e.cap) :
    LengthCell (writeOut e.h₀ e.out0 out) p v := by
  rcases ok.outW with ⟨-, cap0⟩ | W
  · have : out = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this; rw [writeOut_nil]; exact cell
  · exact cell_writeOut_sep cell sep len W

theorem Agree.cell {keep : Nat → Prop} {E H : Heap} (agree : Agree keep E H) {p : BPtr} {v : UInt64}
    (cell : LengthCell E p v) (kept : ∀ r j, p = .ref r j → ∀ c, BRef.block r = some c → keep c) :
    LengthCell H p v :=
  ⟨agree.bytes cell.1 kept, agree.writable cell.2 kept⟩

/-- On a reachable heap with the same stream record and state, the decoder is the same. -/
theorem good_of_reach {H H' : Heap} {r : ZStreamRef} {i : Nat} {z : ZStream}
    {s : InflateState} (good : Good H r i z s) (reach : StreamReachable .inflate H' r)
    (hz : r.get H' = some z) (hs : H'.istates i = some s) : Good H' r i z s := by
  obtain ⟨i', z', s', g', -⟩ := reach_invariant reach
  have ez : z' = z := Option.some.inj (g'.live.hz.symm.trans hz)
  subst ez
  have ei : i' = i := by
    have := g'.live.zst
    rw [good.live.zst] at this
    cases this; rfl
  subst ei
  have es : s' = s := Option.some.inj (g'.live.hs.symm.trans hs)
  subst es
  exact g'

/-- `inflateEnd` leaves every block that is neither the stream nor owned by it. -/
theorem end_same {W : Heap} {k i : Nat} {s : InflateState} (z' : ZStream) (b : Nat) (nk : b ≠ k)
    (no : ¬ InflateOwned i s b) :
    SameAt W ((ZStreamRef.tab k).put (endHeap W i s) z') b := by
  have ni : b ≠ i := fun e => no (Or.inl e)
  have nw : ∀ w, s.window = .ref (.blk w) 0 → b ≠ w := fun w hw e => no (Or.inr (by rw [hw, e]))
  have base : SameAt W (endHeap W i s) b := by
    simp only [endHeap, freeIst, freeWin]
    split
    · rename_i w hw
      exact ⟨by simp [upd_ne _ _ _ _ (nw w hw)], rfl, rfl, rfl, rfl, by simp [upd_ne _ _ _ _ ni], rfl, rfl⟩
    · exact ⟨rfl, rfl, rfl, rfl, rfl, by simp [upd_ne _ _ _ _ ni], rfl, rfl⟩
  refine base.trans ?_
  simp only [ZStreamRef.put]
  split
  · exact ⟨rfl, rfl, by simp [upd_ne _ _ _ _ nk], rfl, rfl, rfl, rfl, rfl⟩
  · exact SameAt.refl _ b

theorem end_globals (W : Heap) (k i : Nat) (s : InflateState) (z' : ZStream) :
    ((ZStreamRef.tab k).put (endHeap W i s) z').static = W.static ∧
    ((ZStreamRef.tab k).put (endHeap W i s) z').allocOk = W.allocOk ∧
    ((ZStreamRef.tab k).put (endHeap W i s) z').garbage = W.garbage ∧
    ((ZStreamRef.tab k).put (endHeap W i s) z').nextBlk = W.nextBlk ∧
    ((ZStreamRef.tab k).put (endHeap W i s) z').nalloc = W.nalloc := by
  simp only [ZStreamRef.put, endHeap, freeIst, freeWin]
  split <;> split <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem cnt_eq_zero {α : Type} {o : Option α} : cnt o = 0 ↔ o = none := by
  cases o <;> simp [cnt]

theorem uniq_streams_only {H : Heap} {b : Nat} {x : ZStream} (u : Uniq H) (hs : H.streams b = some x) :
    H.bytes b = none ∧ H.words b = none ∧ H.gzheaders b = none ∧ H.dstates b = none ∧
      H.istates b = none ∧ H.gzstates b = none := by
  have ub := u b
  rw [hs, cnt_some] at ub
  exact ⟨cnt_eq_zero.1 (by omega), cnt_eq_zero.1 (by omega), cnt_eq_zero.1 (by omega),
    cnt_eq_zero.1 (by omega), cnt_eq_zero.1 (by omega), cnt_eq_zero.1 (by omega)⟩

theorem uniq_bytes_only {H : Heap} {b : Nat} {x : Array UInt8} (u : Uniq H) (hs : H.bytes b = some x) :
    H.words b = none ∧ H.streams b = none ∧ H.gzheaders b = none ∧ H.dstates b = none ∧
      H.istates b = none ∧ H.gzstates b = none := by
  have ub := u b
  rw [hs, cnt_some] at ub
  exact ⟨cnt_eq_zero.1 (by omega), cnt_eq_zero.1 (by omega), cnt_eq_zero.1 (by omega),
    cnt_eq_zero.1 (by omega), cnt_eq_zero.1 (by omega), cnt_eq_zero.1 (by omega)⟩

/-- The final heap: both automatic objects freed. -/
def freedHeap (H : Heap) (k : Nat) : Heap :=
  { reservedFreed H k with streams := upd (reservedFreed H k).streams k none }

/-- Storing the counts, ending the stream and freeing the automatic objects. -/
theorem epilogue {e : Env} (ok : EnvOK e) {sourceLen destLen : BPtr}
    {n64 cap64 : UInt64} (cells : Cells e sourceLen destLen n64 cap64) {l : UncLoop} {rc : Int32}
    {Hp H : Heap} {logp : DataLog} {input output : List UInt8} {u i : Nat} {zp z : ZStream}
    {sp s : InflateState} (fin : SafeFinal e l rc Hp H logp input output u i zp z sp s) :
    ∃ H1 H2 H3,
      load64 sourceLen H = .ok (n64, H) ∧
      store64 sourceLen (n64 - (l.len + z.avail_in.toUInt64)) H = .ok ((), H1) ∧
      load64 destLen H1 = .ok (cap64, H1) ∧
      store64 destLen (cap64 - (l.left + z.avail_out.toUInt64)) H1 = .ok ((), H2) ∧
      C.run (inflateEnd (some e.r)) H2 = .ok (Z_OK, H3) ∧
      H3.bytes (e.k + 1) = some (reservedBytes e.h₀) ∧ H3.ro (e.k + 1) = false ∧
      (∃ zz, (reservedFreed H3 e.k).streams e.k = some zz) ∧
      SameObjectsUpToTableShape
        (writeOut (writeOut (writeOut e.h₀ e.out0 (logp.output ++ output)) sourceLen
          (lengthBytes (n64 - (l.len + z.avail_in.toUInt64)))) destLen
          (lengthBytes (cap64 - (l.left + z.avail_out.toUInt64))))
        (freedHeap H3 e.k) ∧
      (rc = Z_MEM_ERROR → AllocationFailed e.h₀ (freedHeap H3 e.k)) := by
  have outC := fin.outCount
  have outLe : (logp.output ++ output).length ≤ e.cap := by omega
  have k0 : ¬ e.h₀.live e.k := ok.fresh e.k (Nat.le_refl _)
  have k1 : ¬ e.h₀.live (e.k + 1) := ok.fresh (e.k + 1) (Nat.le_succ _)
  have away : ∀ (q : BPtr) (v : UInt64), LengthCell e.h₀ q v → ∀ rr j, q = .ref rr j → ∀ c,
      BRef.block rr = some c → ¬ StreamOwned H e.r c := by
    intro q v cell rr j hq c hc own
    exact fin.notOwned c (Or.inl (cell_blocks cell rr j hq c hc)) (streamOwned_of fin.good own)
  -- the source-length cell
  have cellS_E := cell_after_output ok cells.scell cells.sepS outLe
  have cellS_H := fin.agree.cell cellS_E (cell_blocks cells.scell)
  obtain ⟨H1, run1, st1⟩ := store64_writable (n64 - (l.len + z.avail_in.toUInt64)) cellS_H.2
  have lbne : ∀ v, lengthBytes v ≠ [] := by intro v h; have := congrArg List.length h; simp [lengthBytes_length] at this
  have H1eq := store_eq_writeOut st1 (lbne _)
  subst H1eq
  have agree1 := fin.agree.writeOut_both (xs := lengthBytes (n64 - (l.len + z.avail_in.toUInt64)))
    (cell_blocks cells.scell)
  -- the output-length cell
  have cellD_E := cell_after_output ok cells.dcell cells.sepD outLe
  have cellD_E1 := cell_writeOut_sep (xs := lengthBytes (n64 - (l.len + z.avail_in.toUInt64))) cellD_E cells.sepSD
    (by simp [lengthBytes_length]) cellS_E.2
  have cellD_H1 := agree1.cell cellD_E1 (cell_blocks cells.dcell)
  obtain ⟨H2, run2, st2⟩ := store64_writable (cap64 - (l.left + z.avail_out.toUInt64)) cellD_H1.2
  have H2eq := store_eq_writeOut st2 (lbne _)
  subst H2eq
  have agree2 := agree1.writeOut_both (xs := lengthBytes (cap64 - (l.left + z.avail_out.toUInt64)))
    (cell_blocks cells.dcell)
  -- both writes are caller edits
  obtain ⟨W1, hW1⟩ : ∃ W1, writeOut H sourceLen (lengthBytes (n64 - (l.len + z.avail_in.toUInt64))) = W1 :=
    ⟨_, rfl⟩
  rw [hW1] at run2 agree2 cellD_H1 st2 agree1
  obtain ⟨W2, hW2⟩ : ∃ W2, writeOut W1 destLen (lengthBytes (cap64 - (l.left + z.avail_out.toUInt64))) = W2 :=
    ⟨_, rfl⟩
  rw [hW2] at run2 agree2 st2
  have rb1 : Rebuffer H W1 e.r := hW1 ▸ writeOut_rebuffer fin.good fin.globals (away sourceLen n64 cells.scell)
  have fit1 : ZlibF.PlatformMemory.ByteObjectsFit W1 :=
    hW1 ▸ writeOut_fit fin.fit (by rw [lengthBytes_length]; exact cellS_H.2)
  have reach1 : StreamReachable .inflate W1 e.r := .rebuffer fin.reach rb1 (fun _ => fit1)
  have hz1 : e.r.get W1 = some z := by
    have := fin.good.live.hz
    simp only [Env.r, ZStreamRef.get] at this ⊢
    rw [← hW1, writeOut_streams]; exact this
  have good1 : Good W1 e.r i z s :=
    good_of_reach fin.good reach1 hz1 (by rw [← hW1, writeOut_istates]; exact fin.good.live.hs)
  have globals1 : LibraryGlobals W1 := by
    simp only [LibraryGlobals]
    have g0 := fin.globals
    simp only [LibraryGlobals] at g0
    rw [← hW1, (writeOut_globals _ _ _).1]; exact g0
  have away1 : ∀ rr j, destLen = .ref rr j → ∀ c, BRef.block rr = some c → ¬ StreamOwned W1 e.r c := by
    intro rr j hq c hc own
    exact fin.notOwned c (Or.inl (cell_blocks cells.dcell rr j hq c hc)) (streamOwned_of good1 own)
  have rb2 : Rebuffer W1 W2 e.r := hW2 ▸ writeOut_rebuffer good1 globals1 away1
  have fit2 : ZlibF.PlatformMemory.ByteObjectsFit W2 :=
    hW2 ▸ writeOut_fit fit1 (by rw [lengthBytes_length]; exact cellD_H1.2)
  have reach2 : StreamReachable .inflate W2 e.r := .rebuffer reach1 rb2 (fun _ => fit2)
  have hz2 : e.r.get W2 = some z := by
    have := hz1
    simp only [Env.r, ZStreamRef.get] at this ⊢
    rw [← hW2, writeOut_streams]; exact this
  have good2 : Good W2 e.r i z s :=
    good_of_reach good1 reach2 hz2 (by rw [← hW2, writeOut_istates]; exact good1.live.hs)
  -- the end of the stream
  obtain ⟨H3, runE, H3eq, uniq3, -, get3, owns, -⟩ := inflateEnd_safe good2 fin.alloc.2
  have notOwnK1 : ¬ InflateOwned i s (e.k + 1) := fin.notOwned _ (Or.inr (Or.inr rfl))
  have notOwnK : ¬ InflateOwned i s e.k := fin.notOwned _ (Or.inr (Or.inl rfl))
  have sameK1 : SameAt W2 H3 (e.k + 1) := by
    rw [H3eq]; exact end_same _ _ (by simp [Env.k]) notOwnK1
  have cellsNotK1 : ∀ (q : BPtr) (v : UInt64), LengthCell e.h₀ q v → ∀ rr j, q = .ref rr j →
      BRef.block rr ≠ some (e.k + 1) := by
    intro q v cell rr j hq hb
    exact k1 (cell_blocks cell rr j hq _ hb)
  have resW2 : W2.bytes (e.k + 1) = H.bytes (e.k + 1) ∧ W2.ro (e.k + 1) = H.ro (e.k + 1) := by
    have a := writeOut_same_other (H := H) (p := sourceLen) (xs := lengthBytes (n64 - (l.len + z.avail_in.toUInt64)))
      (e.k + 1) (cellsNotK1 sourceLen n64 cells.scell)
    have b := writeOut_same_other (H := W1) (p := destLen) (xs := lengthBytes (cap64 - (l.left + z.avail_out.toUInt64)))
      (e.k + 1) (cellsNotK1 destLen cap64 cells.dcell)
    rw [hW1] at a; rw [hW2] at b
    exact ⟨b.1.trans a.1, b.2.2.2.2.2.2.2.trans a.2.2.2.2.2.2.2⟩
  have res3 : H3.bytes (e.k + 1) = some (reservedBytes e.h₀) ∧ H3.ro (e.k + 1) = false := by
    refine ⟨?_, ?_⟩
    · rw [sameK1.1, resW2.1]; exact fin.reservedBytes
    · rw [sameK1.2.2.2.2.2.2.2, resW2.2]; exact fin.reservedRo
  have Fg : (freedHeap H3 e.k).static = H.static ∧ (freedHeap H3 e.k).allocOk = H.allocOk ∧
      (freedHeap H3 e.k).garbage = H.garbage ∧ (freedHeap H3 e.k).nextBlk = H.nextBlk ∧
      (freedHeap H3 e.k).nalloc = H.nalloc := by
    obtain ⟨a1, a2, a3, a4, a5⟩ := end_globals W2 e.k i s { z with state := none }
    obtain ⟨b1, b2, b3, b4, b5, -⟩ := writeOut_globals H sourceLen (lengthBytes (n64 - (l.len + z.avail_in.toUInt64)))
    obtain ⟨c1, c2, c3, c4, c5, -⟩ := writeOut_globals W1 destLen (lengthBytes (cap64 - (l.left + z.avail_out.toUInt64)))
    rw [hW1] at b1 b2 b3 b4 b5
    rw [hW2] at c1 c2 c3 c4 c5
    simp only [freedHeap, reservedFreed]
    rw [H3eq]
    exact ⟨a1.trans (c1.trans b1), a2.trans (c2.trans b2), a3.trans (c3.trans b3), a4.trans (c4.trans b4),
      a5.trans (c5.trans b5)⟩
  refine ⟨W1, W2, H3, load64_cell cellS_H, run1.trans (by rw [hW1]), load64_cell cellD_H1, run2, runE,
    res3.1, res3.2, ⟨{ z with state := none }, ?_⟩, ?_, ?_⟩
  · simp only [reservedFreed]
    have := get3
    simp only [Env.r, ZStreamRef.get] at this
    exact this
  · -- every block: the same objects, or empty on both sides
    have E2live : ∀ b, (writeOut (writeOut (writeOut e.h₀ e.out0 (logp.output ++ output)) sourceLen
        (lengthBytes (n64 - (l.len + z.avail_in.toUInt64)))) destLen
        (lengthBytes (cap64 - (l.left + z.avail_out.toUInt64)))).live b ↔ e.h₀.live b := by
      intro b; rw [writeOut_live, writeOut_live, writeOut_live]
    have ownedBy : ∀ b, InflateOwned i s b ↔ OwnedBy i s b := by
      intro b
      simp only [InflateOwned, OwnedBy, WinBlk]
      constructor
      · rintro (x | x)
        · exact Or.inl x
        · exact Or.inr ⟨b, x, rfl⟩
      · rintro (x | ⟨w, hw, rfl⟩)
        · exact Or.inl x
        · exact Or.inr hw
    have H3live : ∀ b, H3.live b ↔ W2.live b ∧ ¬ OwnedBy i s b :=
      owns (fun b => W2.live b) (fun _ => Iff.rfl)
    have W2live : ∀ b, W2.live b ↔ H.live b := by
      intro b
      rw [← hW2, writeOut_live, ← hW1, writeOut_live]
    have Fsame : ∀ b, b ≠ e.k → b ≠ e.k + 1 → SameAt H3 (freedHeap H3 e.k) b := by
      intro b n0 n1
      exact ⟨by simp [freedHeap, reservedFreed, upd_ne _ _ _ _ n1], rfl,
        by simp [freedHeap, reservedFreed, upd_ne _ _ _ _ n0], rfl, rfl, rfl, rfl, rfl⟩
    have Flive : ∀ b, (freedHeap H3 e.k).live b → e.h₀.live b := by
      intro b lb
      have streamK : H3.streams e.k = some { z with state := none } := by
        have := get3; simp only [Env.r, ZStreamRef.get] at this; exact this
      by_cases n0 : b = e.k
      · subst n0
        exfalso
        obtain ⟨u1, u2, u4, u5, u6, u7⟩ := uniq_streams_only uniq3 streamK
        simp only [Heap.live, freedHeap, reservedFreed, upd_apply, ite_true, show e.k ≠ e.k + 1 by omega,
          ite_false] at lb
        simp [u1, u2, u4, u5, u6, u7] at lb
      by_cases n1 : b = e.k + 1
      · subst n1
        exfalso
        obtain ⟨u2, u3, u4, u5, u6, u7⟩ := uniq_bytes_only uniq3 res3.1
        simp only [Heap.live, freedHeap, reservedFreed, upd_apply, ite_true, show e.k + 1 ≠ e.k by omega,
          ite_false] at lb
        simp [u2, u3, u4, u5, u6, u7] at lb
      have l3 : H3.live b := by
        obtain ⟨s1, s2, s3, s4, s5, s6, s7, -⟩ := Fsame b n0 n1
        simp only [Heap.live] at lb ⊢
        rw [s1, s2, s3, s4, s5, s6, s7] at lb; exact lb
      obtain ⟨lw, notOwn⟩ := (H3live b).1 l3
      rcases fin.liveOnly b ((W2live b).1 lw) with x | x | x | x
      · exact x
      · exact absurd x n0
      · exact absurd x n1
      · exact absurd ((ownedBy b).1 x) notOwn
    have per : ∀ b, SameAt (writeOut (writeOut (writeOut e.h₀ e.out0 (logp.output ++ output)) sourceLen
        (lengthBytes (n64 - (l.len + z.avail_in.toUInt64)))) destLen
        (lengthBytes (cap64 - (l.left + z.avail_out.toUInt64)))) (freedHeap H3 e.k) b ∨
        (¬ (writeOut (writeOut (writeOut e.h₀ e.out0 (logp.output ++ output)) sourceLen
        (lengthBytes (n64 - (l.len + z.avail_in.toUInt64)))) destLen
        (lengthBytes (cap64 - (l.left + z.avail_out.toUInt64)))).live b ∧ ¬ (freedHeap H3 e.k).live b) := by
      intro b
      by_cases live : e.h₀.live b
      · left
        have n0 : b ≠ e.k := fun x => k0 (x ▸ live)
        have n1 : b ≠ e.k + 1 := fun x => k1 (x ▸ live)
        have notOwn : ¬ InflateOwned i s b := fin.notOwned b (Or.inl live)
        have a := agree2.blocks b live
        have endS : SameAt W2 H3 b := by rw [H3eq]; exact end_same _ _ n0 notOwn
        exact (a.trans endS).trans (Fsame b n0 n1)
      · right
        exact ⟨fun x => live ((E2live b).1 x), fun x => live (Flive b x)⟩
    have tbl : ∀ {α : Type} (get : Heap → Nat → Option α),
        (∀ b X Y, SameAt X Y b → get Y b = get X b) → (∀ X b, ¬ X.live b → get X b = none) →
        ∀ b, get (freedHeap H3 e.k) b = get (writeOut (writeOut (writeOut e.h₀ e.out0 (logp.output ++ output))
          sourceLen (lengthBytes (n64 - (l.len + z.avail_in.toUInt64)))) destLen
          (lengthBytes (cap64 - (l.left + z.avail_out.toUInt64)))) b := by
      intro α get hs hn b
      rcases per b with x | ⟨x, y⟩
      · exact hs b _ _ x
      · rw [hn _ b x, hn _ b y]
    obtain ⟨eS, eA, eG, eN, eNa, -⟩ := writeOut_globals (writeOut (writeOut e.h₀ e.out0 (logp.output ++ output))
      sourceLen (lengthBytes (n64 - (l.len + z.avail_in.toUInt64)))) destLen
      (lengthBytes (cap64 - (l.left + z.avail_out.toUInt64)))
    obtain ⟨fS, fA, fG, fN, fNa, -⟩ := writeOut_globals (writeOut e.h₀ e.out0 (logp.output ++ output))
      sourceLen (lengthBytes (n64 - (l.len + z.avail_in.toUInt64)))
    obtain ⟨gS, gA, gG, gN, gNa, -⟩ := writeOut_globals e.h₀ e.out0 (logp.output ++ output)
    have hk : e.k < H.nextBlk := by
      by_cases lt : e.k < H.nextBlk
      · exact lt
      · exfalso
        apply fin.good.fresh e.k (by omega)
        have hzK : H.streams e.k = some z := fin.good.live.hz
        exact Or.inr (Or.inr (Or.inl (by rw [hzK]; simp)))
    refine ⟨tbl (fun X b => X.bytes b) (fun b X Y h => h.1) (fun X b h => (Heap.not_live.1 h).1),
      tbl (fun X b => X.words b) (fun b X Y h => h.2.1) (fun X b h => (Heap.not_live.1 h).2.1), ?_,
      tbl (fun X b => X.streams b) (fun b X Y h => h.2.2.1) (fun X b h => (Heap.not_live.1 h).2.2.1),
      tbl (fun X b => X.gzheaders b) (fun b X Y h => h.2.2.2.1) (fun X b h => (Heap.not_live.1 h).2.2.2.1),
      tbl (fun X b => X.dstates b) (fun b X Y h => h.2.2.2.2.1) (fun X b h => (Heap.not_live.1 h).2.2.2.2.1),
      tbl (fun X b => X.istates b) (fun b X Y h => h.2.2.2.2.2.1) (fun X b h => (Heap.not_live.1 h).2.2.2.2.2.1),
      tbl (fun X b => X.gzstates b) (fun b X Y h => h.2.2.2.2.2.2.1) (fun X b h => (Heap.not_live.1 h).2.2.2.2.2.2),
      ?_, ?_, ?_, ?_, ?_⟩
    · intro b el
      rcases per b with x | ⟨x, -⟩
      · exact x.2.2.2.2.2.2.2
      · exact absurd el x
    · have w := writeOut_globals H sourceLen (lengthBytes (n64 - (l.len + z.avail_in.toUInt64)))
      have w' := writeOut_globals W1 destLen (lengthBytes (cap64 - (l.left + z.avail_out.toUInt64)))
      rw [hW1] at w; rw [hW2] at w'
      rw [Fg.1, ← w.1, ← w'.1, agree2.static]
    · have w := writeOut_globals H sourceLen (lengthBytes (n64 - (l.len + z.avail_in.toUInt64)))
      have w' := writeOut_globals W1 destLen (lengthBytes (cap64 - (l.left + z.avail_out.toUInt64)))
      rw [hW1] at w; rw [hW2] at w'
      rw [Fg.2.1, ← w.2.1, ← w'.2.1, agree2.allocOk]
    · have w := writeOut_globals H sourceLen (lengthBytes (n64 - (l.len + z.avail_in.toUInt64)))
      have w' := writeOut_globals W1 destLen (lengthBytes (cap64 - (l.left + z.avail_out.toUInt64)))
      rw [hW1] at w; rw [hW2] at w'
      rw [Fg.2.2.1, ← w.2.2.1, ← w'.2.2.1, agree2.garbage]
    · rw [eN, fN, gN, Fg.2.2.2.1]
      exact Nat.le_of_lt hk
    · rw [eNa, fNa, gNa, Fg.2.2.2.2]
      exact fin.nalloc
  · intro hm
    obtain ⟨j, lo, hi, bad⟩ := fin.mem hm
    exact ⟨j, lo, by rw [Fg.2.2.2.2]; exact hi, bad⟩

end ZlibF.Spec.Public.Proofs.Uncompress
