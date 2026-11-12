import ZlibF.Proof.«public-uncompress-end»

/-!
# uncompr.c: `uncompress2_z`

The goal `Goal.uncompress2_z` from the decoder facts of batch 3 (`DecoderFacts`),
which are explicit hypotheses until the decoder proofs discharge them: argument
refusal, initialization failure, and the decompression run with its cleanup.
-/

namespace ZlibF.Spec.Public.Proofs.Uncompress
open C ZlibF.Spec ZlibF.Spec.Public Zlib.Gzguts Zlib.Inflate.Proofs Zlib.Inflate.Spec Zlib.Uncompr
open Zlib.Inflate (inflate inflateEnd inflateInit_)
set_option autoImplicit false

theorem separate_symm {p q : BPtr} {n m : Nat} (s : Separate p n q m) : Separate q m p n := by
  rcases s with h | h | s
  · exact Or.inr (Or.inl h)
  · exact Or.inl h
  · right; right
    cases p <;> cases q <;> simp_all
    rename_i r i r' j
    rcases s with ne | lt | lt
    · exact Or.inl (Ne.symm ne)
    · exact Or.inr (Or.inr lt)
    · exact Or.inr (Or.inl lt)

theorem bytes_length {h : Heap} {p : BPtr} {n : Nat} {xs : List UInt8} (b : Bytes h p n xs) : xs.length = n := by
  rcases b with ⟨-, rfl, rfl⟩ | ⟨r, i, a, -, -, fit, rfl⟩
  · rfl
  · simp; omega

theorem bytes_bound {h : Heap} {p : BPtr} {n : Nat} {xs : List UInt8} (b : Bytes h p n xs)
    (fit : ZlibF.PlatformMemory.ByteObjectsFit h) : n < 2 ^ 63 := by
  rcases b with ⟨-, rfl, -⟩ | ⟨r, i, a, -, g, hi, -⟩
  · decide
  · have := fit r a g
    simp only [ZlibF.PlatformMemory.byteObjectLimit] at this
    omega

theorem writable_bound {h : Heap} {p : BPtr} {n : Nat} (w : Writable h p n)
    (fit : ZlibF.PlatformMemory.ByteObjectsFit h) : n < 2 ^ 63 := by
  rcases w with ⟨-, rfl⟩ | ⟨r, i, a, -, g, -, hi⟩
  · decide
  · have := fit r a g
    simp only [ZlibF.PlatformMemory.byteObjectLimit] at this
    omega

/-- Writing back the value a cell holds leaves the heap. -/
theorem cell_self_write {h : Heap} {p : BPtr} {v : UInt64} (cell : LengthCell h p v) :
    writeOut h p (lengthBytes v) = h := by
  obtain ⟨bytes, -⟩ := cell
  rcases bytes with ⟨-, h8, -⟩ | ⟨r, i, a, rfl, g, fit, hx⟩
  · cases h8
  have hx' : lengthBytes v = (a.toList.drop i).take 8 := hx
  have ne : lengthBytes v ≠ [] := by intro e; have := congrArg List.length e; simp [lengthBytes_length] at this
  have arr : a.extract 0 i ++ (lengthBytes v).toArray ++ a.extract (i + (lengthBytes v).length) a.size = a := by
    apply Array.ext_getElem?
    intro j
    rw [written_get? a i (lengthBytes v) (by rw [lengthBytes_length]; exact fit)]
    rw [lengthBytes_length]
    by_cases lo : j < i
    · simp [lo]
    by_cases hi : j < i + 8
    · simp only [lo, hi, ite_true, ite_false]
      rw [hx']
      simp only [List.getElem?_take, List.getElem?_drop, show j - i < 8 by omega, ite_true,
        show i + (j - i) = j by omega, Array.getElem?_toList]
    · simp [lo, hi]
  simp only [writeOut, g, ne, ite_false]
  rw [arr]
  exact put_self_any g

/-- The heap after a failed `inflateInit`. -/
def memHeap (h : Heap) (source : BPtr) : Heap :=
  initMemHeap (preHeap h source) (.tab h.nextBlk) (preStream h source)

theorem memHeap_reserved (h : Heap) (source : BPtr) :
    (memHeap h source).bytes (h.nextBlk + 1) = some (reservedBytes h) ∧
      (memHeap h source).ro (h.nextBlk + 1) = false := by
  simp [memHeap, initMemHeap, ZStreamRef.put, preHeap, localHeap, streamHeap]

theorem memHeap_stream (h : Heap) (source : BPtr) :
    (reservedFreed (memHeap h source) h.nextBlk).streams h.nextBlk = some (initStream (preStream h source)) := by
  simp [reservedFreed, memHeap, initMemHeap, ZStreamRef.put, preHeap, localHeap, streamHeap]

/-- After a failed initialization and the frees, the caller heap is unchanged entry by entry. -/
theorem mem_same {h : Heap} (fresh : Fresh h) (source : BPtr) :
    SameObjectsUpToTableShape h (freedHeap (memHeap h source) h.nextBlk) := by
  have n0 := fresh h.nextBlk (Nat.le_refl _)
  have n1 := fresh (h.nextBlk + 1) (by omega)
  simp only [Heap.live, not_or, ne_eq, Decidable.not_not] at n0 n1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro b
    simp only [freedHeap, reservedFreed, memHeap, initMemHeap, ZStreamRef.put, preHeap, localHeap,
      streamHeap, upd_apply]
    split <;> simp_all
  · intro b
    simp only [freedHeap, reservedFreed, memHeap, initMemHeap, ZStreamRef.put, preHeap, localHeap,
      streamHeap, upd_apply]
    split <;> simp_all
  · intro b live
    have ne : b ≠ h.nextBlk + 1 := fun e => fresh b (by omega) live
    simp [freedHeap, reservedFreed, memHeap, initMemHeap, ZStreamRef.put, preHeap, localHeap, streamHeap,
      upd_ne _ _ _ _ ne]
  · intro b
    simp only [freedHeap, reservedFreed, memHeap, initMemHeap, ZStreamRef.put, preHeap, localHeap,
      streamHeap, upd_apply]
    split
    · simp_all
    · split <;> simp_all
  all_goals first
    | (intro b; simp [freedHeap, reservedFreed, memHeap, initMemHeap, ZStreamRef.put, preHeap, localHeap, streamHeap])
    | (simp [freedHeap, reservedFreed, memHeap, initMemHeap, ZStreamRef.put, preHeap, localHeap, streamHeap])
    | (simp [freedHeap, reservedFreed, memHeap, initMemHeap, ZStreamRef.put, preHeap, localHeap, streamHeap]; omega)

theorem finalCode_mem {e : Int32} {R : UInt64} (h : finalCode e R = Z_MEM_ERROR) : e = Z_MEM_ERROR := by
  unfold finalCode at h
  split at h
  · exact absurd h (by decide)
  · split at h
    · exact absurd h (by decide)
    · split at h
      · exact absurd h (by decide)
      · exact h

theorem pos_iff (x : UInt64) : (decide (x > 0) = true) ↔ x ≠ 0 := by
  simp only [decide_eq_true_eq, ne_eq, UInt64.lt_iff_toNat_lt, UInt64.toNat_zero]
  constructor
  · intro hx e; rw [e] at hx; simp at hx
  · intro hx; have : x.toNat ≠ 0 := fun e => hx (UInt64.toNat_inj.mp (by simpa using e)); omega

/-- The accepted arguments: decompression run and cleanup. -/
theorem accepted_run (facts : DecoderFacts) {h : Heap} {dest destLen source sourceLen : BPtr}
    {capacity n : UInt64} {src : List UInt8}
    (fresh : Fresh h) (uniq : Uniq h) (globals : LibraryGlobals h)
    (fit : ZlibF.PlatformMemory.ByteObjectsFit h)
    (dcell : LengthCell h destLen capacity) (scell : LengthCell h sourceLen n)
    (srcB : Bytes h source n.toNat src) (destW : dest ≠ .null → Writable h dest capacity.toNat)
    (sep : UtilitySeparation dest capacity.toNat source n.toNat destLen sourceLen)
    (sl : sourceLen ≠ .null) (dl : destLen ≠ .null) (sN : source = .null → n = 0)
    (dN : dest = .null → capacity = 0) :
    ∃ rc after, C.run (uncompress2_z dest destLen source sourceLen) h = .ok (rc, after) ∧
      ∃ out used got consumed h₁ h₂ expected,
        Store h dest out h₁ ∧ Store h₁ sourceLen (lengthBytes consumed) h₂ ∧
        Store h₂ destLen (lengthBytes got) expected ∧ SameObjectsUpToTableShape expected after ∧
        Uncompressed src capacity.toNat rc out used ∧
        ((got.toNat = out.length ∧ consumed.toNat = used) ∨
          (rc = Z_MEM_ERROR ∧ out = [] ∧ got = capacity ∧ consumed = n)) ∧
        (rc = Z_MEM_ERROR → AllocationFailed h after) := by
  have kept := localHeap_kept fresh
  have ln : load64 sourceLen (localHeap h) = .ok (n, localHeap h) := load64_cell (kept.cell_of scell)
  have ld : load64 destLen (localHeap h) = .ok (capacity, localHeap h) := load64_cell (kept.cell_of dcell)
  have c1 : (decide (n > 0) && source == Ptr.null) = false := by
    cases hb : (decide (n > 0) && source == Ptr.null)
    · rfl
    · simp only [Bool.and_eq_true, beq_iff_eq] at hb
      exact absurd (sN hb.2) ((pos_iff n).1 hb.1)
  have c2 : (decide (capacity > 0) && dest == Ptr.null) = false := by
    cases hb : (decide (capacity > 0) && dest == Ptr.null)
    · rfl
    · simp only [Bool.and_eq_true, beq_iff_eq] at hb
      exact absurd (dN hb.2) ((pos_iff capacity).1 hb.1)
  rw [program_eq]
  unfold program
  simp only [C.run, bind_app, allocLocalZ_run fresh, allocLocal_run fresh,
    show (sourceLen == Ptr.null) = false from beq_false_of_ne sl, Bool.false_eq_true, ite_false, ln, c1,
    show (destLen == Ptr.null) = false from beq_false_of_ne dl, ld, c2, prepare_run, version_run]
  have selfS : Store h sourceLen (lengthBytes n) h := by
    have := store_writeOut (xs := lengthBytes n) (by rw [lengthBytes_length]; exact scell.2)
    rwa [cell_self_write scell] at this
  have selfD : Store h destLen (lengthBytes capacity) h := by
    have := store_writeOut (xs := lengthBytes capacity) (by rw [lengthBytes_length]; exact dcell.2)
    rwa [cell_self_write dcell] at this
  by_cases alloc : h.allocOk h.nalloc = true
  · -- the environment of the run
    let out0 : BPtr :=
      if (capacity == 0 && dest == Ptr.null) = true then Ptr.ref (BRef.blk (h.nextBlk + 1)) 0 else dest
    let e : Env := ⟨h, source, out0, src, n.toNat, capacity.toNat⟩
    have resCase : (capacity == 0 && dest == Ptr.null) = true → capacity = 0 ∧ dest = .null := by
      intro hb; simp only [Bool.and_eq_true, beq_iff_eq] at hb; exact hb
    have ok : EnvOK e := by
      refine ⟨fresh, srcB, bytes_length srcB, ?_, ?_, ?_, bytes_bound srcB fit, ?_⟩
      · by_cases hb : (capacity == 0 && dest == Ptr.null) = true
        · left
          obtain ⟨c0, -⟩ := resCase hb
          refine ⟨by simp only [e, out0, hb, ite_true]; rfl, by simp only [e, c0]; rfl⟩
        · right
          simp only [e, out0, hb, Bool.false_eq_true, ite_false]
          by_cases dn : dest = .null
          · have c0 := dN dn
            exfalso; apply hb; simp [c0, dn]
          · exact destW dn
      · simp only [e, out0]
        split
        · simp
        · intro dn
          rename_i hb
          apply hb; simp [dN dn, dn]
      · simp only [e, out0]
        split
        · rename_i hb
          obtain ⟨c0, -⟩ := resCase hb
          exact Or.inr (Or.inl (by simp [c0]))
        · exact separate_symm sep.1
      · simp only [e]
        by_cases dn : dest = .null
        · rw [dN dn]; decide
        · exact writable_bound (destW dn) fit
    have outSep : ∀ (q : BPtr), Separate q 8 dest capacity.toNat → Separate q 8 e.out0 e.cap := by
      intro q sq
      simp only [e, out0]
      split
      · rename_i hb
        obtain ⟨c0, -⟩ := resCase hb
        exact Or.inr (Or.inl (by simp [c0]))
      · exact sq
    have cells : Cells e sourceLen destLen n capacity :=
      ⟨scell, dcell, rfl, rfl, outSep sourceLen sep.2.2.2.1, outSep destLen sep.2.1, sep.2.2.2.2.2⟩
    -- initialization and the loop
    rw [init_ok_run fresh source alloc]
    have okEq : (Z_OK != Z_OK) = false := by decide
    simp only [okEq, Bool.false_eq_true, ite_false, bind_app, bind_run]
    obtain ⟨s0, st0⟩ := start_state ok uniq globals fit alloc n capacity rfl rfl
    obtain ⟨l', H', loopEq, Hp, logp, input, output, u, zp, z, sp, s, fin⟩ := loop_run facts ok st0
    have loopEq' : cdoWhile (loopBody (some (ZStreamRef.tab h.nextBlk))) loopCond
        { err := Z_OK, len := n, left := capacity } (startHeap h source out0) = .ok (l', H') := loopEq
    rw [loopEq']
    simp only []
    have hz : (ZStreamRef.tab h.nextBlk).get H' = some z := fin.good.live.hz
    obtain ⟨H1, H2, H3, l1, s1, l2, s2, endRun, res1, res2, ⟨zz, hzz⟩, same, memF⟩ := epilogue ok cells fin.toSafeFinal
    have endRun' : inflateEnd (some (ZStreamRef.tab h.nextBlk)) H2 = .ok (Z_OK, H3) := endRun
    simp only [ldZ, ldZStream_ok hz, bind_app, l1, s1, l2, s2, endRun', pure_app]
    rw [freeB_reserved_run (k := h.nextBlk) (H := H3) res1 res2]
    simp only []
    rw [freeZStream_local_run (k := h.nextBlk) (H := reservedFreed H3 h.nextBlk) hzz]
    simp only []
    have eN : e.n = n.toNat := rfl
    have eCap : e.cap = capacity.toNat := rfl
    have eSrc : e.src = src := rfl
    have inC := fin.inCount
    have outC := fin.outCount
    have nB := ok.nBound
    have cB := ok.capBound
    have srcLen := ok.srcLen
    have preIn := fin.pre.inCount
    rw [eN] at inC nB preIn; rw [eCap] at outC cB; rw [eSrc, eN] at srcLen
    have outLe : (logp.output ++ output).length ≤ capacity.toNat := by omega
    -- the counts as natural numbers
    have zin := z.avail_in.toNat_lt
    have zout := z.avail_out.toNat_lt
    have lenNat : (l'.len + z.avail_in.toUInt64).toNat = l'.len.toNat + z.avail_in.toNat := by
      rw [UInt64.toNat_add, UInt32.toNat_toUInt64]
      omega
    have leftNat : (l'.left + z.avail_out.toUInt64).toNat = l'.left.toNat + z.avail_out.toNat := by
      rw [UInt64.toNat_add, UInt32.toNat_toUInt64]
      omega
    have consumedNat : (n - (l'.len + z.avail_in.toUInt64)).toNat = logp.input.length + u := by
      rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, lenNat]; omega), lenNat]
      omega
    have gotNat : (capacity - (l'.left + z.avail_out.toUInt64)).toNat = (logp.output ++ output).length := by
      rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, leftNat]; omega), leftNat]
      omega
    -- the stores
    have h1W : Writable h dest (logp.output ++ output).length ∨ logp.output ++ output = [] := by
      by_cases ne : logp.output ++ output = []
      · exact Or.inr ne
      · left
        have dn : dest ≠ .null := by
          intro dn
          have := dN dn
          rw [this] at outLe
          exact ne (List.eq_nil_of_length_eq_zero (by simpa using outLe))
        have := writable_sub (c := 0) (m := (logp.output ++ output).length) (destW dn) (by omega)
        rwa [advance_zero] at this
    have h1eq : writeOut h dest (logp.output ++ output) = writeOut h out0 (logp.output ++ output) := by
      rcases h1W with w | ne
      · simp only [out0]
        split
        · rename_i hb
          obtain ⟨c0, -⟩ := resCase hb
          rw [c0] at outLe
          simp at outLe
          rw [show logp.output ++ output = [] from List.eq_nil_of_length_eq_zero (by simpa using outLe)]
          simp [writeOut_nil]
        · rfl
      · rw [ne, writeOut_nil, writeOut_nil]
    have store1 : Store h dest (logp.output ++ output) (writeOut h out0 (logp.output ++ output)) := by
      rw [← h1eq]
      rcases h1W with w | ne
      · exact store_writeOut w
      · rw [ne, writeOut_nil]; exact Or.inl ⟨rfl, rfl⟩
    have cS := cell_after_output (out := logp.output ++ output) ok scell cells.sepS outLe
    have cD := cell_after_output (out := logp.output ++ output) ok dcell cells.sepD outLe
    have store2 := store_writeOut (h := writeOut h out0 (logp.output ++ output)) (p := sourceLen)
      (xs := lengthBytes (n - (l'.len + z.avail_in.toUInt64))) (by rw [lengthBytes_length]; exact cS.2)
    have cD1 := cell_writeOut_sep (xs := lengthBytes (n - (l'.len + z.avail_in.toUInt64))) cD cells.sepSD
      (by simp [lengthBytes_length]) cS.2
    have store3 := store_writeOut (h := writeOut (writeOut h out0 (logp.output ++ output)) sourceLen
      (lengthBytes (n - (l'.len + z.avail_in.toUInt64)))) (p := destLen)
      (xs := lengthBytes (capacity - (l'.left + z.avail_out.toUInt64))) (by rw [lengthBytes_length]; exact cD1.2)
    -- the data relation
    have inTake := fin.pre.inTake
    have hin : logp.input ++ input.take u = src.take (logp.input.length + u) := by
      rw [fin.input_eq, List.take_take, Nat.min_eq_left fin.used_le, List.take_add, ← inTake]
    have hgiven : logp.input ++ input <+: src := by
      rw [fin.input_eq]
      have e1 : logp.input ++ (src.drop logp.input.length).take zp.avail_in.toNat =
          src.take (logp.input.length + zp.avail_in.toNat) := by
        conv => lhs; arg 1; rw [inTake]
        rw [← List.take_add]
      rw [e1]
      exact List.take_prefix _ _
    have unc := uncompressed_final (R := l'.len + z.avail_in.toUInt64) facts fin.pre.trace fin.pre.fit fin.pre.single
      fin.pre.dict ⟨_, zp, sp, fin.pre.good⟩ fin.step hin
      (by omega) hgiven outLe fin.noOver fin.codes
      (by
        intro hb
        rcases fin.buf hb with x | x
        · left
          apply UInt64.toNat_inj.mp
          rw [lenNat]; simp only [UInt64.toNat_zero]; omega
        · exact Or.inr ⟨x.1, z, hz, x.2⟩)
      (by rw [lenNat]; omega)
    refine ⟨finalCode l'.err (l'.len + z.avail_in.toUInt64), freedHeap H3 e.k, rfl,
      logp.output ++ output, logp.input.length + u, capacity - (l'.left + z.avail_out.toUInt64),
      n - (l'.len + z.avail_in.toUInt64), _, _, _, store1, store2, store3, same, unc,
      Or.inl ⟨gotNat, consumedNat⟩, fun hm => memF (finalCode_mem hm)⟩
  · -- initialization fails
    rw [init_fail_run fresh source alloc]
    have memNe : (Z_MEM_ERROR != Z_OK) = true := by decide
    simp only [memNe, ite_true, bind_app, pure_app,
      show initMemHeap (preHeap h source) (ZStreamRef.tab h.nextBlk) (preStream h source) =
      memHeap h source from rfl]
    rw [freeB_reserved_run (memHeap_reserved h source).1 (memHeap_reserved h source).2]
    simp only []
    rw [freeZStream_local_run (memHeap_stream h source)]
    refine ⟨Z_MEM_ERROR, freedHeap (memHeap h source) h.nextBlk, rfl, [], 0, capacity, n, h, h, h,
      Or.inl ⟨rfl, rfl⟩, selfS, selfD, mem_same fresh source, uncompressed_mem_init _ _,
      Or.inr ⟨rfl, rfl, rfl, rfl⟩, fun _ => ⟨h.nalloc, Nat.le_refl _, ?_, ?_⟩⟩
    · simp [freedHeap, reservedFreed, memHeap, initMemHeap, preHeap, localHeap, streamHeap]
    · cases e : h.allocOk h.nalloc
      · rfl
      · exact absurd e alloc

/-- `int uncompress2_z(Bytef *dest, z_size_t *destLen, const Bytef *source, z_size_t *sourceLen)`,
from the decoder facts of batch 3 (`DecoderFacts`), which are explicit hypotheses. -/
theorem uncompress2_z_of_facts (facts : DecoderFacts) : Goal.uncompress2_z := by
  intro h dest destLen source sourceLen capacity n src fresh uniq globals fit dcell scell _ srcB destW sep
  by_cases bad : sourceLen = .null ∨ destLen = .null ∨ (source = .null ∧ n ≠ 0) ∨
      (dest = .null ∧ capacity ≠ 0)
  · refine ⟨Z_STREAM_ERROR, releasedHeap (localHeap h) h.nextBlk,
      uncompress2_z_refused fresh dcell scell bad, fun _ => ⟨rfl, released_same fresh⟩, ?_⟩
    intro sl dl sN dN
    exfalso
    rcases bad with b | b | b | b
    · exact sl b
    · exact dl b
    · exact b.2 (sN b.1)
    · exact b.2 (dN b.1)
  · have sl : sourceLen ≠ .null := fun e => bad (Or.inl e)
    have dl : destLen ≠ .null := fun e => bad (Or.inr (Or.inl e))
    have sN : source = .null → n = 0 := fun e => Classical.byContradiction fun ne =>
      bad (Or.inr (Or.inr (Or.inl ⟨e, ne⟩)))
    have dN : dest = .null → capacity = 0 := fun e => Classical.byContradiction fun ne =>
      bad (Or.inr (Or.inr (Or.inr ⟨e, ne⟩)))
    have srcB' : Bytes h source n.toNat (if source = .null then [] else src) := by
      by_cases sn : source = .null
      · rw [if_pos sn, sn, sN sn]; exact Or.inl ⟨rfl, rfl, rfl⟩
      · rw [if_neg sn]; exact srcB sn
    obtain ⟨rc, after, run, rest⟩ := accepted_run facts fresh uniq globals fit (dcell dl) (scell sl) srcB'
      destW sep sl dl sN dN
    exact ⟨rc, after, run, fun b => absurd b bad, fun _ _ _ _ => rest⟩

end ZlibF.Spec.Public.Proofs.Uncompress
