import ZlibF.Proof.«inflate.c.construction-mode»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Fields written by the length-header loops and CODES installation. -/
def LengthTableFrame (before after : InflateState) : Prop :=
  after = { before with lens := after.lens, «have» := after.«have», work := after.work, codes := after.codes, next := after.next, lencode := after.lencode, distcode := after.distcode, lenbits := after.lenbits, mode := after.mode }

/-- The exact length-table metadata update preserves the full default J.
Array bounds and the installed table predicate come from actual execution. -/
theorem DefaultDecodeJ.length_table_update {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z stream : ZStream} {s state : InflateState} (invariant : DefaultDecodeJ h r zs z s)
    (frame : LengthTableFrame s state) (streamFrame : stream = { z with msg := stream.msg })
    (wf : state.WellFormed) (pointers : PtrInv zs state)
    (modes : state.mode = BAD ∨ state.mode = CODELENS) (codes : CodeLengthInvariant zs state) :
    DefaultDecodeJ (setI (r.put h stream) zs state) r zs stream state := by
  have bounds : HEAD ≤ state.mode ∧ state.mode ≤ SYNC := by
    rcases modes with selected | selected <;> rw [selected] <;> decide
  have inv : StInv h zs state := by
    refine ⟨wf, ?_, ?_, ?_, pointers⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals rw [frame]
      · exact invariant.good.inv.win.wbits
      · exact invariant.good.inv.win.block
      · exact invariant.good.inv.win.nullws
      · exact invariant.good.inv.win.ws
      · exact invariant.good.inv.win.hv
      · exact invariant.good.inv.win.wn
      · exact invariant.good.inv.win.eq
    · rw [frame]
      exact invariant.good.inv.reqbits
    · rw [frame]
      exact invariant.good.inv.bits
  have current : Good (setI (r.put h stream) zs state) r zs stream state :=
    invariant.good.setZI (by rw [streamFrame]) (by rw [streamFrame]; exact invariant.good.live.zalloc)
      (by rw [streamFrame]; exact invariant.good.live.zfree) (by rw [frame]) bounds inv
  refine ⟨current, ?_, ?_, codes, ?_, ?_, ?_, ?_, ?_, ?_, ?_, (by simpa only [LibraryGlobals, setI, ZStreamRef.put_static] using invariant.globals),
    (invariant.platform.put_stream r stream).with_istates _⟩
  · apply dataTableInvariant_inactive
    rcases modes with selected | selected <;> rw [selected] <;> unfold DataTableMode <;> decide
  · apply dataPendingInvariant_idle (by rw [frame]; exact invariant.pending.sane)
    rcases modes with selected | selected <;> rw [selected] <;> decide
  · intro active
    rcases modes with selected | selected <;> rw [selected] at active <;> contradiction
  · rw [frame]
    exact invariant.held
  · rw [frame]
    exact invariant.window
  · rw [frame]
    exact invariant.wrapper
  · exact HeaderMemory.step invariant.header invariant.good current (by rw [frame]) (by rw [frame]) sizes
  · right
    rcases modes with selected | selected <;> rw [selected] <;> decide
  · rintro (active | active) <;>
      rcases modes with selected | selected <;> rw [selected] at active <;> contradiction

/-- Both actual LENLENS loops and the CODES call retain the input trace
before entering the actual CODELENS continuation. -/
theorem inflate_LENLENS_table_cursor {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {bs : List UInt8} (hr : c.strm = some r) (hc : c.st = some (.tab zs)) (hz : r.get h = some z)
    (hs : h.istates zs = some s) (hwf : s.WellFormed) (hnc : s.ncode.toNat ≤ 19) (hhn : s.«have».toNat ≤ s.ncode.toNat)
    (hG : Good3 s.lens s.«have».toNat) (B : BitInv h l bs) :
    ∃ l' j, j ≤ bs.length ∧ BitInv h l' (bs.drop j) ∧
      stream l' (bs.drop j) = (stream l bs).drop (3 * min (s.ncode.toNat - s.«have».toNat) ((stream l bs).length / 3)) ∧
      TcRegShape l l' ∧
      (min (s.ncode.toNat - s.«have».toNat) ((stream l bs).length / 3) < s.ncode.toNat - s.«have».toNat →
        l'.have_ = 0 ∧ j = bs.length ∧ l'.bits.toNat < 3 ∧
        runX (inflate_LENLENS c) l h = .ok ((.error Ex.leave, l'), setI h zs
          (llSt s (stream l bs) (min (s.ncode.toNat - s.«have».toNat) ((stream l bs).length / 3))))) ∧
      (min (s.ncode.toNat - s.«have».toNat) ((stream l bs).length / 3) = s.ncode.toNat - s.«have».toNat →
        ∃ (ret : Int32) (wa' : Array UInt16) (ca' : Array Code), wa'.size = 288 ∧ ca'.size = 1444 ∧
          (∀ x, 19 ≤ x → wa'[x]? = s.work[x]?) ∧ (∀ x, 128 ≤ x → ca'[x]? = s.codes[x]?) ∧
          (ret = 0 ∨ ret = -1) ∧
          (ret = -1 ↔ ¬ ZlibF.Spec.Acceptable .codeLength
            (Zlib.Inftrees.Spec.lensList (llDone s (stream l bs)).lens 0 19)) ∧
          (ret = 0 → ∃ u lb, u ≤ 128 ∧ Zlib.Inftrees.Spec.CodeLengthTableSafe ca' 0 lb.toNat ∧ runX (inflate_LENLENS c) l h = runX (inflate_CODELENS c) { l' with ret := 0 }
            (setI h zs (llOkSt zs (llDone s (stream l bs)) u lb wa' ca'))) ∧
          (ret = -1 → ∃ i, strTable[i]? = some "invalid code lengths set" ∧
            runX (inflate_LENLENS c) l h = .ok ((.ok (), { l' with ret := -1 }),
              tcBadHeap (setI h zs (llBadSt zs (llDone s (stream l bs)) wa' ca')) r zs z
                (llBadSt zs (llDone s (stream l bs)) wa' ca') i))) ∧ l'.next = inputAdvance l.next j ∧ l'.bits.toNat ≤ max l.bits.toNat 10 ∧
      ∃ outcome, runX (xwhile (llCond c) (llBody c)) l h =
        .ok ((outcome, l'), setI h zs (llSt s (stream l bs)
          (min (s.ncode.toNat - s.«have».toNat) ((stream l bs).length / 3)))) := by
  obtain ⟨hl, hw, hcs⟩ := hwf
  obtain ⟨r1, l', j, hrun1, hj, B', hS', hsh, hl1, hok1, cursor, bits⟩ := ll1_run_cursor hc hs hl hnc hhn B
  refine ⟨l', j, hj, B', hS', hsh, ?_, ?_, cursor, bits, r1, hrun1⟩
  · intro hlt
    obtain ⟨hr1, h2, h3, h4⟩ := hl1 hlt
    refine ⟨h2, h3, h4, ?_⟩
    rw [inflate_LENLENS_eq, runX_bind, hrun1, hr1]
  · intro heq
    have hr1 := hok1 heq
    obtain ⟨S, hSdef⟩ : ∃ S, S = stream l bs := ⟨_, rfl⟩
    rw [← hSdef] at hrun1 heq ⊢
    rw [heq] at hrun1
    obtain ⟨n, hn⟩ : ∃ n, n = s.ncode.toNat - s.«have».toNat := ⟨_, rfl⟩
    rw [← hn] at hrun1
    have ht1 : (setI h zs (llSt s S n)).istates zs = some (llSt s S n) := by simp
    have hht1 := llSt_have s S n (by omega)
    have hsz1 : (llSt s S n).lens.size = 320 := by simp [llSt, lensRead_size, hl]
    have hlz := lz_run (c := c) (l := l') hc ht1 hsz1 (by omega)
    have hdone : llDone s S = lzSt (llSt s S n) (19 - (llSt s S n).«have».toNat) := by
      unfold llDone; rw [← hn]
    have hmain : runX (inflate_LENLENS c) l h = runX (llTail c) l' (setI h zs (llDone s S)) := by
      rw [inflate_LENLENS_eq, runX_bind, hrun1, hr1]
      simp only []
      rw [runX_bind, hlz, hdone]
      simp only [setI_setI]
    have hgood : Good3 (llDone s S).lens 19 := by
      rw [llDone_lens s S hnc hhn]
      have g1 := lensRead_good (a := s.lens) (i0 := s.«have».toNat) S hG (s.ncode.toNat - s.«have».toNat) (by omega)
      rw [show s.«have».toNat + (s.ncode.toNat - s.«have».toNat) = s.ncode.toNat by omega] at g1
      have g2 := lensZero_good g1 (19 - s.ncode.toNat) (by omega)
      rwa [show s.ncode.toNat + (19 - s.ncode.toNat) = 19 by omega] at g2
    have hwf' : (llDone s S).WellFormed := by
      refine ⟨?_, ?_, ?_⟩
      · rw [llDone_lens s S hnc hhn, lensZero_size, lensRead_size]; exact hl
      · exact hw
      · exact hcs
    have hs' : (setI h zs (llDone s S)).istates zs = some (llDone s S) := by simp
    have hz' : r.get (setI h zs (llDone s S)) = some z := by simpa using hz
    obtain ⟨ret, wa', ca', hwa, hca, hfw, hfc, hret, hacc, hz0, hz1⟩ := llTail_run_table_safe (c := c) (l := l') hr hc hz' hs' hwf' hgood
    refine ⟨ret, wa', ca', hwa, hca, ?_, ?_, hret, hacc, ?_, ?_⟩
    · intro x hx; rw [hfw x hx]; simp [llDone, lzSt, llSt]
    · intro x hx; rw [hfc x hx]; simp [llDone, lzSt, llSt]
    · intro h0
      obtain ⟨u, lb, hu, safe, hrunu⟩ := hz0 h0
      exact ⟨u, lb, hu, safe, by rw [hmain, hrunu]; simp only [setI_setI]⟩
    · intro h0
      obtain ⟨i, hi, hrunb⟩ := hz1 h0
      refine ⟨i, hi, ?_⟩
      rw [hmain, hrunb]
      simp only [setI_setI]


/-- Retain the exact caller packet across a checked length-table update.
The source read trace supplies all input advancement; constructors write
only private metadata and an optional error message. -/
theorem DefaultDecodeJ.length_table_packet {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z stream : ZStream} {s state : InflateState} {l regs : IL} {bs : List UInt8} {used : Nat}
    (invariant : DefaultDecodeJ h r zs z s) (buffers : DispatchBuffers h r l bs)
    (frame : LengthTableFrame s state) (streamFrame : stream = { z with msg := stream.msg })
    (wf : state.WellFormed) (pointers : PtrInv zs state)
    (modes : state.mode = BAD ∨ state.mode = CODELENS) (codes : CodeLengthInvariant zs state)
    (inv : BitInv h regs (bs.drop used)) (cursor : regs.next = inputAdvance l.next used)
    (count : regs.have_.toNat + used = l.have_.toNat) (put : regs.put = l.put)
    (left : regs.left = l.left) (total : regs.out_ = l.out_) :
    DefaultDecodeJ (setI (r.put h stream) zs state) r zs stream state ∧
      DispatchBuffers (setI (r.put h stream) zs state) r regs (bs.drop used) ∧
      ByteViewSizes h (setI (r.put h stream) zs state) := by
  have next := invariant.length_table_update frame streamFrame wf pointers modes codes
  have views : ∀ ref : BRef, Space.get (setI (r.put h stream) zs state) ref = Space.get h ref := by
    intro ref
    rw [byte_view_get_setI, byte_view_get_stream_put]
  have readonly : ∀ ref : BRef, Space.ro (setI (r.put h stream) zs state) ref = Space.ro h ref := by
    intro ref
    rw [byte_view_ro_setI, byte_view_ro_stream_put]
  have sizes : ByteViewSizes h (setI (r.put h stream) zs state) := ByteViewSizes.of_views views readonly (HeaderTableStep.of_eq (fun _ => by header_table_eq))
  have packet := buffers.advance_both invariant.good next.good (by rw [frame]) sizes readonly cursor count
    (made := 0) (by rw [inputAdvance_zero]; exact put) (by rw [left]; rfl) total (inv.byte_views views)
  exact ⟨next, packet, sizes⟩


/-- Both actual LENLENS loops and the real CODES constructor preserve J
at every externally visible boundary and at the actual CODELENS entry.
The zero-filling loop is internal; its temporary have count is not treated
as a resumed LENLENS state. No table contract is assumed. -/
theorem inflate_LENLENS_default_J_entry {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultDecodeJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = LENLENS) :
    ∃ regs after stream state used, used ≤ bs.length ∧ DefaultDecodeJ after r zs stream state ∧
      DispatchBuffers after r regs (bs.drop used) ∧ ByteViewSizes h after ∧
      regs.next = inputAdvance l.next used ∧ regs.have_.toNat + used = l.have_.toNat ∧
      regs.put = l.put ∧ regs.left = l.left ∧ regs.out_ = l.out_ ∧
      regs.bits.toNat ≤ max l.bits.toNat 10 ∧ regs.bits.toNat ≤ l.bits.toNat + 8 * used ∧
      ((∃ outcome, runX (inflate_LENLENS c) l h = .ok ((outcome, regs), after) ∧
          (outcome = .error Ex.leave ∨ (outcome = .ok () ∧ state.mode = BAD))) ∨
       (state.mode = CODELENS ∧ runX (inflate_LENLENS c) l h = runX (inflate_CODELENS c) regs after)) := by
  obtain ⟨ncode, haveBound, nlen, ndist, prefixValues⟩ := invariant.headerLengths mode
  obtain ⟨regs, used, bound, inv, streamBits, shape, wait, full, cursor, bits, prefixExit, read⟩ :=
    inflate_LENLENS_table_cursor E.strm E.st E.hz E.hs invariant.good.inv.wf ncode haveBound prefixValues buffers.bits
  let m := min (s.ncode.toNat - s.«have».toNat) ((Zlib.Inflate.Proofs.stream l bs).length / 3)
  have mBound : m ≤ s.ncode.toNat - s.«have».toNat := Nat.min_le_left _ _
  have count : regs.have_.toNat + used = l.have_.toNat := by
    rw [inv.have_eq, buffers.bits.have_eq, List.length_drop]
    omega
  have put : regs.put = l.put := by rw [shape]
  have left : regs.left = l.left := by rw [shape]
  have total : regs.out_ = l.out_ := by rw [shape]
  have budget : regs.bits.toNat ≤ l.bits.toNat + 8 * used := by
    have shorter : (Zlib.Inflate.Proofs.stream regs (bs.drop used)).length ≤
        (Zlib.Inflate.Proofs.stream l bs).length := by rw [streamBits, List.length_drop]; omega
    rw [tcStream_length inv, tcStream_length buffers.bits, List.length_drop] at shorter
    omega
  by_cases short : m < s.ncode.toNat - s.«have».toNat
  · obtain ⟨_, _, _, run⟩ := wait short
    obtain ⟨exit2, regs2, heap2, state2, used2, bound2, read2, nextJ,
      packet, sizes, _, count2, _, _, _, _, _⟩ := ll1_default_J E invariant buffers mode
    rw [read] at read2
    cases read2
    have sameUse : used2 = used := by omega
    subst used2
    exact ⟨regs, _, z, state2, used, bound, nextJ, packet, sizes, cursor, count,
      put, left, total, bits, budget, Or.inl ⟨.error Ex.leave, run, Or.inl rfl⟩⟩
  · have complete : m = s.ncode.toNat - s.«have».toNat := by omega
    obtain ⟨ret, work, codes, workSize, codeSize, _, _, kinds, _, accepted, rejected⟩ := full complete
    let filled := llDone s (Zlib.Inflate.Proofs.stream l bs)
    have lensSize : filled.lens.size = 320 := by
      simp only [filled, llDone, lzSt, llSt, lensZero_size, lensRead_size]
      exact invariant.good.inv.wf.1
    rcases kinds with success | failure
    · obtain ⟨usedCodes, root, capacity, safe, run⟩ := accepted success
      let state := llOkSt zs filled usedCodes root work codes
      have frame : LengthTableFrame s state := by
        simp only [LengthTableFrame, state, llOkSt, llPre, filled, llDone, lzSt, llSt]
      have wf : state.WellFormed := ⟨lensSize, workSize, codeSize⟩
      have pointers : PtrInv zs state :=
        ⟨⟨usedCodes, rfl, by omega⟩, Or.inl ⟨0, 0, rfl, rfl, by decide, by decide⟩⟩
      have codeInv : CodeLengthInvariant zs state :=
        llOkSt_codeLengthInvariant zs filled usedCodes root work codes safe nlen ndist
      have bitInv : BitInv h { regs with ret := 0 } (bs.drop used) := ⟨inv.have_eq, inv.next, inv.hold_lt⟩
      obtain ⟨nextJ, packet, sizes⟩ := invariant.length_table_packet buffers frame
        (stream := z) (by rfl) wf pointers (Or.inr rfl) codeInv bitInv cursor count put left total
      rw [ZStreamRef.put_self E.hz] at nextJ packet sizes
      exact ⟨{ regs with ret := 0 }, _, z, state, used, bound, nextJ, packet, sizes,
        cursor, count, put, left, total, bits, budget, Or.inr ⟨rfl, run⟩⟩
    · obtain ⟨i, _, run⟩ := rejected failure
      let state := { llBadSt zs filled work codes with mode := BAD }
      let stream := { z with msg := .ref (.str i) 0 }
      have frame : LengthTableFrame s state := by
        simp only [LengthTableFrame, state, llBadSt, llPre, filled, llDone, lzSt, llSt]
      have wf : state.WellFormed := ⟨lensSize, workSize, codeSize⟩
      have pointers : PtrInv zs state :=
        ⟨⟨0, rfl, by decide⟩, Or.inl ⟨0, 0, rfl, rfl, by decide, by decide⟩⟩
      have codeInv : CodeLengthInvariant zs state := by
        intro active
        change BAD = CODELENS at active
        exact False.elim ((by decide : BAD ≠ CODELENS) active)
      have bitInv : BitInv h { regs with ret := -1 } (bs.drop used) := ⟨inv.have_eq, inv.next, inv.hold_lt⟩
      obtain ⟨nextJ, packet, sizes⟩ := invariant.length_table_packet buffers frame
        (stream := stream) (by rfl) wf pointers (Or.inl rfl) codeInv bitInv cursor count put left total
      refine ⟨{ regs with ret := -1 }, _, stream, state, used, bound, nextJ, packet, sizes,
        cursor, count, put, left, total, bits, budget, Or.inl ⟨.ok (), ?_, Or.inr ⟨rfl, rfl⟩⟩⟩
      simpa only [tcBadHeap, ZStreamRef.put_setI, setI_setI] using run


/-- The actual complete LENLENS and CODELENS construction chain carries J,
exact public buffers and the combined input trace to an exit or the real
LEN_ continuation. Both length alphabets and both error paths are executed. -/
theorem inflate_LENLENS_default_J_boundary {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultDecodeJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = LENLENS) :
    ∃ regs after stream state used, used ≤ bs.length ∧ DefaultDecodeJ after r zs stream state ∧
      DispatchBuffers after r regs (bs.drop used) ∧ ByteViewSizes h after ∧
      regs.next = inputAdvance l.next used ∧ regs.have_.toNat + used = l.have_.toNat ∧
      regs.put = l.put ∧ regs.left = l.left ∧ regs.out_ = l.out_ ∧
      regs.bits.toNat ≤ max l.bits.toNat 21 ∧ regs.bits.toNat ≤ l.bits.toNat + 8 * used ∧
      ((∃ outcome, runX (inflate_LENLENS c) l h = .ok ((outcome, regs), after) ∧
          (outcome ≠ .ok () ∨ state.mode = BAD)) ∨
       (state.mode = LEN_ ∧ runX (inflate_LENLENS c) l h =
          if c.flush = Z_TREES then .ok ((.error Ex.leave, regs), after)
          else runX (inflate_LEN_ c) regs after)) := by
  obtain ⟨first, heap0, stream0, state0, used0, bound0, nextJ, packet0, sizes0, cursor0, count0,
    put0, left0, total0, bits0, budget0, stopped | continued⟩ :=
    inflate_LENLENS_default_J_entry E invariant buffers mode
  · obtain ⟨outcome, run, why⟩ := stopped
    refine ⟨first, heap0, stream0, state0, used0, bound0, nextJ, packet0, sizes0, cursor0, count0,
      put0, left0, total0, by omega, budget0, Or.inl ⟨outcome, run, ?_⟩⟩
    rcases why with wait | ⟨_, bad⟩
    · left
      intro impossible
      rw [wait] at impossible
      cases impossible
    · exact Or.inr bad
  · obtain ⟨codesMode, source⟩ := continued
    have E0 : Env c heap0 r zs stream0 state0 := ⟨E.strm, E.st, nextJ.good.live.hz, nextJ.good.live.hs⟩
    obtain ⟨regs, after, stream, state, used1, bound1, finalJ, packet, sizes, cursor1, count1,
      put1, left1, total1, bits1, budget1, kinds⟩ :=
      inflate_CODELENS_default_J_boundary E0 nextJ packet0 codesMode
    have bound : used0 + used1 ≤ bs.length := by rw [List.length_drop] at bound1; omega
    have cursor : regs.next = inputAdvance l.next (used0 + used1) := by rw [cursor1, cursor0, inputAdvance_add]
    refine ⟨regs, after, stream, state, used0 + used1, bound, finalJ,
      ?_, sizes0.trans sizes, cursor, by omega, put1.trans put0, left1.trans left0, total1.trans total0,
      by omega, by omega, ?_⟩
    · simpa only [List.drop_drop] using packet
    · rcases kinds with stopped | continued
      · obtain ⟨outcome, run, why⟩ := stopped
        exact Or.inl ⟨outcome, source.trans run, why⟩
      · obtain ⟨mode, run⟩ := continued
        exact Or.inr ⟨mode, source.trans run⟩

end Zlib.Inflate.Proofs
