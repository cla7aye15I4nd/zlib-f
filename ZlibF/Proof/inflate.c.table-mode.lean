import ZlibF.Proof.«inflate.c.lenlens-mode»
import ZlibF.Proof.«inflate.c.no-return»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The actual four-bit HCLEN field always gives at most nineteen entries. -/
theorem tableCounts_ncode_bound (s : InflateState) (hold : UInt64) :
    (tableCounts s hold).ncode.toNat ≤ 19 := by
  have mask : (((hold >>> 5 >>> 5).toUInt32 &&& 15).toNat) ≤ 15 := by
    rw [UInt32.toNat_and]
    exact Nat.and_le_right
  change (((hold >>> 5 >>> 5).toUInt32 &&& 15) + 4).toNat ≤ 19
  rw [UInt32.toNat_add]
  change (_ + 4) % 2 ^ 32 ≤ 19
  omega

/-- Scalar fields written while reading the dynamic alphabet counts. -/
def TableCountsFrame (before after : InflateState) : Prop :=
  after = { before with nlen := after.nlen, ndist := after.ndist, ncode := after.ncode, «have» := after.«have», mode := after.mode }

/-- Actual count writes retain J once the real validity check has supplied
its guarded LENLENS clause. BAD activates no construction precondition. -/
theorem DefaultDecodeJ.counts_update {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z stream : ZStream} {s state : InflateState} (invariant : DefaultDecodeJ h r zs z s)
    (frame : TableCountsFrame s state) (streamFrame : stream = { z with msg := stream.msg })
    (modes : state.mode = BAD ∨ state.mode = LENLENS) (lengths : LengthHeaderInvariant state) :
    DefaultDecodeJ (setI (r.put h stream) zs state) r zs stream state := by
  have bounds : HEAD ≤ state.mode ∧ state.mode ≤ SYNC := by
    rcases modes with selected | selected <;> rw [selected] <;> decide
  have inv : StInv h zs state := by
    apply invariant.good.inv.of_fields
    all_goals rw [frame]
    exact invariant.good.inv.bits
  have current : Good (setI (r.put h stream) zs state) r zs stream state :=
    invariant.good.setZI (by rw [streamFrame]) (by rw [streamFrame]; exact invariant.good.live.zalloc)
      (by rw [streamFrame]; exact invariant.good.live.zfree) (by rw [frame]) bounds inv
  refine ⟨current, ?_, ?_, ?_, lengths, ?_, ?_, ?_, ?_, ?_, ?_,
    (by simpa only [LibraryGlobals, setI, ZStreamRef.put_static] using invariant.globals),
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

/-- The accepted dynamic count check initializes the exact LENLENS guard.
No lens entry is constrained before it has been written. -/
theorem tableCounts_header_invariant (s : InflateState) (hold : UInt64)
    (valid : ¬ ((tableCounts s hold).nlen > 286 ∨ (tableCounts s hold).ndist > 30)) :
    LengthHeaderInvariant { tableCounts s hold with «have» := 0, mode := LENLENS } := by
  intro _
  have nlen := (not_or.mp valid).1
  have ndist := (not_or.mp valid).2
  rw [gt_iff_lt, UInt32.lt_iff_toNat_lt] at nlen ndist
  refine ⟨tableCounts_ncode_bound s hold, ?_, ?_, ?_, ?_⟩
  · change 0 ≤ _
    omega
  · change (tableCounts s hold).nlen.toNat ≤ 286
    change ¬ 286 < (tableCounts s hold).nlen.toNat at nlen
    omega
  · change (tableCounts s hold).ndist.toNat ≤ 30
    change ¬ 30 < (tableCounts s hold).ndist.toNat at ndist
    omega
  · intro k inside
    change k < 0 at inside
    omega


/-- Exact metadata writes preserve all public byte views and transport
an already checked input trace without changing the output interval. -/
theorem DispatchBuffers.metadata_advance {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z stream : ZStream} {s state : InflateState} {l regs : IL} {bs : List UInt8} {used : Nat}
    (buffers : DispatchBuffers h r l bs) (before : Good h r zs z s)
    (current : Good (setI (r.put h stream) zs state) r zs stream state)
    (window : state.window = s.window) (inv : BitInv h regs (bs.drop used))
    (cursor : regs.next = inputAdvance l.next used) (count : regs.have_.toNat + used = l.have_.toNat)
    (put : regs.put = l.put) (left : regs.left = l.left) (total : regs.out_ = l.out_) :
    DispatchBuffers (setI (r.put h stream) zs state) r regs (bs.drop used) ∧
      ByteViewSizes h (setI (r.put h stream) zs state) := by
  have views : ∀ ref : BRef, Space.get (setI (r.put h stream) zs state) ref = Space.get h ref := by
    intro ref
    rw [byte_view_get_setI, byte_view_get_stream_put]
  have readonly : ∀ ref : BRef, Space.ro (setI (r.put h stream) zs state) ref = Space.ro h ref := by
    intro ref
    rw [byte_view_ro_setI, byte_view_ro_stream_put]
  have sizes : ByteViewSizes h (setI (r.put h stream) zs state) := ByteViewSizes.of_views views readonly (HeaderTableStep.of_eq (fun _ => by header_table_eq))
  exact ⟨buffers.advance_both before current window sizes readonly cursor count (made := 0)
    (by rw [inputAdvance_zero]; exact put) (by rw [left]; rfl) total (inv.byte_views views), sizes⟩

/-- Actual TABLE parsing establishes the precise LENLENS entry clause.
Invalid counts take BAD before the continuation; partial input retains J.
The fourteen source bits and exact input cursor are accounted on one run. -/
theorem inflate_TABLE_default_J_entry {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultDecodeJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = TABLE) :
    ∃ regs after stream state used, used ≤ bs.length ∧ DefaultDecodeJ after r zs stream state ∧
      DispatchBuffers after r regs (bs.drop used) ∧ ByteViewSizes h after ∧
      regs.next = inputAdvance l.next used ∧ regs.have_.toNat + used = l.have_.toNat ∧
      regs.put = l.put ∧ regs.left = l.left ∧ regs.out_ = l.out_ ∧
      regs.bits.toNat ≤ max l.bits.toNat 21 ∧ regs.bits.toNat ≤ l.bits.toNat + 8 * used ∧
      ((∃ outcome, runX (inflate_TABLE c) l h = .ok ((outcome, regs), after) ∧
          (outcome = .error Ex.leave ∨ (outcome = .ok () ∧ state.mode = BAD))) ∨
       (state.mode = LENLENS ∧ runX (inflate_TABLE c) l h = runX (inflate_LENLENS c) regs after)) := by
  obtain ⟨outcome, current, used, pull, bound, inv, _, wait, full⟩ :=
    inflate_TABLE_run E.strm E.st E.hz E.hs buffers.bits
  obtain ⟨outcome2, current2, used2, pull2, bound2, inv2, _, bitCount, shape, bitBound, _, _, _, kinds, cursor⟩ :=
    NEEDBITS_run_cursor buffers.bits 14 (by decide)
  rw [pull] at pull2
  cases pull2
  have sameUse : used2 = used := by
    have one := inv.have_eq
    have two := inv2.have_eq
    rw [List.length_drop] at one two
    omega
  subst used2
  change current.bits.toNat ≤ max l.bits.toNat 21 at bitBound
  have count : current.have_.toNat + used = l.have_.toNat := by
    rw [inv.have_eq, buffers.bits.have_eq, List.length_drop]
    omega
  have put : current.put = l.put := by rw [shape]
  have left : current.left = l.left := by rw [shape]
  have total : current.out_ = l.out_ := by rw [shape]
  rcases kinds with normal | leaves
  · obtain ⟨enough, dropInv, _, badRun, readyRun⟩ := full normal
    have dropCount : (tableRegs current).bits.toNat = current.bits.toNat - 14 := by
      change (current.bits - 14).toNat = _
      exact UInt32.toNat_sub_of_le _ _ (by apply UInt32.le_iff_toNat_le.mpr; exact enough)
    have bits : (tableRegs current).bits.toNat ≤ max l.bits.toNat 21 := by rw [dropCount]; omega
    have budget : (tableRegs current).bits.toNat ≤ l.bits.toNat + 8 * used := by rw [dropCount]; omega
    by_cases invalid : (tableCounts s current.hold).nlen > 286 ∨ (tableCounts s current.hold).ndist > 30
    · obtain ⟨i, _, run⟩ := badRun invalid
      let state := { tableCounts s current.hold with mode := BAD }
      let stream := { z with msg := .ref (.str i) 0 }
      have frame : TableCountsFrame s state := by rfl
      have lengths : LengthHeaderInvariant state := by
        intro active
        change BAD = LENLENS at active
        exact False.elim ((by decide : BAD ≠ LENLENS) active)
      have nextJ := invariant.counts_update frame (stream := stream) (by rfl) (Or.inl rfl) lengths
      obtain ⟨packet, sizes⟩ := buffers.metadata_advance invariant.good nextJ.good rfl dropInv
        cursor count put left total
      refine ⟨tableRegs current, _, stream, state, used, bound, nextJ, packet, sizes,
        cursor, count, put, left, total, bits, budget, Or.inl ⟨.ok (), ?_, Or.inr ⟨rfl, rfl⟩⟩⟩
      exact run
    · let state := { tableCounts s current.hold with «have» := 0, mode := LENLENS }
      have frame : TableCountsFrame s state := by rfl
      have lengths : LengthHeaderInvariant state := tableCounts_header_invariant s current.hold invalid
      have nextJ := invariant.counts_update frame (stream := z) (by rfl) (Or.inr rfl) lengths
      obtain ⟨packet, sizes⟩ := buffers.metadata_advance invariant.good nextJ.good rfl dropInv
        cursor count put left total
      rw [ZStreamRef.put_self E.hz] at nextJ packet sizes
      exact ⟨tableRegs current, _, z, state, used, bound, nextJ, packet, sizes,
        cursor, count, put, left, total, bits, budget, Or.inr ⟨rfl, readyRun invalid⟩⟩
  · obtain ⟨_, _, _, run⟩ := wait leaves
    have packet : DispatchBuffers h r current (bs.drop used) :=
      buffers.consume invariant.good invariant.good rfl (fun _ => rfl) (fun _ => rfl)
        (by rw [shape]; rfl) cursor bound inv
    exact ⟨current, h, z, s, used, bound, invariant, packet, ByteViewSizes.refl h,
      cursor, count, put, left, total, bitBound, by omega, Or.inl ⟨.error Ex.leave, run, Or.inl rfl⟩⟩

/-- The entire actual dynamic construction chain starts from TABLE
and retains J and exact buffers to an exit or the real LEN_ call. -/
theorem inflate_TABLE_default_J_boundary {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultDecodeJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = TABLE) :
    ∃ regs after stream state used, used ≤ bs.length ∧ DefaultDecodeJ after r zs stream state ∧
      DispatchBuffers after r regs (bs.drop used) ∧ ByteViewSizes h after ∧
      regs.next = inputAdvance l.next used ∧ regs.have_.toNat + used = l.have_.toNat ∧
      regs.put = l.put ∧ regs.left = l.left ∧ regs.out_ = l.out_ ∧
      regs.bits.toNat ≤ max l.bits.toNat 21 ∧ regs.bits.toNat ≤ l.bits.toNat + 8 * used ∧
      ((∃ outcome, runX (inflate_TABLE c) l h = .ok ((outcome, regs), after) ∧
          (outcome ≠ .ok () ∨ state.mode = BAD)) ∨
       (state.mode = LEN_ ∧ runX (inflate_TABLE c) l h =
          if c.flush = Z_TREES then .ok ((.error Ex.leave, regs), after)
          else runX (inflate_LEN_ c) regs after)) := by
  obtain ⟨first, heap0, stream0, state0, used0, bound0, nextJ, packet0, sizes0, cursor0, count0,
    put0, left0, total0, bits0, budget0, stopped | continued⟩ :=
    inflate_TABLE_default_J_entry E invariant buffers mode
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
      inflate_LENLENS_default_J_boundary E0 nextJ packet0 codesMode
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

/-- The real switch selects the TABLE construction mode. -/
theorem inflate_dispatch_TABLE {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (E : Env c h r zs z s) (l : IL) (mode : s.mode = TABLE) :
    runX (inflate_dispatch c) l h = runX (inflate_TABLE c) l h := by
  unfold inflate_dispatch
  rw [runX_bind, runX_rdS E]
  with_reducible simp [mode, HEAD, FLAGS, TIME, OS, EXLEN, EXTRA, NAME, COMMENT, HCRC,
    DICTID, DICT, TYPE, TYPEDO, STORED, COPY_, COPY, TABLE, LENLENS, CODELENS]

/-- The real switch selects the LENLENS construction mode. -/
theorem inflate_dispatch_LENLENS {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (E : Env c h r zs z s) (l : IL) (mode : s.mode = LENLENS) :
    runX (inflate_dispatch c) l h = runX (inflate_LENLENS c) l h := by
  unfold inflate_dispatch
  rw [runX_bind, runX_rdS E]
  with_reducible simp [mode, HEAD, FLAGS, TIME, OS, EXLEN, EXTRA, NAME, COMMENT, HCRC,
    DICTID, DICT, TYPE, TYPEDO, STORED, COPY_, COPY, TABLE, LENLENS, CODELENS]

/-- The real switch selects the CODELENS construction mode. -/
theorem inflate_dispatch_CODELENS {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (E : Env c h r zs z s) (l : IL) (mode : s.mode = CODELENS) :
    runX (inflate_dispatch c) l h = runX (inflate_CODELENS c) l h := by
  unfold inflate_dispatch
  rw [runX_bind, runX_rdS E]
  with_reducible simp [mode, HEAD, FLAGS, TIME, OS, EXLEN, EXTRA, NAME, COMMENT, HCRC,
    DICTID, DICT, TYPE, TYPEDO, STORED, COPY_, COPY, TABLE, LENLENS, CODELENS]

/-- All three actual construction cases share J, the same public buffer
relation and an exact input trace through the real switch. The only open
continuation in this result is the actual LEN_ decoder call. -/
theorem inflate_dispatch_construction_J_boundary {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultDecodeJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = TABLE ∨ s.mode = LENLENS ∨ s.mode = CODELENS) :
    ∃ regs after stream state used, used ≤ bs.length ∧ DefaultDecodeJ after r zs stream state ∧
      DispatchBuffers after r regs (bs.drop used) ∧ ByteViewSizes h after ∧
      regs.next = inputAdvance l.next used ∧ regs.have_.toNat + used = l.have_.toNat ∧
      regs.put = l.put ∧ regs.left = l.left ∧ regs.out_ = l.out_ ∧
      regs.bits.toNat ≤ max l.bits.toNat 21 ∧ regs.bits.toNat ≤ l.bits.toNat + 8 * used ∧
      ((∃ outcome, runX (inflate_dispatch c) l h = .ok ((outcome, regs), after) ∧
          (outcome ≠ .ok () ∨ state.mode = BAD)) ∨
       (state.mode = LEN_ ∧ runX (inflate_dispatch c) l h =
          if c.flush = Z_TREES then .ok ((.error Ex.leave, regs), after)
          else runX (inflate_LEN_ c) regs after)) := by
  rcases mode with table | lengths | codes
  · rw [inflate_dispatch_TABLE E l table]
    exact inflate_TABLE_default_J_boundary E invariant buffers table
  · rw [inflate_dispatch_LENLENS E l lengths]
    exact inflate_LENLENS_default_J_boundary E invariant buffers lengths
  · rw [inflate_dispatch_CODELENS E l codes]
    exact inflate_CODELENS_default_J_boundary E invariant buffers codes


/-- The construction cases of the actual switch cannot invent a direct
API return. The result follows from the translated mode bodies. -/
theorem inflate_dispatch_construction_outcomes {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l regs : IL} {after : Heap} {outcome : Except Ex Unit}
    (E : Env c h r zs z s) (mode : s.mode = TABLE ∨ s.mode = LENLENS ∨ s.mode = CODELENS)
    (run : runX (inflate_dispatch c) l h = .ok ((outcome, regs), after)) :
    outcome = .error Ex.leave ∨ outcome = .ok () := by
  rcases mode with table | lengths | codes
  · exact (noRet_inflate_TABLE c).outcomes ((inflate_dispatch_TABLE E l table).symm.trans run)
  · exact (noRet_inflate_LENLENS c).outcomes ((inflate_dispatch_LENLENS E l lengths).symm.trans run)
  · exact (noRet_inflate_CODELENS c).outcomes ((inflate_dispatch_CODELENS E l codes).symm.trans run)

/-- All three actual construction cases are closed for Z_TREES. Every
normal continuation preserves J and strictly decreases the same rank as
the data and control cases; all other outcomes leave the mode loop. -/
theorem inflate_dispatch_construction_trees_J_rank {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultDecodeJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = TABLE ∨ s.mode = LENLENS ∨ s.mode = CODELENS)
    (flush : c.flush = Z_TREES) (incoming : l.bits.toNat ≤ 39) :
    ∃ outcome regs after stream state used, used ≤ bs.length ∧
      runX (inflate_dispatch c) l h = .ok ((outcome, regs), after) ∧ DefaultDecodeJ after r zs stream state ∧
      DispatchBuffers after r regs (bs.drop used) ∧ ByteViewSizes h after ∧
      regs.next = inputAdvance l.next used ∧ regs.have_.toNat + used = l.have_.toNat ∧
      regs.put = l.put ∧ regs.left = l.left ∧ regs.out_ = l.out_ ∧ regs.bits.toNat ≤ 39 ∧
      (outcome = .error Ex.leave ∨ (outcome = .ok () ∧ dispatchRank regs state.mode < dispatchRank l s.mode)) := by
  obtain ⟨regs, after, stream, state, used, bound, nextJ, packet, sizes, cursor, count,
    put, left, total, bits, budget, stopped | continued⟩ :=
    inflate_dispatch_construction_J_boundary E invariant buffers mode
  · obtain ⟨outcome, run, why⟩ := stopped
    refine ⟨outcome, regs, after, stream, state, used, bound, run, nextJ, packet, sizes,
      cursor, count, put, left, total, by omega, ?_⟩
    rcases inflate_dispatch_construction_outcomes E mode run with leaves | normal
    · exact Or.inl leaves
    · have bad : state.mode = BAD := why.resolve_left (fun impossible => impossible normal)
      refine Or.inr ⟨normal, ?_⟩
      apply dispatchRank_advance (l := l) (regs := regs) (used := used) (made := 0) count
      · change regs.left.toNat + 0 = l.left.toNat
        rw [left]
        rfl
      · exact budget
      · right
        rw [bad]
        rcases mode with selected | selected | selected <;> rw [selected] <;> decide
  · obtain ⟨_, run⟩ := continued
    rw [if_pos flush] at run
    exact ⟨.error Ex.leave, regs, after, stream, state, used, bound, run, nextJ, packet, sizes,
      cursor, count, put, left, total, by omega, Or.inl rfl⟩

end Zlib.Inflate.Proofs
