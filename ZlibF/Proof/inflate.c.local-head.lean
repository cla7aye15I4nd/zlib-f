import ZlibF.Proof.«inflate.c.local-buffers»
import ZlibF.Proof.«inflate.c.header-default»

/-! Actual default zlib-header handling on local decoder storage.
The caller's old typed tables remain unchanged and need no global uniqueness. -/
namespace Zlib.Inflate.Local
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

theorem head_bad_packet {h : Heap} {first : Nat} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l regs : IL} {bs : List UInt8} (good : LocalGood h first r zs z s) (pending : DataPendingInvariant s)
    (buffers : DispatchBuffers h r l bs) (regBits : BitInv h regs bs) (frame : HeadRegFrame l regs) (i : Nat) :
    LocalGood (badHeap h r zs z s i) first r zs { z with msg := .ref (.str i) 0 } { s with mode := BAD } ∧
      DataTableInvariant (badHeap h r zs z s i) { s with mode := BAD } ∧
      DataPendingInvariant { s with mode := BAD } ∧ DispatchBuffers (badHeap h r zs z s i) r regs bs ∧
      ByteViewSizes h (badHeap h r zs z s i) ∧ (badHeap h r zs z s i).static = h.static := by
  have nextGood : LocalGood (badHeap h r zs z s i) first r zs { z with msg := .ref (.str i) 0 } { s with mode := BAD } :=
    good.setZI rfl good.live.zalloc good.live.zfree rfl (by change HEAD ≤ BAD ∧ BAD ≤ SYNC; decide)
      (good.inv.of_fields rfl rfl rfl rfl rfl rfl rfl rfl rfl good.inv.bits rfl rfl rfl)
  have views : ∀ ref : BRef, (Space.get (badHeap h r zs z s i) ref : Option (Array UInt8)) = Space.get h ref := by
    intro ref
    unfold badHeap
    rw [byte_view_get_setI, byte_view_get_stream_put]
  have readonly : ∀ ref : BRef, Space.ro (badHeap h r zs z s i) ref = Space.ro h ref := by
    intro ref
    unfold badHeap
    rw [byte_view_ro_setI, byte_view_ro_stream_put]
  have sizes : ByteViewSizes h (badHeap h r zs z s i) := by intro ref; rw [views]
  have packet : DispatchBuffers (badHeap h r zs z s i) r regs bs := by
    have bits := regBits.byte_views views
    simpa only [List.drop_zero] using dispatch_advance_both_local buffers good nextGood rfl sizes readonly
      (used := 0) (made := 0) (by rw [frame]; simp only [inputAdvance_zero])
      (by rw [frame]; rfl) (by rw [frame]; simp only [inputAdvance_zero])
      (by rw [frame]; rfl) (by rw [frame]) (by simpa only [List.drop_zero] using bits)
  refine ⟨nextGood, ?_, ?_, packet, sizes, ?_⟩
  · intro active
    exact False.elim ((by unfold DataTableMode; decide : ¬ DataTableMode BAD) active)
  · apply dataPendingInvariant_idle (s := { s with mode := BAD }) pending.sane
    change BAD ≠ LENEXT ∧ BAD ≠ DIST ∧ BAD ≠ DISTEXT ∧ BAD ≠ MATCH
    decide
  · simp only [badHeap, setI, ZStreamRef.put_static]

/-- A valid default header retains the common packet and establishes the
next header/block mode by the actual state writes. -/
theorem head_accept_packet {h : Heap} {first : Nat} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8} (good : LocalGood h first r zs z s) (pending : DataPendingInvariant s)
    (buffers : DispatchBuffers h r l bs) :
    let regs := { headWindowRegs l with hold := 0, bits := 0 }
    let after := setI (r.put h { z with adler := 1 }) zs (headDefaultState s l)
    LocalGood after first r zs { z with adler := 1 } (headDefaultState s l) ∧ DataTableInvariant after (headDefaultState s l) ∧
      DataPendingInvariant (headDefaultState s l) ∧ DispatchBuffers after r regs bs ∧ ByteViewSizes h after ∧
      after.static = h.static ∧ ((headDefaultState s l).mode = TYPE ∨ (headDefaultState s l).mode = DICTID) := by
  dsimp only
  let regs := { headWindowRegs l with hold := 0, bits := 0 }
  let state := headDefaultState s l
  let after := setI (r.put h { z with adler := 1 }) zs state
  have mode : state.mode = TYPE ∨ state.mode = DICTID := by
    change headDefaultMode l = TYPE ∨ headDefaultMode l = DICTID
    unfold headDefaultMode
    split
    · exact Or.inr rfl
    · exact Or.inl rfl
  have modeRange : HEAD ≤ state.mode ∧ state.mode ≤ SYNC := by
    rcases mode with type | dictionary
    · rw [type]; decide
    · rw [dictionary]; decide
  have nextGood : LocalGood after first r zs { z with adler := 1 } state :=
    good.setZI rfl good.live.zalloc good.live.zfree rfl modeRange
      (good.inv.of_fields rfl rfl rfl rfl rfl rfl rfl rfl rfl good.inv.bits rfl rfl rfl)
  have views : ∀ ref : BRef, (Space.get after ref : Option (Array UInt8)) = Space.get h ref := by
    intro ref
    rw [byte_view_get_setI, byte_view_get_stream_put]
  have readonly : ∀ ref : BRef, Space.ro after ref = Space.ro h ref := by
    intro ref
    rw [byte_view_ro_setI, byte_view_ro_stream_put]
  have sizes : ByteViewSizes h after := by intro ref; rw [views]
  have localBits : BitInv h regs bs :=
    ⟨buffers.bits.have_eq, buffers.bits.next, by change (0 : UInt64).toNat < 2 ^ (0 : UInt32).toNat; decide⟩
  have frame : HeadRegFrame l regs := by rfl
  have packet : DispatchBuffers after r regs bs := by
    have bits := localBits.byte_views views
    simpa only [List.drop_zero] using dispatch_advance_both_local buffers good nextGood rfl sizes readonly
      (used := 0) (made := 0) (by rw [frame]; simp only [inputAdvance_zero])
      (by rw [frame]; rfl) (by rw [frame]; simp only [inputAdvance_zero])
      (by rw [frame]; rfl) (by rw [frame]) (by simpa only [List.drop_zero] using bits)
  refine ⟨nextGood, ?_, ?_, packet, sizes, ?_, mode⟩
  · intro active
    rcases mode with type | dictionary
    · rw [type] at active
      exact False.elim ((by unfold DataTableMode; decide : ¬ DataTableMode TYPE) active)
    · rw [dictionary] at active
      exact False.elim ((by unfold DataTableMode; decide : ¬ DataTableMode DICTID) active)
  · apply dataPendingInvariant_idle (s := state) pending.sane
    change state.mode ≠ LENEXT ∧ state.mode ≠ DIST ∧ state.mode ≠ DISTEXT ∧ state.mode ≠ MATCH
    rcases mode with type | dictionary
    · rw [type]; decide
    · rw [dictionary]; decide
  · simp only [after, setI, ZStreamRef.put_static]

/-- All actual default-header checks retain the same boundary packet. The
only exits are BAD, dictionary-id and block parsing. Bit-count premises are
supplied by the preceding NEEDBITS execution. -/
theorem headDefaultCheck_boundary_frame {c : Ctx} {h : Heap} {first : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (good : LocalGood h first r zs z s) (pending : DataPendingInvariant s)
    (buffers : DispatchBuffers h r l bs) (full : 16 ≤ l.bits.toNat) (wbits : s.wbits = 15) :
    ∃ regs after stream state,
      runX (headDefaultCheck c s l) l h = .ok ((.ok (), regs), after) ∧
      LocalGood after first r zs stream state ∧ DataTableInvariant after state ∧ DataPendingInvariant state ∧
      DispatchBuffers after r regs bs ∧ ByteViewSizes h after ∧ HeadRegFrame l regs ∧
      regs.bits.toNat ≤ l.bits.toNat ∧ (state.mode = BAD ∨ state.mode = TYPE ∨ state.mode = DICTID) ∧
      state.window = s.window ∧ state.wbits = s.wbits ∧ after.static = h.static ∧
      HeaderStateFrame s state ∧ HeaderStreamFrame z stream := by
  let Result : Prop :=
    ∃ regs after stream state,
      runX (headDefaultCheck c s l) l h = .ok ((.ok (), regs), after) ∧
      LocalGood after first r zs stream state ∧ DataTableInvariant after state ∧ DataPendingInvariant state ∧
      DispatchBuffers after r regs bs ∧ ByteViewSizes h after ∧ HeadRegFrame l regs ∧
      regs.bits.toNat ≤ l.bits.toNat ∧ (state.mode = BAD ∨ state.mode = TYPE ∨ state.mode = DICTID) ∧
      state.window = s.window ∧ state.wbits = s.wbits ∧ after.static = h.static ∧
      HeaderStateFrame s state ∧ HeaderStreamFrame z stream
  change Result
  have badResult (regs : IL) (i : Nat) (inv : BitInv h regs bs) (frame : HeadRegFrame l regs)
      (bits : regs.bits.toNat ≤ l.bits.toNat)
      (run : runX (headDefaultCheck c s l) l h = .ok ((.ok (), regs), badHeap h r zs z s i)) : Result := by
    obtain ⟨nextGood, tables, nextPending, packet, sizes, static⟩ := head_bad_packet good pending buffers inv frame i
    exact ⟨regs, badHeap h r zs z s i, { z with msg := .ref (.str i) 0 }, { s with mode := BAD },
      run, nextGood, tables, nextPending, packet, sizes, frame, bits, Or.inl rfl, rfl, rfl, static, by rfl, by rfl⟩
  by_cases header : headHeaderRejected s l = true
  · obtain ⟨i, run⟩ := headDefaultCheck_bad_header E l header
    exact badResult l i buffers.bits (by rfl) (Nat.le_refl _) run
  have headerFalse : headHeaderRejected s l = false := by cases eq : headHeaderRejected s l <;> simp_all
  by_cases method : headMethodRejected l = true
  · obtain ⟨i, run⟩ := headDefaultCheck_bad_method E l headerFalse method
    exact badResult l i buffers.bits (by rfl) (Nat.le_refl _) run
  have methodFalse : headMethodRejected l = false := by cases eq : headMethodRejected l <;> simp_all
  by_cases window : 15 < (headWindowRegs l).len.toNat
  · obtain ⟨i, run⟩ := headDefaultCheck_bad_window E l headerFalse methodFalse window
    obtain ⟨inv, _, count⟩ := DROPBITS_inv buffers.bits 4 (by change 4 ≤ l.bits.toNat; omega) (by decide)
    have inv' : BitInv h (headWindowRegs l) bs := ⟨inv.have_eq, inv.next, inv.hold_lt⟩
    apply badResult (headWindowRegs l) i inv' (by rfl) _ run
    change (l.bits - 4).toNat ≤ l.bits.toNat
    rw [count]
    omega
  · have bound : (headWindowRegs l).len.toNat ≤ 15 := by omega
    have run := headDefaultCheck_accept E l headerFalse methodFalse bound wbits
    obtain ⟨nextGood, tables, nextPending, packet, sizes, static, mode⟩ := head_accept_packet good pending buffers
    refine ⟨{ headWindowRegs l with hold := 0, bits := 0 }, _, { z with adler := 1 }, headDefaultState s l,
      run, nextGood, tables, nextPending, packet, sizes, by rfl, ?_, Or.inr mode, rfl, rfl, static, by rfl, by rfl⟩
    change 0 ≤ l.bits.toNat
    omega

/-- Projection retaining the original header boundary. -/
theorem headDefaultCheck_boundary {c : Ctx} {h : Heap} {first : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (good : LocalGood h first r zs z s) (pending : DataPendingInvariant s)
    (buffers : DispatchBuffers h r l bs) (full : 16 ≤ l.bits.toNat) (wbits : s.wbits = 15) :
    ∃ regs after stream state,
      runX (headDefaultCheck c s l) l h = .ok ((.ok (), regs), after) ∧
      LocalGood after first r zs stream state ∧ DataTableInvariant after state ∧ DataPendingInvariant state ∧
      DispatchBuffers after r regs bs ∧ ByteViewSizes h after ∧ HeadRegFrame l regs ∧
      regs.bits.toNat ≤ l.bits.toNat ∧ (state.mode = BAD ∨ state.mode = TYPE ∨ state.mode = DICTID) ∧
      state.window = s.window ∧ state.wbits = s.wbits ∧ after.static = h.static := by
  obtain ⟨regs, after, stream, state, run, nextGood, tables, nextPending, packet, sizes,
    frame, bits, mode, window, width, static, _, _⟩ :=
    headDefaultCheck_boundary_frame E good pending buffers full wbits
  exact ⟨regs, after, stream, state, run, nextGood, tables, nextPending, packet, sizes,
    frame, bits, mode, window, width, static⟩

/-- The complete actual default HEAD mode retains the common relation.
Every byte pull is supplied by NEEDBITS; checks retain the exact unread
input and output cursors. Empty input and partial-header calls are included.
The initialized default fields are internal premises, not caller parameters. -/
theorem inflate_HEAD_zlib_window_boundary_budget {c : Ctx} {h : Heap} {first : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (good : LocalGood h first r zs z s) (pending : DataPendingInvariant s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = HEAD) (wrap : s.wrap = 1 ∨ s.wrap = 5)
    (header : s.head = none) (wbits : s.wbits = 15) :
    ∃ (outcome : Except Ex Unit) (regs : IL) (after : Heap) (stream : ZStream) (state : InflateState) (used : Nat), used ≤ bs.length ∧
      runX (inflate_HEAD c) l h = .ok ((outcome, regs), after) ∧ LocalGood after first r zs stream state ∧
      DataTableInvariant after state ∧ DataPendingInvariant state ∧ DispatchBuffers after r regs (bs.drop used) ∧
      ByteViewSizes h after ∧ regs.next = inputAdvance l.next used ∧
      regs.have_.toNat + used = l.have_.toNat ∧ regs.put = l.put ∧ regs.left = l.left ∧
      regs.bits.toNat ≤ max l.bits.toNat 23 ∧ after.static = h.static ∧
      ((outcome = .error Ex.leave ∧ state = s) ∨
        (outcome = .ok () ∧ (state.mode = BAD ∨ state.mode = TYPE ∨ state.mode = DICTID))) ∧
      HeaderStateFrame s state ∧ HeaderStreamFrame z stream ∧ regs.bits.toNat ≤ l.bits.toNat + 8 * used := by
  obtain ⟨outcome, current, used, usedBound, bitInv, cursor, shape, bits, kinds, full, cut, bitCount⟩ :=
    inflate_HEAD_zlib_window_prefix_count E buffers.bits wrap header
  have symbolShape : SymbolRegShape l current := by rw [shape]; rfl
  have packet : DispatchBuffers h r current (bs.drop used) :=
    dispatch_consume_local buffers good good rfl (fun _ => rfl) (fun _ => rfl) symbolShape cursor usedBound bitInv
  have haveCount : current.have_.toNat + used = l.have_.toNat := by
    rw [bitInv.have_eq, buffers.bits.have_eq, List.length_drop]
    omega
  rcases kinds with normal | wait
  · rw [normal] at cut
    obtain ⟨regs, after, stream, state, run, nextGood, tables, nextPending, nextPacket, sizes,
      frame, bitBound, nextMode, _, _, static, stateFrame, streamFrame⟩ :=
      headDefaultCheck_boundary_frame E good pending packet (full normal) wbits
    refine ⟨.ok (), regs, after, stream, state, used, usedBound, cut.trans run, nextGood, tables,
      nextPending, nextPacket, sizes, ?_, ?_, ?_, ?_, Nat.le_trans bitBound bits, static, Or.inr ⟨rfl, nextMode⟩, stateFrame, streamFrame, by omega⟩
    · rw [frame]
      exact cursor
    · rw [frame]
      exact haveCount
    · rw [frame, shape]
    · rw [frame, shape]
  · rw [wait] at cut
    refine ⟨.error Ex.leave, current, h, z, s, used, usedBound, cut, good,
      dataTableInvariant_head mode, pending, packet, ByteViewSizes.refl h, cursor, haveCount,
      ?_, ?_, bits, rfl, Or.inl ⟨rfl, rfl⟩, by rfl, by rfl, by omega⟩
    · rw [shape]
    · rw [shape]


#print axioms head_bad_packet
#print axioms head_accept_packet
#print axioms headDefaultCheck_boundary_frame
#print axioms inflate_HEAD_zlib_window_boundary_budget
end Zlib.Inflate.Local
