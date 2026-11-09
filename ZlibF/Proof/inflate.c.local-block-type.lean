import ZlibF.Proof.«inflate.c.local-head»
import ZlibF.Proof.«inflate.c.block-type»

/-! Actual block-type switching with locally unique decoder storage.
No condition is imposed on old caller typed-table collisions. -/
namespace Zlib.Inflate.Local
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

theorem block_header_good {h : Heap} {first : Nat} {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {s state : InflateState} (good : LocalGood h first r zs z s) (frame : BlockHeaderFrame s state)
    (pointers : BlockHeaderPointers s state) (mode : HEAD ≤ state.mode ∧ state.mode ≤ SYNC) :
    LocalGood (setI h zs state) first r zs z state := by
  have restored : StInv h zs { state with lencode := s.lencode, distcode := s.distcode } := by
    apply good.inv.of_fields
    all_goals rw [frame]
    exact good.inv.bits
  have ptr : PtrInv zs state := by
    refine ⟨?_, ?_⟩
    · rw [frame]
      exact good.inv.ptr.1
    · rcases pointers with ⟨len, dist⟩ | fixed
      · rw [len, dist]
        exact good.inv.ptr.2
      · exact Or.inr fixed
  have inv : StInv h zs state :=
    ⟨restored.wf, ⟨restored.win.wbits, restored.win.block, restored.win.nullws,
      restored.win.ws, restored.win.hv, restored.win.wn, restored.win.eq⟩,
      restored.reqbits, restored.bits, ptr⟩
  exact LocalGood.state good (by rw [frame]) mode inv

/-- A pure block-header write retains the exact caller packet and byte views. -/
theorem block_header_packet {h : Heap} {first : Nat} {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {s state : InflateState} {l regs : IL} {bs : List UInt8}
    (good : LocalGood h first r zs z s) (buffers : DispatchBuffers h r l bs)
    (frame : BlockHeaderFrame s state) (pointers : BlockHeaderPointers s state)
    (mode : HEAD ≤ state.mode ∧ state.mode ≤ SYNC)
    (bits : BitInv h regs bs) (locals : HeadRegFrame l regs) :
    LocalGood (setI h zs state) first r zs z state ∧ DispatchBuffers (setI h zs state) r regs bs ∧
      ByteViewSizes h (setI h zs state) := by
  have nextGood := block_header_good good frame pointers mode
  have views := fun ref => byte_view_get_setI h zs state ref
  have readonly := fun ref => byte_view_ro_setI h zs state ref
  have sizes := byte_view_sizes_setI h zs state
  refine ⟨nextGood, ?_, sizes⟩
  simpa only [List.drop_zero] using dispatch_advance_both_local buffers good nextGood (by rw [frame]) sizes readonly
    (used := 0) (made := 0) (by rw [locals]; simp only [inputAdvance_zero])
    (by rw [locals]; rfl) (by rw [locals]; simp only [inputAdvance_zero])
    (by rw [locals]; rfl) (by rw [locals])
    (by simpa only [List.drop_zero] using bits.byte_views views)

theorem inflate_TYPEDO_last_boundary {c : Ctx} {h : Heap} {first : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (good : LocalGood h first r zs z s) (pending : DataPendingInvariant s)
    (buffers : DispatchBuffers h r l bs) (last : s.last ≠ 0) :
    let state := { s with mode := CHECK }
    let after := setI h zs state
    runX (inflate_TYPEDO c) l h = .ok ((.ok (), bytebits l), after) ∧
      LocalGood after first r zs z state ∧ DataTableInvariant after state ∧ DataPendingInvariant state ∧
      DispatchBuffers after r (bytebits l) bs ∧ ByteViewSizes h after ∧
      (bytebits l).bits.toNat ≤ l.bits.toNat ∧ after.static = h.static ∧
      BlockHeaderFrame s state := by
  dsimp only
  obtain ⟨bits, _, _⟩ := BYTEBITS_inv buffers.bits
  obtain ⟨current, packet, sizes⟩ := block_header_packet good buffers
    (state := { s with mode := CHECK }) (regs := bytebits l) (by rfl)
    (Or.inl ⟨rfl, rfl⟩) (by change HEAD ≤ CHECK ∧ CHECK ≤ SYNC; decide) bits (by rfl)
  have bound := UInt32.toNat_sub_of_le l.bits (l.bits &&& 7)
    (UInt32.le_iff_toNat_le.mpr (and7_le l))
  exact ⟨inflate_TYPEDO_last E l last, current,
    dataTableInvariant_inactive (by change ¬ DataTableMode CHECK; unfold DataTableMode; decide),
    block_header_pending pending (by rfl) (Or.inr (Or.inr (Or.inr rfl))), packet, sizes,
    by change (l.bits - (l.bits &&& 7)).toNat ≤ _; rw [bound]; omega, rfl, by rfl⟩

/-- Every actual block-type branch retains the common decoder relation.
Fixed-code table contents come from the library statics and the checked
installer. Invalid block types reach BAD. Z_TREES retains its early exit. -/
theorem typedoTail_boundary {c : Ctx} {h : Heap} {first : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (good : LocalGood h first r zs z s) (pending : DataPendingInvariant s)
    (buffers : DispatchBuffers h r l bs) (globals : LibraryGlobals h) (full : 2 ≤ l.bits.toNat) :
    ∃ (outcome : Except Ex Unit) (after : Heap) (stream : ZStream) (state : InflateState),
      let regs := { l with hold := l.hold >>> (2 : UInt32).toUInt64, bits := l.bits - 2 }
      runX (typedoTail c) l h = .ok ((outcome, regs), after) ∧
      LocalGood after first r zs stream state ∧ DataTableInvariant after state ∧ DataPendingInvariant state ∧
      DispatchBuffers after r regs bs ∧ ByteViewSizes h after ∧ after.static = h.static ∧
      BlockHeaderFrame s state ∧ HeaderStreamFrame z stream ∧
      ((outcome = .ok () ∧ (state.mode = STORED ∨ state.mode = TABLE ∨ state.mode = LEN_ ∨ state.mode = BAD)) ∨
        (outcome = .error Ex.leave ∧ state.mode = LEN_ ∧ c.flush = Z_TREES)) := by
  let regs := { l with hold := l.hold >>> (2 : UInt32).toUInt64, bits := l.bits - 2 }
  obtain ⟨bits, _, _⟩ := DROPBITS_inv buffers.bits 2 full (by decide)
  let Result : Prop := ∃ (outcome : Except Ex Unit) (after : Heap) (stream : ZStream) (state : InflateState),
      runX (typedoTail c) l h = .ok ((outcome, regs), after) ∧
      LocalGood after first r zs stream state ∧ DataTableInvariant after state ∧ DataPendingInvariant state ∧
      DispatchBuffers after r regs bs ∧ ByteViewSizes h after ∧ after.static = h.static ∧
      BlockHeaderFrame s state ∧ HeaderStreamFrame z stream ∧
      ((outcome = .ok () ∧ (state.mode = STORED ∨ state.mode = TABLE ∨ state.mode = LEN_ ∨ state.mode = BAD)) ∨
        (outcome = .error Ex.leave ∧ state.mode = LEN_ ∧ c.flush = Z_TREES))
  change Result
  have branch (state : InflateState) (outcome : Except Ex Unit)
      (frame : BlockHeaderFrame s state) (pointers : BlockHeaderPointers s state)
      (modes : state.mode = STORED ∨ state.mode = TABLE ∨ state.mode = LEN_)
      (tables : DataTableInvariant (setI h zs state) state)
      (run : runX (typedoTail c) l h = .ok ((outcome, regs), setI h zs state))
      (exit : (outcome = .ok () ∧ (state.mode = STORED ∨ state.mode = TABLE ∨ state.mode = LEN_ ∨ state.mode = BAD)) ∨
        (outcome = .error Ex.leave ∧ state.mode = LEN_ ∧ c.flush = Z_TREES)) : Result := by
    have range : HEAD ≤ state.mode ∧ state.mode ≤ SYNC := by
      rcases modes with mode | mode | mode <;> rw [mode] <;> decide
    obtain ⟨current, packet, sizes⟩ := block_header_packet good buffers frame pointers range bits (by rfl)
    have idle := block_header_pending pending frame (modes.elim Or.inl (fun more =>
      more.elim (fun mode => Or.inr (Or.inl mode)) (fun mode => Or.inr (Or.inr (Or.inl mode)))))
    exact ⟨outcome, setI h zs state, z, state, run, current, tables, idle, packet, sizes,
      rfl, frame, by rfl, exit⟩
  have value : l.hold.toNat % 4 < 4 := Nat.mod_lt _ (by decide)
  have cases : l.hold.toNat % 4 = 0 ∨ l.hold.toNat % 4 = 1 ∨
      l.hold.toNat % 4 = 2 ∨ l.hold.toNat % 4 = 3 := by omega
  rcases cases with stored | fixed | dynamic | bad
  · exact branch { s with mode := STORED } (.ok ()) (by rfl) (Or.inl ⟨rfl, rfl⟩)
      (Or.inl rfl) (dataTableInvariant_inactive (by change ¬ DataTableMode STORED; unfold DataTableMode; decide))
      (typedoTail_stored E l stored) (Or.inl ⟨rfl, Or.inl rfl⟩)
  · have tables : DataTableInvariant (setI h zs { fixedState s with mode := LEN_ })
        { fixedState s with mode := LEN_ } := by
      intro _
      have safe := fixedState_tables_safe (h := setI h zs { fixedState s with mode := LEN_ }) s globals
      exact ⟨safe.lengthTable, safe.distanceTable⟩
    by_cases trees : c.flush = Z_TREES
    · exact branch { fixedState s with mode := LEN_ } (.error Ex.leave) (by rfl) (Or.inr ⟨rfl, rfl⟩)
        (Or.inr (Or.inr rfl)) tables (typedoTail_fixed_trees E l fixed trees) (Or.inr ⟨rfl, rfl, trees⟩)
    · exact branch { fixedState s with mode := LEN_ } (.ok ()) (by rfl) (Or.inr ⟨rfl, rfl⟩)
        (Or.inr (Or.inr rfl)) tables (typedoTail_fixed E l fixed trees) (Or.inl ⟨rfl, Or.inr (Or.inr (Or.inl rfl))⟩)
  · exact branch { s with mode := TABLE } (.ok ()) (by rfl) (Or.inl ⟨rfl, rfl⟩)
      (Or.inr (Or.inl rfl)) (dataTableInvariant_inactive (by change ¬ DataTableMode TABLE; unfold DataTableMode; decide))
      (typedoTail_table E l dynamic) (Or.inl ⟨rfl, Or.inr (Or.inl rfl)⟩)
  · obtain ⟨i, _, run⟩ := typedoTail_bad E l bad
    obtain ⟨current, tables, idle, packet, sizes, static⟩ :=
      Zlib.Inflate.Local.head_bad_packet good pending buffers bits (by rfl) i
    exact ⟨.ok (), badHeap h r zs z s i, { z with msg := .ref (.str i) 0 }, { s with mode := BAD },
      run, current, tables, idle, packet, sizes, static, by rfl, by rfl,
      Or.inl ⟨rfl, Or.inr (Or.inr (Or.inr rfl))⟩⟩

/-- The whole real TYPEDO mode retains input, output and decoder clauses.
The bit equation records the three consumed header bits, or the final
byte alignment. Partial input is a checked exit rather than a fault. -/
theorem inflate_TYPEDO_boundary {c : Ctx} {h : Heap} {first : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (good : LocalGood h first r zs z s) (pending : DataPendingInvariant s)
    (buffers : DispatchBuffers h r l bs) (globals : LibraryGlobals h)
    (mode : s.mode = TYPE ∨ s.mode = TYPEDO) :
    ∃ (outcome : Except Ex Unit) (regs : IL) (after : Heap) (stream : ZStream)
      (state : InflateState) (used consumed : Nat), used ≤ bs.length ∧
      runX (inflate_TYPEDO c) l h = .ok ((outcome, regs), after) ∧
      LocalGood after first r zs stream state ∧ DataTableInvariant after state ∧ DataPendingInvariant state ∧
      DispatchBuffers after r regs (bs.drop used) ∧ ByteViewSizes h after ∧
      regs.next = inputAdvance l.next used ∧ regs.have_.toNat + used = l.have_.toNat ∧
      regs.put = l.put ∧ regs.left = l.left ∧
      regs.bits.toNat + consumed = l.bits.toNat + 8 * used ∧
      regs.bits.toNat ≤ max l.bits.toNat 10 ∧ after.static = h.static ∧
      BlockHeaderFrame s state ∧ HeaderStreamFrame z stream ∧
      (outcome = .ok () ∨ outcome = .error Ex.leave) ∧
      (s.last = 0 → outcome = .ok () → consumed = 3) := by
  by_cases last : s.last = 0
  · obtain ⟨outcome, current, used, pull, usedBound, bitInv, _, bitCount, shape,
      bitsBound, _, full, _, kinds, cursor⟩ := NEEDBITS_run_cursor buffers.bits 3 (by decide)
    have symbolShape : SymbolRegShape l current := by rw [shape]; rfl
    have packet := dispatch_consume_local buffers good good rfl (fun _ => rfl) (fun _ => rfl)
      symbolShape cursor usedBound bitInv
    have haveCount : current.have_.toNat + used = l.have_.toNat := by
      rw [bitInv.have_eq, buffers.bits.have_eq, List.length_drop]
      omega
    rcases kinds with normal | wait
    · rw [normal] at pull
      have enough : 3 ≤ current.bits.toNat := full normal
      change current.bits.toNat ≤ max l.bits.toNat 10 at bitsBound
      let middle := { s with last := u2i (current.hold.toUInt32 &&& ((1 : UInt32) <<< 1 - 1)) }
      let first := { current with hold := current.hold >>> (1 : UInt32).toUInt64, bits := current.bits - 1 }
      let heap1 := setI h zs middle
      obtain ⟨firstBits, _, firstCount⟩ := DROPBITS_inv bitInv 1 (by change 1 ≤ current.bits.toNat; omega) (by decide)
      change (current.bits - 1).toNat = current.bits.toNat - 1 at firstCount
      obtain ⟨good1, packet1, sizes1⟩ := block_header_packet good packet
        (state := middle) (regs := first) (by rfl) (Or.inl ⟨rfl, rfl⟩) good.live.mode firstBits (by rfl)
      have pending1 : DataPendingInvariant middle := by
        apply dataPendingInvariant_idle (s := middle) (by exact pending.sane)
        rcases mode with mode | mode <;> change s.mode ≠ LENEXT ∧ s.mode ≠ DIST ∧ s.mode ≠ DISTEXT ∧ s.mode ≠ MATCH <;> rw [mode] <;> decide
      have E1 : Env c heap1 r zs z middle := ⟨E.strm, E.st, good1.live.hz, good1.live.hs⟩
      have enough1 : 2 ≤ first.bits.toNat := by change 2 ≤ (current.bits - 1).toNat; rw [firstCount]; omega
      obtain ⟨exit, after, stream, state, run, nextGood, tables, nextPending,
        nextPacket, sizes2, static, frame, streamFrame, exits⟩ :=
        typedoTail_boundary E1 good1 pending1 packet1 globals enough1
      let regs := { first with hold := first.hold >>> (2 : UInt32).toUInt64, bits := first.bits - 2 }
      have runTyped := inflate_TYPEDO_head E l current last pull
      obtain ⟨_, _, secondCount⟩ := DROPBITS_inv firstBits 2 enough1 (by decide)
      change (first.bits - 2).toNat = first.bits.toNat - 2 at secondCount
      have count : regs.bits.toNat + 3 = l.bits.toNat + 8 * used := by
        change (first.bits - 2).toNat + 3 = _
        rw [secondCount]
        change (current.bits - 1).toNat - 2 + 3 = _
        rw [firstCount]
        omega
      have nextBits : regs.bits.toNat ≤ max l.bits.toNat 10 := by
        change (first.bits - 2).toNat ≤ _
        rw [secondCount]
        change (current.bits - 1).toNat - 2 ≤ _
        rw [firstCount]
        omega
      have exitKinds : exit = .ok () ∨ exit = .error Ex.leave := by
        rcases exits with normal | trees
        · exact Or.inl normal.1
        · exact Or.inr trees.1
      refine ⟨exit, regs, after, stream, state, used, 3, usedBound,
        runTyped.trans run, nextGood, tables, nextPending, nextPacket, sizes1.trans sizes2,
        ?_, ?_, ?_, ?_, count, nextBits, static, BlockHeaderFrame.trans (by rfl) frame,
        streamFrame, exitKinds, fun _ _ => rfl⟩
      · exact cursor
      · exact haveCount
      · change current.put = l.put
        rw [shape]
      · change current.left = l.left
        rw [shape]
    · have run := inflate_TYPEDO_wait E l current last Ex.leave (by rwa [wait] at pull)
      refine ⟨.error Ex.leave, current, h, z, s, used, 0, usedBound, run, good,
        dataTableInvariant_inactive ?_, pending, packet, ByteViewSizes.refl h, cursor, haveCount,
        ?_, ?_, by omega, bitsBound, rfl, by rfl, by rfl, Or.inr rfl, ?_⟩
      · rcases mode with mode | mode <;> rw [mode] <;> unfold DataTableMode <;> decide
      · rw [shape]
      · rw [shape]
      · intro _ impossible
        cases impossible
  · obtain ⟨run, current, tables, nextPending, packet, sizes, bitBound, static, frame⟩ :=
      inflate_TYPEDO_last_boundary E good pending buffers last
    have sub := UInt32.toNat_sub_of_le l.bits (l.bits &&& 7)
      (UInt32.le_iff_toNat_le.mpr (and7_le l))
    refine ⟨.ok (), bytebits l, setI h zs { s with mode := CHECK }, z, { s with mode := CHECK },
      0, l.bits.toNat % 8, by omega, run, current, tables, nextPending,
      by simpa only [List.drop_zero] using packet, sizes, ?_, by simp [bytebits], rfl, rfl,
      ?_, by omega, static, frame, by rfl, Or.inl rfl, fun zero _ => False.elim (last zero)⟩
    · exact (inputAdvance_zero l.next).symm
    · change (l.bits - (l.bits &&& 7)).toNat + l.bits.toNat % 8 = _
      rw [sub, and7_toNat]
      omega

/-- TYPE preserves its documented Z_BLOCK/Z_TREES return before otherwise
executing the proved complete block-header mode. -/
theorem inflate_TYPE_boundary {c : Ctx} {h : Heap} {first : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (good : LocalGood h first r zs z s) (pending : DataPendingInvariant s)
    (buffers : DispatchBuffers h r l bs) (globals : LibraryGlobals h)
    (mode : s.mode = TYPE) :
    ∃ (outcome : Except Ex Unit) (regs : IL) (after : Heap) (stream : ZStream)
      (state : InflateState) (used consumed : Nat), used ≤ bs.length ∧
      runX (inflate_TYPE c) l h = .ok ((outcome, regs), after) ∧
      LocalGood after first r zs stream state ∧ DataTableInvariant after state ∧ DataPendingInvariant state ∧
      DispatchBuffers after r regs (bs.drop used) ∧ ByteViewSizes h after ∧
      regs.next = inputAdvance l.next used ∧ regs.have_.toNat + used = l.have_.toNat ∧
      regs.put = l.put ∧ regs.left = l.left ∧
      regs.bits.toNat + consumed = l.bits.toNat + 8 * used ∧
      regs.bits.toNat ≤ max l.bits.toNat 10 ∧ after.static = h.static ∧
      BlockHeaderFrame s state ∧ HeaderStreamFrame z stream ∧
      (outcome = .ok () ∨ outcome = .error Ex.leave) ∧
      (s.last = 0 → outcome = .ok () → consumed = 3) := by
  by_cases flush : c.flush = Z_BLOCK ∨ c.flush = Z_TREES
  · refine ⟨.error Ex.leave, l, h, z, s, 0, 0, by omega,
      inflate_TYPE_leave c l h flush, good,
      dataTableInvariant_inactive (by rw [mode]; unfold DataTableMode; decide), pending,
      by simpa only [List.drop_zero] using buffers, ByteViewSizes.refl h,
      (inputAdvance_zero l.next).symm, by omega, rfl, rfl, by omega,
      by omega, rfl, by rfl, by rfl, Or.inr rfl, ?_⟩
    intro _ impossible
    cases impossible
  · have go : c.flush ≠ Z_BLOCK ∧ c.flush ≠ Z_TREES :=
      ⟨fun equal => flush (Or.inl equal), fun equal => flush (Or.inr equal)⟩
    rw [inflate_TYPE_go c l h go]
    exact inflate_TYPEDO_boundary E good pending buffers globals (Or.inl mode)


#print axioms block_header_good
#print axioms block_header_packet
#print axioms inflate_TYPEDO_last_boundary
#print axioms typedoTail_boundary
#print axioms inflate_TYPEDO_boundary
#print axioms inflate_TYPE_boundary
end Zlib.Inflate.Local
