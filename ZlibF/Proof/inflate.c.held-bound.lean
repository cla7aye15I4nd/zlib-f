import ZlibF.Proof.«inflate.c.default-view-dispatch-rank»

/-!
# inflate.c: at most 32 held bits outside `BAD`

Between two dispatches, and so between two public calls, the decoder holds at
most 32 bits unless it is in `BAD`. `NEEDBITS(n)` leaves with fewer than
`n ≤ 32` bits; every successful `NEEDBITS(32)` is followed by `INITBITS` or by
`BAD`; the code readers pull bytes only while fewer bits than the code needs
are held; `inflatePrime` refuses a total above 32. The 39-bit bound of the
safety proofs is reached only inside a dispatch.
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Two runs of one program from one start have one result. -/
theorem runX_same {α : Type} {x : X α} {l : IL} {h : Heap} {o1 o2 : Except Ex α} {r1 r2 : IL} {a1 a2 : Heap}
    (one : runX x l h = .ok ((o1, r1), a1)) (two : runX x l h = .ok ((o2, r2), a2)) :
    o1 = o2 ∧ r1 = r2 ∧ a1 = a2 := by
  have same := Except.ok.inj (one.symm.trans two)
  simp only [Prod.mk.injEq] at same
  exact ⟨same.1.1, same.1.2, same.2⟩

/-- `case STORED`: a result outside `BAD` holds fewer than 32 bits. -/
theorem inflate_STORED_held {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = STORED)
    {outcome : Except Ex Unit} {regs : IL} {after : Heap} {state : InflateState}
    (run : runX (inflate_STORED c) l h = .ok ((outcome, regs), after))
    (get : after.istates zs = some state) :
    state.mode ≠ BAD → regs.bits.toNat < 32 := by
  intro notBad
  obtain ⟨aligned, _, _⟩ := BYTEBITS_inv buffers.bits
  obtain ⟨pullOutcome, current, used, pull, bound, bitInv, _, _, shape, _, _, _, leaveFacts, kinds, cursor⟩ :=
    NEEDBITS_run_cursor aligned 32 (by decide)
  have symbolShape : SymbolRegShape l current := by rw [shape]; rfl
  have packet := buffers.consume invariant.good invariant.good rfl (fun _ => rfl) (fun _ => rfl)
    symbolShape cursor bound bitInv
  rcases kinds with normal | wait
  · rw [normal] at pull
    by_cases bad : ((current.hold &&& (0xffff : UInt64)) != ((current.hold >>> 16) ^^^ (0xffff : UInt64))) = true
    · obtain ⟨i, _, run2⟩ := inflate_STORED_bad E l current pull bad
      obtain ⟨good, _⟩ := head_bad_packet invariant.good invariant.pending packet bitInv (by rfl) i
      obtain ⟨_, _, heapEq⟩ := runX_same run run2
      subst heapEq
      have same := Option.some.inj (get.symm.trans good.live.hs)
      rw [same] at notBad
      exact absurd rfl notBad
    · let ready := { s with length := current.hold.toUInt32 &&& 0xffff, mode := COPY_ }
      let heap0 := setI h zs ready
      let first := { current with hold := 0, bits := 0 }
      have frame : DecodeStateFrame s ready := by rfl
      have good0 : Good heap0 r zs z ready := invariant.good.decode_update frame
        (by change HEAD ≤ COPY_ ∧ COPY_ ≤ SYNC; decide)
      have pending0 : DataPendingInvariant ready := by
        apply dataPendingInvariant_idle (s := ready) invariant.pending.sane
        change COPY_ ≠ LENEXT ∧ COPY_ ≠ DIST ∧ COPY_ ≠ DISTEXT ∧ COPY_ ≠ MATCH
        decide
      have E0 : Env c heap0 r zs z ready := ⟨E.strm, E.st, good0.live.hz, good0.live.hs⟩
      have inv0 : BitInv heap0 first (bs.drop used) := (INITBITS_inv bitInv).1.decode_update zs ready
      have packet0 : DispatchBuffers heap0 r first (bs.drop used) :=
        buffers.consume invariant.good good0 rfl (fun ref => byte_view_get_setI h zs ready ref)
          (fun ref => byte_view_ro_setI h zs ready ref) (by dsimp only [first]; rw [shape]; rfl) cursor bound inv0
      have sourceCut := inflate_STORED_ok E l current pull bad
      by_cases trees : c.flush = Z_TREES
      · have run2 : runX (inflate_STORED c) l h = .ok ((.error Ex.leave, first), heap0) := by
          rw [sourceCut]
          simp only [trees, beq_self_eq_true, ↓reduceIte]
          rfl
        obtain ⟨_, regsEq, _⟩ := runX_same run run2
        rw [regsEq]
        change (0 : UInt32).toNat < 32
        simp
      · have sourceRun : runX (inflate_STORED c) l h = runX (inflate_COPY_ c) first heap0 := by
          rw [sourceCut]
          simp only [beq_iff_eq, trees, ↓reduceIte]
          rfl
        obtain ⟨_, regs2, _, _, _, _, run2, _, _, _, _, _, _, _, _, _, _, bitsEq, _⟩ :=
          inflate_COPY_start_boundary_frame E0 good0 pending0 packet0 rfl
        obtain ⟨_, regsEq, _⟩ := runX_same run (sourceRun.trans run2)
        rw [regsEq, bitsEq]
        change (0 : UInt32).toNat < 32
        simp
  · have run2 := inflate_STORED_wait (c := c) l current h Ex.leave (by rwa [wait] at pull)
    obtain ⟨_, regsEq, _⟩ := runX_same run run2
    rw [regsEq]
    exact (leaveFacts wait).2.2

/-- `case STORED` with no input makes no output. -/
theorem inflate_STORED_no_output {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (empty : l.have_ = 0)
    {outcome : Except Ex Unit} {regs : IL} {after : Heap}
    (run : runX (inflate_STORED c) l h = .ok ((outcome, regs), after)) :
    regs.left = l.left := by
  obtain ⟨aligned, _, _⟩ := BYTEBITS_inv buffers.bits
  obtain ⟨pullOutcome, current, used, pull, bound, bitInv, _, _, shape, _, _, _, _, kinds, cursor⟩ :=
    NEEDBITS_run_cursor aligned 32 (by decide)
  have symbolShape : SymbolRegShape l current := by rw [shape]; rfl
  have left : current.left = l.left := by rw [shape]; rfl
  have noBytes : bs.length = 0 := by
    have count := buffers.bits.have_eq
    rw [empty] at count
    simpa using count.symm
  have packet := buffers.consume invariant.good invariant.good rfl (fun _ => rfl) (fun _ => rfl)
    symbolShape cursor bound bitInv
  rcases kinds with normal | wait
  · rw [normal] at pull
    by_cases bad : ((current.hold &&& (0xffff : UInt64)) != ((current.hold >>> 16) ^^^ (0xffff : UInt64))) = true
    · obtain ⟨i, _, run2⟩ := inflate_STORED_bad E l current pull bad
      obtain ⟨_, regsEq, _⟩ := runX_same run run2
      rw [regsEq, left]
    · let ready := { s with length := current.hold.toUInt32 &&& 0xffff, mode := COPY_ }
      let heap0 := setI h zs ready
      let first := { current with hold := 0, bits := 0 }
      have frame : DecodeStateFrame s ready := by rfl
      have good0 : Good heap0 r zs z ready := invariant.good.decode_update frame
        (by change HEAD ≤ COPY_ ∧ COPY_ ≤ SYNC; decide)
      have pending0 : DataPendingInvariant ready := by
        apply dataPendingInvariant_idle (s := ready) invariant.pending.sane
        change COPY_ ≠ LENEXT ∧ COPY_ ≠ DIST ∧ COPY_ ≠ DISTEXT ∧ COPY_ ≠ MATCH
        decide
      have E0 : Env c heap0 r zs z ready := ⟨E.strm, E.st, good0.live.hz, good0.live.hs⟩
      have inv0 : BitInv heap0 first (bs.drop used) := (INITBITS_inv bitInv).1.decode_update zs ready
      have packet0 : DispatchBuffers heap0 r first (bs.drop used) :=
        buffers.consume invariant.good good0 rfl (fun ref => byte_view_get_setI h zs ready ref)
          (fun ref => byte_view_ro_setI h zs ready ref) (by dsimp only [first]; rw [shape]; rfl) cursor bound inv0
      have sourceCut := inflate_STORED_ok E l current pull bad
      by_cases trees : c.flush = Z_TREES
      · have run2 : runX (inflate_STORED c) l h = .ok ((.error Ex.leave, first), heap0) := by
          rw [sourceCut]
          simp only [trees, beq_self_eq_true, ↓reduceIte]
          rfl
        obtain ⟨_, regsEq, _⟩ := runX_same run run2
        rw [regsEq]
        exact left
      · have sourceRun : runX (inflate_STORED c) l h = runX (inflate_COPY_ c) first heap0 := by
          rw [sourceCut]
          simp only [beq_iff_eq, trees, ↓reduceIte]
          rfl
        obtain ⟨_, regs2, _, _, made, madeBound, run2, _, _, _, _, _, _, _, _, _, leftCount, _⟩ :=
          inflate_COPY_start_boundary_frame E0 good0 pending0 packet0 rfl
        obtain ⟨_, regsEq, _⟩ := runX_same run (sourceRun.trans run2)
        rw [regsEq]
        rw [List.length_drop, noBytes] at madeBound
        apply UInt32.toNat_inj.mp
        change regs2.left.toNat + made = current.left.toNat at leftCount
        rw [← left]
        omega
  · have run2 := inflate_STORED_wait (c := c) l current h Ex.leave (by rwa [wait] at pull)
    obtain ⟨_, regsEq, _⟩ := runX_same run run2
    rw [regsEq, left]

/-- One stored-block dispatch keeps at most 32 held bits outside `BAD`. -/
theorem inflate_dispatch_stored_held {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = STORED ∨ s.mode = COPY_ ∨ s.mode = COPY)
    (held : l.bits.toNat ≤ 32)
    {outcome : Except Ex Unit} {regs : IL} {after : Heap} {state : InflateState}
    (run : runX (inflate_dispatch c) l h = .ok ((outcome, regs), after))
    (get : after.istates zs = some state) :
    state.mode ≠ BAD → regs.bits.toNat ≤ 32 := by
  intro notBad
  rcases mode with stored | start | copy
  · rw [inflate_dispatch_STORED E l stored] at run
    have := inflate_STORED_held E invariant buffers stored run get notBad
    omega
  · rw [inflate_dispatch_COPY_start E l start] at run
    obtain ⟨_, regs2, _, _, _, _, run2, _, _, _, _, _, _, _, _, _, _, bitsEq, _⟩ :=
      inflate_COPY_start_boundary_frame E invariant.good invariant.pending buffers start
    obtain ⟨_, regsEq, _⟩ := runX_same run run2
    rw [regsEq, bitsEq]
    exact held
  · rw [inflate_dispatch_COPY E l copy] at run
    obtain ⟨_, regs2, _, _, _, _, run2, _, _, _, _, _, _, _, _, _, _, bitsEq, _⟩ :=
      inflate_COPY_boundary_frame E invariant.good invariant.pending buffers copy
    obtain ⟨_, regsEq, _⟩ := runX_same run run2
    rw [regsEq, bitsEq]
    exact held

/-- One block-type dispatch holds at most `max bits 10`. -/
theorem inflate_dispatch_type_held {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = TYPE ∨ s.mode = TYPEDO)
    {outcome : Except Ex Unit} {regs : IL} {after : Heap}
    (run : runX (inflate_dispatch c) l h = .ok ((outcome, regs), after)) :
    regs.bits.toNat ≤ max l.bits.toNat 10 := by
  rw [inflate_dispatch_block_type E l mode] at run
  rcases mode with type | typedo
  · rw [if_pos type] at run
    obtain ⟨_, regs2, _, _, _, _, _, _, run2, _, _, _, _, _, _, _, _, _, _, bits2, _⟩ :=
      inflate_TYPE_boundary E invariant.good invariant.pending buffers invariant.globals type
    obtain ⟨_, regsEq, _⟩ := runX_same run run2
    rw [regsEq]
    exact bits2
  · have notType : s.mode ≠ TYPE := by rw [typedo]; decide
    rw [if_neg notType] at run
    obtain ⟨_, regs2, _, _, _, _, _, _, run2, _, _, _, _, _, _, _, _, _, _, bits2, _⟩ :=
      inflate_TYPEDO_boundary E invariant.good invariant.pending buffers invariant.globals (Or.inr typedo)
    obtain ⟨_, regsEq, _⟩ := runX_same run run2
    rw [regsEq]
    exact bits2

/-- One table-construction dispatch, with its `LEN_` continuation, holds at
most `max bits 22`. -/
theorem inflate_dispatch_construction_held {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = TABLE ∨ s.mode = LENLENS ∨ s.mode = CODELENS)
    {outcome : Except Ex Unit} {regs : IL} {after : Heap}
    (run : runX (inflate_dispatch c) l h = .ok ((outcome, regs), after)) :
    regs.bits.toNat ≤ max l.bits.toNat 22 := by
  obtain ⟨regs1, after1, stream1, state1, used, _, nextJ, _, packet, _, _, _,
    _, _, _, bits1, _, stopped | continued⟩ :=
    inflate_dispatch_construction_state_boundary E invariant buffers mode
  · obtain ⟨_, run1, _⟩ := stopped
    obtain ⟨_, regsEq, _⟩ := runX_same run run1
    rw [regsEq]
    omega
  · obtain ⟨nextMode, source⟩ := continued
    by_cases trees : c.flush = Z_TREES
    · rw [if_pos trees] at source
      obtain ⟨_, regsEq, _⟩ := runX_same run source
      rw [regsEq]
      omega
    · rw [if_neg trees] at source
      have nextEnv : Env c after1 r zs stream1 state1 :=
        ⟨E.strm, E.st, nextJ.good.live.hz, nextJ.good.live.hs⟩
      have dataMode : DataTableMode state1.mode := by rw [nextMode]; unfold DataTableMode; decide
      obtain ⟨_, regs2, _, _, _, _, _, _, run2, _, _, _, _, _, _, _, _, bits2, _⟩ :=
        inflate_dispatch_data_view_state_rank nextEnv nextJ packet dataMode
      obtain ⟨_, regsEq, _⟩ :=
        runX_same run (source.trans ((inflate_dispatch_LEN_start nextEnv regs1 nextMode).symm.trans run2))
      rw [regsEq]
      omega

/-- One data dispatch holds at most `max bits 22`. -/
theorem inflate_dispatch_data_held {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : DataTableMode s.mode)
    {outcome : Except Ex Unit} {regs : IL} {after : Heap}
    (run : runX (inflate_dispatch c) l h = .ok ((outcome, regs), after)) :
    regs.bits.toNat ≤ max l.bits.toNat 22 := by
  obtain ⟨_, regs2, _, _, _, _, _, _, run2, _, _, _, _, _, _, _, _, bits2, _⟩ :=
    inflate_dispatch_data_view_state_rank E invariant buffers mode
  obtain ⟨_, regsEq, _⟩ := runX_same run run2
  rw [regsEq]
  exact bits2

/-- One `HEAD` dispatch holds at most `max bits 23`. -/
theorem inflate_dispatch_HEAD_held {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (local_ : HeaderLocal c h r s l) (mode : s.mode = HEAD)
    (incoming : l.bits.toNat ≤ 39)
    {outcome : Except Ex Unit} {regs : IL} {after : Heap}
    (run : runX (inflate_dispatch c) l h = .ok ((outcome, regs), after)) :
    regs.bits.toNat ≤ max l.bits.toNat 23 := by
  by_cases gzip : GzipAllowed s.wrap
  · obtain ⟨_, regs2, _, _, _, _, _, run2, _, _, _, _, _, _, _, _, bits2, _⟩ :=
      inflate_dispatch_HEAD_gzip_state_rank E invariant buffers mode gzip
        (local_ (by rw [mode]; decide) (by rw [mode]; decide)) incoming
    obtain ⟨_, regsEq, _⟩ := runX_same run run2
    rw [regsEq]
    exact bits2
  rw [inflate_dispatch_HEAD E l mode] at run
  rcases invariant.wrapper with raw | wrapped
  · obtain ⟨_, regsEq, _⟩ := runX_same run (inflate_HEAD_raw_run E l raw)
    rw [regsEq]
    omega
  · have zlib : s.wrap = 1 ∨ s.wrap = 5 := by
      rcases wrapped with w | w | w | w | w | w
      · exact Or.inl w
      · exact absurd (Or.inl w) gzip
      · exact absurd (Or.inr (Or.inl w)) gzip
      · exact Or.inr w
      · exact absurd (Or.inr (Or.inr (Or.inl w))) gzip
      · exact absurd (Or.inr (Or.inr (Or.inr w))) gzip
    obtain ⟨_, regs2, _, _, _, _, _, run2, _, _, _, _, _, _, _, _, _, bits2, _⟩ :=
      inflate_HEAD_zlib_window_boundary_budget E invariant.good invariant.pending buffers mode zlib
        (invariant.head_none zlib) invariant.toDefaultDecodeJ.headWindow
    obtain ⟨_, regsEq, _⟩ := runX_same run run2
    rw [regsEq]
    exact bits2

/-- `case DICT`: the result holds at most `max bits 10`. -/
theorem inflate_DICT_held {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = DICT) (incoming : l.bits.toNat ≤ 39)
    {outcome : Except Ex Unit} {regs : IL} {after : Heap}
    (run : runX (inflate_DICT c) l h = .ok ((outcome, regs), after)) :
    regs.bits.toNat ≤ max l.bits.toNat 10 := by
  by_cases missing : s.havedict = 0
  · obtain ⟨run2, _⟩ := inflate_DICT_wait_boundary E invariant.good invariant.pending buffers mode missing incoming
    obtain ⟨_, regsEq, _⟩ := runX_same run run2
    rw [regsEq]
    omega
  · let ready := { s with check := 1, mode := TYPE }
    let stream0 := { z with adler := 1 }
    let heap0 := setI (r.put h stream0) zs ready
    have good0 : Good heap0 r zs stream0 ready :=
      invariant.good.setZI rfl invariant.good.live.zalloc invariant.good.live.zfree rfl
        (by change HEAD ≤ TYPE ∧ TYPE ≤ SYNC; decide)
        (invariant.good.inv.of_fields rfl rfl rfl rfl rfl rfl rfl rfl rfl invariant.good.inv.bits rfl rfl rfl)
    have views : ∀ ref : BRef, (Space.get heap0 ref : Option (Array UInt8)) = Space.get h ref := by
      intro ref
      rw [byte_view_get_setI, byte_view_get_stream_put]
    have readonly : ∀ ref : BRef, Space.ro heap0 ref = Space.ro h ref := by
      intro ref
      rw [byte_view_ro_setI, byte_view_ro_stream_put]
    have sizes0 : ByteViewSizes h heap0 := by intro ref; rw [views]
    have static0 : heap0.static = h.static := by simp only [heap0, setI, ZStreamRef.put_static]
    have E0 : Env c heap0 r zs stream0 ready := ⟨E.strm, E.st, good0.live.hz, good0.live.hs⟩
    have pending0 : DataPendingInvariant ready := by
      apply dataPendingInvariant_idle (s := ready) invariant.pending.sane
      change TYPE ≠ LENEXT ∧ TYPE ≠ DIST ∧ TYPE ≠ DISTEXT ∧ TYPE ≠ MATCH
      decide
    have tables0 : DataTableInvariant heap0 ready :=
      dataTableInvariant_inactive (by change ¬ DataTableMode TYPE; unfold DataTableMode; decide)
    have state0 := invariant.dictionary_update (Or.inr mode) good0 tables0 pending0
      (by rfl) (Or.inr rfl) invariant.held sizes0 static0
    have packet0 := buffers.byte_views invariant.good good0 rfl views readonly
    have selector : runX (inflate_dispatch c) l heap0 = runX (inflate_TYPE c) l heap0 := by
      rw [inflate_dispatch_block_type E0 l (Or.inl rfl), if_pos rfl]
    exact inflate_dispatch_type_held E0 state0 packet0 (Or.inl rfl)
      (selector.trans ((inflate_DICT_ready_cut E l missing).symm.trans run))

/-- One dictionary dispatch keeps at most 32 held bits. -/
theorem inflate_dispatch_dictionary_held {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = DICTID ∨ s.mode = DICT)
    (held : l.bits.toNat ≤ 32)
    {outcome : Except Ex Unit} {regs : IL} {after : Heap}
    (run : runX (inflate_dispatch c) l h = .ok ((outcome, regs), after)) :
    regs.bits.toNat ≤ 32 := by
  rcases mode with id | dictionary
  · rw [inflate_dispatch_DICTID E l id] at run
    obtain ⟨_, current, used, pull, usedBound, bitInv, _, _, shape, _, _, _, leaveFacts, kinds, cursor⟩ :=
      NEEDBITS_run_cursor buffers.bits 32 (by decide)
    rcases kinds with normal | wait
    · rw [normal] at pull
      let value := ZSWAP32 current.hold
      let ready := { s with check := value, mode := DICT }
      let stream0 := { z with adler := value }
      let heap0 := setI (r.put h stream0) zs ready
      let first := { current with hold := 0, bits := 0 }
      have good0 : Good heap0 r zs stream0 ready :=
        invariant.good.setZI rfl invariant.good.live.zalloc invariant.good.live.zfree rfl
          (by change HEAD ≤ DICT ∧ DICT ≤ SYNC; decide)
          (invariant.good.inv.of_fields rfl rfl rfl rfl rfl rfl rfl rfl rfl invariant.good.inv.bits rfl rfl rfl)
      have E0 : Env c heap0 r zs stream0 ready := ⟨E.strm, E.st, good0.live.hz, good0.live.hs⟩
      have pending0 : DataPendingInvariant ready := by
        apply dataPendingInvariant_idle (s := ready) (by exact invariant.pending.sane)
        change DICT ≠ LENEXT ∧ DICT ≠ DIST ∧ DICT ≠ DISTEXT ∧ DICT ≠ MATCH
        decide
      have inv0 : BitInv heap0 first (bs.drop used) := by
        have inv := (INITBITS_inv bitInv).1
        apply inv.byte_views
        intro ref
        rw [byte_view_get_setI, byte_view_get_stream_put]
      have packet0 : DispatchBuffers heap0 r first (bs.drop used) :=
        buffers.consume invariant.good good0 rfl (fun ref => by rw [byte_view_get_setI, byte_view_get_stream_put])
          (fun ref => by rw [byte_view_ro_setI, byte_view_ro_stream_put])
          (by dsimp only [first]; rw [shape]; rfl) cursor usedBound inv0
      have sizes0 : ByteViewSizes h heap0 := by
        intro ref
        rw [byte_view_get_setI, byte_view_get_stream_put]
      have static0 : heap0.static = h.static := by simp only [heap0, setI, ZStreamRef.put_static]
      have tables0 : DataTableInvariant heap0 ready :=
        dataTableInvariant_inactive (by change ¬ DataTableMode DICT; unfold DataTableMode; decide)
      have state0 := invariant.dictionary_update (Or.inl id) good0 tables0 pending0
        (by rfl) (Or.inl rfl) invariant.held sizes0 static0
      have bound := inflate_DICT_held E0 state0 packet0 rfl (by change (0 : UInt32).toNat ≤ 39; simp)
        ((inflate_DICTID_parsed_cut E l current pull).symm.trans run)
      change regs.bits.toNat ≤ max (0 : UInt32).toNat 10 at bound
      simp at bound
      omega
    · obtain ⟨_, regsEq, _⟩ := runX_same run (inflate_DICTID_wait (c := c) (by rwa [wait] at pull))
      rw [regsEq]
      exact Nat.le_of_lt (leaveFacts wait).2.2
  · rw [inflate_dispatch_DICT E l dictionary] at run
    have := inflate_DICT_held E invariant buffers dictionary (by omega) run
    omega

/-- One trailer dispatch keeps at most `max bits 31` outside `BAD`. -/
theorem inflate_dispatch_trailer_held {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = CHECK ∨ s.mode = LENGTH)
    (incoming : l.bits.toNat ≤ 39)
    {outcome : Except Ex Unit} {regs : IL} {after : Heap} {state : InflateState}
    (run : runX (inflate_dispatch c) l h = .ok ((outcome, regs), after))
    (get : after.istates zs = some state) :
    state.mode ≠ BAD → regs.bits.toNat ≤ max l.bits.toNat 31 := by
  rcases mode with check | length
  · rw [inflate_dispatch_CHECK E l check] at run
    obtain ⟨_, regs2, after2, _, state2, _, _, run2, final, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      ⟨_, _, _, _, held2, _⟩⟩ :=
      inflate_CHECK_default_state_accounting_rank E invariant buffers check incoming
    obtain ⟨_, regsEq, heapEq⟩ := runX_same run run2
    subst heapEq
    have same : state = state2 := Option.some.inj (get.symm.trans final.good.live.hs)
    subst same
    rw [regsEq]
    exact held2
  · rw [inflate_dispatch_LENGTH E l length] at run
    exact (inflate_LENGTH_held E invariant buffers run get).1

/-- OPEN: the gzip header field modes keep at most 32 held bits outside `BAD`. -/
theorem inflate_dispatch_gzip_fields_held {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (local_ : HeaderLocal c h r s l) (mode : GzipHeaderMode s)
    (held : l.bits.toNat ≤ 32)
    {outcome : Except Ex Unit} {regs : IL} {after : Heap} {state : InflateState}
    (run : runX (inflate_dispatch c) l h = .ok ((outcome, regs), after))
    (get : after.istates zs = some state) :
    state.mode ≠ BAD → regs.bits.toNat ≤ 32 := by
  sorry

/-- One default dispatch keeps at most 32 held bits outside `BAD`. -/
theorem inflate_dispatch_held_bound {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (local_ : HeaderLocal c h r s l)
    (held : s.mode ≠ BAD → l.bits.toNat ≤ 32)
    {outcome : Except Ex Unit} {regs : IL} {after : Heap} {state : InflateState}
    (run : runX (inflate_dispatch c) l h = .ok ((outcome, regs), after))
    (get : after.istates zs = some state) :
    state.mode ≠ BAD → regs.bits.toNat ≤ 32 := by
  intro notBad
  rcases defaultMode_cases invariant.modes with head | dictionary | type | stored | construction | data | trailer | terminal | gzipHeader
  · have entry := held (by rw [head]; decide)
    have := inflate_dispatch_HEAD_held E invariant buffers local_ head (by omega) run
    omega
  · have entry := held (by rcases dictionary with m | m <;> rw [m] <;> decide)
    exact inflate_dispatch_dictionary_held E invariant buffers dictionary entry run
  · have entry := held (by rcases type with m | m <;> rw [m] <;> decide)
    have := inflate_dispatch_type_held E invariant buffers type run
    omega
  · have entry := held (by rcases stored with m | m | m <;> rw [m] <;> decide)
    exact inflate_dispatch_stored_held E invariant buffers stored entry run get notBad
  · have entry := held (by rcases construction with m | m | m <;> rw [m] <;> decide)
    have := inflate_dispatch_construction_held E invariant buffers construction run
    omega
  · have entry := held (by
      rcases data with m | m | m | m | m | m | m <;> rw [m] <;> decide)
    have := inflate_dispatch_data_held E invariant buffers data run
    omega
  · have entry := held (by rcases trailer with m | m <;> rw [m] <;> decide)
    have := inflate_dispatch_trailer_held E invariant buffers trailer (by omega) run get notBad
    omega
  · obtain ⟨run2, _, _, bits2, _⟩ := inflate_dispatch_terminal_state E invariant buffers terminal
    obtain ⟨_, regsEq, heapEq⟩ := runX_same run run2
    subst heapEq
    have same : state = s := Option.some.inj (get.symm.trans invariant.good.live.hs)
    subst same
    rw [regsEq, bits2]
    exact held notBad
  · have entry := held (by
      obtain ⟨_, high, _⟩ := gzipHeader
      intro bad
      rw [bad] at high
      exact absurd high (by decide))
    exact inflate_dispatch_gzip_fields_held E invariant buffers local_ gzipHeader entry run get notBad

end Zlib.Inflate.Proofs
