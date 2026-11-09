import ZlibF.Proof.«inflate.c.local-construction-core»

namespace Zlib.Inflate.Local
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- The complete actual CODELENS reading loop preserves every clause of
J, including partial input and malformed repeats. Its exact input trace
is retained for subsequent dispatch composition. -/
theorem clRead_default_J_complete {c : Ctx} {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : LocalDecodeJ h cutoff r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = CODELENS) :
    ∃ outcome regs after stream state used, used ≤ bs.length ∧
      runX (clRead c) l h = .ok ((outcome, regs), after) ∧ LocalDecodeJ after cutoff r zs stream state ∧
      DispatchBuffers after r regs (bs.drop used) ∧ ByteViewSizes h after ∧
      regs.next = inputAdvance l.next used ∧ regs.have_.toNat + used = l.have_.toNat ∧
      regs.put = l.put ∧ regs.left = l.left ∧ regs.out_ = l.out_ ∧
      regs.bits.toNat ≤ max l.bits.toNat 21 ∧ regs.bits.toNat ≤ l.bits.toNat + 8 * used ∧
      (state.mode = CODELENS ∨ state.mode = BAD) ∧
      (outcome = .ok () → state.mode = BAD ∨ state.«have».toNat = state.nlen.toNat + state.ndist.toNat) := by
  obtain ⟨outcome, regs, after, stream, state, used, bound, run, current, tables, pending, codes,
    packet, sizes, cursor, count, put, left, total, bits, budget, static, frame, modes, complete⟩ :=
    clRead_buffers E invariant.good invariant.pending invariant.lengths buffers mode
  have next : LocalDecodeJ after cutoff r zs stream state := by
    refine ⟨current, tables, pending, codes, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, sizes.platform invariant.platform⟩
    · intro active
      rcases modes with selected | selected <;> rw [selected] at active <;> contradiction
    · rw [frame]
      exact invariant.held
    · rw [frame]
      exact invariant.window
    · rw [frame]
      exact invariant.wrapper
    · rw [frame]
      exact invariant.header
    · right
      rcases modes with selected | selected <;> rw [selected] <;> decide
    · rintro (active | active) <;>
        rcases modes with selected | selected <;> rw [selected] at active <;> contradiction
    · change after.static = _
      rw [static]
      exact invariant.globals
  refine ⟨outcome, regs, after, stream, state, used, bound, run, next,
    packet, sizes, cursor, count, put, left, total, bits, budget, modes, ?_⟩

  intro normal
  rcases complete normal with bad | full
  · exact Or.inl bad
  · right
    rw [show state.nlen = s.nlen by rw [frame], show state.ndist = s.ndist by rw [frame]]
    exact full


/-- The entire actual LENLENS reading loop preserves J's initialized
prefix and every other clause. Unused lens cells remain arbitrary. -/
theorem ll1_default_J {c : Ctx} {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : LocalDecodeJ h cutoff r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = LENLENS) :
    ∃ outcome regs after state used, used ≤ bs.length ∧
      runX (xwhile (llCond c) (llBody c)) l h = .ok ((outcome, regs), after) ∧
      LocalDecodeJ after cutoff r zs z state ∧ DispatchBuffers after r regs (bs.drop used) ∧
      ByteViewSizes h after ∧ regs.next = inputAdvance l.next used ∧
      regs.have_.toNat + used = l.have_.toNat ∧ regs.put = l.put ∧ regs.left = l.left ∧
      regs.out_ = l.out_ ∧ regs.bits.toNat ≤ max l.bits.toNat 10 ∧
      regs.bits.toNat ≤ l.bits.toNat + 8 * used := by
  obtain ⟨ncode, haveBound, nlen, ndist, prefixValues⟩ := invariant.headerLengths mode
  obtain ⟨outcome, regs, used, run, bound, inv, stream, shape, _, _, cursor, bits⟩ :=
    ll1_run_cursor E.st E.hs invariant.good.inv.wf.1 ncode haveBound buffers.bits
  let m := min (s.ncode.toNat - s.«have».toNat) ((Zlib.Inflate.Proofs.stream l bs).length / 3)
  let state := llSt s (Zlib.Inflate.Proofs.stream l bs) m
  let after := setI h zs state
  have mBound : s.«have».toNat + m ≤ 19 := by
    have := Nat.min_le_left (s.ncode.toNat - s.«have».toNat) ((Zlib.Inflate.Proofs.stream l bs).length / 3)
    omega
  have stateCount : state.«have».toNat = s.«have».toNat + m := llSt_have s _ m mBound
  have statePrefix : Good3 state.lens state.«have».toNat := by
    rw [stateCount]
    exact lensRead_good _ prefixValues m mBound
  have current : LocalGood after cutoff r zs z state := by
    apply invariant.good.state (state := state) rfl invariant.good.live.mode
    refine ⟨⟨?_, invariant.good.inv.wf.2.1, invariant.good.inv.wf.2.2⟩, ?_,
      invariant.good.inv.reqbits, invariant.good.inv.bits, invariant.good.inv.ptr⟩
    · change (lensRead s.lens s.«have».toNat _ m).size = 320
      rw [lensRead_size]
      exact invariant.good.inv.wf.1
    · exact ⟨invariant.good.inv.win.wbits, invariant.good.inv.win.block, invariant.good.inv.win.nullws,
        invariant.good.inv.win.ws, invariant.good.inv.win.hv, invariant.good.inv.win.wn, invariant.good.inv.win.eq⟩
  have next : LocalDecodeJ after cutoff r zs z state := by
    refine ⟨current, ?_, ⟨invariant.pending.sane, invariant.pending.lenext, invariant.pending.dist,
      invariant.pending.distext, invariant.pending.matching⟩, ?_, ?_, invariant.held,
      invariant.window, invariant.wrapper, invariant.header, invariant.modes, invariant.trailer,
      invariant.globals, invariant.platform.with_istates _⟩
    · exact dataTableInvariant_inactive (by change ¬ DataTableMode s.mode; rw [mode]; unfold DataTableMode; decide)
    · intro active
      change s.mode = CODELENS at active
      rw [mode] at active
      contradiction
    · intro _
      refine ⟨ncode, ?_, nlen, ndist, statePrefix⟩
      change state.«have».toNat ≤ s.ncode.toNat
      rw [stateCount]
      have := Nat.min_le_left (s.ncode.toNat - s.«have».toNat) ((Zlib.Inflate.Proofs.stream l bs).length / 3)
      omega
  have sizes : ByteViewSizes h after := byte_view_sizes_setI h zs state
  have count : regs.have_.toNat + used = l.have_.toNat := by
    rw [inv.have_eq, buffers.bits.have_eq, List.length_drop]
    omega
  have packet : DispatchBuffers after r regs (bs.drop used) :=
    dispatch_advance_both_local buffers invariant.good current rfl sizes (fun ref => byte_view_ro_setI h zs state ref)
      cursor count (made := 0) (by rw [shape, inputAdvance_zero]) (by rw [shape]; rfl) (by rw [shape]) (inv.decode_update zs state)
  have budget : regs.bits.toNat ≤ l.bits.toNat + 8 * used := by
    have shorter : (Zlib.Inflate.Proofs.stream regs (bs.drop used)).length ≤
        (Zlib.Inflate.Proofs.stream l bs).length := by
      rw [stream, List.length_drop]
      omega
    rw [tcStream_length inv, tcStream_length buffers.bits, List.length_drop] at shorter
    omega
  exact ⟨outcome, regs, after, state, used, bound, run, next, packet, sizes, cursor, count,
    by rw [shape], by rw [shape], by rw [shape], bits, budget⟩


/-- Actual constructor metadata changes retain all other clauses of J. -/
theorem LocalDecodeJ.table_update {h after : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z stream : ZStream} {s state : InflateState} (invariant : LocalDecodeJ h cutoff r zs z s)
    (current : LocalGood after cutoff r zs stream state) (tables : DataTableInvariant after state)
    (pending : DataPendingInvariant state) (sizes : ByteViewSizes h after) (static : after.static = h.static)
    (update : ClTablesUpdate h r zs z s after stream state) (modes : state.mode = BAD ∨ state.mode = LEN_) :
    LocalDecodeJ after cutoff r zs stream state := by
  have frame := update.2.2
  refine ⟨current, tables, pending, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, sizes.platform invariant.platform⟩
  · intro active
    rcases modes with selected | selected <;> rw [selected] at active <;> contradiction
  · intro active
    rcases modes with selected | selected <;> rw [selected] at active <;> contradiction
  · rw [frame]
    exact invariant.held
  · rw [frame]
    exact invariant.window
  · rw [frame]
    exact invariant.wrapper
  · rw [frame]
    exact invariant.header
  · right
    rcases modes with selected | selected <;> rw [selected] <;> decide
  · rintro (active | active) <;>
      rcases modes with selected | selected <;> rw [selected] at active <;> contradiction
  · change after.static = _
    rw [static]
    exact invariant.globals

/-- The exact length-table metadata update preserves the full local J.
Array bounds and the installed table predicate come from actual execution. -/
theorem LocalDecodeJ.length_table_update {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z stream : ZStream} {s state : InflateState} (invariant : LocalDecodeJ h cutoff r zs z s)
    (frame : LengthTableFrame s state) (streamFrame : stream = { z with msg := stream.msg })
    (wf : state.WellFormed) (pointers : PtrInv zs state)
    (modes : state.mode = BAD ∨ state.mode = CODELENS) (codes : CodeLengthInvariant zs state) :
    LocalDecodeJ (setI (r.put h stream) zs state) cutoff r zs stream state := by
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
  have current : LocalGood (setI (r.put h stream) zs state) cutoff r zs stream state :=
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
  · rw [frame]
    exact invariant.header
  · right
    rcases modes with selected | selected <;> rw [selected] <;> decide
  · rintro (active | active) <;>
      rcases modes with selected | selected <;> rw [selected] at active <;> contradiction

/-- Retain the exact caller packet across a checked length-table update.
The source read trace supplies all input advancement; constructors write
only private metadata and an optional error message. -/
theorem LocalDecodeJ.length_table_packet {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z stream : ZStream} {s state : InflateState} {l regs : IL} {bs : List UInt8} {used : Nat}
    (invariant : LocalDecodeJ h cutoff r zs z s) (buffers : DispatchBuffers h r l bs)
    (frame : LengthTableFrame s state) (streamFrame : stream = { z with msg := stream.msg })
    (wf : state.WellFormed) (pointers : PtrInv zs state)
    (modes : state.mode = BAD ∨ state.mode = CODELENS) (codes : CodeLengthInvariant zs state)
    (inv : BitInv h regs (bs.drop used)) (cursor : regs.next = inputAdvance l.next used)
    (count : regs.have_.toNat + used = l.have_.toNat) (put : regs.put = l.put)
    (left : regs.left = l.left) (total : regs.out_ = l.out_) :
    LocalDecodeJ (setI (r.put h stream) zs state) cutoff r zs stream state ∧
      DispatchBuffers (setI (r.put h stream) zs state) r regs (bs.drop used) ∧
      ByteViewSizes h (setI (r.put h stream) zs state) := by
  have next := invariant.length_table_update frame streamFrame wf pointers modes codes
  have views : ∀ ref : BRef, Space.get (setI (r.put h stream) zs state) ref = Space.get h ref := by
    intro ref
    rw [byte_view_get_setI, byte_view_get_stream_put]
  have sizes : ByteViewSizes h (setI (r.put h stream) zs state) := by intro ref; rw [views]
  have readonly : ∀ ref : BRef, Space.ro (setI (r.put h stream) zs state) ref = Space.ro h ref := by
    intro ref
    rw [byte_view_ro_setI, byte_view_ro_stream_put]
  have packet := dispatch_advance_both_local buffers invariant.good next.good (by rw [frame]) sizes readonly cursor count
    (made := 0) (by rw [inputAdvance_zero]; exact put) (by rw [left]; rfl) total (inv.byte_views views)
  exact ⟨next, packet, sizes⟩


/-- Actual count writes retain J once the real validity check has supplied
its guarded LENLENS clause. BAD activates no construction precondition. -/
theorem LocalDecodeJ.counts_update {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z stream : ZStream} {s state : InflateState} (invariant : LocalDecodeJ h cutoff r zs z s)
    (frame : TableCountsFrame s state) (streamFrame : stream = { z with msg := stream.msg })
    (modes : state.mode = BAD ∨ state.mode = LENLENS) (lengths : LengthHeaderInvariant state) :
    LocalDecodeJ (setI (r.put h stream) zs state) cutoff r zs stream state := by
  have bounds : HEAD ≤ state.mode ∧ state.mode ≤ SYNC := by
    rcases modes with selected | selected <;> rw [selected] <;> decide
  have inv : StInv h zs state := by
    apply invariant.good.inv.of_fields
    all_goals rw [frame]
    exact invariant.good.inv.bits
  have current : LocalGood (setI (r.put h stream) zs state) cutoff r zs stream state :=
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
  · rw [frame]
    exact invariant.header
  · right
    rcases modes with selected | selected <;> rw [selected] <;> decide
  · rintro (active | active) <;>
      rcases modes with selected | selected <;> rw [selected] at active <;> contradiction

/-- Exact metadata writes preserve all public byte views and transport
an already checked input trace without changing the output interval. -/
theorem metadata_advance {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z stream : ZStream} {s state : InflateState} {l regs : IL} {bs : List UInt8} {used : Nat}
    (buffers : DispatchBuffers h r l bs) (before : LocalGood h cutoff r zs z s)
    (current : LocalGood (setI (r.put h stream) zs state) cutoff r zs stream state)
    (window : state.window = s.window) (inv : BitInv h regs (bs.drop used))
    (cursor : regs.next = inputAdvance l.next used) (count : regs.have_.toNat + used = l.have_.toNat)
    (put : regs.put = l.put) (left : regs.left = l.left) (total : regs.out_ = l.out_) :
    DispatchBuffers (setI (r.put h stream) zs state) r regs (bs.drop used) ∧
      ByteViewSizes h (setI (r.put h stream) zs state) := by
  have views : ∀ ref : BRef, Space.get (setI (r.put h stream) zs state) ref = Space.get h ref := by
    intro ref
    rw [byte_view_get_setI, byte_view_get_stream_put]
  have sizes : ByteViewSizes h (setI (r.put h stream) zs state) := by intro ref; rw [views]
  have readonly : ∀ ref : BRef, Space.ro (setI (r.put h stream) zs state) ref = Space.ro h ref := by
    intro ref
    rw [byte_view_ro_setI, byte_view_ro_stream_put]
  exact ⟨dispatch_advance_both_local buffers before current window sizes readonly cursor count (made := 0)
    (by rw [inputAdvance_zero]; exact put) (by rw [left]; rfl) total (inv.byte_views views), sizes⟩


end Zlib.Inflate.Local
