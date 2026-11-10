import ZlibF.Proof.«inflate.c.global-header-composition»
import ZlibF.Proof.«inflate.c.installed-payload-tables»
import ZlibF.Proof.«inffixed.h.fixed-decode-invariant-global»
import ZlibF.Proof.«inflate.c.slow-token-syntax»
import ZlibF.Proof.«inflate.c.slow-token-phase-frames»

namespace Zlib.Inflate.Proofs.FunctionalEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inftrees
open Zlib.Inftrees.Spec.DecodeTableInvariant Zlib.Inftrees.Spec.DecodeTableStability
set_option autoImplicit false

theorem fixed_installed_tables (h : Heap) (s : InflateState) (globals : LibraryGlobals h) :
    InstalledTables h { fixedState s with mode := LEN_ } fixedLitLens fixedDistLens := by
  constructor
  · refine ⟨.st_lenfix, 0, Zlib.InffixedH.lenfix, 512, rfl, ?_,
      Zlib.InffixedH.Proofs.lenfix_decode_invariant, Zlib.InffixedH.Proofs.lenfix_stable_query⟩
    change some h.static.lenfix = some Zlib.InffixedH.lenfix
    rw [globals]
    rfl
  · refine ⟨.st_distfix, 0, Zlib.InffixedH.distfix, 32, rfl, ?_,
      Zlib.InffixedH.Proofs.distfix_decode_invariant, Zlib.InffixedH.Proofs.distfix_stable_query⟩
    change some h.static.distfix = some Zlib.InffixedH.distfix
    rw [globals]
    rfl

/-- The first-header representation gives an actual empty saved history;
this follows from the real window count bound, including a lazy window. -/
theorem zero_window_dictionary {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (good : Good h r zs z s) (zero : s.wsize = 0) :
    InflateDictionary h s [] := by
  have count := good.inv.win.hv
  rw [zero] at count
  have empty : s.whave = 0 := UInt32.toNat_inj.mp (by simpa using Nat.eq_zero_of_le_zero count)
  exact Or.inl ⟨empty, rfl⟩

theorem dictionary_zero_window_empty {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {history : List UInt8}
    (good : Good h r zs z s) (zero : s.wsize = 0)
    (dictionary : InflateDictionary h s history) : history = [] := by
  have count := good.inv.win.hv
  have next := good.inv.win.wn
  rw [zero] at count next
  simp only [UInt32.toNat_zero] at count next
  have haveZero : s.whave = 0 := UInt32.toNat_inj.mp (by simpa using Nat.eq_zero_of_le_zero count)
  have nextZero : s.wnext = 0 := UInt32.toNat_inj.mp (by change s.wnext.toNat = 0; omega)
  rcases dictionary with ⟨_, empty⟩ | ⟨_ref, _off, _a, _window, _get, _bound, values⟩
  · exact empty
  · simpa only [haveZero, nextZero, UInt32.sub_self, UInt32.toNat_zero, List.take_zero, List.nil_append] using values

/-- The exact actual saved-window theorem forces the logical history to
be empty at a zero-window active header. This also handles a successfully
installed empty dictionary; no one-setter or no-dictionary assumption is
introduced for callers. -/
theorem protocol_zero_window_history
    {h : Heap} {r : ZStreamRef} {log : DataLog} {pending : Bool}
    {zs : Nat} {z : ZStream} {s : InflateState}
    (trace : InflateProtocolTrace 15 r h log pending) (scope : ProtocolWindow.PlatformScope trace)
    (good : Good h r zs z s) (active : s.mode < CHECK) (zero : s.wsize = 0) :
    log.dictionary ++ log.output = [] := by
  obtain ⟨physical, history, equality, _facts⟩ := ProtocolWindow.exact_physical_history trace scope
  obtain ⟨index, stream, state, current, _allocator, saved⟩ := history.invariant
  have sameZ : stream = z := Option.some.inj (current.good.live.hz.symm.trans good.live.hz)
  subst stream
  have sameIndex : index = zs := by simpa using current.good.live.zst.symm.trans good.live.zst
  subst index
  have sameS : state = s := Option.some.inj (current.good.live.hs.symm.trans good.live.hs)
  subst state
  have dictionary := saved active
  rw [equality] at dictionary
  have retained := dictionary_zero_window_empty good zero dictionary
  have length := congrArg List.length retained
  simp only [List.length_drop, List.length_nil] at length
  have capacity := Nat.two_pow_pos s.wbits.toNat
  exact List.length_eq_zero_iff.mp (by omega)

/-- A real block-header field update retains the full chronological
dictionary. No assumption about the window contents is added. -/
theorem dictionary_block_header {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s state : InflateState} {history : List UInt8}
    (good : Good h r zs z s) (frame : BlockHeaderFrame s state)
    (dictionary : InflateDictionary h s history) :
    InflateDictionary (setI h zs state) state history := by
  rcases dictionary with ⟨zero, empty⟩ | ⟨ref, off, a, window, get, bound, values⟩
  · exact Or.inl ⟨by rw [frame]; exact zero, empty⟩
  · rcases good.inv.win.block with null | ⟨b, bytes, ptr, _get, _ro, _size⟩
    · rw [null] at window
      cases window
    · rw [ptr] at window
      cases window
      refine Or.inr ⟨.blk b, 0, a, ?_, ?_, ?_, ?_⟩
      · rw [frame]
        exact ptr
      · simpa only [Space.get, BRef.get_blk, setI] using get
      · rw [frame]
        exact bound
      · rw [frame]
        exact values

/-- This is an internal payload representation produced at actual source
cuts. Its table and dictionary fields are conclusions of the constructors
and protocol history. It is not a premise of a public history constructor. -/
def PayloadRepresentation (h : Heap) (r : ZStreamRef) (zs : Nat) (z : ZStream)
    (s : InflateState) (regs : IL) (unread : List UInt8)
    (L D : List Nat) (logical : List UInt8) : Prop :=
  DefaultOriginState h r zs z s ∧ DispatchBuffers h r regs unread ∧
  regs.bits.toNat ≤ 39 ∧ InstalledTables h s L D ∧
  InflateDictionary h s (logical.drop (logical.length - 2 ^ s.wbits.toNat))

/-- Actual fixed-block selection produces both semantic table invariants,
both StableQuery facts, the real outgoing packet and the retained logical
window on one source state. Z_TREES is the actual leave branch. -/
theorem typedo_fixed_representation
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8} {logical : List UInt8}
    (E : Env c h r zs z s) (origin : DefaultOriginState h r zs z s)
    (buffers : DispatchBuffers h r l bs) (modes : s.mode = TYPE ∨ s.mode = TYPEDO)
    (full : 2 ≤ l.bits.toNat) (incoming : l.bits.toNat ≤ 39)
    (kind : l.hold.toNat % 4 = 1)
    (dictionary : InflateDictionary h s (logical.drop (logical.length - 2 ^ s.wbits.toNat))) :
    let regs := { l with hold := l.hold >>> (2 : UInt32).toUInt64, bits := l.bits - 2 }
    let state := { fixedState s with mode := LEN_ }
    let after := setI h zs state
    runX (typedoTail c) l h =
      .ok ((if c.flush = Z_TREES then .error Ex.leave else .ok (), regs), after) ∧
      PayloadRepresentation after r zs z state regs bs fixedLitLens fixedDistLens logical ∧
      regs.next = l.next ∧ regs.put = l.put ∧ regs.have_ = l.have_ ∧
      regs.left = l.left ∧ regs.out_ = l.out_ ∧
      stream regs bs = (stream l bs).drop 2 := by
  dsimp only
  let regs := { l with hold := l.hold >>> (2 : UInt32).toUInt64, bits := l.bits - 2 }
  let state := { fixedState s with mode := LEN_ }
  let after := setI h zs state
  have frame : BlockHeaderFrame s state := rfl
  have pointers : BlockHeaderPointers s state := Or.inr ⟨rfl, rfl⟩
  obtain ⟨bits, remaining, bitCount⟩ := DROPBITS_inv buffers.bits 2 full (by decide)
  obtain ⟨good, packet, sizes⟩ := block_header_packet origin.good buffers frame pointers
    (by change HEAD ≤ LEN_ ∧ LEN_ ≤ SYNC; decide) bits (by rfl)
  have tables : DataTableInvariant after state := by
    intro _
    have safe := fixedState_tables_safe (h := after) s (show LibraryGlobals after from origin.globals)
    exact ⟨safe.lengthTable, safe.distanceTable⟩
  have pending := block_header_pending origin.pending frame (Or.inr (Or.inr (Or.inl rfl)))
  have format := origin.toDefaultStateJ.block_format modes
  have current := origin.toDefaultDecodeJ.block_update good tables pending frame
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) format sizes rfl
  have final := origin.toDefaultStateJ.config_update current (by exact ⟨rfl, rfl, rfl, rfl⟩) format
  have finalOrigin := origin.of_pointer_alternatives final rfl (Or.inr ⟨rfl, rfl⟩)
  have finalDictionary : InflateDictionary after state
      (logical.drop (logical.length - 2 ^ state.wbits.toNat)) := dictionary_block_header origin.good frame dictionary
  refine ⟨?_, ⟨finalOrigin, packet, ?_, fixed_installed_tables after s origin.globals,
    finalDictionary⟩, rfl, rfl, rfl, rfl, rfl, remaining⟩
  · by_cases trees : c.flush = Z_TREES
    · have shift : l.hold >>> (2 : UInt32).toUInt64 = l.hold >>> 2 := by congr 1
      simpa only [ite_eq_left trees, shift] using typedoTail_fixed_trees E l kind trees
    · have shift : l.hold >>> (2 : UInt32).toUInt64 = l.hold >>> 2 := by congr 1
      simpa only [ite_eq_right trees, shift] using typedoTail_fixed E l kind trees
  · change (l.bits - 2).toNat ≤ 39
    rw [bitCount]
    omega

/-- Independent fixed block bits determine the actual two-bit source
guard and exact remaining current/future stream. No current code-width
or desired returned mode is imposed. -/
theorem fixed_kind_future
    {h : Heap} {l : IL} {bs : List UInt8} {future payload : List Bool}
    (B : BitInv h l bs) (full : 2 ≤ l.bits.toNat)
    (parsed : readBits 2 (stream l bs ++ future) = some (1, payload)) :
    l.hold.toNat % 4 = 1 ∧
      stream { l with hold := l.hold >>> (2 : UInt32).toUInt64, bits := l.bits - 2 } bs ++ future = payload := by
  have current := readBits_held_stream l bs 2 full
  have extended := ZlibF.Spec.Proofs.readBits_append 2 (stream l bs)
    (l.hold.toNat % 2 ^ 2) ((stream l bs).drop 2) future current
  obtain ⟨value, rest⟩ := Prod.mk.inj (Option.some.inj (extended.symm.trans parsed))
  obtain ⟨_bits, remaining, _count⟩ := DROPBITS_inv B 2 full (by decide)
  exact ⟨by simpa using value, by rw [remaining]; exact rest⟩

theorem InstalledTables.decode_update
    {h : Heap} {zs : Nat} {s state : InflateState} {L D : List Nat}
    (tables : InstalledTables h s L D) (get : h.istates zs = some s)
    (frame : DecodeStateFrame s state) : InstalledTables (setI h zs state) state L D := by
  constructor
  · obtain ⟨ref, offset, ca, used, pointer, tableGet, meaning, stable⟩ := tables.1
    refine ⟨ref, offset, ca, used, ?_, ?_, ?_, ?_⟩
    · rw [frame]; exact pointer
    · rw [decode_code_views get frame]; exact tableGet
    · rw [frame]; exact meaning
    · rw [frame]; exact stable
  · obtain ⟨ref, offset, ca, used, pointer, tableGet, meaning, stable⟩ := tables.2
    refine ⟨ref, offset, ca, used, ?_, ?_, ?_, ?_⟩
    · rw [frame]; exact pointer
    · rw [decode_code_views get frame]; exact tableGet
    · rw [frame]; exact meaning
    · rw [frame]; exact stable

theorem dictionary_decode_update {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s state : InflateState} {history : List UInt8}
    (good : Good h r zs z s) (frame : DecodeStateFrame s state)
    (dictionary : InflateDictionary h s history) :
    InflateDictionary (setI h zs state) state history := by
  rcases dictionary with ⟨zero, empty⟩ | ⟨ref, off, a, window, get, bound, values⟩
  · exact Or.inl ⟨by rw [frame]; exact zero, empty⟩
  · rcases good.inv.win.block with null | ⟨b, bytes, ptr, _get, _ro, _size⟩
    · rw [null] at window
      cases window
    · rw [ptr] at window
      cases window
      refine Or.inr ⟨.blk b, 0, a, ?_, ?_, ?_, ?_⟩
      · rw [frame]; exact ptr
      · simpa only [Space.get, BRef.get_blk, setI] using get
      · rw [frame]; exact bound
      · rw [frame]; exact values

/-- The actual no-output slow-code packet composes with the real dispatch
safety producer. Both semantic tables, the logical saved window and every
outgoing caller byte view survive partial input, literal and EOB events. -/
theorem code_point_representation
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {s state : InflateState} {l regs : IL} {bs : List UInt8} {L D : List Nat}
    {future residual : List Bool} {used : Nat} {logical : List UInt8} {outcome : Except Ex Unit}
    (E : Env c h r zs z s)
    (before : PayloadRepresentation h r zs z s l bs L D logical)
    (point : SlowTokenPath.CodePoint h s l bs future r zs z after state regs used residual)
    (actual : runX (inflate_dispatch c) l h = .ok ((outcome, regs), after)) :
    PayloadRepresentation after r zs z state regs (bs.drop used) L D logical ∧
      (∀ ref : BRef, (Space.get after ref : Option (Array UInt8)) = Space.get h ref) := by
  obtain ⟨origin, buffers, bits, tables, dictionary⟩ := before
  obtain ⟨exit, finalRegs, finalHeap, stream, observed, consumed, made, _bound, source,
    current, _packet, _sizes, _next, _have, _put, _left, finalBits, _rank⟩ :=
    inflate_dispatch_default_origin_state_rank E origin buffers bits
  have same := Except.ok.inj (source.symm.trans actual)
  cases same
  have sameZ : stream = z := Option.some.inj (current.good.live.hz.symm.trans point.good.live.hz)
  subst stream
  have sameS : observed = state := Option.some.inj (current.good.live.hs.symm.trans point.good.live.hs)
  subst observed
  refine ⟨⟨current, point.buffers origin.good buffers, finalBits, ?_, ?_⟩, ?_⟩
  · rw [point.heap]
    exact tables.decode_update origin.good.live.hs point.frame
  · rw [point.heap]
    have retained := dictionary_decode_update origin.good point.frame dictionary
    simpa only [show state.wbits = s.wbits from by rw [point.frame]] using retained
  · intro ref
    rw [point.heap, byte_view_get_setI]

/-- Initial payload grammar produces the first independent pending token
from the original Symbols relation. This does not select an actual branch
or assume any callee return. -/
theorem payload_token_from_symbols
    {L D : List Nat} {dict prior decoded : List UInt8} {payload rest : List Bool}
    {state : InflateState}
    (symbols : Symbols L D dict prior payload rest decoded) (mode : state.mode = LEN_) :
    ∃ token : SlowTokenPath.TokenSyntax L D,
      token.input = payload ∧ token.admissible dict prior ∧
      SlowTokenPath.TokenPhase token state payload ∧
      ((token.ended = true ∧ token.rest = rest ∧ decoded = prior) ∨
       (token.ended = false ∧ Symbols L D dict (token.effect dict prior) token.rest rest decoded)) := by
  obtain ⟨token, input, admissible, continuation⟩ := SlowTokenPath.TokenSyntax.of_symbols symbols
  exact ⟨token, input, admissible, by rw [← input]; exact .code (Or.inr mode), continuation⟩

theorem InstalledTables.leave_restore
    {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState} {L D : List Nat}
    (tables : InstalledTables h s L D) (get : h.istates zs = some s) (l : IL) :
    InstalledTables (setI (r.put h (leaveStream z l)) zs (leaveState s l)) (leaveState s l) L D := by
  have stored : (r.put h (leaveStream z l)).istates zs = some s := by simpa using get
  constructor
  · obtain ⟨ref, offset, ca, used, pointer, tableGet, meaning, stable⟩ := tables.1
    refine ⟨ref, offset, ca, used, pointer, ?_, meaning, stable⟩
    unfold leaveState
    rw [code_views_set_bits stored, code_views_put_stream]
    exact tableGet
  · obtain ⟨ref, offset, ca, used, pointer, tableGet, meaning, stable⟩ := tables.2
    refine ⟨ref, offset, ca, used, pointer, ?_, meaning, stable⟩
    unfold leaveState
    rw [code_views_set_bits stored, code_views_put_stream]
    exact tableGet

/-- The literal LEN_ mode write preserves the actual semantic tables and
saved logical history before selecting the real slow or fast LEN branch. -/
theorem PayloadRepresentation.len_start
    {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8} {L D : List Nat} {logical : List UInt8}
    (before : PayloadRepresentation h r zs z s l bs L D logical) (mode : s.mode = LEN_) :
    PayloadRepresentation (setI h zs {s with mode := LEN}) r zs z {s with mode := LEN} l bs L D logical := by
  obtain ⟨origin, buffers, bits, tables, dictionary⟩ := before
  let state := {s with mode := LEN}
  have frame : DecodeStateFrame s state := rfl
  have good := origin.good.decode_update frame (by change HEAD ≤ LEN ∧ LEN ≤ SYNC; decide)
  have dataMode : DataTableMode s.mode := by rw [mode]; unfold DataTableMode; decide
  have safe := (origin.tables dataMode).decode_update origin.good.live.hs frame
  have pending : DataPendingInvariant state := by
    apply dataPendingInvariant_idle (s := state) origin.pending.sane
    change LEN ≠ LENEXT ∧ LEN ≠ DIST ∧ LEN ≠ DISTEXT ∧ LEN ≠ MATCH
    decide
  have decoded := origin.toDefaultDecodeJ.decode_update good (fun _ => safe) pending frame
    (Or.inl (by change DataTableMode LEN; unfold DataTableMode; decide)) (byte_view_sizes_setI h zs state) rfl
  have current : DefaultStateJ (setI h zs state) r zs z state :=
    ⟨decoded, origin.requestedBits, origin.requestedWrap,
      Or.inr (Or.inr (Or.inr (Or.inr (origin.toDefaultStateJ.data_format dataMode))))⟩
  have packet := buffers.byte_views origin.good good rfl (byte_view_get_setI h zs state) (byte_view_ro_setI h zs state)
  exact ⟨origin.decode_update current frame, packet, bits, tables.decode_update origin.good.live.hs frame,
    dictionary_decode_update origin.good frame dictionary⟩

/-- Actual RESTORE synchronizes callee records with the live local
cursors while retaining both table meanings and logical saved window. -/
theorem PayloadRepresentation.restore
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8} {L D : List Nat} {logical : List UInt8}
    (E : Env c h r zs z s) (before : PayloadRepresentation h r zs z s l bs L D logical) :
    runX (RESTORE c.strm c.st) l h =
      .ok ((.ok (), l), setI (r.put h (leaveStream z l)) zs (leaveState s l)) ∧
    PayloadRepresentation (setI (r.put h (leaveStream z l)) zs (leaveState s l))
      r zs (leaveStream z l) (leaveState s l) l bs L D logical := by
  obtain ⟨origin, buffers, bits, tables, dictionary⟩ := before
  obtain ⟨current, packet⟩ := origin.toDefaultStateJ.leave_restore E buffers bits
  have nextOrigin := origin.of_fields current rfl rfl rfl
  have retained : InflateDictionary (setI (r.put h (leaveStream z l)) zs (leaveState s l))
      (leaveState s l) (logical.drop (logical.length - 2 ^ (leaveState s l).wbits.toNat)) := by
    rcases dictionary with ⟨zero, empty⟩ | ⟨ref, off, a, window, get, bound, values⟩
    · exact Or.inl ⟨zero, empty⟩
    · refine Or.inr ⟨ref, off, a, window, ?_, bound, values⟩
      rw [byte_view_get_setI, byte_view_get_stream_put]
      exact get
  exact ⟨RESTORE_pending_run E, nextOrigin, packet, bits,
    tables.leave_restore origin.good.live.hs l, retained⟩

#print axioms fixed_installed_tables
#print axioms zero_window_dictionary
#print axioms dictionary_zero_window_empty
#print axioms protocol_zero_window_history
#print axioms dictionary_block_header
#print axioms typedo_fixed_representation
#print axioms fixed_kind_future
#print axioms InstalledTables.decode_update
#print axioms dictionary_decode_update
#print axioms code_point_representation
#print axioms payload_token_from_symbols
#print axioms InstalledTables.leave_restore
#print axioms PayloadRepresentation.len_start
#print axioms PayloadRepresentation.restore
end Zlib.Inflate.Proofs.FunctionalEpoch
