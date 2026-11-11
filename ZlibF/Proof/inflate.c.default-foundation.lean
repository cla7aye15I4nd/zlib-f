import ZlibF.Proof.«inflate.c.default-entry»
import ZlibF.Proof.«inflate.c.main.table2»
import ZlibF.Spec.InflatePendingInvariant
import ZlibF.Spec.InflateCodeLengthInvariant

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The initialized length-header prefix needed when LENLENS resumes.
Arbitrary unused lens cells impose no constraint. -/
def LengthHeaderInvariant (s : InflateState) : Prop :=
  s.mode = LENLENS → s.ncode.toNat ≤ 19 ∧ s.«have».toNat ≤ s.ncode.toNat ∧
    s.nlen.toNat ≤ 286 ∧ s.ndist.toNat ≤ 30 ∧ Good3 s.lens s.«have».toNat

/-- Bit 1 of the wrapper: a gzip header is accepted. -/
def GzipAllowed (w : Int32) : Prop :=
  w = 2 ∨ w = 3 ∨ w = 6 ∨ w = 7

/-- The header is behind the decoder: a raw stream, a zlib header (flags 0),
or a gzip header whose 16-bit method-and-flags word was read (nonzero). -/
def HeaderDone (s : InflateState) : Prop :=
  s.wrap = 0 ∨ s.flags = 0 ∨ (GzipAllowed s.wrap ∧ s.flags ≠ -1 ∧ s.flags ≠ 0)

/-- `FLAGS` after the gzip magic bytes: the flags word is not read yet, the
width is set. -/
def GzipFlagsPending (s : InflateState) : Prop :=
  s.mode = FLAGS ∧ GzipAllowed s.wrap ∧ s.wbits ≠ 0

/-- The gzip header modes `FLAGS` .. `HCRC`: gzip is allowed, and past `FLAGS`
the method-and-flags word is read. -/
def GzipHeaderMode (s : InflateState) : Prop :=
  FLAGS ≤ s.mode ∧ s.mode ≤ HCRC ∧ GzipAllowed s.wrap ∧ (FLAGS < s.mode → s.flags ≠ -1 ∧ s.flags ≠ 0)

/-- The common state relation for the default-wrapper proof. It combines
representation, actual table contents, pending scalar bounds and the two
construction phases. The configuration is explicit: any window width from
8 to 15 bits (equal to the requested width), no gzip header, and raw
recovery or zlib validation settings. A requested width of 0 and gzip
wrapping are not yet covered. Full dispatch/history closure remains open. -/
structure DefaultDecodeJ (h : Heap) (r : ZStreamRef) (zs : Nat) (z : ZStream) (s : InflateState) : Prop where
  good : Good h r zs z s
  tables : DataTableInvariant h s
  pending : DataPendingInvariant s
  lengths : CodeLengthInvariant zs s
  headerLengths : LengthHeaderInvariant s
  held : s.hold.toNat < 2 ^ s.bits.toNat
  window : (8 ≤ s.wbits.toNat ∧ s.wbits.toNat ≤ 15) ∨
    (s.wbits = 0 ∧ s.window = .null ∧ s.flags = -1 ∧ s.wrap ≠ 0)
  wrapper : s.wrap = 0 ∨ s.wrap = 1 ∨ s.wrap = 2 ∨ s.wrap = 3 ∨ s.wrap = 5 ∨ s.wrap = 6 ∨ s.wrap = 7
  header : s.head ≠ none ∨ (s.flags ≠ -1 ∧ s.flags ≠ 0) → s.wrap = 2 ∨ s.wrap = 3 ∨ s.wrap = 6 ∨ s.wrap = 7
  modes : s.mode = HEAD ∨ DICTID ≤ s.mode ∧ s.mode ≤ SYNC ∨ GzipHeaderMode s
  trailer : s.mode = CHECK ∨ s.mode = LENGTH → HeaderDone s
  globals : LibraryGlobals h
  platform : ZlibF.PlatformMemory.ByteObjectsFit h

/-- The requested width is the current width, or 0 (the header chose the
current width); a raw request has a nonzero width. -/
def RequestedBitsOK (reqbits wbits : UInt32) (reqwrap : Int32) : Prop :=
  (reqbits = wbits ∨ reqbits = 0) ∧ (reqwrap = 0 → reqbits ≠ 0)

/-- The requested wrapper is a valid wrapper value; unless the stream runs
raw, it allows gzip exactly when the current wrapper does. -/
def RequestedWrapOK (reqwrap wrap : Int32) : Prop :=
  (reqwrap = 0 ∨ reqwrap = 1 ∨ reqwrap = 2 ∨ reqwrap = 3 ∨ reqwrap = 5 ∨ reqwrap = 6 ∨ reqwrap = 7) ∧
  (wrap = 0 ∨ ((wrap = 2 ∨ wrap = 3 ∨ wrap = 6 ∨ wrap = 7) ↔
    (reqwrap = 2 ∨ reqwrap = 3 ∨ reqwrap = 6 ∨ reqwrap = 7)))

theorem RequestedBitsOK.congr {reqbits wbits reqbits' wbits' : UInt32} {reqwrap reqwrap' : Int32}
    (ok : RequestedBitsOK reqbits wbits reqwrap) (bits : reqbits' = reqbits) (width : wbits' = wbits)
    (wrap : reqwrap' = reqwrap) : RequestedBitsOK reqbits' wbits' reqwrap' := by
  subst bits width wrap
  exact ok

theorem RequestedWrapOK.congr {reqwrap wrap reqwrap' wrap' : Int32}
    (ok : RequestedWrapOK reqwrap wrap) (requested : reqwrap' = reqwrap) (current : wrap' = wrap) :
    RequestedWrapOK reqwrap' wrap' := by
  subst requested current
  exact ok

/-- The default request: the requested width is the current width, and the
requested wrapper is raw, zlib, or zlib with checking. -/
theorem RequestedBitsOK.of_default {reqbits wbits : UInt32} {reqwrap : Int32}
    (bits : reqbits = wbits) (nonzero : wbits ≠ 0) : RequestedBitsOK reqbits wbits reqwrap :=
  ⟨Or.inl bits, fun _ => by rw [bits]; exact nonzero⟩

theorem RequestedWrapOK.of_default {reqwrap wrap : Int32}
    (requested : reqwrap = 0 ∨ reqwrap = 1 ∨ reqwrap = 5) (current : wrap = 0 ∨ wrap = 1 ∨ wrap = 5) :
    RequestedWrapOK reqwrap wrap := by
  refine ⟨?_, ?_⟩
  · rcases requested with e | e | e <;> rw [e] <;> decide
  · rcases current with c | c | c
    · exact Or.inl c
    · right
      rw [c]
      rcases requested with e | e | e <;> rw [e] <;> decide
    · right
      rw [c]
      rcases requested with e | e | e <;> rw [e] <;> decide

/-- The default request: the requested width is the current one, and the
requested wrapper is raw, zlib, or zlib with checking. A reset keeps the
default configuration only under this request. -/
def DefaultRequest (s : InflateState) : Prop :=
  s.reqbits = s.wbits ∧ (s.reqwrap = 0 ∨ s.reqwrap = 1 ∨ s.reqwrap = 5)

/-- A default wrapper value is a wrapper value. -/
theorem wrapper_of_default {w : Int32} (value : w = 0 ∨ w = 1 ∨ w = 5) :
    w = 0 ∨ w = 1 ∨ w = 2 ∨ w = 3 ∨ w = 5 ∨ w = 6 ∨ w = 7 := by
  rcases value with e | e | e
  · exact Or.inl e
  · exact Or.inr (Or.inl e)
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e))))

/-- Toggling bit 2 of a wrapper value gives a wrapper value, and 0 only from 0. -/
theorem wrapper_validate {w check : Int32}
    (value : w = 0 ∨ w = 1 ∨ w = 2 ∨ w = 3 ∨ w = 5 ∨ w = 6 ∨ w = 7) :
    let v := if check != 0 && w != 0 then w ||| 4 else w &&& ~~~4
    (v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 ∨ v = 5 ∨ v = 6 ∨ v = 7) ∧ (v = 0 → w = 0) ∧
      ((w = 2 ∨ w = 3 ∨ w = 6 ∨ w = 7) → (v = 2 ∨ v = 3 ∨ v = 6 ∨ v = 7)) := by
  rcases value with e | e | e | e | e | e | e <;> subst e <;> cases (check != 0) <;> decide

/-- WORKER STUB: the gzip HEAD cases are not handled yet at this site. -/
theorem zlibStub {w : Int32} (_value : w = 1 ∨ w = 2 ∨ w = 3 ∨ w = 5 ∨ w = 6 ∨ w = 7) : w = 1 ∨ w = 5 := by
  sorry

/-- A zlib wrapper has no gzip header record. -/
theorem DefaultDecodeJ.head_none {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {s : InflateState} (current : DefaultDecodeJ h r zs z s) (wrap : s.wrap = 1 ∨ s.wrap = 5) :
    s.head = none :=
  Classical.byContradiction fun attached => by
    rcases current.header (Or.inl attached) with e | e | e | e <;> rcases wrap with w | w <;>
      rw [w] at e <;> exact absurd e (by decide)

/-- Default-history fields that reset and entry into CHECK need. An unread
or rejected header may retain the initial flags. Active block decoding
requires raw recovery or a completed zlib header. These fields supplement
the checked decoder relation; full history closure is still open. -/
structure DefaultStateJ (h : Heap) (r : ZStreamRef) (zs : Nat) (z : ZStream) (s : InflateState)
    : Prop extends DefaultDecodeJ h r zs z s where
  requestedBits : RequestedBitsOK s.reqbits s.wbits s.reqwrap
  requestedWrap : RequestedWrapOK s.reqwrap s.wrap
  phase : s.mode = HEAD ∨ s.mode = BAD ∨ s.mode = MEM ∨ s.mode = SYNC ∨ HeaderDone s ∨
    GzipFlagsPending s

/-- A completed header carries over to a state with the same flags whose
wrapper stays raw and keeps gzip allowed. -/
theorem HeaderDone.transfer {s t : InflateState} (read : HeaderDone s)
    (flags : t.flags = s.flags) (raw : s.wrap = 0 → t.wrap = 0)
    (gzip : GzipAllowed s.wrap → GzipAllowed t.wrap) : HeaderDone t := by
  rcases read with zero | read | ⟨allowed, notUnread, notZero⟩
  · exact Or.inl (raw zero)
  · exact Or.inr (Or.inl (flags.trans read))
  · exact Or.inr (Or.inr ⟨gzip allowed, flags ▸ notUnread, flags ▸ notZero⟩)

theorem HeaderDone.same {s t : InflateState} (read : HeaderDone s) (flags : t.flags = s.flags)
    (wrap : t.wrap = s.wrap) : HeaderDone t :=
  read.transfer flags (fun zero => wrap.trans zero) (fun allowed => wrap ▸ allowed)

/-- The mode range carries over to a state with the same mode and flags
whose wrapper keeps gzip allowed. -/
theorem defaultModes_transfer {s t : InflateState}
    (modes : s.mode = HEAD ∨ DICTID ≤ s.mode ∧ s.mode ≤ SYNC ∨ GzipHeaderMode s)
    (mode : t.mode = s.mode) (flags : t.flags = s.flags)
    (gzip : GzipAllowed s.wrap → GzipAllowed t.wrap) :
    t.mode = HEAD ∨ DICTID ≤ t.mode ∧ t.mode ≤ SYNC ∨ GzipHeaderMode t := by
  rw [mode]
  rcases modes with head | range | ⟨low, high, allowed, read⟩
  · exact Or.inl head
  · exact Or.inr (Or.inl range)
  · exact Or.inr (Or.inr ⟨mode ▸ low, mode ▸ high, gzip allowed, fun past => flags ▸ read (mode ▸ past)⟩)

/-- The width is at most 15. -/
theorem DefaultDecodeJ.wbits_small {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {s : InflateState} (current : DefaultDecodeJ h r zs z s) : s.wbits.toNat ≤ 15 := by
  rcases current.window with range | ⟨zero, _, _⟩
  · exact range.2
  · rw [zero]
    decide

/-- A nonzero width is a window width. -/
theorem DefaultDecodeJ.range_of_nonzero {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {s : InflateState} (current : DefaultDecodeJ h r zs z s) (nonzero : s.wbits ≠ 0) :
    8 ≤ s.wbits.toNat ∧ s.wbits.toNat ≤ 15 := by
  rcases current.window with range | ⟨zero, _, _⟩
  · exact range
  · exact absurd zero nonzero

/-- A local byte array is not the window: the width is a window width, or
there is no window. -/
theorem DefaultDecodeJ.local_width {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {s : InflateState} (current : DefaultDecodeJ h r zs z s) : 8 ≤ s.wbits.toNat ∨ s.window = .null := by
  rcases current.window with range | ⟨_, null, _, _⟩
  · exact Or.inl range.1
  · exact Or.inr null

/-- A decoder with a window has a window width. -/
theorem DefaultDecodeJ.range_of_window {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {s : InflateState} (current : DefaultDecodeJ h r zs z s) (windowed : s.window ≠ .null) :
    8 ≤ s.wbits.toNat ∧ s.wbits.toNat ≤ 15 := by
  rcases current.window with range | ⟨_, null, _, _⟩
  · exact range
  · exact absurd null windowed

/-- Once a header was read, or in a raw stream, the width was set. -/
theorem DefaultDecodeJ.range_of_read {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {s : InflateState} (current : DefaultDecodeJ h r zs z s) (read : HeaderDone s) :
    8 ≤ s.wbits.toNat ∧ s.wbits.toNat ≤ 15 := by
  rcases current.window with range | ⟨_, _, unread, wrapped⟩
  · exact range
  · rcases read with raw | zero | ⟨_, read, _⟩
    · exact absurd raw wrapped
    · rw [unread] at zero
      exact absurd zero (by decide)
    · exact absurd unread read

/-- In `FLAGS` after the magic bytes the width is a window width. -/
theorem DefaultDecodeJ.range_of_pending {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {s : InflateState} (current : DefaultDecodeJ h r zs z s) (pending : GzipFlagsPending s) :
    8 ≤ s.wbits.toNat ∧ s.wbits.toNat ≤ 15 :=
  current.range_of_nonzero pending.2.2

theorem DefaultDecodeJ.requestedBits_of {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {s : InflateState} (_current : DefaultDecodeJ h r zs z s) (bits : s.reqbits = s.wbits)
    (nonzero : s.wbits ≠ 0) : RequestedBitsOK s.reqbits s.wbits s.reqwrap :=
  RequestedBitsOK.of_default bits nonzero

theorem DefaultDecodeJ.requestedWrap_of {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {s : InflateState} (current : DefaultDecodeJ h r zs z s)
    (wrap : s.reqwrap = 0 ∨ s.reqwrap = 1 ∨ s.reqwrap = 5)
    (current_wrap : s.wrap = 0 ∨ s.wrap = 1 ∨ s.wrap = 5) : RequestedWrapOK s.reqwrap s.wrap :=
  RequestedWrapOK.of_default wrap current_wrap

/-- Actual successful default initialization establishes every clause of J
on its returned heap. No representation or callee contract is assumed.
A full history theorem still requires preservation by every admitted call. -/
theorem inflate_default_J_initial
    (h : Heap) (r : ZStreamRef) (version : BPtr)
    (domain : InitDomain h r version) (platform : ZlibF.PlatformMemory.ByteObjectsFit h)
    (allocation : h.allocOk h.nalloc = true) :
    ∃ after z s, C.run (inflateInit_ (some r) version 112) h = .ok (Z_OK, after) ∧
      InflateInitial h after r .zlib 15 ∧ DefaultDecodeJ after r h.nextBlk z s ∧
      StreamReachable .inflate after r := by
  obtain ⟨after, z, s, run, initial, good, head, wrap, bits, header, tables, fit, reachable⟩ :=
    inflate_default_init_boundary h r version domain platform allocation
  have sane := inflate_default_success_sane domain allocation run good
  have headPending : DataPendingInvariant s := by
    refine ⟨sane, ?_, ?_, ?_, ?_⟩
    all_goals intro selected; rw [head] at selected; contradiction
  have initialCopy := initial
  obtain ⟨stream, state, stateGood, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, frame, _⟩ := initialCopy
  have globals : LibraryGlobals after := by
    change after.static = _
    rw [← frame.1]
    exact domain.2.2.1
  refine ⟨after, z, s, run, initial, ⟨good, tables, headPending,
    ?_, ?_, inflate_initial_hold initial good, ?_, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl wrap)))),
    fun attached => absurd header attached,
    Or.inl head, ?_, globals, fit⟩, reachable⟩
  · intro active
    rw [head] at active
    contradiction
  · intro active
    rw [head] at active
    contradiction
  · exact Or.inl ⟨by omega, by omega⟩
  · rintro (active | active) <;> rw [head] at active <;> contradiction

/-- The default relation has a concrete initialized caller. This rules out
an empty invariant independently of its still-open preservation proof. -/
theorem inflate_default_J_witness :
    ∃ after z s, C.run (inflateInit_ (some (.tab 0)) (.ref (.blk 1) 0) 112) witnessHeap = .ok (Z_OK, after) ∧
      DefaultDecodeJ after (.tab 0) witnessHeap.nextBlk z s ∧ StreamReachable .inflate after (.tab 0) := by
  obtain ⟨after, z, s, run, _, invariant, reachable⟩ :=
    inflate_default_J_initial witnessHeap (.tab 0) (.ref (.blk 1) 0)
      ZlibF.Spec.Public.Proofs.InflateInit.public_witness_domain inflate_default_witness_platform rfl
  exact ⟨after, z, s, run, invariant, reachable⟩


/-- Successful actual default initialization establishes both the decoder
relation and its reset/header history fields. -/
theorem inflate_default_state_initial
    (h : Heap) (r : ZStreamRef) (version : BPtr)
    (domain : InitDomain h r version) (platform : ZlibF.PlatformMemory.ByteObjectsFit h)
    (allocation : h.allocOk h.nalloc = true) :
    ∃ after z s, C.run (inflateInit_ (some r) version 112) h = .ok (Z_OK, after) ∧
      InflateInitial h after r .zlib 15 ∧ DefaultStateJ after r h.nextBlk z s ∧
      StreamReachable .inflate after r := by
  obtain ⟨after, z, s, run, initial, invariant, reachable⟩ :=
    inflate_default_J_initial h r version domain platform allocation
  have initialCopy := initial
  obtain ⟨initialZ, initialS, good, _, _, head, _, activeBits, requested, wrap, requestedWrap, _⟩ := initialCopy
  have sameState : initialS = s := Option.some.inj (good.live.hs.symm.trans invariant.good.live.hs)
  subst initialS
  have requestedBits : s.reqbits = s.wbits := UInt32.toNat_inj.mp (requested.trans activeBits.symm)
  have wrapper : s.reqwrap = 5 := requestedWrap.trans wrap
  exact ⟨after, z, s, run, initial, ⟨invariant, invariant.requestedBits_of requestedBits
      (fun zero => by rw [zero] at activeBits; exact absurd activeBits (by decide)),
    invariant.requestedWrap_of (Or.inr (Or.inr wrapper)) (Or.inr (Or.inr wrap)), Or.inl head⟩, reachable⟩

/-- The history relation has an actual initialized caller. -/
theorem inflate_default_state_witness :
    ∃ after z s, C.run (inflateInit_ (some (.tab 0)) (.ref (.blk 1) 0) 112) witnessHeap = .ok (Z_OK, after) ∧
      DefaultStateJ after (.tab 0) witnessHeap.nextBlk z s ∧ StreamReachable .inflate after (.tab 0) := by
  obtain ⟨after, z, s, run, _, invariant, reachable⟩ :=
    inflate_default_state_initial witnessHeap (.tab 0) (.ref (.blk 1) 0)
      ZlibF.Spec.Public.Proofs.InflateInit.public_witness_domain inflate_default_witness_platform rfl
  exact ⟨after, z, s, run, invariant, reachable⟩


#print axioms inflate_default_state_initial
#print axioms inflate_default_state_witness
end Zlib.Inflate.Proofs
