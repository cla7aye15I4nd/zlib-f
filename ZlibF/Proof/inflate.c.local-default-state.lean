import ZlibF.Proof.«inflate.c.local-good»
import ZlibF.Proof.«inflate.c.default-foundation»

/-! An internal decoder relation with local allocation uniqueness.
All former decoding, default configuration and table-content clauses remain.
This is distinct from the unchanged public invariant and utility goals. -/
namespace Zlib.Inflate.Local
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- The real stream, state and any window were allocated after this caller boundary. -/
structure LocalRoots (cutoff : Nat) (r : ZStreamRef) (zs : Nat) (s : InflateState) : Prop where
  stream : ∀ b, StreamRoot r b → cutoff ≤ b
  state : cutoff ≤ zs
  window : ∀ w, s.window = .ref (.blk w) 0 → cutoff ≤ w

/-- Decoder, actual table and construction clauses with local representation. -/
structure LocalDecodeJ (h : Heap) (cutoff : Nat) (r : ZStreamRef) (zs : Nat) (z : ZStream) (s : InflateState) : Prop where
  good : LocalGood h cutoff r zs z s
  tables : DataTableInvariant h s
  pending : DataPendingInvariant s
  lengths : CodeLengthInvariant zs s
  headerLengths : LengthHeaderInvariant s
  held : s.hold.toNat < 2 ^ s.bits.toNat
  window : s.wbits = 15
  wrapper : s.wrap = 0 ∨ s.wrap = 1 ∨ s.wrap = 5
  header : s.head = none
  modes : s.mode = HEAD ∨ DICTID ≤ s.mode ∧ s.mode ≤ SYNC
  trailer : s.mode = CHECK ∨ s.mode = LENGTH → s.wrap = 0 ∨ s.flags = 0
  globals : LibraryGlobals h
  platform : ZlibF.PlatformMemory.ByteObjectsFit h

/-- Default-history fields that reset and entry into CHECK need. An unread
or rejected header may retain the initial flags. Active block decoding
requires raw recovery or a completed zlib header. These fields supplement
the checked decoder relation; full history closure is still open. -/
structure LocalStateJ (h : Heap) (cutoff : Nat) (r : ZStreamRef) (zs : Nat) (z : ZStream) (s : InflateState)
    : Prop extends LocalDecodeJ h cutoff r zs z s where
  requestedBits : s.reqbits = 15
  requestedWrap : s.reqwrap = 1 ∨ s.reqwrap = 5
  phase : s.mode = HEAD ∨ s.mode = BAD ∨ s.mode = MEM ∨ s.mode = SYNC ∨ s.wrap = 0 ∨ s.flags = 0
  roots : LocalRoots cutoff r zs s


end Zlib.Inflate.Local
