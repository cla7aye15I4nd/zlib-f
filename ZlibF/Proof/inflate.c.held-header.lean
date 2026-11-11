import ZlibF.Proof.«inflate.c.gzip-header-dispatch»
import ZlibF.Proof.«inflate.c.head-gzip»
import ZlibF.Proof.«inflate.c.head-default-state»
import ZlibF.Proof.«inflate.c.dictionary-default-state»
import ZlibF.Proof.«inflate.c.check-dispatch»

/-!
# inflate.c: header dispatches keep at most 32 held bits

Per-group exit facts for the held-bit bound of the inflate owner (`HeldBound`):
from at most 32 held bits, one dispatch from `HEAD`, `DICTID` or `DICT`
ends with at most 32 held bits, whatever mode it reaches. `NEEDBITS(16)` in
`HEAD` reaches at most 23 bits from a smaller buffer, the zlib checks only
drop bits, the gzip magic empties the buffer; `NEEDBITS(32)` in `DICTID`
either leaves with fewer than 32 or empties the buffer; `DICT` keeps the
buffer, or with a dictionary enters `TYPE`, which ends with at most
`max bits 10`. The gzip header modes are `inflate_dispatch_gzip_header_bits`.
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- `case HEAD` from at most 32 held bits ends with at most 32. -/
theorem inflate_dispatch_HEAD_held {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l regs : IL} {bs : List UInt8} {outcome : Except Ex Unit}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (hbuf : LocalHbuf c h) (record : HeaderMemory h r s.head true)
    (mode : s.mode = HEAD) (held : l.bits.toNat ≤ 32)
    (run : runX (inflate_dispatch c) l h = .ok ((outcome, regs), after)) :
    regs.bits.toNat ≤ 32 := by
  rw [inflate_dispatch_HEAD E l mode] at run
  by_cases raw : s.wrap = 0
  · rw [inflate_HEAD_raw_run E l raw] at run
    cases run
    exact held
  obtain ⟨result, current, used, pull, usedBound, bitInv, _, _, shape,
    bitBound, _, full, leaveFacts, kinds, cursor⟩ := NEEDBITS_run_cursor buffers.bits 16 (by decide)
  change current.bits.toNat ≤ max l.bits.toNat 23 at bitBound
  have small : current.bits.toNat ≤ 32 := by
    rw [Nat.max_def] at bitBound
    split at bitBound <;> omega
  have wrapNe : (s.wrap == 0) = false := by simpa using raw
  rw [inflate_HEAD_split, runX_bind, runX_rdS E] at run
  simp only [wrapNe, Bool.false_eq_true, ↓reduceIte] at run
  rw [runX_bind, pull] at run
  rcases kinds with normal | wait
  · subst normal
    simp only [] at run
    have enough := full rfl
    by_cases magic : ((s.wrap &&& 2) != 0 && current.hold == 0x8b1f) = true
    · obtain ⟨b, a, hbufAt, bytes, size, writable⟩ := hbuf
      have statics : Zlib.Crc32.Proofs.StaticsOK h := by
        unfold Zlib.Crc32.Proofs.StaticsOK
        rw [invariant.globals]
        exact ⟨rfl, rfl⟩
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at magic
      rw [headAfterBits_gzip E current hbufAt bytes size writable statics magic.1 magic.2] at run
      cases run
      show (0 : UInt32).toNat ≤ 32
      decide
    · have notMagic : ((s.wrap &&& 2) != 0 && current.hold == 0x8b1f) = false := by simpa using magic
      have exists_record : ∀ i, s.head = some (.tab i) → (h.gzheaders i).isSome := by
        intro i attached
        rcases record with none | ⟨j, g, pointer, get, _⟩
        · rw [none] at attached
          cases attached
        · rw [attached] at pointer
          cases pointer
          simp [get]
      rw [headAfterBits_zlib E current notMagic exists_record] at run
      have packet : DispatchBuffers h r current (bs.drop used) :=
        buffers.consume invariant.good invariant.good rfl (fun _ => rfl) (fun _ => rfl)
          (by rw [shape]; rfl) cursor usedBound bitInv
      have doneEnv := E.headDone s.head
      have doneGood : Good (headDoneHeap h s.head) r zs z s := by
        unfold headDoneHeap
        split
        · exact invariant.good
        · split
          · next g get =>
            have good' := invariant.good.headerPut get { g with done := -1 }
            simp only [GzHeaderRef.put, get] at good'
            exact good'
          · exact invariant.good
      have views : ∀ ref : BRef, Space.get (headDoneHeap h s.head) ref = Space.get h ref := by
        intro ref
        unfold headDoneHeap
        split
        · rfl
        · split
          · cases ref <;> rfl
          · rfl
      have ro : ∀ ref : BRef, Space.ro (headDoneHeap h s.head) ref = Space.ro h ref := by
        intro ref
        unfold headDoneHeap
        split
        · rfl
        · split
          · cases ref <;> rfl
          · rfl
      have donePacket : DispatchBuffers (headDoneHeap h s.head) r current (bs.drop used) :=
        packet.byte_views invariant.good doneGood rfl views ro
      obtain ⟨regs1, _, _, _, run1, _, _, _, _, _, _, regBits, _⟩ :=
        headDefaultCheck_boundary_frame doneEnv doneGood invariant.pending donePacket enough
          invariant.toDefaultDecodeJ.headWindow
      rw [run1] at run
      cases run
      omega
  · subst wait
    simp only [] at run
    cases run
    exact small

/-- `case DICT` from at most 32 held bits ends with at most 32. -/
theorem inflate_DICT_held {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l regs : IL} {bs : List UInt8} {outcome : Except Ex Unit}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = DICT) (held : l.bits.toNat ≤ 32)
    (run : runX (inflate_DICT c) l h = .ok ((outcome, regs), after)) :
    regs.bits.toNat ≤ 32 := by
  by_cases missing : s.havedict = 0
  · rw [inflate_DICT_wait_run E l missing] at run
    cases run
    exact held
  · rw [inflate_DICT_ready_cut E l missing] at run
    have current := invariant.prepare_dictionary (Or.inr mode) 1 TYPE (Or.inr rfl)
    have env : Env c (setI (r.put h { z with adler := 1 }) zs { s with check := 1, mode := TYPE }) r zs
        { z with adler := 1 } { s with check := 1, mode := TYPE } :=
      ⟨E.strm, E.st, current.good.live.hz, current.good.live.hs⟩
    have views : ∀ ref : BRef, (Space.get (setI (r.put h { z with adler := 1 }) zs
        { s with check := 1, mode := TYPE }) ref : Option (Array UInt8)) = Space.get h ref := by
      intro ref
      rw [byte_view_get_setI, byte_view_get_stream_put]
    have ro : ∀ ref : BRef, Space.ro (setI (r.put h { z with adler := 1 }) zs
        { s with check := 1, mode := TYPE }) ref = Space.ro h ref := by
      intro ref
      rw [byte_view_ro_setI, byte_view_ro_stream_put]
    have packet := buffers.byte_views invariant.good current.good rfl views ro
    obtain ⟨_, regs1, _, _, _, _, _, _, run1, _, _, _, _, _, _, _, _, _, _, bits1, _⟩ :=
      inflate_TYPE_boundary env current.good current.pending packet current.globals rfl
    rw [run1] at run
    cases run
    rw [Nat.max_def] at bits1
    split at bits1 <;> omega

/-- `case DICTID` and `case DICT` from at most 32 held bits end with at most 32. -/
theorem inflate_dispatch_dictionary_held {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l regs : IL} {bs : List UInt8} {outcome : Except Ex Unit}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = DICTID ∨ s.mode = DICT)
    (held : l.bits.toNat ≤ 32)
    (run : runX (inflate_dispatch c) l h = .ok ((outcome, regs), after)) :
    regs.bits.toNat ≤ 32 := by
  rcases mode with dictid | dict
  · rw [inflate_dispatch_DICTID E l dictid] at run
    obtain ⟨result, current, used, pull, usedBound, bitInv, _, _, shape,
      _, _, _, leaveFacts, kinds, cursor⟩ := NEEDBITS_run_cursor buffers.bits 32 (by decide)
    rcases kinds with normal | wait
    · rw [normal] at pull
      rw [inflate_DICTID_parsed_cut E l current pull] at run
      have ready := invariant.prepare_dictionary (Or.inl dictid) (ZSWAP32 current.hold) DICT (Or.inl rfl)
      have env : Env c (setI (r.put h { z with adler := ZSWAP32 current.hold }) zs
          { s with check := ZSWAP32 current.hold, mode := DICT }) r zs { z with adler := ZSWAP32 current.hold }
          { s with check := ZSWAP32 current.hold, mode := DICT } :=
        ⟨E.strm, E.st, ready.good.live.hz, ready.good.live.hs⟩
      have packet : DispatchBuffers h r current (bs.drop used) :=
        buffers.consume invariant.good invariant.good rfl (fun _ => rfl) (fun _ => rfl)
          (by rw [shape]; rfl) cursor usedBound bitInv
      have views : ∀ ref : BRef, (Space.get (setI (r.put h { z with adler := ZSWAP32 current.hold }) zs
          { s with check := ZSWAP32 current.hold, mode := DICT }) ref : Option (Array UInt8)) =
          Space.get h ref := by
        intro ref
        rw [byte_view_get_setI, byte_view_get_stream_put]
      have ro : ∀ ref : BRef, Space.ro (setI (r.put h { z with adler := ZSWAP32 current.hold }) zs
          { s with check := ZSWAP32 current.hold, mode := DICT }) ref = Space.ro h ref := by
        intro ref
        rw [byte_view_ro_setI, byte_view_ro_stream_put]
      have packet0 := (packet.byte_views invariant.good ready.good rfl views ro).clear_bits
      exact inflate_DICT_held env ready packet0 rfl (by change 0 ≤ 32; decide) run
    · have pull' := pull
      rw [wait] at pull'
      rw [inflate_DICTID_wait pull'] at run
      cases run
      have below := (leaveFacts wait).2.2
      have n32 : (32 : UInt32).toNat = 32 := rfl
      rw [n32] at below
      omega
  · rw [inflate_dispatch_DICT E l dict] at run
    exact inflate_DICT_held E invariant buffers dict held run

#print axioms inflate_dispatch_HEAD_held
#print axioms inflate_dispatch_dictionary_held

end Zlib.Inflate.Proofs
