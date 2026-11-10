import ZlibF.Proof.«inflate.c.control-rank»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The actual dictionary-id mode leaves immediately when its word is incomplete. -/
theorem inflate_DICTID_wait {c : Ctx} {h : Heap} {l current : IL} {exit : Ex}
    (pull : runX (NEEDBITS 32) l h = .ok ((.error exit, current), h)) :
    runX (inflate_DICTID c) l h = .ok ((.error exit, current), h) := by
  unfold inflate_DICTID
  rw [runX_bind, pull]

/-- After the actual word read, DICTID writes the swapped checksum,
clears the local bit buffer and enters the real DICT continuation. -/
theorem inflate_DICTID_parsed_cut {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (E : Env c h r zs z s) (l current : IL)
    (pull : runX (NEEDBITS 32) l h = .ok ((.ok (), current), h)) :
    runX (inflate_DICTID c) l h = runX (inflate_DICT c) { current with hold := 0, bits := 0 }
      (setI (r.put h { z with adler := ZSWAP32 current.hold }) zs
        { s with check := ZSWAP32 current.hold, mode := DICT }) := by
  let value := ZSWAP32 current.hold
  unfold inflate_DICTID
  rw [runX_bind, pull]
  simp only []
  rw [runX_bind, runX_get]
  simp only []
  rw [runX_bind, runX_wrS E]
  simp only []
  have E1 : Env c (setI h zs { s with check := value }) r zs z { s with check := value } :=
    ⟨E.strm, E.st, by simpa only [ZStreamRef.get_setI] using E.hz, by simp⟩
  have write : wrZ c.strm (fun stream => { stream with adler := value }) (setI h zs { s with check := value }) =
      .ok ((), setI (r.put h { z with adler := value }) zs { s with check := value }) := by
    simp only [E.strm, wrZ_eq, E1.hz, ZStreamRef.put_setI]
  rw [runX_bind, runX_lift_ok write]
  simp only []
  rw [runX_bind, runX_INITBITS]
  simp only []
  have E2 : Env c (setI (r.put h { z with adler := value }) zs { s with check := value }) r zs
      { z with adler := value } { s with check := value } :=
    ⟨E.strm, E.st, by rw [ZStreamRef.get_setI]; exact ZStreamRef.get_put_same E.hz _, by simp⟩
  rw [runX_bind, runX_setMode E2, setI_setI]

/-- The complete actual dictionary-id chain preserves the common packet
and either exits or decreases the same bounded main-loop rank. -/
theorem inflate_DICTID_rank {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (good : Good h r zs z s) (pending : DataPendingInvariant s)
    (buffers : DispatchBuffers h r l bs) (globals : LibraryGlobals h)
    (mode : s.mode = DICTID) (incoming : l.bits.toNat ≤ 39) :
    ∃ outcome regs after stream state used, used ≤ bs.length ∧
      runX (inflate_DICTID c) l h = .ok ((outcome, regs), after) ∧
      Good after r zs stream state ∧ DataTableInvariant after state ∧ DataPendingInvariant state ∧
      DispatchBuffers after r regs (bs.drop used) ∧ ByteViewSizes h after ∧
      regs.next = inputAdvance l.next used ∧ regs.have_.toNat + used = l.have_.toNat ∧
      regs.put = l.put ∧ regs.left = l.left ∧ regs.bits.toNat ≤ 39 ∧ after.static = h.static ∧
      (outcome = .error (Ex.ret Z_NEED_DICT) ∨ outcome = .error Ex.leave ∨
        (outcome = .ok () ∧ dispatchRank regs state.mode < dispatchRank l s.mode)) := by
  obtain ⟨outcome, current, used, pull, usedBound, bitInv, _, _, shape,
    bitBound, _, _, _, kinds, cursor⟩ := NEEDBITS_run_cursor buffers.bits 32 (by decide)
  change current.bits.toNat ≤ max l.bits.toNat 39 at bitBound
  have count : current.have_.toNat + used = l.have_.toNat := by
    rw [bitInv.have_eq, buffers.bits.have_eq, List.length_drop]
    omega
  have put : current.put = l.put := by rw [shape]
  have left : current.left = l.left := by rw [shape]
  have packet : DispatchBuffers h r current (bs.drop used) :=
    buffers.consume good good rfl (fun _ => rfl) (fun _ => rfl) (by rw [shape]; rfl) cursor usedBound bitInv
  rcases kinds with normal | wait
  · rw [normal] at pull
    let value := ZSWAP32 current.hold
    let ready := { s with check := value, mode := DICT }
    let stream0 := { z with adler := value }
    let heap0 := setI (r.put h stream0) zs ready
    let first := { current with hold := 0, bits := 0 }
    have good0 : Good heap0 r zs stream0 ready :=
      good.setZI rfl good.live.zalloc good.live.zfree rfl (by change HEAD ≤ DICT ∧ DICT ≤ SYNC; decide)
        (good.inv.of_fields rfl rfl rfl rfl rfl rfl rfl rfl rfl good.inv.bits rfl rfl rfl)
    have E0 : Env c heap0 r zs stream0 ready := ⟨E.strm, E.st, good0.live.hz, good0.live.hs⟩
    have pending0 : DataPendingInvariant ready := by
      apply dataPendingInvariant_idle (s := ready) (by exact pending.sane)
      change DICT ≠ LENEXT ∧ DICT ≠ DIST ∧ DICT ≠ DISTEXT ∧ DICT ≠ MATCH
      decide
    have inv0 : BitInv heap0 first (bs.drop used) := by
      have inv := (INITBITS_inv bitInv).1
      apply inv.byte_views
      intro ref
      rw [byte_view_get_setI, byte_view_get_stream_put]
    have packet0 : DispatchBuffers heap0 r first (bs.drop used) :=
      buffers.consume good good0 rfl (fun ref => by rw [byte_view_get_setI, byte_view_get_stream_put])
        (fun ref => by rw [byte_view_ro_setI, byte_view_ro_stream_put])
        (by dsimp only [first]; rw [shape]; rfl) cursor usedBound inv0
    have sizes0 : ByteViewSizes h heap0 := by
      intro ref
      rw [byte_view_get_setI, byte_view_get_stream_put]
    have static0 : heap0.static = h.static := by simp only [heap0, setI, ZStreamRef.put_static]
    have globals0 : LibraryGlobals heap0 := by change heap0.static = _; rw [static0]; exact globals
    obtain ⟨exit, regs, after, stream, state, used2, bound2, run, currentGood, tables, nextPending,
      nextPacket, sizes, next2, count2, put2, left2, bits, static, exits⟩ :=
      inflate_DICT_rank E0 good0 pending0 packet0 globals0 rfl (by change 0 ≤ 39; decide)
    have before : dispatchRank first ready.mode < dispatchRank l s.mode := by
      apply dispatchRank_advance (l := l) (regs := first) (used := used) (made := 0) count
      · change current.left.toNat + 0 = l.left.toNat
        rw [left]
        rfl
      · change 0 ≤ _
        omega
      · right
        change dispatchCredit DICT < dispatchCredit s.mode
        rw [mode]
        decide
    have totalBound : used + used2 ≤ bs.length := by rw [List.length_drop] at bound2; omega
    refine ⟨exit, regs, after, stream, state, used + used2, totalBound,
      (inflate_DICTID_parsed_cut E l current pull).trans run, currentGood, tables, nextPending,
      ?_, sizes0.trans sizes, ?_, ?_, ?_, ?_, bits, static.trans static0, ?_⟩
    · simpa only [List.drop_drop] using nextPacket
    · rw [next2]
      change inputAdvance current.next used2 = _
      rw [cursor, inputAdvance_add]
    · change regs.have_.toNat + used2 = current.have_.toNat at count2
      omega
    · exact put2.trans put
    · exact left2.trans left
    · rcases exits with needed | wait | ⟨normal, decreases⟩
      · exact Or.inl needed
      · exact Or.inr (Or.inl wait)
      · exact Or.inr (Or.inr ⟨normal, Nat.lt_trans decreases before⟩)
  · have run := inflate_DICTID_wait (c := c) (by rwa [wait] at pull)
    exact ⟨.error Ex.leave, current, h, z, s, used, usedBound, run, good,
      dataTableInvariant_inactive (by rw [mode]; unfold DataTableMode; decide), pending,
      packet, ByteViewSizes.refl h, cursor, count, put, left, by omega, rfl, Or.inr (Or.inl rfl)⟩

end Zlib.Inflate.Proofs
