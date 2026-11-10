import ZlibF.Proof.«inflate.c.header-exhaustive-progress»
import ZlibF.Proof.«inflate.c.origin-fields-construction-tail»
namespace Zlib.Inflate.Proofs.PayloadPhaseView
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs
set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- Exact constructor metadata and actual table safety transport the
incoming representation and buffer packet to the private payload boundary.
All premises are field/array facts produced by the constructors. -/
theorem constructor_metadata_packet
    {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s state : InflateState}
    {l : IL} {bs : List UInt8}
    (before : DefaultOriginState h r zs z s)
    (buffers : DispatchBuffers h r l bs)
    (frame : state = { s with next := state.next, lencode := state.lencode, distcode := state.distcode, lenbits := state.lenbits, distbits := state.distbits, work := state.work, codes := state.codes, mode := state.mode })
    (workSize : state.work.size = 288) (codeSize : state.codes.size = 1444)
    (pointers : PtrInv zs state) (mode : state.mode = LEN_)
    (tables : DataTablesSafe (setI h zs state) state)
    (dynamic : state.lencode = .ref (.istate_codes zs) 0)
    (format : s.wrap = 0 ∨ s.flags = 0) :
    DefaultOriginState (setI h zs state) r zs z state ∧
      DispatchBuffers (setI h zs state) r {l with ret := 0} bs ∧
      ByteViewSizes h (setI h zs state) := by
  have inv : StInv h zs state := by
    constructor
    · refine ⟨?_, workSize, codeSize⟩
      rw [frame]; exact before.good.inv.wf.1
    · rw [frame]
      exact ⟨before.good.inv.win.wbits, before.good.inv.win.block, before.good.inv.win.nullws,
        before.good.inv.win.ws, before.good.inv.win.hv, before.good.inv.win.wn, before.good.inv.win.eq⟩
    · rw [frame]; exact before.good.inv.reqbits
    · rw [frame]; exact before.good.inv.bits
    · exact pointers
  have good := before.good.setZI (z' := z) rfl before.good.live.zalloc before.good.live.zfree
    (by rw [frame]) (by rw [mode]; decide) inv
  rw [ZStreamRef.put_self before.good.live.hz] at good
  have update : ClTablesUpdate h r zs z s (setI h zs state) z state := by
    refine ⟨?_, ?_, frame⟩
    · rw [ZStreamRef.put_self before.good.live.hz]
    · cases z; rfl
  obtain ⟨packet, sizes, static⟩ := update.buffers before.good good buffers 0
  have pending : DataPendingInvariant state := by
    apply dataPendingInvariant_idle (by rw [frame]; exact before.pending.sane)
    rw [mode]; decide
  have current := before.toDefaultDecodeJ.table_update good (fun _ => tables) pending sizes static update (Or.inr mode)
  have config : DefaultConfigFrame s state := by rw [frame]; exact ⟨rfl, rfl, rfl, rfl⟩
  have stateJ := before.toDefaultStateJ.config_update current config format
  refine ⟨⟨stateJ, ?_, Or.inl dynamic⟩, packet, sizes⟩
  rw [frame]
  exact before.flagsOrigin

/-- A real completed reader execution retains its incoming origin and
public packet. The getter, input consumption and output cursors are
derived by execution uniqueness against the proved complete reader. -/
theorem read_completed_packet
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s state : InflateState}
    {l regs : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (before : DefaultOriginState h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = CODELENS)
    (actual : runX (clRead c) l h = .ok ((.ok (), regs), setI h zs state)) :
    ∃ stream used, used ≤ bs.length ∧
      DefaultOriginState (setI h zs state) r zs stream state ∧
      DispatchBuffers (setI h zs state) r regs (bs.drop used) ∧
      regs.next = inputAdvance l.next used ∧ regs.have_.toNat + used = l.have_.toNat ∧
      regs.put = l.put ∧ regs.left = l.left ∧ regs.out_ = l.out_ ∧
      regs.bits.toNat ≤ max l.bits.toNat 21 ∧
      ByteViewSizes h (setI h zs state) := by
  obtain ⟨outcome, regs0, after, stream, state0, used, bound, run, current,
    _config, packet, sizes, cursor, count, put, left, total, bits, _budget, _modes, _complete⟩ :=
    clRead_default_state_complete E before.toDefaultStateJ buffers mode
  rw [actual] at run
  cases run
  have same : state0 = state := Option.some.inj (current.good.live.hs.symm.trans (setI_istates_same ..))
  subst state0
  have origin := before.of_field_frame current (originFieldFrameX_clRead r c E.strm _ _ _ _ _ actual)
  exact ⟨stream, used, bound, origin, packet, cursor, count, put, left, total, bits, sizes⟩

#print axioms constructor_metadata_packet
#print axioms read_completed_packet
end Zlib.Inflate.Proofs.PayloadPhaseView
