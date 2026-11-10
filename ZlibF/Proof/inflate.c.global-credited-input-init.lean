import ZlibF.Proof.«inflate.c.global-credited-input-rebuffer»
import ZlibF.Proof.«inflate.c.protocol-window-history»
namespace Zlib.Inflate.Proofs.CausalInput
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs
set_option autoImplicit false

/-- Successful actual default initialization establishes the exact empty
public input source. Allocation success is derived from the actual run,
not imposed as a new caller condition. -/
theorem AtPublic.init
    {before after : Heap} {r : ZStreamRef} {version : BPtr}
    (domain : InitDomain before r version)
    (platform : ZlibF.PlatformMemory.ByteObjectsFit before)
    (actual : C.run (inflateInit2_ (some r) 15 version 112) before = .ok (Z_OK, after)) :
    ∃ point : AtPublic after r {} [], point.zs = before.nextBlk ∧
      point.state.mode = HEAD ∧ point.state.bits = 0 ∧ point.state.hold = 0 := by
  have allocation := ProtocolWindow.successful_init_allocation domain actual
  obtain ⟨computed, z, s, run, initial, good, head, _wrap, _window, _header, _tables, _fit, _reachable⟩ :=
    inflate_default_init_boundary before r version domain platform allocation
  change C.run (inflateInit_ (some r) version 112) before = .ok (Z_OK, after) at actual
  have same := Except.ok.inj (run.symm.trans actual)
  cases same
  obtain ⟨initialZ, initialState, initialGood, _alloc, _free, _head, _window,
    _wbits, _requested, _wrap, _requestedWrap, _wsize, _whave, _wnext, hold, bits, _rest⟩ := initial
  have stateEq : s = initialState := Option.some.inj (good.live.hs.symm.trans initialGood.live.hs)
  have heldZero : s.hold = 0 := by rw [stateEq]; exact hold
  have bitsZero : s.bits = 0 := by rw [stateEq]; exact bits
  refine ⟨⟨before.nextBlk, z, s, good, ?_⟩, rfl, head, bitsZero, heldZero⟩
  change Credited [] [] s.bits s.hold
  rw [bitsZero]
  exact Credited.initial _

end Zlib.Inflate.Proofs.CausalInput
