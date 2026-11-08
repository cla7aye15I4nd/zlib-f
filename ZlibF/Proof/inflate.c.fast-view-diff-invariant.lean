import ZlibF.Proof.«inflate.c.fast-view-match-invariant»
import ZlibF.Proof.«inflate.c.fast-view-geometry»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The translated pointer difference and match copy retain the default
decoder relation across valid copies and invalid-distance errors. -/
theorem FastInputPacket.copy_match_after_diff_default_state
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow bs l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow bs)
    (streamPtr : c.strm = some r)
    (statePtr : c.state = some (.tab zs))
    (whaveEq : c.whave = s.whave)
    (wsizeEq : c.wsize = s.wsize)
    (wnextEq : c.wnext = s.wnext)
    (windowEq : c.window = s.window)
    (left : slow.left ≠ 0)
    (avail : 258 ≤ slow.left.toNat)
    (length : 3 ≤ l.len.toNat ∧ l.len.toNat ≤ 258)
    {dest : BRef} {output : Array UInt8} {oo bg j : Nat}
    (outPtr : l.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (begPtr : c.beg = .ref dest bg)
    (endPtr : c.end_ = .ref dest
      (oo + slow.left.toNat - 257))
    (outputGet : Space.get h dest = some output)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (current : oo ≤ j)
    (beginLe : bg ≤ j)
    (span : j - bg < 2 ^ 32)
    (guard : C.run (Ptr.lt l.out c.end_) h = .ok (true, h)) :
    let atCopy : Zlib.Inffast.L :=
      { l with op := (Int64.ofInt ((j - bg : Nat) : Int)).toUInt64.toUInt32 }
    ∃ result after,
      C.run (do
        let d ← Ptr.diff l.out c.beg
        Zlib.Inffast.copyMatch c { l with op := d.toUInt64.toUInt32 }) h =
        .ok (result, after) ∧
      FastInputPacket after slow bs result ∧
      DispatchBuffers after r slow bs ∧
      ByteViewSizes h after ∧
      result.againD = atCopy.againD ∧
      result.againL = atCopy.againL ∧
      ((∃ i, result.broke = true ∧
        after = setI
          (r.put h { z with msg := .ref (.str i) 0 }) zs
          { s with mode := BAD } ∧
        DefaultStateJ after r zs
          { z with msg := .ref (.str i) 0 } { s with mode := BAD } ∧
        Space.get after dest = some output ∧
        Space.ro after dest = false) ∨
       (∃ array, result.broke = atCopy.broke ∧
        DefaultStateJ after r zs z s ∧
        result.out = .ref dest (j + l.len.toNat) ∧
        Space.get after dest = some array ∧
        array.size = output.size ∧
        Space.ro after dest = false ∧
        after = Space.put h dest array ∧
        BufferFrame h after (fun _ => False)
          [⟨slow.put, slow.left.toNat⟩])) := by
  have geometry := fast_output_room_of_guard outPtr endPtr
    outputGet outputSize current avail length.2 guard
  have currentBound : j ≤ output.size := geometry.1
  have outputRoom : oo ≤ j ∧
      j + l.len.toNat ≤ oo + slow.left.toNat := geometry.2
  have beginBound : bg ≤ output.size := by omega
  have diffRun : C.run (Ptr.diff l.out c.beg) h =
      .ok (Int64.ofInt ((j - bg : Nat) : Int), h) := by
    rw [outPtr, begPtr]
    have run := Ptr.diff_ok (r := dest) (a := output)
      outputGet currentBound beginBound
      (by omega : -(2 ^ 63 : Int) ≤ (j : Int) - (bg : Int) ∧
        (j : Int) - (bg : Int) < 2 ^ 63)
    have intEq : (j : Int) - (bg : Int) = ((j - bg : Nat) : Int) := by
      omega
    change (Ptr.diff (.ref dest j) (.ref dest bg)) h =
      .ok (Int64.ofInt ((j : Int) - (bg : Int)), h) at run
    simpa only [C.run, intEq] using run
  let atCopy : Zlib.Inffast.L :=
    { l with op := (Int64.ofInt ((j - bg : Nat) : Int)).toUInt64.toUInt32 }
  have produced : atCopy.op.toNat ≤ j :=
    (fast_produced_of_diff (l := atCopy) outputGet
      currentBound beginBound beginLe span
      (by simpa only [outPtr, begPtr] using diffRun) rfl).2
  have copyPacket : FastInputPacket h slow bs atCopy :=
    packet.with_op _
  have whaveBound : c.whave.toNat ≤ c.wsize.toNat := by
    rw [whaveEq, wsizeEq]
    exact invariant.good.inv.win.hv
  have wnextBound : c.wnext.toNat ≤ c.wsize.toNat := by
    rw [wnextEq, wsizeEq]
    rcases invariant.good.inv.win.wn with lt | zero
    · omega
    · omega
  have wsizeBound : c.wsize.toNat ≤ 32768 := by
    rw [wsizeEq]
    have pow := Nat.pow_le_pow_right
      (by decide : 0 < 2) invariant.good.inv.win.wbits
    rcases invariant.good.inv.win.ws with zero | size
    · omega
    · omega
  have windowData := fast_window_data_of_caller (l := atCopy)
    invariant.good buffers.output.range outputPtr
    whaveEq wsizeEq windowEq
  obtain ⟨result, after, copyRun, packetAfter, nextBuffers,
    sizes, againD, againL, outcome⟩ :=
    copyPacket.copyMatch_default_state invariant buffers
      streamPtr statePtr left (by simpa only [atCopy] using length.1)
      whaveBound wnextBound wsizeBound outPtr outputPtr
      outputGet outputWrite outputSize outputRoom produced
      windowData
  refine ⟨result, after, ?_, packetAfter, nextBuffers,
    sizes, againD, againL, ?_⟩
  · change (do
      let d ← Ptr.diff l.out c.beg
      Zlib.Inffast.copyMatch c { l with op := d.toUInt64.toUInt32 }) h =
        .ok (result, after)
    rw [bind_ok (by simpa only [C.run] using diffRun)]
    exact copyRun
  · simpa only [atCopy] using outcome

end Zlib.Inflate.Proofs
