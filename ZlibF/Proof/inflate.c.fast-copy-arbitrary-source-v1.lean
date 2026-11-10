import ZlibF.Proof.«inflate.c.payload-unified-two-pull-output-cursor-stage-relinked»
import ZlibF.Proof.«inflate.c.accepted-token-soundness»

namespace Zlib.Inflate.Proofs.FastArbitrarySource
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inffast.Spec
set_option autoImplicit false

/-- Generic caller-view fast copying classifies its actual distance bound.
It either enters real BAD without changing output or emits the independent
copyBack result. No input parse or caller-supplied distance fit is used. -/
theorem copyMatch_current_source
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow bs l) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow bs) (streamPtr : c.strm = some r)
    (statePtr : c.state = some (.tab zs)) (left : slow.left ≠ 0)
    (length : 3 ≤ l.len.toNat) (distance : 0 < l.dist.toNat)
    (whaveBound : c.whave.toNat ≤ c.wsize.toNat)
    (wnextBound : c.wnext.toNat ≤ c.wsize.toNat) (wsizeBound : c.wsize.toNat ≤ 32768)
    {dest : BRef} {output saved : Array UInt8} {oo j woff : Nat}
    (outPtr : l.out = .ref dest j) (outputPtr : slow.put = .ref dest oo)
    (outputGet : Space.get h dest = some output) (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (outputRoom : oo ≤ j ∧ j + l.len.toNat ≤ oo + slow.left.toNat)
    (produced : l.op.toNat ≤ j)
    (windowData : l.dist > l.op → ¬ l.dist - l.op > c.whave → ∃ window,
      window ≠ dest ∧ c.window = .ref window woff ∧ Space.get h window = some saved ∧
      woff + c.wsize.toNat ≤ saved.size) :
    ∃ result after,
      C.run (Zlib.Inffast.copyMatch c l) h = .ok (result, after) ∧
      FastInputPacket after slow bs result ∧ DispatchBuffers after r slow bs ∧
      ByteViewSizes h after ∧ result.againD = l.againD ∧ result.againL = l.againL ∧
      ((¬ l.dist.toNat ≤ c.whave.toNat + l.op.toNat ∧ ∃ i,
        result.broke = true ∧ result.out = l.out ∧
        after = setI (r.put h {z with msg := .ref (.str i) 0}) zs {s with mode := BAD} ∧
        DefaultStateJ after r zs {z with msg := .ref (.str i) 0} {s with mode := BAD} ∧
        Space.get after dest = some output ∧ Space.ro after dest = false) ∨
       (l.dist.toNat ≤ c.whave.toNat + l.op.toNat ∧ ∃ array,
        result.broke = l.broke ∧ result.out = .ref dest (j + l.len.toNat) ∧
        DefaultStateJ after r zs z s ∧ Space.get after dest = some array ∧
        array.size = output.size ∧ Space.ro after dest = false ∧ after = Space.put h dest array ∧
        BufferFrame h after (fun _ => False) [⟨slow.put, slow.left.toNat⟩] ∧
        ZlibF.Math.LZ77Copy.writtenBytes array (j + l.len.toNat) (l.op.toNat + l.len.toNat) =
          copyBack (Zlib.Inffast.Spec.MatchHistory.saved saved c.wsize.toNat c.wnext.toNat c.whave.toNat woff)
            l.dist.toNat l.len.toNat (ZlibF.Math.LZ77Copy.writtenBytes output j l.op.toNat))) := by
  by_cases available : l.dist.toNat ≤ c.whave.toNat + l.op.toNat
  · have validBack : l.dist > l.op → ¬ l.dist - l.op > c.whave := by
      intro branch invalid
      have more := UInt32.lt_iff_toNat_lt.mp branch
      have bad := UInt32.lt_iff_toNat_lt.mp invalid
      rw [UInt32.toNat_sub_of_le _ _ (by omega : l.op.toNat ≤ l.dist.toNat)] at bad
      omega
    obtain ⟨result, after, array, actual, nextPacket, out, broke, againD, againL,
      get, size, ro, _array, bytes⟩ := packet.copyMatch_valid_lz77_view buffers.separate left length distance
        available whaveBound wnextBound wsizeBound outPtr outputPtr outputGet outputWrite
        outputSize outputRoom produced (fun branch => windowData branch (validBack branch))
    obtain ⟨safeResult, safeAfter, safeArray, safeRun, _safePacket, current, nextBuffers,
      sizes, _out, _broke, _againD, _againL, safeGet, _size, _ro, heap, frame⟩ :=
      packet.copyMatch_valid_default_state invariant buffers left length whaveBound wnextBound wsizeBound
        outPtr outputPtr outputGet outputWrite outputSize outputRoom produced validBack
        (fun branch valid => by obtain ⟨window, different, ptr, get, fit⟩ := windowData branch valid; exact ⟨window, saved, woff, different, ptr, get, fit⟩)
    have same := Except.ok.inj (actual.symm.trans safeRun)
    cases same
    have arrayEq : safeArray = array := Option.some.inj (safeGet.symm.trans get)
    subst safeArray
    exact ⟨result, after, actual, nextPacket, nextBuffers, sizes, againD, againL,
      Or.inr ⟨available, array, broke, out, current, get, size, ro, heap, frame, bytes⟩⟩
  · have branch : l.dist > l.op := UInt32.lt_iff_toNat_lt.mpr (by omega)
    have subtraction : (l.dist - l.op).toNat = l.dist.toNat - l.op.toNat :=
      UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by omega))
    have invalid : l.dist - l.op > c.whave := UInt32.lt_iff_toNat_lt.mpr (by rw [subtraction]; omega)
    obtain ⟨i, after, actual, heap, nextPacket, current, nextBuffers, sizes, get, ro⟩ :=
      packet.copyMatch_invalid_default_state invariant buffers streamPtr statePtr branch invalid outputGet outputWrite
    exact ⟨_, after, actual, nextPacket, nextBuffers, sizes, rfl, rfl,
      Or.inl ⟨available, i, rfl, rfl, heap, current, get, ro⟩⟩

/-- Actual fast distance extras and pointer difference are identified
before any copy. This reads only the represented current input. -/
theorem distCont_current_prefix
    {h : Heap} {slow : IL} {bs : List UInt8} {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} (packet : FastInputPacket h slow bs l) (buffers : DispatchBuffers h r slow bs)
    (extraFits : l.op.toNat ≤ slow.bits.toNat) (extraSmall : l.op.toNat < 32)
    (budget : l.dist.toNat + 2 ^ l.op.toNat ≤ 2 ^ 32)
    {dest : BRef} {output : Array UInt8} {bg j : Nat}
    (outPtr : l.out = .ref dest j) (begPtr : c.beg = .ref dest bg)
    (get : Space.get h dest = some output) (currentBound : j ≤ output.size)
    (beginLe : bg ≤ j) (span : j - bg < 2 ^ 32) :
    ∃ extra rest slowNext fastNext,
      readBits l.op.toNat (stream slow bs) = some (extra, rest) ∧ extra < 2 ^ l.op.toNat ∧
      C.run (Zlib.Inffast.Proofs.distCont c l) h = C.run (Zlib.Inffast.copyMatch c fastNext) h ∧
      FastInputPacket h slowNext bs fastNext ∧ DispatchBuffers h r slowNext bs ∧
      stream slowNext bs = rest ∧ slowNext.next = slow.next ∧ slowNext.have_ = slow.have_ ∧
      slowNext.left = slow.left ∧ slowNext.put = slow.put ∧
      fastNext.in_ = l.in_ ∧ fastNext.out = l.out ∧ fastNext.len = l.len ∧
      fastNext.againD = l.againD ∧ fastNext.againL = l.againL ∧ fastNext.broke = l.broke ∧
      fastNext.dist.toNat = l.dist.toNat + extra ∧ fastNext.op.toNat = j - bg ∧
      rest = (stream slow bs).drop l.op.toNat := by
  let extra := l.hold.toNat % 2 ^ l.op.toNat
  let distance := l.dist + (l.hold.toUInt32 &&& (((1 : UInt32) <<< l.op) - 1))
  let distanceLocal : Zlib.Inffast.L := {l with dist := distance}
  let slowNext : IL := {slow with hold := slow.hold >>> l.op.toUInt64, bits := slow.bits - l.op}
  let fastDrop : Zlib.Inffast.L := {distanceLocal with hold := l.hold >>> l.op.toUInt64, bits := l.bits - l.op}
  let fastNext : Zlib.Inffast.L := {fastDrop with op := (Int64.ofInt ((j - bg : Nat) : Int)).toUInt64.toUInt32}
  have distancePacket : FastInputPacket h slow bs distanceLocal := ⟨packet.source, packet.cursor, packet.hold, packet.bits⟩
  have dropped := distancePacket.drop_bits_default_state buffers l.op extraFits (by omega)
  have dropPacket : FastInputPacket h slowNext bs fastDrop := dropped.1
  have nextPacket : FastInputPacket h slowNext bs fastNext := dropPacket.with_op _
  have read := readBits_held_stream slow bs l.op.toNat extraFits
  have actualRead : readBits l.op.toNat (stream slow bs) = some (extra, (stream slow bs).drop l.op.toNat) := by
    simpa only [extra, packet.hold] using read
  have bound : extra < 2 ^ l.op.toNat := Nat.mod_lt _ (Nat.two_pow_pos _)
  have low : (l.hold.toUInt32 &&& (((1 : UInt32) <<< l.op) - 1)).toNat = extra :=
    Zlib.Inffast.Proofs.hold_low32 extraSmall
  have noWrap : distance.toNat = l.dist.toNat + extra := by
    rw [UInt32.toNat_add, low, Nat.mod_eq_of_lt (by omega)]
  have diff : C.run (Ptr.diff l.out c.beg) h = .ok (Int64.ofInt ((j - bg : Nat) : Int), h) := by
    change Ptr.diff l.out c.beg h = _
    rw [outPtr, begPtr]
    have run := Ptr.diff_ok (r := dest) (a := output) get currentBound (by omega : bg ≤ output.size)
      (by omega : -(2 ^ 63 : Int) ≤ (j : Int) - (bg : Int) ∧ (j : Int) - (bg : Int) < 2 ^ 63)
    have difference : (j : Int) - (bg : Int) = ((j - bg : Nat) : Int) := by omega
    simpa only [OkOn, difference] using run
  have shlRun : C.run (Zlib.Inffast.shl32 1 l.op) h = .ok ((1 : UInt32) <<< l.op, h) :=
    Zlib.Inffast.Proofs.shl32_ok extraSmall
  have shrRun : C.run (Zlib.Inffast.shr64 l.hold l.op.toUInt64) h = .ok (l.hold >>> l.op.toUInt64, h) := by
    apply Zlib.Inffast.Proofs.shr64_ok
    rw [UInt32.toNat_toUInt64]
    omega
  refine ⟨extra, (stream slow bs).drop l.op.toNat, slowNext, fastNext, actualRead, bound,
    ?_, nextPacket, dropped.2.1, dropped.2.2.1, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    noWrap, ?_, rfl⟩
  · change Zlib.Inffast.Proofs.distCont c l h = Zlib.Inffast.copyMatch c fastNext h
    change Zlib.Inffast.shl32 1 l.op h = .ok ((1 : UInt32) <<< l.op, h) at shlRun
    change Zlib.Inffast.shr64 l.hold l.op.toUInt64 h = .ok (l.hold >>> l.op.toUInt64, h) at shrRun
    change Ptr.diff l.out c.beg h = .ok (Int64.ofInt ((j - bg : Nat) : Int), h) at diff
    unfold Zlib.Inffast.Proofs.distCont
    rw [bind_ok shlRun, bind_ok shrRun]
    change (do
      let d ← Ptr.diff l.out c.beg
      Zlib.Inffast.copyMatch c {fastDrop with op := d.toUInt64.toUInt32}) h = _
    rw [bind_ok diff]
  · exact Zlib.Inffast.Proofs.i64_toU32 _ (by omega)

/-- Actual distance extras plus a complete fast copy on arbitrary current
input. Distance availability is classified internally, including real BAD.
The only window premise is its physical view when any history exists. -/
theorem distCont_current_source
    {h : Heap} {slow : IL} {bs : List UInt8} {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow bs l) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow bs) (streamPtr : c.strm = some r)
    (statePtr : c.state = some (.tab zs)) (extraFits : l.op.toNat ≤ slow.bits.toNat)
    (extraSmall : l.op.toNat < 32) (basePositive : 0 < l.dist.toNat)
    (budget : l.dist.toNat + 2 ^ l.op.toNat ≤ 2 ^ 32)
    (left : slow.left ≠ 0) (length : 3 ≤ l.len.toNat)
    (whaveBound : c.whave.toNat ≤ c.wsize.toNat)
    (wnextBound : c.wnext.toNat ≤ c.wsize.toNat) (wsizeBound : c.wsize.toNat ≤ 32768)
    {dest : BRef} {output saved : Array UInt8} {oo bg j woff : Nat}
    (outPtr : l.out = .ref dest j) (outputPtr : slow.put = .ref dest oo)
    (begPtr : c.beg = .ref dest bg) (get : Space.get h dest = some output)
    (write : Space.ro h dest = false) (room : oo + slow.left.toNat ≤ output.size)
    (copyRoom : oo ≤ j ∧ j + l.len.toNat ≤ oo + slow.left.toNat)
    (beginLe : bg ≤ j) (span : j - bg < 2 ^ 32)
    (windowData : c.whave ≠ 0 → ∃ window,
      window ≠ dest ∧ c.window = .ref window woff ∧ Space.get h window = some saved ∧
      woff + c.wsize.toNat ≤ saved.size) :
    ∃ extra rest slowNext result after,
      readBits l.op.toNat (stream slow bs) = some (extra, rest) ∧ extra < 2 ^ l.op.toNat ∧
      C.run (Zlib.Inffast.Proofs.distCont c l) h = .ok (result, after) ∧
      FastInputPacket after slowNext bs result ∧ DispatchBuffers after r slowNext bs ∧ ByteViewSizes h after ∧
      stream slowNext bs = rest ∧ slowNext.next = slow.next ∧ slowNext.have_ = slow.have_ ∧
      slowNext.left = slow.left ∧ slowNext.put = slow.put ∧ result.in_ = l.in_ ∧
      result.againD = l.againD ∧ result.againL = l.againL ∧
      ((¬ l.dist.toNat + extra ≤ c.whave.toNat + (j - bg) ∧ ∃ i,
        result.broke = true ∧ result.out = l.out ∧
        after = setI (r.put h {z with msg := .ref (.str i) 0}) zs {s with mode := BAD} ∧
        DefaultStateJ after r zs {z with msg := .ref (.str i) 0} {s with mode := BAD} ∧
        Space.get after dest = some output ∧ Space.ro after dest = false) ∨
       (l.dist.toNat + extra ≤ c.whave.toNat + (j - bg) ∧ ∃ array,
        result.broke = l.broke ∧ result.out = .ref dest (j + l.len.toNat) ∧
        DefaultStateJ after r zs z s ∧ Space.get after dest = some array ∧
        array.size = output.size ∧ Space.ro after dest = false ∧ after = Space.put h dest array ∧
        ZlibF.Math.LZ77Copy.writtenBytes array (j + l.len.toNat) ((j - bg) + l.len.toNat) =
          copyBack (Zlib.Inffast.Spec.MatchHistory.saved saved c.wsize.toNat c.wnext.toNat c.whave.toNat woff)
            (l.dist.toNat + extra) l.len.toNat (ZlibF.Math.LZ77Copy.writtenBytes output j (j - bg)))) := by
  obtain ⟨extra, rest, slowNext, fastNext, read, extraBound, prefixRun, nextPacket, nextBuffers,
    source, next, inputCount, outputCount, outputCursor, fastIn, fastOut, fastLen,
    fastAgainD, fastAgainL, fastBroke, distance, op, _restEq⟩ :=
    distCont_current_prefix packet buffers extraFits extraSmall budget outPtr begPtr get
      (by omega : j ≤ output.size) beginLe span
  have windowDataNext : fastNext.dist > fastNext.op → ¬ fastNext.dist - fastNext.op > c.whave → ∃ window,
      window ≠ dest ∧ c.window = .ref window woff ∧ Space.get h window = some saved ∧
      woff + c.wsize.toNat ≤ saved.size := by
    intro branch valid
    have branchNat := UInt32.lt_iff_toNat_lt.mp branch
    have subtraction := UInt32.toNat_sub_of_le fastNext.dist fastNext.op (UInt32.le_iff_toNat_le.mpr (by omega))
    apply windowData
    intro zero
    apply valid
    exact UInt32.lt_iff_toNat_lt.mpr (by rw [zero, UInt32.toNat_zero, subtraction]; omega)
  obtain ⟨result, after, actual, finalPacket, finalBuffers, sizes, againD, againL, outcome⟩ :=
    copyMatch_current_source nextPacket invariant nextBuffers streamPtr statePtr
      (by rw [outputCount]; exact left) (by rw [fastLen]; exact length)
      (by rw [distance]; omega) whaveBound wnextBound wsizeBound
      (fastOut.trans outPtr) (outputCursor.trans outputPtr) get write
      (by rw [outputCount]; exact room) (by rw [fastLen, outputCount]; exact copyRoom)
      (by rw [op]; omega) windowDataNext
  have resultIn : result.in_ = l.in_ := finalPacket.cursor.trans (next.trans (packet.cursor.symm))
  refine ⟨extra, rest, slowNext, result, after, read, extraBound, prefixRun.trans actual,
    finalPacket, finalBuffers, sizes, source, next, inputCount, outputCount, outputCursor,
    resultIn, againD.trans fastAgainD, againL.trans fastAgainL, ?_⟩
  rcases outcome with bad | copied
  · obtain ⟨unavailable, i, broke, out, heap, current, outputGet, outputRo⟩ := bad
    refine Or.inl ⟨?_, i, broke, out.trans fastOut, heap, current, outputGet, outputRo⟩
    simpa only [distance, op] using unavailable
  · obtain ⟨available, array, broke, out, current, outputGet, size, outputRo, heap, _frame, bytes⟩ := copied
    refine Or.inr ⟨?_, array, broke.trans fastBroke, ?_, current, outputGet, size, outputRo, heap, ?_⟩
    · simpa only [distance, op] using available
    · simpa only [fastLen] using out
    · simpa only [fastLen, distance, op] using bytes

#print axioms copyMatch_current_source
#print axioms distCont_current_prefix
#print axioms distCont_current_source
end Zlib.Inflate.Proofs.FastArbitrarySource
