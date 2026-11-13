import ZlibF.Proof.«inflate.c.leave-restore»
import ZlibF.Proof.«inffast.c.platform»
import ZlibF.Proof.«inffast.c.progress»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- A fast-path dispatch packet yields bounded input and writable output
views for every public byte-object representation. Their occupied ranges
may be disjoint slices of one object. This is the caller-side premise for
generalizing the translated fast callee beyond raw blocks. -/
theorem DispatchBuffers.fast_views {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (good : Good h r zs z s)
    (fit : ZlibF.PlatformMemory.ByteObjectsFit h)
    (buffers : DispatchBuffers h r l bs)
    (fast : (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    ∃ (ir or : BRef) (ia oa : Array UInt8) (io oo : Nat),
      l.next = .ref ir io ∧ Space.get h ir = some ia ∧
      io + l.have_.toNat ≤ ia.size ∧ ia.size < 2 ^ 63 ∧
      bs = (ia.toList.drop io).take bs.length ∧
      l.put = .ref or oo ∧ Space.get h or = some oa ∧
      Space.ro h or = false ∧ oo + l.left.toNat ≤ oa.size ∧
      oa.size < 2 ^ 63 ∧
      (ir ≠ or ∨ io + l.have_.toNat ≤ oo ∨
        oo + l.left.toNat ≤ io) := by
  have margins : (6 ≤ l.have_ ∧ 258 ≤ l.left) ∧ l.bits < 8 := by
    simpa only [Bool.and_eq_true, decide_eq_true_eq] using fast
  have inputRoom : 6 ≤ l.have_.toNat := by
    simpa [UInt32.le_iff_toNat_le] using margins.1.1
  have outputRoom : 258 ≤ l.left.toNat := by
    simpa [UInt32.le_iff_toNat_le] using margins.1.2
  have nonempty : bs ≠ [] := by
    intro empty
    have count := buffers.bits.have_eq
    rw [empty] at count
    simp at count
    omega
  obtain ⟨ir, ia, io, inputPtr, inputGet, inputSize, inputBytes⟩ :=
    buffers.bits.next.resolve_left nonempty
  obtain ⟨or, oa, oo, outputPtr, outputGet, outputWrite,
      outputSize, _, _, _⟩ :=
    callerRange_slow_output good l buffers.output.range
      buffers.output.nonnull buffers.output.count
      buffers.output.produced
  have separated : ir ≠ or ∨ io + l.have_.toNat ≤ oo ∨
      oo + l.left.toNat ≤ io := by
    have packet := buffers.separate
    rw [inputPtr, outputPtr] at packet
    dsimp [Separate] at packet
    rcases packet with zeroIn | zeroOut | disjoint
    · omega
    · omega
    · exact disjoint
  exact ⟨ir, or, ia, oa, io, oo, inputPtr, inputGet,
    by rw [buffers.bits.have_eq]; exact inputSize,
    fit.size_lt inputGet, inputBytes, outputPtr, outputGet,
    outputWrite, outputSize, fit.size_lt outputGet, separated⟩

/-- The three actual fast-callee entry pointer expressions are safe for
general represented byte views, including disjoint slices of one object.
The initial `last`, `beg` and `end` positions do not require raw blocks. -/
theorem DispatchBuffers.fast_pointer_setup {h : Heap} {r : ZStreamRef}
    {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8}
    (good : Good h r zs z s)
    (fit : ZlibF.PlatformMemory.ByteObjectsFit h)
    (buffers : DispatchBuffers h r l bs)
    (fast : (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    ∃ (ir or : BRef) (io oo : Nat),
      l.next = .ref ir io ∧ l.put = .ref or oo ∧
      OkOn h (Ptr.add l.next (l.have_ - 5).toNat)
        (.ref ir (io + l.have_.toNat - 5)) ∧
      OkOn h (Zlib.Inffast.subn l.put (l.out_ - l.left))
        (.ref or (oo - (l.out_.toNat - l.left.toNat))) ∧
      OkOn h (Ptr.add l.put (l.left - 257).toNat)
        (.ref or (oo + l.left.toNat - 257)) := by
  obtain ⟨ir, or, ia, oa, io, oo, inputPtr, inputGet,
    inputSize, _, _, outputPtr, outputGet, _, outputSize, _, _⟩ :=
    buffers.fast_views good fit fast
  have margins : (6 ≤ l.have_ ∧ 258 ≤ l.left) ∧ l.bits < 8 := by
    simpa only [Bool.and_eq_true, decide_eq_true_eq] using fast
  have inputRoom : 5 ≤ l.have_.toNat := by
    have : 6 ≤ l.have_.toNat := by
      simpa [UInt32.le_iff_toNat_le] using margins.1.1
    omega
  have outputRoom : 257 ≤ l.left.toNat := by
    have : 258 ≤ l.left.toNat := by
      simpa [UInt32.le_iff_toNat_le] using margins.1.2
    omega
  have inputSub : (l.have_ - 5).toNat = l.have_.toNat - 5 :=
    Zlib.Inffast.Proofs.u32_toNat_sub inputRoom
  have outputSub : (l.left - 257).toNat = l.left.toNat - 257 :=
    Zlib.Inffast.Proofs.u32_toNat_sub outputRoom
  have startSub : (l.out_ - l.left).toNat =
      l.out_.toNat - l.left.toNat :=
    Zlib.Inffast.Proofs.u32_toNat_sub buffers.output.count
  have begBound : l.out_.toNat - l.left.toNat ≤ oo :=
    buffers.output.produced or oo outputPtr
  refine ⟨ir, or, io, oo, inputPtr, outputPtr, ?_, ?_, ?_⟩
  · rw [inputPtr, inputSub]
    have step := Ptr.add_nat_ok (h := h) (r := ir) (a := ia)
      (off := io) (n := l.have_.toNat - 5) inputGet (by omega)
    simpa only [show io + (l.have_.toNat - 5) = io + l.have_.toNat - 5 by omega] using step
  · rw [outputPtr]
    have step := Zlib.Inffast.Proofs.subn_ok (h := h) (r := or)
      (a := oa) (off := oo) (n := l.out_ - l.left)
      outputGet (by rw [startSub]; exact begBound) (by omega)
    simpa only [startSub] using step
  · rw [outputPtr, outputSub]
    have step := Ptr.add_nat_ok (h := h) (r := or) (a := oa)
      (off := oo) (n := l.left.toNat - 257) outputGet (by omega)
    simpa only [show oo + (l.left.toNat - 257) = oo + l.left.toNat - 257 by omega] using step

/-- The translated fast `pull` reads one byte and advances its pointer for
any represented byte view. This is the source read used by both initial
bit-buffer fills and later length or distance decoding. -/
theorem inflate_fast_pull_view {h : Heap} {l : Zlib.Inffast.L}
    {ref : BRef} {array : Array UInt8} {off : Nat}
    (pointer : l.in_ = .ref ref off)
    (get : Space.get h ref = some array)
    (bound : off < array.size)
    (bits : l.bits.toNat ≤ 22) :
    OkOn h (Zlib.Inffast.pull l)
      (Zlib.Inffast.Proofs.pullL l array[off] (.ref ref (off + 1))) := by
  unfold Zlib.Inffast.pull
  rw [pointer]
  refine OkOn.bind (x := array[off]) (Ptr.load_ok get bound) ?_
  have advance := Ptr.add_nat_ok (h := h) (r := ref) (a := array)
    (off := off) (n := 1) get (by omega)
  refine OkOn.bind (x := Ptr.ref ref (off + 1)) (by simpa using advance) ?_
  have shift : Zlib.Inffast.shl64 array[off].toUInt64 l.bits.toUInt64 =
      pure (array[off].toUInt64 <<< l.bits.toUInt64) :=
    Zlib.Inffast.Proofs.shl64_eq (by rw [UInt32.toNat_toUInt64]; omega)
  rw [shift]
  rfl

/-- The first actual fast bit-buffer read follows from the public dispatch
packet, without a raw-block or different-allocation premise. -/
theorem DispatchBuffers.fast_first_pull {h : Heap} {r : ZStreamRef}
    {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8} {fastLocal : Zlib.Inffast.L}
    (good : Good h r zs z s)
    (fit : ZlibF.PlatformMemory.ByteObjectsFit h)
    (buffers : DispatchBuffers h r l bs)
    (fast : (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true)
    (cursor : fastLocal.in_ = l.next)
    (bits : fastLocal.bits.toNat ≤ 22) :
    ∃ byte, OkOn h (Zlib.Inffast.pull fastLocal)
      (Zlib.Inffast.Proofs.pullL fastLocal byte
        (inputAdvance l.next 1)) := by
  obtain ⟨ir, or, ia, oa, io, oo, inputPtr, inputGet,
    inputSize, _, _, _, _, _, _, _, _⟩ :=
    buffers.fast_views good fit fast
  have margins : (6 ≤ l.have_ ∧ 258 ≤ l.left) ∧ l.bits < 8 := by
    simpa only [Bool.and_eq_true, decide_eq_true_eq] using fast
  have available : 6 ≤ l.have_.toNat := by
    simpa [UInt32.le_iff_toNat_le] using margins.1.1
  have readBound : io < ia.size := by omega
  refine ⟨ia[io], ?_⟩
  have run := inflate_fast_pull_view (l := fastLocal)
    (ref := ir) (array := ia) (off := io)
    (cursor.trans inputPtr) inputGet readBound bits
  simpa only [inputPtr, inputAdvance] using run

/-- A fast output-byte write inside the caller's output range leaves the
unread input packet valid, even if both ranges share one byte object. The
next translated `pull` is therefore safe on the written heap. -/
theorem DispatchBuffers.fast_pull_after_output_byte
    {h : Heap} {r : ZStreamRef} {l : IL} {bs : List UInt8}
    (buffers : DispatchBuffers h r l bs)
    (fast : (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true)
    {dest : BRef} {array : Array UInt8} {oo j : Nat}
    (outputPtr : l.put = .ref dest oo)
    (outputGet : Space.get h dest = some array)
    (outputWrite : Space.ro h dest = false)
    (inside : oo ≤ j ∧ j < oo + l.left.toNat)
    (value : UInt8)
    {fastLocal : Zlib.Inffast.L}
    (cursor : fastLocal.in_ = l.next)
    (bits : fastLocal.bits.toNat ≤ 22) :
    let after := Space.put h dest (array.set! j value)
    BitInv after l bs ∧
      ∃ byte, OkOn after (Zlib.Inffast.pull fastLocal)
        (Zlib.Inffast.Proofs.pullL fastLocal byte
          (inputAdvance l.next 1)) := by
  have margins : (6 ≤ l.have_ ∧ 258 ≤ l.left) ∧ l.bits < 8 := by
    simpa only [Bool.and_eq_true, decide_eq_true_eq] using fast
  have inputRoom : 6 ≤ l.have_.toNat := by
    simpa [UInt32.le_iff_toNat_le] using margins.1.1
  have nonempty : bs ≠ [] := by
    intro empty
    have count := buffers.bits.have_eq
    rw [empty] at count
    simp at count
    omega
  have left : l.left ≠ 0 := by
    intro zero
    rw [zero] at margins
    simp at margins
  have separated := buffers.bits.output_positions outputPtr left
    buffers.separate
  have nextSeparated : bs = [] ∨
      ∀ i, l.next = .ref dest i →
        i + bs.length ≤ j ∨ j + 1 ≤ i := by
    rcases separated with empty | positions
    · exact Or.inl empty
    · right
      intro i ptr
      rcases positions i ptr with before | after
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
  have packet := buffers.bits.store_byte outputGet outputWrite value nextSeparated
  refine ⟨packet, ?_⟩
  obtain ⟨ref, saved, off, inputPtr, inputGet, inputSize, _⟩ :=
    packet.next.resolve_left nonempty
  have readBound : off < saved.size := by
    have count := packet.have_eq
    omega
  refine ⟨saved[off], ?_⟩
  have run := inflate_fast_pull_view (l := fastLocal)
    (ref := ref) (array := saved) (off := off)
    (cursor.trans inputPtr) inputGet readBound bits
  simpa only [inputPtr, inputAdvance] using run

/-- Synchronize the public bit-source packet with the current registers of
the translated fast decoder. Output writes may change the heap, but the
packet continues to describe the unread input suffix. -/
structure FastInputPacket (h : Heap) (slow : IL) (bs : List UInt8)
    (fastLocal : Zlib.Inffast.L) : Prop where
  source : BitInv h slow bs
  cursor : fastLocal.in_ = slow.next
  hold : fastLocal.hold = slow.hold
  bits : fastLocal.bits = slow.bits

/-- The `copyOp` loop condition changes only its repetition counter. -/
theorem FastInputPacket.with_op {h : Heap} {slow : IL}
    {bs : List UInt8} {fastLocal : Zlib.Inffast.L}
    (packet : FastInputPacket h slow bs fastLocal)
    (op : UInt32) :
    FastInputPacket h slow bs { fastLocal with op } := by
  exact ⟨packet.source, packet.cursor, packet.hold, packet.bits⟩

/-- One actual fast `pull` consumes the next public input byte, retains the
same bit stream and re-establishes the synchronized packet. -/
theorem FastInputPacket.pull {h : Heap} {slow : IL}
    {b : UInt8} {bs : List UInt8} {fastLocal : Zlib.Inffast.L}
    (packet : FastInputPacket h slow (b :: bs) fastLocal)
    (small : slow.bits.toNat ≤ 22) :
    ∃ next fastNext slowNext,
      C.run (Zlib.Inffast.pull fastLocal) h = .ok (fastNext, h) ∧
      next = inputAdvance slow.next 1 ∧
      slowNext = pulled slow b next ∧
      fastNext = Zlib.Inffast.Proofs.pullL fastLocal b next ∧
      FastInputPacket h slowNext bs fastNext ∧
      stream slowNext bs = stream slow (b :: bs) := by
  obtain ⟨ref, array, off, sourcePtr, sourceGet, room, contents⟩ :=
    packet.source.next.resolve_left (by simp)
  have room' : off + bs.length + 1 ≤ array.size := by
    simp only [List.length_cons] at room
    omega
  have readBound : off < array.size := by omega
  have contents' : b :: bs = array[off] ::
      (array.toList.drop (off + 1)).take bs.length := by
    have sliced := take_succ_drop array off bs.length room'
    simp only [List.length_cons] at contents
    rw [← sliced]
    exact contents
  have byteEq : array[off] = b := by
    injection contents' with eq
    exact eq.symm
  have suffix : bs = (array.toList.drop (off + 1)).take bs.length := by
    injection contents' with _ eq
  let next := Ptr.ref ref (off + 1)
  let slowNext := pulled slow b next
  let fastNext := Zlib.Inffast.Proofs.pullL fastLocal b next
  have run : C.run (Zlib.Inffast.pull fastLocal) h = .ok (fastNext, h) := by
    change Zlib.Inffast.pull fastLocal h = .ok (fastNext, h)
    have step := inflate_fast_pull_view (l := fastLocal)
      (ref := ref) (array := array) (off := off)
      (packet.cursor.trans sourcePtr) sourceGet readBound
      (by rw [packet.bits]; exact small)
    simpa only [byteEq, fastNext, next, OkOn] using step
  have held := pull_hold slow.hold b slow.bits (by omega) packet.source.hold_lt
  have count := u32_add8 slow.bits (by omega)
  have sourceNext : BitInv h slowNext bs := by
    refine ⟨?_, Or.inr ⟨ref, array, off + 1, rfl,
      sourceGet, by omega, suffix⟩, ?_⟩
    · have oldCount := packet.source.have_eq
      simp only [slowNext, pulled, List.length_cons] at oldCount ⊢
      rw [UInt32.toNat_sub_of_le _ _
        (by rw [UInt32.le_iff_toNat_le]; simp; omega)]
      simp
      omega
    · simp only [slowNext, pulled, count, held.1]
      exact held.2
  have nextPacket : FastInputPacket h slowNext bs fastNext := by
    refine ⟨sourceNext, rfl, ?_, ?_⟩
    · simp only [fastNext, Zlib.Inffast.Proofs.pullL,
        slowNext, pulled, packet.hold, packet.bits]
    · simp only [fastNext, Zlib.Inffast.Proofs.pullL,
        slowNext, pulled, packet.bits]
  have sameStream : stream slowNext bs = stream slow (b :: bs) := by
    unfold stream
    simp only [slowNext, pulled, count, held.1]
    rw [natBits_pull _ _ _ packet.source.hold_lt
      (UInt8.toNat_lt _), List.append_assoc, bytesBits_cons]
  exact ⟨next, fastNext, slowNext, run,
    by rw [sourcePtr]; rfl, rfl, rfl, nextPacket, sameStream⟩

/-- The two consecutive `pull` calls in the fast body's `bits < 15`
branch consume two public bytes and preserve the exact bitstream. -/
theorem FastInputPacket.pull_twice {h : Heap} {slow : IL}
    {first second : UInt8} {rest : List UInt8}
    {fastLocal : Zlib.Inffast.L}
    (packet : FastInputPacket h slow (first :: second :: rest) fastLocal)
    (small : slow.bits.toNat < 15) :
    ∃ fastNext slowNext,
      C.run (do
        let one ← Zlib.Inffast.pull fastLocal
        Zlib.Inffast.pull one) h = .ok (fastNext, h) ∧
      FastInputPacket h slowNext rest fastNext ∧
      stream slowNext rest = stream slow (first :: second :: rest) := by
  obtain ⟨next1, fast1, slow1, run1, _, slow1Eq, _, packet1, stream1⟩ :=
    packet.pull (by omega)
  have small1 : slow1.bits.toNat ≤ 22 := by
    have nextBits : slow1.bits.toNat = slow.bits.toNat + 8 := by
      rw [slow1Eq]
      exact u32_add8 slow.bits (by omega)
    omega
  obtain ⟨next2, fast2, slow2, run2, _, _, _, packet2, stream2⟩ :=
    packet1.pull small1
  refine ⟨fast2, slow2, ?_, packet2, stream2.trans stream1⟩
  change (Zlib.Inffast.pull fastLocal >>= Zlib.Inffast.pull) h = .ok (fast2, h)
  change Zlib.Inffast.pull fastLocal h = .ok (fast1, h) at run1
  change Zlib.Inffast.pull fast1 h = .ok (fast2, h) at run2
  rw [bind_app, run1]
  exact run2

/-- A byte written within the separated public output range preserves the
fast loop's synchronized unread-input packet. This permits the following
translated `pull` even when input and output share an allocation. -/
theorem FastInputPacket.output_byte {h : Heap} {slow : IL}
    {bs : List UInt8} {fastLocal : Zlib.Inffast.L}
    (packet : FastInputPacket h slow bs fastLocal)
    (separate : Separate slow.next slow.have_.toNat
      slow.put slow.left.toNat)
    (left : slow.left ≠ 0)
    {dest : BRef} {array : Array UInt8} {oo j : Nat}
    (outputPtr : slow.put = .ref dest oo)
    (outputGet : Space.get h dest = some array)
    (outputWrite : Space.ro h dest = false)
    (inside : oo ≤ j ∧ j < oo + slow.left.toNat)
    (value : UInt8) :
    FastInputPacket
      (Space.put h dest (array.set! j value)) slow bs fastLocal := by
  have positions := packet.source.output_positions outputPtr left separate
  have writeSeparated : bs = [] ∨
      ∀ i, slow.next = .ref dest i →
        i + bs.length ≤ j ∨ j + 1 ≤ i := by
    rcases positions with empty | positions
    · exact Or.inl empty
    · right
      intro i ptr
      rcases positions i ptr with before | after
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
  exact ⟨packet.source.store_byte outputGet outputWrite value
      writeSeparated, packet.cursor, packet.hold, packet.bits⟩

/-- The actual translated output store implements the packet-preserving
array update for every writable public byte view. -/
theorem FastInputPacket.store8_output {h : Heap} {slow : IL}
    {bs : List UInt8} {fastLocal : Zlib.Inffast.L}
    (packet : FastInputPacket h slow bs fastLocal)
    (separate : Separate slow.next slow.have_.toNat
      slow.put slow.left.toNat)
    (left : slow.left ≠ 0)
    {dest : BRef} {array : Array UInt8} {oo j : Nat}
    (outputPtr : slow.put = .ref dest oo)
    (outputGet : Space.get h dest = some array)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ array.size)
    (inside : oo ≤ j ∧ j < oo + slow.left.toNat)
    (value : UInt8) :
    let after := Space.put h dest (array.set! j value)
    C.run (store8 (.ref dest j) value) h = .ok ((), after) ∧
      FastInputPacket after slow bs fastLocal := by
  have bound : j < array.size := by omega
  have written := Ptr.store_ok outputGet outputWrite bound (v := value)
  exact ⟨written,
    packet.output_byte separate left outputPtr outputGet
      outputWrite inside value⟩

/-- A translated output store followed immediately by a translated fast
input read is safe and bitstream-preserving on shared or separate storage. -/
theorem FastInputPacket.store8_then_pull {h : Heap} {slow : IL}
    {b : UInt8} {bs : List UInt8} {fastLocal : Zlib.Inffast.L}
    (packet : FastInputPacket h slow (b :: bs) fastLocal)
    (small : slow.bits.toNat ≤ 22)
    (separate : Separate slow.next slow.have_.toNat
      slow.put slow.left.toNat)
    (left : slow.left ≠ 0)
    {dest : BRef} {array : Array UInt8} {oo j : Nat}
    (outputPtr : slow.put = .ref dest oo)
    (outputGet : Space.get h dest = some array)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ array.size)
    (inside : oo ≤ j ∧ j < oo + slow.left.toNat)
    (value : UInt8) :
    ∃ after fastNext slowNext,
      C.run (do
        store8 (.ref dest j) value
        Zlib.Inffast.pull fastLocal) h = .ok (fastNext, after) ∧
      FastInputPacket after slowNext bs fastNext ∧
      stream slowNext bs = stream slow (b :: bs) := by
  let after := Space.put h dest (array.set! j value)
  have ⟨written, current⟩ :=
    packet.store8_output separate left outputPtr outputGet
      outputWrite outputSize inside value
  obtain ⟨next, fastNext, slowNext, read, _, _, _, finalPacket,
      sameStream⟩ := current.pull small
  refine ⟨after, fastNext, slowNext, ?_, finalPacket, sameStream⟩
  change (store8 (.ref dest j) value >>= fun _ =>
    Zlib.Inffast.pull fastLocal) h = .ok (fastNext, after)
  change store8 (.ref dest j) value h = .ok ((), after) at written
  change Zlib.Inffast.pull fastLocal after = .ok (fastNext, after) at read
  rw [bind_app, written]
  exact read

/-- One actual fast back-reference copy reads its source before writing the
destination. Its byte-view proof permits source and destination in the same
object and retains the separate caller input packet. -/
theorem FastInputPacket.copy1_view {h : Heap} {slow : IL}
    {bs : List UInt8} {fastLocal : Zlib.Inffast.L}
    (packet : FastInputPacket h slow bs fastLocal)
    (separate : Separate slow.next slow.have_.toNat
      slow.put slow.left.toNat)
    (left : slow.left ≠ 0)
    {source : BRef} {saved : Array UInt8} {sourceOff : Nat}
    (fromPtr : fastLocal.from_ = .ref source sourceOff)
    (sourceGet : Space.get h source = some saved)
    (sourceBound : sourceOff < saved.size)
    {dest : BRef} {array : Array UInt8} {oo j : Nat}
    (outPtr : fastLocal.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (outputGet : Space.get h dest = some array)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ array.size)
    (inside : oo ≤ j ∧ j < oo + slow.left.toNat) :
    let after := Space.put h dest
      (array.set! j saved[sourceOff])
    let fastNext := { fastLocal with
      from_ := .ref source (sourceOff + 1),
      out := .ref dest (j + 1) }
    C.run (Zlib.Inffast.copy1 fastLocal) h =
      .ok (fastNext, after) ∧
    FastInputPacket after slow bs fastNext := by
  have outputBound : j < array.size := by omega
  have sourceAdvance := Ptr.add_nat_ok (h := h) (r := source)
    (a := saved) (off := sourceOff) (n := 1) sourceGet
    (by omega)
  have stored := Ptr.store_ok outputGet outputWrite outputBound
    (v := saved[sourceOff])
  have afterGet : Space.get
      (Space.put h dest (array.set! j saved[sourceOff])) dest =
      some (array.set! j saved[sourceOff]) :=
    byte_view_get_put outputGet outputWrite _
  have outputAdvance := Ptr.add_nat_ok
    (h := Space.put h dest (array.set! j saved[sourceOff]))
    (r := dest) (a := array.set! j saved[sourceOff])
    (off := j) (n := 1) afterGet
    (by simpa using (show j + 1 ≤ array.size by omega))
  let after := Space.put h dest (array.set! j saved[sourceOff])
  let fastNext : Zlib.Inffast.L := { fastLocal with
    from_ := .ref source (sourceOff + 1),
    out := .ref dest (j + 1) }
  have run : C.run (Zlib.Inffast.copy1 fastLocal) h =
      .ok (fastNext, after) := by
    change Zlib.Inffast.copy1 fastLocal h = _
    change (Ptr.ref source sourceOff).add 1 h =
      .ok (.ref source (sourceOff + 1), h) at sourceAdvance
    change (Ptr.ref dest j).add 1 after =
      .ok (.ref dest (j + 1), after) at outputAdvance
    unfold Zlib.Inffast.copy1
    rw [fromPtr, outPtr,
      bind_ok (Ptr.load_ok sourceGet sourceBound),
      bind_ok sourceAdvance, bind_ok stored, bind_ok outputAdvance]
    rfl
  have nextPacket := packet.output_byte separate left outputPtr
    outputGet outputWrite inside saved[sourceOff]
  refine ⟨run, ?_⟩
  exact ⟨nextPacket.source, nextPacket.cursor,
    nextPacket.hold, nextPacket.bits⟩

/-- The mode's actual RESTORE macro uses the same checked writeback prefix. -/
theorem RESTORE_pending_run {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (E : Env c h r zs z s) :
    runX (RESTORE c.strm c.st) l h =
      .ok ((.ok (), l), setI (r.put h (leaveStream z l)) zs (leaveState s l)) := by
  unfold RESTORE
  rw [runX_bind, runX_get]
  simp only []
  have write : wrZ c.strm (fun z => { z with next_out := l.put, avail_out := l.left, next_in := l.next, avail_in := l.have_ }) h = .ok ((), r.put h (leaveStream z l)) := by
    rw [E.strm, wrZ_eq, E.hz]
    rfl
  rw [runX_bind, runX_lift_ok write]
  simp only []
  have env : Env c (r.put h (leaveStream z l)) r zs (leaveStream z l) s :=
    ⟨E.strm, E.st, ZStreamRef.get_put_same E.hz _, by simpa using E.hs⟩
  rw [runX_wrS env]
  rfl

/-- Establish every existing fast-callee premise from the actual dispatch
packet after RESTORE. This internal producer covers distinct raw byte
blocks. Shared-allocation slices and other caller byte views remain the
separate general-interface obligation; no public domain is changed. -/
theorem inflate_fast_raw_entry {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {bs : List UInt8} {ib io ob oo : Nat}
    (E : Env c h r zs z s) (good : Good h r zs z s)
    (fit : ZlibF.PlatformMemory.ByteObjectsFit h) (tables : DataTablesSafe h s)
    (buffers : DispatchBuffers h r l bs) (pending : DataPendingInvariant s)
    (input : l.next = .ref (.blk ib) io) (output : l.put = .ref (.blk ob) oo)
    (different : ib ≠ ob) (fast : (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    ∃ entry : Zlib.Inffast.Spec.PlatformEntry,
      entry.h0 = setI (r.put h (leaveStream z l)) zs (leaveState s l) ∧
      entry.strm = c.strm ∧ entry.start = l.out_ ∧ entry.r = r ∧ entry.stid = zs ∧
      entry.sm0 = leaveStream z l ∧ entry.s0 = leaveState s l ∧
      entry.ib = ib ∧ entry.i0 = io ∧ entry.ob = ob ∧ entry.o0 = oo := by
  have margins : (6 ≤ l.have_ ∧ 258 ≤ l.left) ∧ l.bits < 8 := by
    simpa only [Bool.and_eq_true, decide_eq_true_eq] using fast
  have inputRoom : 6 ≤ l.have_.toNat := by simpa [UInt32.le_iff_toNat_le] using margins.1.1
  have outputRoom : 258 ≤ l.left.toNat := by simpa [UInt32.le_iff_toNat_le] using margins.1.2
  have bits : l.bits.toNat < 8 := by simpa [UInt32.lt_iff_toNat_lt] using margins.2
  have nonempty : bs ≠ [] := by intro empty; have := buffers.bits.have_eq; rw [empty] at this; simp at this; omega
  obtain ⟨inref, ina, inoff, inptr, inget, insize, _⟩ := buffers.bits.next.resolve_left nonempty
  have sameInput : inref = .blk ib ∧ inoff = io := by rw [input] at inptr; cases inptr; exact ⟨rfl, rfl⟩
  rcases sameInput with ⟨refEq, offEq⟩
  subst inref
  subst inoff
  obtain ⟨outref, outa, outoff, outptr, outget, outwrite, outsize, _, made, privateWindow⟩ :=
    callerRange_slow_output good l buffers.output.range buffers.output.nonnull buffers.output.count buffers.output.produced
  have sameOutput : outref = .blk ob ∧ outoff = oo := by rw [output] at outptr; cases outptr; exact ⟨rfl, rfl⟩
  rcases sameOutput with ⟨refEq, offEq⟩
  subst outref
  subst outoff
  let stream0 := leaveStream z l
  let state0 := leaveState s l
  let heap0 := setI (r.put h stream0) zs state0
  obtain ⟨good0, _, _, sizes0⟩ := leave_restore_invariant E good pending buffers.bits (by omega)
  have fit0 : ZlibF.PlatformMemory.ByteObjectsFit heap0 := sizes0.platform fit
  obtain ⟨lr, lo, la, lp, lg, ls⟩ := tables.lengthTable
  obtain ⟨dr, doff, da, dp, dg, ds⟩ := tables.distanceTable
  have codeViews : ∀ ref : CodeRef,
      (Space.get heap0 ref : Option (Array Code)) = Space.get h ref := by
    intro ref
    unfold heap0 state0 leaveState
    rw [code_views_set_bits (by simpa using E.hs), code_views_put_stream]
  have window : ∃ (wb : Nat) (wa : Array UInt8),
      state0.whave ≠ 0 → state0.window = .ref (.blk wb) 0 ∧ wb ≠ ob ∧
        heap0.bytes wb = some wa ∧ state0.wsize.toNat ≤ wa.size := by
    rcases good.inv.win.block with null | ⟨wb, wa, ptr, get, ro, size⟩
    · refine ⟨0, #[], ?_⟩
      intro live
      have zero := good.inv.win.nullws null
      have whave := good.inv.win.hv
      have : s.whave = 0 := UInt32.toNat_inj.mp (by rw [zero] at whave; simpa using whave)
      exact False.elim (live this)
    · refine ⟨wb, wa, ?_⟩
      intro _
      refine ⟨ptr, fun eq => privateWindow wb ptr (by rw [eq]), by simpa [heap0] using get, ?_⟩
      have := good.inv.win.ws
      change s.wsize.toNat ≤ wa.size
      rw [size]
      omega
  obtain ⟨wb, wa, win⟩ := window
  have wsize : s.wsize.toNat ≤ 32768 := by
    have pow := Nat.pow_le_pow_right (by decide : 0 < 2) good.inv.win.wbits
    have := good.inv.win.ws
    omega
  let entry : Zlib.Inffast.Spec.PlatformEntry := {
    h0 := heap0, platform := fit0, strm := c.strm, start := l.out_, r, sm0 := stream0, stid := zs, s0 := state0
    hstrm := E.strm, hsm := good0.live.hz, hrw := by cases r <;> rfl, hstate := good0.live.zst, hs0 := good0.live.hs
    ib, i0 := io, IN := ina, hnin := input, hIN := by simpa [heap0] using inget
    hai := inputRoom, hINsz := by change io + l.have_.toNat ≤ ina.size; rw [buffers.bits.have_eq]; exact insize
    ob, o0 := oo, A0 := outa, hnout := output, hA0 := by simpa [heap0] using outget
    hro := by simpa [heap0] using outwrite, hao := outputRoom, hAsz := outsize
    hstart := buffers.output.count, hbeg := made, hsep := different
    hbits := bits, hhold := buffers.bits.hold_lt, hsane := by change s.sane ≠ 0; rw [pending.sane]; decide
    hws := wsize, hwh := good.inv.win.hv, hwn := by change s.wnext.toNat ≤ s.wsize.toNat; have := good.inv.win.wn; omega
    wb, woff := 0, W := wa, hwin := by simpa using win
    rl := lr, ol := lo, LCA := la, hlc := lp, hLCA := by rw [codeViews]; exact lg, hlt := ls
    rd := dr, od := doff, DCA := da, hdc := dp, hDCA := by rw [codeViews]; exact dg, hdt := ds }
  exact ⟨entry, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Actual source continuation after the fast callee returns. -/
def inflateAfterFast (c : Ctx) : X Unit := do
  LOAD c.strm c.st
  if (← rdS c.st (·.mode)) == TYPE then wrS c.st fun s => { s with back := -1 }
  return

/-- The actual fast branch reaches LOAD on the exact heap returned by the
proved translated callee. Every callee entry fact is produced above from
this dispatch state; only the documented internal raw-buffer case is used. -/
theorem inflate_LEN_fast_raw_cut_progress {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {bs : List UInt8} {ib io ob oo : Nat}
    (E : Env c h r zs z s) (good : Good h r zs z s)
    (fit : ZlibF.PlatformMemory.ByteObjectsFit h) (tables : DataTablesSafe h s)
    (buffers : DispatchBuffers h r l bs) (pending : DataPendingInvariant s)
    (input : l.next = .ref (.blk ib) io) (output : l.put = .ref (.blk ob) oo)
    (different : ib ≠ ob) (fast : (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    ∃ (entry : Zlib.Inffast.Spec.PlatformEntry) (after : Heap),
      runX (inflate_LEN c) l h = runX (inflateAfterFast c) l after ∧
      Zlib.Inffast.Spec.FastPost entry.toEnv after ∧ ZlibF.PlatformMemory.ByteObjectsFit after ∧
      entry.strm = c.strm ∧ entry.r = r ∧ entry.stid = zs ∧ entry.s0 = leaveState s l ∧ entry.sm0 = leaveStream z l ∧
      entry.h0 = setI (r.put h (leaveStream z l)) zs (leaveState s l) ∧ entry.ob = ob ∧ Zlib.Inffast.Proofs.FastProgress entry.toEnv after := by
  obtain ⟨entry, heapEq, streamEq, startEq, refEq, stateId, stream0, state0, _, _, outBlock, _⟩ :=
    inflate_fast_raw_entry E good fit tables buffers pending input output different fast
  obtain ⟨after, call, post, progress⟩ := Zlib.Inffast.Proofs.inflate_fast_safe_progress entry.toEnv
  change C.run (Zlib.Inffast.inflate_fast entry.strm entry.start) entry.h0 = .ok ((), after) at call
  have platform := Zlib.Inffast.Proofs.PlatformEntry.fit_after entry post
  have execution : Zlib.Inffast.inflate_fast c.strm l.out_
      (setI (r.put h (leaveStream z l)) zs (leaveState s l)) = .ok ((), after) := by
    simpa only [C.run, heapEq, streamEq, startEq] using call
  refine ⟨entry, after, ?_, post, platform, streamEq, refEq, stateId, state0, stream0, heapEq, outBlock, progress⟩
  unfold inflate_LEN
  rw [runX_bind, runX_get]
  simp only [fast, ↓reduceIte]
  rw [runX_bind, RESTORE_pending_run E]
  simp only []
  rw [runX_bind, runX_lift_ok execution]
  rfl

/-- Projection retaining the original actual fast-call source cut. -/
theorem inflate_LEN_fast_raw_cut {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {bs : List UInt8} {ib io ob oo : Nat}
    (E : Env c h r zs z s) (good : Good h r zs z s)
    (fit : ZlibF.PlatformMemory.ByteObjectsFit h) (tables : DataTablesSafe h s)
    (buffers : DispatchBuffers h r l bs) (pending : DataPendingInvariant s)
    (input : l.next = .ref (.blk ib) io) (output : l.put = .ref (.blk ob) oo)
    (different : ib ≠ ob) (fast : (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    ∃ (entry : Zlib.Inffast.Spec.PlatformEntry) (after : Heap),
      runX (inflate_LEN c) l h = runX (inflateAfterFast c) l after ∧
      Zlib.Inffast.Spec.FastPost entry.toEnv after ∧ ZlibF.PlatformMemory.ByteObjectsFit after ∧
      entry.strm = c.strm ∧ entry.r = r ∧ entry.stid = zs ∧ entry.s0 = leaveState s l ∧ entry.sm0 = leaveStream z l ∧
      entry.h0 = setI (r.put h (leaveStream z l)) zs (leaveState s l) ∧ entry.ob = ob := by
  obtain ⟨entry, after, run, post, fit, strm, ref, id, state, stream, heap, out, _⟩ :=
    inflate_LEN_fast_raw_cut_progress E good fit tables buffers pending input output different fast
  exact ⟨entry, after, run, post, fit, strm, ref, id, state, stream, heap, out⟩

/-- LOAD and the final TYPE back-counter write execute on a live fast
result. This is the actual source suffix, with its exact state update. -/
theorem inflateAfterFast_run {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (E : Env c h r zs z s) :
    runX (inflateAfterFast c) l h = .ok ((.ok (),
      { l with put := z.next_out, left := z.avail_out, next := z.next_in, have_ := z.avail_in, hold := s.hold, bits := s.bits }),
      if s.mode = TYPE then setI h zs { s with back := -1 } else h) := by
  unfold inflateAfterFast
  rw [runX_bind, LOAD_run E]
  simp only []
  rw [runX_bind, runX_rdS E]
  by_cases type : s.mode = TYPE
  · simp only [type, beq_self_eq_true, ↓reduceIte]
    rw [runX_bind, runX_wrS E]
    simp only [type, runX_pure]
  · simp only [beq_iff_eq, type, ↓reduceIte]
    rfl

/-- A concrete fast postcondition supplies the live records used by LOAD.
No specification of the fast callee is assumed to obtain that postcondition
in the mode theorem below. -/
theorem fastPost_environment (e : Zlib.Inffast.Proofs.Env) {after : Heap}
    (post : Zlib.Inffast.Spec.FastPost e after) {c : Ctx}
    (strm : c.strm = e.strm) (state : c.st = some (.tab e.stid)) :
    ∃ z s, Env c after e.r e.stid z s := by
  obtain ⟨used, made, buffered, bytes, msg, mode, bits, hold, _, _, _, _, _, _, heapEq, _, _, _⟩ := post
  let z := { e.sm0 with next_in := .ref (.blk e.ib) (e.i0 + used), next_out := .ref (.blk e.ob) (e.o0 + made), avail_in := UInt32.ofNat (e.sm0.avail_in.toNat - used), avail_out := UInt32.ofNat (e.sm0.avail_out.toNat - made), msg }
  let s := { e.s0 with mode, bits, hold }
  have baseGet : e.r.get { e.h0 with bytes := upd e.h0.bytes e.ob (some bytes), istates := upd e.h0.istates e.stid (some s) } = some e.sm0 := by
    cases refEq : e.r with
    | tab i => simpa only [refEq, ZStreamRef.get] using e.hsm
    | in_gzstate_strm i => simpa only [refEq, ZStreamRef.get] using e.hsm
  refine ⟨z, s, ⟨strm.trans e.hstrm, state, ?_, ?_⟩⟩
  · rw [heapEq, ZStreamRef.get_put, baseGet]
    rfl
  · rw [heapEq, ZStreamRef.put_istates, upd_same]

/-- The complete actual fast LEN branch returns in the distinct-raw-buffer
case. Its caller premises are all established by the dispatch packet.
Transport of the common post-invariant and the broader caller-view cases
remain separate obligations. -/
theorem inflate_LEN_fast_raw_run {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {bs : List UInt8} {ib io ob oo : Nat}
    (E : Env c h r zs z s) (good : Good h r zs z s)
    (fit : ZlibF.PlatformMemory.ByteObjectsFit h) (tables : DataTablesSafe h s)
    (buffers : DispatchBuffers h r l bs) (pending : DataPendingInvariant s)
    (input : l.next = .ref (.blk ib) io) (output : l.put = .ref (.blk ob) oo)
    (different : ib ≠ ob) (fast : (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    ∃ regs after, runX (inflate_LEN c) l h = .ok ((.ok (), regs), after) := by
  obtain ⟨entry, heap1, cut, post, _, strmEq, refEq, idEq, _, _, _, _⟩ :=
    inflate_LEN_fast_raw_cut E good fit tables buffers pending input output different fast
  have contextState : c.st = some (.tab entry.toEnv.stid) := by change c.st = some (.tab entry.stid); rw [E.st, idEq]
  obtain ⟨stream1, state1, env1⟩ := fastPost_environment entry.toEnv post (by change c.strm = entry.strm; exact strmEq.symm) contextState
  rw [cut, inflateAfterFast_run env1]
  exact ⟨_, _, rfl⟩

/-- The fast entry heap keeps the length-table leaves of the decoder state. -/
theorem leaveEntry_leaves {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState} {l : IL}
    (state : h.istates zs = some s) (tables : DataTablesSafe h s) :
    ∀ ref offset ca, (leaveState s l).lencode = .ref ref offset →
      Space.get (setI (r.put h (leaveStream z l)) zs (leaveState s l)) ref = some ca →
      Zlib.Inffast.Spec.LenLeavesPositive ca offset (leaveState s l).lenbits.toNat :=
  tables.lengthLeaves_frame rfl rfl (fun ref _ _ => by
    have current : (r.put h (leaveStream z l)).istates zs = some s := by simpa using state
    unfold leaveState
    rw [code_views_set_bits current, code_views_put_stream])

/-- Retain the common scalar/table state on the exact heap described by a
proved fast execution. This is a heap-transport lemma, not a callee
specification assumed by the enclosing mode proof. -/
theorem fastPost_retained (e : Zlib.Inffast.Proofs.Env) {after : Heap}
    (good : Good e.h0 e.r e.stid e.sm0 e.s0) (pending : DataPendingInvariant e.s0)
    (leaves : ∀ ref offset ca, e.s0.lencode = .ref ref offset → Space.get e.h0 ref = some ca →
      Zlib.Inffast.Spec.LenLeavesPositive ca offset e.s0.lenbits.toNat)
    (unowned : ∀ w, e.s0.window = .ref (.blk w) 0 → e.ob ≠ w)
    (post : Zlib.Inffast.Spec.FastPost e after) :
    ∃ z s, Good after e.r e.stid z s ∧ DataTableInvariant after s ∧ DataPendingInvariant s ∧
      s.hold.toNat < 2 ^ s.bits.toNat ∧ s.bits.toNat < 8 ∧ s.window = e.s0.window := by
  obtain ⟨used, made, buffered, bytes, msg, mode, bits, hold, _, _, _, size, bitCount,
    held, heapEq, _, classification, _⟩ := post
  let stream := { e.sm0 with next_in := .ref (.blk e.ib) (e.i0 + used), next_out := .ref (.blk e.ob) (e.o0 + made), avail_in := UInt32.ofNat (e.sm0.avail_in.toNat - used), avail_out := UInt32.ofNat (e.sm0.avail_out.toNat - made), msg }
  let state := { e.s0 with mode, bits, hold }
  let written : Heap := { e.h0 with bytes := upd e.h0.bytes e.ob (some bytes) }
  have goodWritten : Good written e.r e.stid e.sm0 e.s0 := by
    have result := good.byte_view_put (dest := .blk e.ob) e.hA0 e.hro (fun w hw => by
      intro equal
      exact unowned w hw (by cases equal; rfl)) bytes
    simpa only [Space.put, Space.ro, e.hro, Bool.false_eq_true, ↓reduceIte] using result
  have modeRange : HEAD ≤ mode ∧ mode ≤ SYNC := by
    rcases classification with same | type | bad
    · rw [same.1]; exact good.live.mode
    · rw [type.1]; decide
    · rw [bad]; decide
  have goodFinal : Good after e.r e.stid stream state := by
    have result := goodWritten.setZI (z' := stream) (st' := state) rfl good.live.zalloc good.live.zfree
      rfl modeRange (goodWritten.inv.of_fields rfl rfl rfl rfl rfl rfl rfl rfl rfl (by exact Nat.le_trans (Nat.le_of_lt bitCount) (by decide)) rfl rfl rfl)
    rw [heapEq]
    change Good (e.r.put (setI written e.stid state) stream) e.r e.stid stream state
    rw [ZStreamRef.put_setI]
    exact result
  have pendingFinal : DataPendingInvariant state := by
    rcases classification with same | type | bad
    · have modeEq : state.mode = e.s0.mode := same.1
      exact ⟨pending.sane, fun m => pending.lenext (modeEq.symm.trans m),
        fun m => pending.dist (modeEq.symm.trans m), fun m => pending.distext (modeEq.symm.trans m),
        fun m => pending.matching (modeEq.symm.trans m)⟩
    · apply dataPendingInvariant_idle (s := state) pending.sane
      change mode ≠ LENEXT ∧ mode ≠ DIST ∧ mode ≠ DISTEXT ∧ mode ≠ MATCH
      rw [type.1]; decide
    · apply dataPendingInvariant_idle (s := state) pending.sane
      change mode ≠ LENEXT ∧ mode ≠ DIST ∧ mode ≠ DISTEXT ∧ mode ≠ MATCH
      rw [bad]; decide
  have views : ∀ ref : CodeRef, (Space.get after ref : Option (Array Code)) = Space.get e.h0 ref := by
    intro ref
    cases ref with
    | istate_codes i =>
      by_cases same : i = e.stid
      · subst i
        simp only [Space.get, goodFinal.live.hs, e.hs0, Option.map_some]
        rfl
      · rw [heapEq]
        simp only [Space.get, ZStreamRef.put_istates, upd_ne _ _ _ _ same]
    | st_lenfix => rw [heapEq]; simp only [Space.get, ZStreamRef.put_static]
    | st_distfix => rw [heapEq]; simp only [Space.get, ZStreamRef.put_static]
  have tablesFinal : DataTableInvariant after state := by
    intro _
    exact ⟨⟨e.rl, e.ol, e.LCA, e.hlc, by rw [views]; exact e.hLCA, e.hlt⟩,
      ⟨e.rd, e.od, e.DCA, e.hdc, by rw [views]; exact e.hDCA, e.hdt⟩,
      fun ref offset ca pointer get => leaves ref offset ca pointer (by rw [views] at get; exact get)⟩
  exact ⟨stream, state, goodFinal, tablesFinal, pendingFinal, held, bitCount, rfl⟩

/-- The actual raw-buffer fast branch now retains the same scalar/table
clauses as the slow data dispatch. Its buffer and progress transport remain
the next composition obligations; broader caller views are still open. -/
theorem inflate_LEN_fast_raw_retained {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {bs : List UInt8} {ib io ob oo : Nat}
    (E : Env c h r zs z s) (good : Good h r zs z s)
    (fit : ZlibF.PlatformMemory.ByteObjectsFit h) (tables : DataTablesSafe h s)
    (buffers : DispatchBuffers h r l bs) (pending : DataPendingInvariant s)
    (input : l.next = .ref (.blk ib) io) (output : l.put = .ref (.blk ob) oo)
    (different : ib ≠ ob) (fast : (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    ∃ regs after stream state, runX (inflate_LEN c) l h = .ok ((.ok (), regs), after) ∧
      Good after r zs stream state ∧ DataTableInvariant after state ∧ DataPendingInvariant state ∧
      state.hold.toNat < 2 ^ state.bits.toNat ∧ state.bits.toNat < 8 := by
  obtain ⟨entry, heap1, cut, post, _, strmEq, refEq, idEq, stateEq, streamEq, heapEq, outputEq⟩ :=
    inflate_LEN_fast_raw_cut E good fit tables buffers pending input output different fast
  have count : l.bits.toNat < 8 := by
    have margins : (6 ≤ l.have_ ∧ 258 ≤ l.left) ∧ l.bits < 8 := by
      simpa only [Bool.and_eq_true, decide_eq_true_eq] using fast
    simpa [UInt32.lt_iff_toNat_lt] using margins.2
  obtain ⟨good0, pending0, _, _⟩ := leave_restore_invariant E good pending buffers.bits (by omega)
  have entryGood : Good entry.toEnv.h0 entry.toEnv.r entry.toEnv.stid entry.toEnv.sm0 entry.toEnv.s0 := by
    change Good entry.h0 entry.r entry.stid entry.sm0 entry.s0
    rw [heapEq, refEq, idEq, streamEq, stateEq]
    exact good0
  have entryPending : DataPendingInvariant entry.toEnv.s0 := by change DataPendingInvariant entry.s0; rw [stateEq]; exact pending0
  have privateWindow := callerRange_private_window good buffers.output.range output
  have window : ∀ w, entry.toEnv.s0.window = .ref (.blk w) 0 → entry.toEnv.ob ≠ w := by
    change ∀ w, entry.s0.window = .ref (.blk w) 0 → entry.ob ≠ w
    rw [stateEq, outputEq]
    intro w win equal
    exact privateWindow w win (by rw [equal])
  obtain ⟨stream1, state1, good1, tables1, pending1, held1, bits1, _⟩ :=
    fastPost_retained entry.toEnv entryGood entryPending (by
      change ∀ ref offset ca, entry.s0.lencode = .ref ref offset → Space.get entry.h0 ref = some ca →
        Zlib.Inffast.Spec.LenLeavesPositive ca offset entry.s0.lenbits.toNat
      rw [stateEq, heapEq]
      exact leaveEntry_leaves good.live.hs tables) window post
  have good1' : Good heap1 r zs stream1 state1 := by change Good heap1 entry.r entry.stid stream1 state1 at good1; simpa only [refEq, idEq] using good1
  have env1 : Env c heap1 r zs stream1 state1 := ⟨E.strm, E.st, good1'.live.hz, good1'.live.hs⟩
  let regs := { l with put := stream1.next_out, left := stream1.avail_out, next := stream1.next_in, have_ := stream1.avail_in, hold := state1.hold, bits := state1.bits }
  by_cases type : state1.mode = TYPE
  · let state2 := { state1 with back := -1 }
    have good2 := good1'.decode_update (after := state2) (by rfl) (by exact good1'.live.mode)
    have pending2 : DataPendingInvariant state2 := by
      apply dataPendingInvariant_idle (s := state2) pending1.sane
      change state1.mode ≠ LENEXT ∧ state1.mode ≠ DIST ∧ state1.mode ≠ DISTEXT ∧ state1.mode ≠ MATCH
      rw [type]; decide
    have tables2 : DataTableInvariant (setI heap1 zs state2) state2 := by
      intro active
      change DataTableMode state1.mode at active
      rw [type] at active
      exact False.elim ((by unfold DataTableMode; decide : ¬ DataTableMode TYPE) active)
    refine ⟨regs, setI heap1 zs state2, stream1, state2, ?_, good2, tables2, pending2, held1, bits1⟩
    rw [cut, inflateAfterFast_run env1]
    simp only [state2, type, ↓reduceIte, regs]
  · refine ⟨regs, heap1, stream1, state1, ?_, good1', tables1, pending1, held1, bits1⟩
    rw [cut, inflateAfterFast_run env1]
    simp only [type, ↓reduceIte, regs]

end Zlib.Inflate.Proofs
