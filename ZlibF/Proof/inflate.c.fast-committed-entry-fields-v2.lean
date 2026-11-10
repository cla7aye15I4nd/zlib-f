import ZlibF.Proof.«inflate.c.fast-committed-entry»
import ZlibF.Proof.«inflate.c.fast-future-generic-entry»
import ZlibF.Proof.«inflate.c.global-pair-length-flags»
import ZlibF.Math.InflateCommittedTokens

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public ZlibF.Spec
open Zlib.Inffast.Spec Zlib.Inftrees
open Zlib.Inftrees.Spec.DecodeTableInvariant
open Zlib.Inftrees.Spec.DecodeTableStability
open ZlibF.Math.LZ77Copy ZlibF.Math.InflateCommittedTokens
set_option autoImplicit false
set_option maxRecDepth 10000

/-- The translated fast prelude initializes the causal word loop from
actual installed tables, caller byte views, and retained window. No future
source or expected decoded target is supplied. -/
theorem fastEntryPrefix_committed_general_v2
    {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState}
    {slow : IL} {bs : List UInt8}
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow bs)
    (mode : DataTableMode s.mode)
    (inputCursor : z.next_in = slow.next)
    (inputCount : z.avail_in = slow.have_)
    (outputCursor : z.next_out = slow.put)
    (outputCount : z.avail_out = slow.left)
    (stateHold : s.hold = slow.hold)
    (stateBits : s.bits = slow.bits)
    {L D : List Nat} {dict past current : List UInt8}
    (tables : FunctionalEpoch.InstalledTables h s L D)
    (flags : FunctionalEpoch.InstalledQueryFlags h s)
    (dictionary : InflateDictionary h s
      ((dict ++ past).drop ((dict ++ past).length - 32768)))
    (historyView : ∀ dest oo output,
      slow.put = .ref dest oo → Space.get h dest = some output →
      writtenBytes output oo (slow.out_.toNat - slow.left.toNat) = current)
    (fast : (slow.have_ >= 6 && slow.left >= 258 &&
      slow.bits < 8) = true) :
    ∃ (ctx : FastLoopContext) (q : Zlib.Inffast.L)
      (p : FastCommittedLoop.Parameters ctx),
      C.run (fastEntryPrefix (some r) slow.out_) h =
        .ok ((ctx.c, q), h) ∧
      Nonempty (FastCommittedLoop.WordReady p h q) ∧
      p.L = L ∧ p.D = D ∧ p.dict = dict ∧ p.past = past ∧
      p.start = past ++ current ∧ p.initialWords = [] ∧
      p.input = bs ∧ p.entry = q ∧
      ctx.r = r ∧ ctx.zs = zs ∧ ctx.z = z ∧ ctx.s = s ∧
      slow.put = .ref ctx.dest ctx.oo ∧
      ctx.leftTotal = slow.left ∧ ctx.outTotal = slow.out_ ∧
      q.in_ = slow.next ∧ q.bits = slow.bits ∧ q.hold = slow.hold := by
  obtain ⟨ir, dest, io, oo, nextPtr, putPtr, prefixRun⟩ :=
    fastEntryPrefix_run invariant.good invariant.platform buffers
      (invariant.tables mode) inputCursor inputCount outputCursor
      outputCount stateHold stateBits fast
  obtain ⟨lr, lo, lc, lptr, lget, lsafe⟩ :=
    (invariant.tables mode).lengthTable
  obtain ⟨dr, doff, dc, dptr, dget, dsafe⟩ :=
    (invariant.tables mode).distanceTable
  have margins : (6 ≤ slow.have_ ∧ 258 ≤ slow.left) ∧
      slow.bits < 8 := by
    simpa only [Bool.and_eq_true, decide_eq_true_eq] using fast
  have inputMargin : 6 ≤ slow.have_.toNat := by
    simpa [UInt32.le_iff_toNat_le] using margins.1.1
  have outputMargin : 258 ≤ slow.left.toNat := by
    simpa [UInt32.le_iff_toNat_le] using margins.1.2
  have bitsBound : slow.bits.toNat ≤ 30 := by
    have small : slow.bits.toNat < 8 := by
      simpa [UInt32.lt_iff_toNat_lt] using margins.2
    omega
  let bg := oo - (slow.out_.toNat - slow.left.toNat)
  let c0 : Zlib.Inffast.Ctx := {
    strm := some r, state := some (.tab zs),
    last := .ref ir (io + slow.have_.toNat - 5),
    beg := .ref dest bg,
    end_ := .ref dest (oo + slow.left.toNat - 257),
    wsize := s.wsize, whave := s.whave,
    wnext := s.wnext, window := s.window,
    lcode := s.lencode, dcode := s.distcode,
    lmask := ((1 : UInt32) <<< s.lenbits) - 1,
    dmask := ((1 : UInt32) <<< s.distbits) - 1 }
  let q0 : Zlib.Inffast.L := {
    in_ := slow.next, out := slow.put,
    hold := slow.hold, bits := slow.bits,
    here := default, op := 0, len := 0, dist := 0,
    from_ := default, broke := false,
    againL := false, againD := false }
  let ctx : FastLoopContext := {
    c := c0, r, zs, z, s,
    codeRef := lr, codes := lc, baseOff := lo,
    rootWidth := s.lenbits.toNat,
    distRef := dr, distCodes := dc, distOff := doff,
    distWidth := s.distbits.toNat,
    dest, inputRef := ir, oo, bg,
    leftTotal := slow.left, outTotal := slow.out_,
    streamPtr := rfl, statePtr := rfl, mode,
    whaveEq := rfl, wsizeEq := rfl, wnextEq := rfl,
    windowEq := rfl,
    lcodePtr := lptr, lenSafe := lsafe,
    lenMask := by
      change ((((1 : UInt32) <<< s.lenbits) - 1).toUInt64.toNat) =
        2 ^ s.lenbits.toNat - 1
      rw [UInt32.toNat_toUInt64]
      exact Zlib.Inffast.Proofs.u32_shl1_sub1 (by
        have width := lsafe.1
        omega),
    dcodePtr := dptr, distSafe := dsafe,
    distMask := by
      change ((((1 : UInt32) <<< s.distbits) - 1).toUInt64.toNat) =
        2 ^ s.distbits.toNat - 1
      rw [UInt32.toNat_toUInt64]
      exact Zlib.Inffast.Proofs.u32_shl1_sub1 (by
        have width := dsafe.1
        omega),
    leftNonzero := by
      intro zero
      rw [zero] at outputMargin
      simp at outputMargin,
    avail := outputMargin,
    begPtr := rfl, endPtr := rfl,
    count := buffers.output.count,
    made := buffers.output.produced dest oo putPtr,
    beginEq := rfl }
  have packet : FastInputPacket h slow bs q0 :=
    ⟨buffers.bits, rfl, rfl, rfl⟩
  have safety : FastLoopReady ctx h q0 :=
    FastLoopReady.initial packet invariant buffers lget dget
      rfl rfl putPtr nextPtr rfl inputMargin bitsBound rfl
  have lenMeaning : ∃ used, Inv LENS lc lo s.lenbits.toNat used L := by
    obtain ⟨ref, offset, array, used, pointer, get, meaning, stable⟩ := tables.1
    have samePointer := pointer.symm.trans lptr
    cases samePointer
    have sameArray : array = lc := Option.some.inj (get.symm.trans lget)
    subst array
    exact ⟨used, meaning⟩
  have lenStable : StableQuery LENS lc lo s.lenbits.toNat := by
    obtain ⟨ref, offset, array, used, pointer, get, meaning, stable⟩ := tables.1
    have samePointer := pointer.symm.trans lptr
    cases samePointer
    have sameArray : array = lc := Option.some.inj (get.symm.trans lget)
    subst array
    exact stable
  have distMeaning : ∃ used, Inv DISTS dc doff s.distbits.toNat used D := by
    obtain ⟨ref, offset, array, used, pointer, get, meaning, stable⟩ := tables.2
    have samePointer := pointer.symm.trans dptr
    cases samePointer
    have sameArray : array = dc := Option.some.inj (get.symm.trans dget)
    subst array
    exact ⟨used, meaning⟩
  have lenFlags : Zlib.Inftrees.Spec.FastTableFlags.QueryCompatible
      LENS lc lo s.lenbits.toNat := by
    obtain ⟨ref, offset, array, pointer, get, compatible⟩ := flags.1
    have samePointer := pointer.symm.trans lptr
    cases samePointer
    have sameArray : array = lc := Option.some.inj (get.symm.trans lget)
    subst array
    exact compatible
  have distFlags : Zlib.Inftrees.Spec.FastTableFlags.QueryCompatible
      DISTS dc doff s.distbits.toNat := by
    obtain ⟨ref, offset, array, pointer, get, compatible⟩ := flags.2
    have samePointer := pointer.symm.trans dptr
    cases samePointer
    have sameArray : array = dc := Option.some.inj (get.symm.trans dget)
    subst array
    exact compatible
  obtain ⟨saved, woff, windowData, savedEq, dictCount⟩ :=
    fast_saved_of_dictionary invariant.good buffers.output.range
      putPtr dictionary
  let p : FastCommittedLoop.Parameters ctx := {
    L, D, dict, past, start := past ++ current, initialWords := [],
    entry := q0, input := bs, startOff := io,
    saved, woff, lmeaning := lenMeaning, lstable := lenStable,
    lflags := lenFlags, dmeaning := distMeaning,
    dflags := distFlags, dictionary := savedEq,
    dictCount := dictCount, rawMargin := by rw [← buffers.bits.have_eq]; exact inputMargin,
    initialLast := by rw [← buffers.bits.have_eq] }
  have observed : ∀ j output,
      q0.out = .ref ctx.dest j → Space.get h ctx.dest = some output →
      writtenBytes output j (j - ctx.bg) = current := by
    intro j output out get
    have jEq : j = oo := (Ptr.ref.inj (putPtr.symm.trans out)).2.symm
    subst j
    have count := buffers.output.produced dest oo putPtr
    have span : oo - ctx.bg = slow.out_.toNat - slow.left.toNat := by
      dsimp only [ctx, bg]
      omega
    simpa only [span] using historyView dest oo output putPtr get
  have windowObserved : ctx.c.whave ≠ 0 →
      ∃ window, window ≠ ctx.dest ∧ ctx.c.window = .ref window p.woff ∧
        Space.get h window = some p.saved ∧
        p.woff + ctx.c.wsize.toNat ≤ p.saved.size := by
    intro nonzero
    have positive : 0 < s.whave.toNat := by
      by_cases positive : 0 < s.whave.toNat
      · exact positive
      · have zero : s.whave = 0 := UInt32.toNat_inj.mp (by simp only [UInt32.toNat_zero]; omega)
        exact False.elim (nonzero zero)
    exact windowData positive
  have committed : Committed L D dict (past ++ current) [] (past ++ current) :=
    Committed.initial L D dict (past ++ current)
  have ready := FastCommittedLoop.WordReady.initial
    (p := p) safety packet (by simpa only [q0] using nextPtr) current observed committed windowObserved
  rcases ready with ⟨wordReady⟩
  exact ⟨ctx, q0, p, prefixRun, ⟨wordReady⟩,
    rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    putPtr, rfl, rfl, rfl, rfl, rfl⟩

#print axioms fastEntryPrefix_committed_general_v2
end Zlib.Inflate.Proofs
