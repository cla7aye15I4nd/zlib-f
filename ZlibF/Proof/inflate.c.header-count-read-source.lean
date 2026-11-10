import ZlibF.Proof.«inflate.c.header-actual-table-classifier»
import ZlibF.Proof.«inflate.c.header-actual-prefix-history»
namespace Zlib.Inflate.Proofs.ActualHeader
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs
set_option autoImplicit false
set_option maxHeartbeats 1500000

/-- The actual three count reads, indexed by the accumulated LENLENS word
and current caller buffer. No completed alphabet or Header is asserted. -/
structure CountReadSource (s : InflateState) (received : List Bool) (bs : List UInt8) where
  body : List Bool
  r1 : List Bool
  r2 : List Bool
  hlit : Nat
  hdist : Nat
  hclen : Nat
  first : readBits 5 body = some (hlit, r1)
  second : readBits 5 r1 = some (hdist, r2)
  third : readBits 4 r2 = some (hclen, received ++ bytesBits bs)
  counts : DynamicCountsOK hlit hdist
  literalCount : s.nlen.toNat = hlit + 257
  distanceCount : s.ndist.toNat = hdist + 1
  codeCount : s.ncode.toNat = hclen + 4

/-- The actual accepted TABLE count branch supplies the initial causal
count record. Bounds come from the produced initialized private state. -/
theorem table_count_read_source
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8}
    (observation : TableBranchObservation c h r zs z s l bs)
    (normal : observation.outcome = .ok ()) :
    (∃ i, strTable[i]? = some "too many length or distance symbols" ∧
      runX (inflate_TABLE c) l h = .ok ((.ok (), tableRegs observation.pulled),
        tcBadHeap h r zs z (tableCounts s observation.pulled.hold) i)) ∨
    (let state := {tableCounts s observation.pulled.hold with «have» := 0, mode := LENLENS}
     ∃ data : CountReadSource state
       (natBits (tableRegs observation.pulled).bits.toNat (tableRegs observation.pulled).hold.toNat)
       (bs.drop observation.used), data.body = stream l bs) := by
  rcases observation.normal normal with rejected | accepted
  · exact Or.inl rejected
  obtain ⟨origin, _buffers, _progress, reads, _actual, _cases⟩ := accepted
  obtain ⟨hlit, hdist, hclen, r1, r2, first, second, third, lit, dist, code⟩ := reads
  obtain ⟨_codeBound, _haveBound, litBound, distBound, _good⟩ := origin.headerLengths rfl
  have counts : DynamicCountsOK hlit hdist := by
    change hlit + 257 ≤ 286 ∧ hdist + 1 ≤ 30
    exact ⟨by omega, by omega⟩
  exact Or.inr ⟨⟨stream l bs, r1, r2, hlit, hdist, hclen, first, second, third, counts, lit, dist, code⟩, rfl⟩

/-- A real LENLENS short read moves only its actually consumed caller
bytes into the cumulative alphabet word; the three count reads remain
unchanged. -/
theorem CountReadSource.wait_transport
    {s state : InflateState} {received : List Bool} {bs : List UInt8} {used : Nat}
    (data : CountReadSource s received bs)
    (lit : state.nlen = s.nlen) (dist : state.ndist = s.ndist) (code : state.ncode = s.ncode) :
    ∃ next : CountReadSource state (received ++ bytesBits (bs.take used)) (bs.drop used),
      next.body = data.body := by
  refine ⟨⟨data.body, data.r1, data.r2, data.hlit, data.hdist, data.hclen,
    data.first, data.second, ?_, data.counts, ?_, ?_, ?_⟩, rfl⟩
  · simpa only [List.append_assoc, ← bytesBits_append, List.take_append_drop] using data.third
  · rw [lit]; exact data.literalCount
  · rw [dist]; exact data.distanceCount
  · rw [code]; exact data.codeCount

/-- The source-produced complete alphabet and its actual empty CODELENS
prefix initialize the cumulative code-length parser relation. -/
theorem CountReadSource.alphabet_seed
    {s state : InflateState} {received : List Bool} {bs : List UInt8} {used : Nat}
    {regs : IL} {alphabet : List Nat}
    (data : CountReadSource s received bs)
    (lit : state.nlen = s.nlen) (dist : state.ndist = s.ndist)
    (read : ∀ tail, readCodeLenLens s.ncode.toNat ((received ++ bytesBits (bs.take used)) ++ tail) =
      some (alphabet, natBits regs.bits.toNat regs.hold.toNat ++ tail))
    (valid : Acceptable .codeLength alphabet) (empty : actualLengthPrefix state = []) :
    ∃ prefixData : HeaderSourcePrefix state {regs with ret := 0} (bs.drop used) alphabet,
      prefixData.bodyInput = data.body := by
  have alphabetRead := read (bytesBits (bs.drop used))
  rw [data.codeCount] at alphabetRead
  have actualRead : readCodeLenLens (data.hclen + 4) (received ++ bytesBits bs) =
      some (alphabet, stream {regs with ret := 0} (bs.drop used)) := by
    simpa only [stream, List.append_assoc, ← bytesBits_append, List.take_append_drop] using alphabetRead
  exact HeaderSourcePrefix.seed data.first data.second data.third data.counts
    (by rw [lit]; exact data.literalCount) (by rw [dist]; exact data.distanceCount) actualRead valid empty

#print axioms table_count_read_source
#print axioms CountReadSource.wait_transport
#print axioms CountReadSource.alphabet_seed
end Zlib.Inflate.Proofs.ActualHeader
