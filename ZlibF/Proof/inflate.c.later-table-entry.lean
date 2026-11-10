import ZlibF.Proof.«inflate.c.later-code-observers»
namespace Zlib.Inflate.Proofs.LaterHeader
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.HeaderPhaseView
open ZlibF.Math.InflateHuffmanBodyContext
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- A source-created private CODELENS entry from an arbitrary TABLE state.
Neither its saved window nor its current output cursor is reset. -/
structure TableCodeEntry (c : Ctx) (h : Heap) (r : ZStreamRef) (zs : Nat) (z : ZStream)
    (s : InflateState) (l : IL) (bs : List UInt8) (future payload : List Bool) (L D : List Nat) where
  regs : IL
  state : InflateState
  used : Nat
  alphabet : List Nat
  decoded : List Nat
  bound : used ≤ bs.length
  origin : DefaultOriginState (setI h zs state) r zs z state
  buffers : DispatchBuffers (setI h zs state) r regs (bs.drop used)
  mode : state.mode = CODELENS
  contents : Zlib.Inftrees.Proofs.CodeLengthContents state.codes 0 state.lenbits.toNat alphabet
  ordinary : ∀ index, index < 2 ^ state.lenbits.toNat → ∃ entry, state.codes[index]? = some entry ∧ entry.op = 0
  emptyPrefix : actualLengthPrefix state = []
  last : state.last = s.last
  cursor : regs.next = inputAdvance l.next used
  count : regs.have_.toNat + used = l.have_.toNat
  put : regs.put = l.put
  left : regs.left = l.left
  out : regs.out_ = l.out_
  bits : regs.bits.toNat ≤ max l.bits.toNat 21
  frame : HeaderFrame s state
  parsed : CodeLens alphabet (state.nlen.toNat + state.ndist.toNat) [] (stream regs (bs.drop used) ++ future) payload decoded
  eob : HasEndOfBlock (decoded.take state.nlen.toNat)
  validL : Acceptable .litLen (decoded.take state.nlen.toNat)
  validD : Acceptable .dist (decoded.drop state.nlen.toNat)
  actualL : L = decoded.take state.nlen.toNat
  actualD : D = decoded.drop state.nlen.toNat
  reads : ∃ hlit hdist hclen r1 r2 r3,
    readBits 5 (stream l bs) = some (hlit, r1) ∧ readBits 5 r1 = some (hdist, r2) ∧
    readBits 4 r2 = some (hclen, r3) ∧ DynamicCountsOK hlit hdist ∧
    readCodeLenLens (hclen + 4) r3 = some (alphabet, stream regs (bs.drop used)) ∧
    Acceptable .codeLength alphabet ∧ state.nlen.toNat = hlit + 257 ∧ state.ndist.toNat = hdist + 1
  actual : runX (inflate_TABLE c) l h = runX (inflate_CODELENS c) regs (setI h zs state)

/-- Available count/alphabet prefixes produce the above entry from actual
CODES execution. The guard is the real remaining alphabet-bit count,
exposed after the actual NEEDBITS14 prefix. -/
theorem table_code_entry
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8} {future payload : List Bool} {L D : List Nat}
    (E : Env c h r zs z s) (origin : DefaultOriginState h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = TABLE)
    (available : 14 ≤ (stream l bs).length)
    (header : Header 2 (stream l bs ++ future) L D payload) :
    ∃ pulled tableUsed,
      runX (NEEDBITS 14) l h = .ok ((.ok (), pulled), h) ∧ tableUsed ≤ bs.length ∧ BitInv h pulled (bs.drop tableUsed) ∧
      (3 * (tableCounts s pulled.hold).ncode.toNat ≤ (stream (tableRegs pulled) (bs.drop tableUsed)).length →
        Nonempty (TableCodeEntry c h r zs z s l bs future payload L D)) := by
  obtain ⟨pulled, tableUsed, pull, bound, B, ready⟩ := table_header_packet_prefix E origin buffers mode available header
  refine ⟨pulled, tableUsed, pull, bound, B, ?_⟩
  intro enough
  obtain ⟨regs, state, used, lensUsed, alphabet, decoded, payloadInput, _usedEq, _lensBound, _alphabetRead,
    usedBound, _B, code, _wf, _codeInv, contents, ordinary, emptyPrefix, last, _ncode, _nlen, _ndist,
    put, left, out, _window, parsed, eob, validL, validD, actualL, actualD, payloadEq, frame, reads,
    current, packet, cursor, count, bits, actual⟩ := ready enough
  subst payloadInput
  exact ⟨⟨regs, state, used, alphabet, decoded, usedBound, current, packet, code, contents, ordinary,
    emptyPrefix, last, cursor, count, put, left, out, bits, frame, parsed, eob, validL, validD, actualL, actualD, reads, actual⟩⟩

/-- A complete source-created dynamic header and actual completed reader
produce a current-input independent Header, even for a malformed payload. -/
theorem TableCodeEntry.completed_header
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8} {future payload : List Bool} {L D : List Nat}
    (E : Env c h r zs z s)
    (e : TableCodeEntry c h r zs z s l bs future payload L D)
    (b : PayloadPhaseView.CodeBoundary c (setI h zs e.state) r zs z e.state e.regs (bs.drop e.used) e.decoded future payload) :
    Header 2 (stream l bs) L D b.payload := by
  have codeE : Env c (setI h zs e.state) r zs z e.state := ⟨E.strm, E.st, e.origin.good.live.hz, e.origin.good.live.hs⟩
  have parsed := code_boundary_current_parse codeE e.origin e.buffers e.mode e.contents e.ordinary b
  rw [e.emptyPrefix] at parsed
  obtain ⟨hlit, hdist, hclen, r1, r2, r3, first, second, third, counts, alphabetRead, validAlphabet, nlen, ndist⟩ := e.reads
  rw [nlen, ndist] at parsed
  have header0 := Header.dynamic first second third counts alphabetRead validAlphabet parsed
    (by simpa only [nlen] using e.eob)
    (by simpa only [nlen] using e.validL)
    (by simpa only [nlen] using e.validD)
  simpa only [← nlen, ← e.actualL, ← e.actualD] using header0

#print axioms table_code_entry
#print axioms TableCodeEntry.completed_header
end Zlib.Inflate.Proofs.LaterHeader
