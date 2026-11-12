import ZlibF.Proof.«deflate.c.universal-call-hcrc»

/-!
# deflate.c: the trailer of one `deflate` call

Batch C (`deflate_header_trailer`). On `Z_FINISH` with a positive `wrap`, the gzip trailer (CRC and
input length, eight bytes) or the zlib trailer (Adler-32, four bytes) goes into `pending_buf`, is
flushed, and `wrap` is negated so that the trailer is written once.
-/

namespace Zlib.Deflate.Universal.Call
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Deflate.Engine.Proofs
open Zlib.Trees.Proofs.Out (TreesInvAt BitsDiff)
set_option autoImplicit false

/-- The trailer bytes. -/
def trailerBytes (strm : ZStreamPtr) (s : DeflateStatePtr) (k : M Int32) : M Int32 := do
  if (← rd s (·.wrap)) == 2 then
    let a ← zrd strm (·.adler)
    put_byte s (a &&& 0xff).toUInt8
    put_byte s ((a >>> 8) &&& 0xff).toUInt8
    put_byte s ((a >>> 16) &&& 0xff).toUInt8
    put_byte s ((a >>> 24) &&& 0xff).toUInt8
    let t ← zrd strm (·.total_in)
    put_byte s (t &&& 0xff).toUInt8
    put_byte s ((t >>> 8) &&& 0xff).toUInt8
    put_byte s ((t >>> 16) &&& 0xff).toUInt8
    put_byte s ((t >>> 24) &&& 0xff).toUInt8
  else
    let a ← zrd strm (·.adler)
    putShortMSB s (a >>> 16).toUInt32
    putShortMSB s (a &&& 0xffff).toUInt32
  k

/-- The end of the trailer: flush, negate `wrap`, report whether bytes are left. -/
def trailerEnd (strm : ZStreamPtr) (s : DeflateStatePtr) : M Int32 := do
  flush_pending strm
  let w ← rd s (·.wrap)
  if w > 0 then
    let nw ← ineg w
    wr s (fun d => { d with wrap := nw })
  return if (← rd s (·.pending)) != 0 then Z_OK else Z_STREAM_END

def trailerPhase' (strm : ZStreamPtr) (s : DeflateStatePtr) (flush : Int32) : M Int32 := do
  if flush != Z_FINISH then return Z_OK
  if (← rd s (·.wrap)) ≤ 0 then return Z_STREAM_END
  trailerBytes strm s (trailerEnd strm s)

theorem trailer_phase_split (strm : ZStreamPtr) (s : DeflateStatePtr) (flush : Int32) :
    trailerPhase strm s flush = trailerPhase' strm s flush := by
  delta trailerPhase trailerPhase' trailerBytes trailerEnd
  exact rfl

/-- **The gzip trailer bytes**: eight bytes, with room. -/
theorem trailer_gzip {h : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream} {d : DeflateState}
    {buf : Array UInt8} (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) (cursor : d.pending_out = d.pending_buf)
    (room : d.pending.toNat + 8 ≤ buf.size) (wrap : d.wrap = 2) (K : M Int32) :
    ∃ (after : Heap) (d1 : DeflateState) (buf1 : Array UInt8),
      trailerBytes (some r) (some (.tab ds)) K h = K after ∧ DGood after r ds z d1 ∧
      TreesInvAt after ds d1 pb buf1 ∧ buf1.size = buf.size ∧ StreamBuffers after r ∧
      HeaderFrame h after r ds pb ∧ d1 = { d with pending := d1.pending } ∧ d1.pending.toNat = d.pending.toNat + 8 := by
  have small := trees.base.pending_small
  let e0 := d
  let e1 : DeflateState := { e0 with pending := e0.pending + 1 }
  let e2 : DeflateState := { e1 with pending := e1.pending + 1 }
  let e3 : DeflateState := { e2 with pending := e2.pending + 1 }
  let e4 : DeflateState := { e3 with pending := e3.pending + 1 }
  let e5 : DeflateState := { e4 with pending := e4.pending + 1 }
  let e6 : DeflateState := { e5 with pending := e5.pending + 1 }
  let e7 : DeflateState := { e6 with pending := e6.pending + 1 }
  let e8 : DeflateState := { e7 with pending := e7.pending + 1 }
  have pe0 : e0.pending.toNat = d.pending.toNat := rfl
  have pe1 : e1.pending.toNat = d.pending.toNat + 1 := by
    change (e0.pending + 1).toNat = _
    rw [Zlib.Trees.Proofs.Out.toNat_add_one_u64 (by rw [pe0]; have := trees.base.size; have := trees.base.lit_hi; omega), pe0]
  have pe2 : e2.pending.toNat = d.pending.toNat + 2 := by
    change (e1.pending + 1).toNat = _
    rw [Zlib.Trees.Proofs.Out.toNat_add_one_u64 (by rw [pe1]; have := trees.base.size; have := trees.base.lit_hi; omega), pe1]
  have pe3 : e3.pending.toNat = d.pending.toNat + 3 := by
    change (e2.pending + 1).toNat = _
    rw [Zlib.Trees.Proofs.Out.toNat_add_one_u64 (by rw [pe2]; have := trees.base.size; have := trees.base.lit_hi; omega), pe2]
  have pe4 : e4.pending.toNat = d.pending.toNat + 4 := by
    change (e3.pending + 1).toNat = _
    rw [Zlib.Trees.Proofs.Out.toNat_add_one_u64 (by rw [pe3]; have := trees.base.size; have := trees.base.lit_hi; omega), pe3]
  have pe5 : e5.pending.toNat = d.pending.toNat + 5 := by
    change (e4.pending + 1).toNat = _
    rw [Zlib.Trees.Proofs.Out.toNat_add_one_u64 (by rw [pe4]; have := trees.base.size; have := trees.base.lit_hi; omega), pe4]
  have pe6 : e6.pending.toNat = d.pending.toNat + 6 := by
    change (e5.pending + 1).toNat = _
    rw [Zlib.Trees.Proofs.Out.toNat_add_one_u64 (by rw [pe5]; have := trees.base.size; have := trees.base.lit_hi; omega), pe5]
  have pe7 : e7.pending.toNat = d.pending.toNat + 7 := by
    change (e6.pending + 1).toNat = _
    rw [Zlib.Trees.Proofs.Out.toNat_add_one_u64 (by rw [pe6]; have := trees.base.size; have := trees.base.lit_hi; omega), pe6]
  have pe8 : e8.pending.toNat = d.pending.toNat + 8 := by
    change (e7.pending + 1).toNat = _
    rw [Zlib.Trees.Proofs.Out.toNat_add_one_u64 (by rw [pe7]; have := trees.base.size; have := trees.base.lit_hi; omega), pe7]
  let F0 := h
  let B0 := buf
  have G0 : DGood F0 r ds z e0 ∧ TreesInvAt F0 ds e0 pb B0 ∧ StreamBuffers F0 r ∧ B0.size = buf.size ∧
      HeaderFrame h F0 r ds pb := ⟨good, trees, buffers, rfl, HeaderFrame.refl h pb⟩
  let F1 := fun (c0 : UInt8) => byteHeap (F0) ds pb e0 (B0) c0
  let B1 := fun (c0 : UInt8) => (B0).set! e0.pending.toNat c0
  have step0 : (∀ c, put_byte (some (.tab ds)) c (F0) =
      .ok ((), byteHeap (F0) ds pb e0 (B0) c)) ∧
      (∀ c, DGood (byteHeap (F0) ds pb e0 (B0) c) r ds z { e0 with pending := e0.pending + 1 } ∧
        TreesInvAt (byteHeap (F0) ds pb e0 (B0) c) ds { e0 with pending := e0.pending + 1 } pb
          ((B0).set! e0.pending.toNat c) ∧
        StreamBuffers (byteHeap (F0) ds pb e0 (B0) c) r ∧
        (e0.pending + 1).toNat = e0.pending.toNat + 1 ∧ ((B0).set! e0.pending.toNat c).size = (B0).size) :=
    header_byte_eq G0.1 G0.2.1 G0.2.2.1 (show e0.pending_out = e0.pending_buf from cursor)
      (by rw [pe0, G0.2.2.2.1]; omega)
  have G1 : ∀ (c0 : UInt8), DGood (F1 c0) r ds z e1 ∧
      TreesInvAt (F1 c0) ds e1 pb (B1 c0) ∧ StreamBuffers (F1 c0) r ∧
      (B1 c0).size = buf.size ∧ HeaderFrame h (F1 c0) r ds pb := by
    intro c0
    obtain ⟨gd, tr, bu, _, sz'⟩ := (step0).2 c0
    exact ⟨gd, tr, bu, sz'.trans G0.2.2.2.1,
      G0.2.2.2.2.trans (HeaderFrame.byte pb G0.1.live.hs G0.2.1.base.bytes c0)⟩
  let F2 := fun (c0 : UInt8) (c1 : UInt8) => byteHeap (F1 c0) ds pb e1 (B1 c0) c1
  let B2 := fun (c0 : UInt8) (c1 : UInt8) => (B1 c0).set! e1.pending.toNat c1
  have step1 : ∀ (c0 : UInt8), (∀ c, put_byte (some (.tab ds)) c (F1 c0) =
      .ok ((), byteHeap (F1 c0) ds pb e1 (B1 c0) c)) ∧
      (∀ c, DGood (byteHeap (F1 c0) ds pb e1 (B1 c0) c) r ds z { e1 with pending := e1.pending + 1 } ∧
        TreesInvAt (byteHeap (F1 c0) ds pb e1 (B1 c0) c) ds { e1 with pending := e1.pending + 1 } pb
          ((B1 c0).set! e1.pending.toNat c) ∧
        StreamBuffers (byteHeap (F1 c0) ds pb e1 (B1 c0) c) r ∧
        (e1.pending + 1).toNat = e1.pending.toNat + 1 ∧ ((B1 c0).set! e1.pending.toNat c).size = (B1 c0).size) :=
    fun (c0 : UInt8) => header_byte_eq (G1 c0).1 (G1 c0).2.1 (G1 c0).2.2.1 (show e1.pending_out = e1.pending_buf from cursor)
      (by rw [pe1, (G1 c0).2.2.2.1]; omega)
  have G2 : ∀ (c0 : UInt8) (c1 : UInt8), DGood (F2 c0 c1) r ds z e2 ∧
      TreesInvAt (F2 c0 c1) ds e2 pb (B2 c0 c1) ∧ StreamBuffers (F2 c0 c1) r ∧
      (B2 c0 c1).size = buf.size ∧ HeaderFrame h (F2 c0 c1) r ds pb := by
    intro c0 c1
    obtain ⟨gd, tr, bu, _, sz'⟩ := (step1 c0).2 c1
    exact ⟨gd, tr, bu, sz'.trans (G1 c0).2.2.2.1,
      (G1 c0).2.2.2.2.trans (HeaderFrame.byte pb (G1 c0).1.live.hs (G1 c0).2.1.base.bytes c1)⟩
  let F3 := fun (c0 : UInt8) (c1 : UInt8) (c2 : UInt8) => byteHeap (F2 c0 c1) ds pb e2 (B2 c0 c1) c2
  let B3 := fun (c0 : UInt8) (c1 : UInt8) (c2 : UInt8) => (B2 c0 c1).set! e2.pending.toNat c2
  have step2 : ∀ (c0 : UInt8) (c1 : UInt8), (∀ c, put_byte (some (.tab ds)) c (F2 c0 c1) =
      .ok ((), byteHeap (F2 c0 c1) ds pb e2 (B2 c0 c1) c)) ∧
      (∀ c, DGood (byteHeap (F2 c0 c1) ds pb e2 (B2 c0 c1) c) r ds z { e2 with pending := e2.pending + 1 } ∧
        TreesInvAt (byteHeap (F2 c0 c1) ds pb e2 (B2 c0 c1) c) ds { e2 with pending := e2.pending + 1 } pb
          ((B2 c0 c1).set! e2.pending.toNat c) ∧
        StreamBuffers (byteHeap (F2 c0 c1) ds pb e2 (B2 c0 c1) c) r ∧
        (e2.pending + 1).toNat = e2.pending.toNat + 1 ∧ ((B2 c0 c1).set! e2.pending.toNat c).size = (B2 c0 c1).size) :=
    fun (c0 : UInt8) (c1 : UInt8) => header_byte_eq (G2 c0 c1).1 (G2 c0 c1).2.1 (G2 c0 c1).2.2.1 (show e2.pending_out = e2.pending_buf from cursor)
      (by rw [pe2, (G2 c0 c1).2.2.2.1]; omega)
  have G3 : ∀ (c0 : UInt8) (c1 : UInt8) (c2 : UInt8), DGood (F3 c0 c1 c2) r ds z e3 ∧
      TreesInvAt (F3 c0 c1 c2) ds e3 pb (B3 c0 c1 c2) ∧ StreamBuffers (F3 c0 c1 c2) r ∧
      (B3 c0 c1 c2).size = buf.size ∧ HeaderFrame h (F3 c0 c1 c2) r ds pb := by
    intro c0 c1 c2
    obtain ⟨gd, tr, bu, _, sz'⟩ := (step2 c0 c1).2 c2
    exact ⟨gd, tr, bu, sz'.trans (G2 c0 c1).2.2.2.1,
      (G2 c0 c1).2.2.2.2.trans (HeaderFrame.byte pb (G2 c0 c1).1.live.hs (G2 c0 c1).2.1.base.bytes c2)⟩
  let F4 := fun (c0 : UInt8) (c1 : UInt8) (c2 : UInt8) (c3 : UInt8) => byteHeap (F3 c0 c1 c2) ds pb e3 (B3 c0 c1 c2) c3
  let B4 := fun (c0 : UInt8) (c1 : UInt8) (c2 : UInt8) (c3 : UInt8) => (B3 c0 c1 c2).set! e3.pending.toNat c3
  have step3 : ∀ (c0 : UInt8) (c1 : UInt8) (c2 : UInt8), (∀ c, put_byte (some (.tab ds)) c (F3 c0 c1 c2) =
      .ok ((), byteHeap (F3 c0 c1 c2) ds pb e3 (B3 c0 c1 c2) c)) ∧
      (∀ c, DGood (byteHeap (F3 c0 c1 c2) ds pb e3 (B3 c0 c1 c2) c) r ds z { e3 with pending := e3.pending + 1 } ∧
        TreesInvAt (byteHeap (F3 c0 c1 c2) ds pb e3 (B3 c0 c1 c2) c) ds { e3 with pending := e3.pending + 1 } pb
          ((B3 c0 c1 c2).set! e3.pending.toNat c) ∧
        StreamBuffers (byteHeap (F3 c0 c1 c2) ds pb e3 (B3 c0 c1 c2) c) r ∧
        (e3.pending + 1).toNat = e3.pending.toNat + 1 ∧ ((B3 c0 c1 c2).set! e3.pending.toNat c).size = (B3 c0 c1 c2).size) :=
    fun (c0 : UInt8) (c1 : UInt8) (c2 : UInt8) => header_byte_eq (G3 c0 c1 c2).1 (G3 c0 c1 c2).2.1 (G3 c0 c1 c2).2.2.1 (show e3.pending_out = e3.pending_buf from cursor)
      (by rw [pe3, (G3 c0 c1 c2).2.2.2.1]; omega)
  have G4 : ∀ (c0 : UInt8) (c1 : UInt8) (c2 : UInt8) (c3 : UInt8), DGood (F4 c0 c1 c2 c3) r ds z e4 ∧
      TreesInvAt (F4 c0 c1 c2 c3) ds e4 pb (B4 c0 c1 c2 c3) ∧ StreamBuffers (F4 c0 c1 c2 c3) r ∧
      (B4 c0 c1 c2 c3).size = buf.size ∧ HeaderFrame h (F4 c0 c1 c2 c3) r ds pb := by
    intro c0 c1 c2 c3
    obtain ⟨gd, tr, bu, _, sz'⟩ := (step3 c0 c1 c2).2 c3
    exact ⟨gd, tr, bu, sz'.trans (G3 c0 c1 c2).2.2.2.1,
      (G3 c0 c1 c2).2.2.2.2.trans (HeaderFrame.byte pb (G3 c0 c1 c2).1.live.hs (G3 c0 c1 c2).2.1.base.bytes c3)⟩
  let F5 := fun (c0 : UInt8) (c1 : UInt8) (c2 : UInt8) (c3 : UInt8) (c4 : UInt8) => byteHeap (F4 c0 c1 c2 c3) ds pb e4 (B4 c0 c1 c2 c3) c4
  let B5 := fun (c0 : UInt8) (c1 : UInt8) (c2 : UInt8) (c3 : UInt8) (c4 : UInt8) => (B4 c0 c1 c2 c3).set! e4.pending.toNat c4
  have step4 : ∀ (c0 : UInt8) (c1 : UInt8) (c2 : UInt8) (c3 : UInt8), (∀ c, put_byte (some (.tab ds)) c (F4 c0 c1 c2 c3) =
      .ok ((), byteHeap (F4 c0 c1 c2 c3) ds pb e4 (B4 c0 c1 c2 c3) c)) ∧
      (∀ c, DGood (byteHeap (F4 c0 c1 c2 c3) ds pb e4 (B4 c0 c1 c2 c3) c) r ds z { e4 with pending := e4.pending + 1 } ∧
        TreesInvAt (byteHeap (F4 c0 c1 c2 c3) ds pb e4 (B4 c0 c1 c2 c3) c) ds { e4 with pending := e4.pending + 1 } pb
          ((B4 c0 c1 c2 c3).set! e4.pending.toNat c) ∧
        StreamBuffers (byteHeap (F4 c0 c1 c2 c3) ds pb e4 (B4 c0 c1 c2 c3) c) r ∧
        (e4.pending + 1).toNat = e4.pending.toNat + 1 ∧ ((B4 c0 c1 c2 c3).set! e4.pending.toNat c).size = (B4 c0 c1 c2 c3).size) :=
    fun (c0 : UInt8) (c1 : UInt8) (c2 : UInt8) (c3 : UInt8) => header_byte_eq (G4 c0 c1 c2 c3).1 (G4 c0 c1 c2 c3).2.1 (G4 c0 c1 c2 c3).2.2.1 (show e4.pending_out = e4.pending_buf from cursor)
      (by rw [pe4, (G4 c0 c1 c2 c3).2.2.2.1]; omega)
  have G5 : ∀ (c0 : UInt8) (c1 : UInt8) (c2 : UInt8) (c3 : UInt8) (c4 : UInt8), DGood (F5 c0 c1 c2 c3 c4) r ds z e5 ∧
      TreesInvAt (F5 c0 c1 c2 c3 c4) ds e5 pb (B5 c0 c1 c2 c3 c4) ∧ StreamBuffers (F5 c0 c1 c2 c3 c4) r ∧
      (B5 c0 c1 c2 c3 c4).size = buf.size ∧ HeaderFrame h (F5 c0 c1 c2 c3 c4) r ds pb := by
    intro c0 c1 c2 c3 c4
    obtain ⟨gd, tr, bu, _, sz'⟩ := (step4 c0 c1 c2 c3).2 c4
    exact ⟨gd, tr, bu, sz'.trans (G4 c0 c1 c2 c3).2.2.2.1,
      (G4 c0 c1 c2 c3).2.2.2.2.trans (HeaderFrame.byte pb (G4 c0 c1 c2 c3).1.live.hs (G4 c0 c1 c2 c3).2.1.base.bytes c4)⟩
  let F6 := fun (c0 : UInt8) (c1 : UInt8) (c2 : UInt8) (c3 : UInt8) (c4 : UInt8) (c5 : UInt8) => byteHeap (F5 c0 c1 c2 c3 c4) ds pb e5 (B5 c0 c1 c2 c3 c4) c5
  let B6 := fun (c0 : UInt8) (c1 : UInt8) (c2 : UInt8) (c3 : UInt8) (c4 : UInt8) (c5 : UInt8) => (B5 c0 c1 c2 c3 c4).set! e5.pending.toNat c5
  have step5 : ∀ (c0 : UInt8) (c1 : UInt8) (c2 : UInt8) (c3 : UInt8) (c4 : UInt8), (∀ c, put_byte (some (.tab ds)) c (F5 c0 c1 c2 c3 c4) =
      .ok ((), byteHeap (F5 c0 c1 c2 c3 c4) ds pb e5 (B5 c0 c1 c2 c3 c4) c)) ∧
      (∀ c, DGood (byteHeap (F5 c0 c1 c2 c3 c4) ds pb e5 (B5 c0 c1 c2 c3 c4) c) r ds z { e5 with pending := e5.pending + 1 } ∧
        TreesInvAt (byteHeap (F5 c0 c1 c2 c3 c4) ds pb e5 (B5 c0 c1 c2 c3 c4) c) ds { e5 with pending := e5.pending + 1 } pb
          ((B5 c0 c1 c2 c3 c4).set! e5.pending.toNat c) ∧
        StreamBuffers (byteHeap (F5 c0 c1 c2 c3 c4) ds pb e5 (B5 c0 c1 c2 c3 c4) c) r ∧
        (e5.pending + 1).toNat = e5.pending.toNat + 1 ∧ ((B5 c0 c1 c2 c3 c4).set! e5.pending.toNat c).size = (B5 c0 c1 c2 c3 c4).size) :=
    fun (c0 : UInt8) (c1 : UInt8) (c2 : UInt8) (c3 : UInt8) (c4 : UInt8) => header_byte_eq (G5 c0 c1 c2 c3 c4).1 (G5 c0 c1 c2 c3 c4).2.1 (G5 c0 c1 c2 c3 c4).2.2.1 (show e5.pending_out = e5.pending_buf from cursor)
      (by rw [pe5, (G5 c0 c1 c2 c3 c4).2.2.2.1]; omega)
  have G6 : ∀ (c0 : UInt8) (c1 : UInt8) (c2 : UInt8) (c3 : UInt8) (c4 : UInt8) (c5 : UInt8), DGood (F6 c0 c1 c2 c3 c4 c5) r ds z e6 ∧
      TreesInvAt (F6 c0 c1 c2 c3 c4 c5) ds e6 pb (B6 c0 c1 c2 c3 c4 c5) ∧ StreamBuffers (F6 c0 c1 c2 c3 c4 c5) r ∧
      (B6 c0 c1 c2 c3 c4 c5).size = buf.size ∧ HeaderFrame h (F6 c0 c1 c2 c3 c4 c5) r ds pb := by
    intro c0 c1 c2 c3 c4 c5
    obtain ⟨gd, tr, bu, _, sz'⟩ := (step5 c0 c1 c2 c3 c4).2 c5
    exact ⟨gd, tr, bu, sz'.trans (G5 c0 c1 c2 c3 c4).2.2.2.1,
      (G5 c0 c1 c2 c3 c4).2.2.2.2.trans (HeaderFrame.byte pb (G5 c0 c1 c2 c3 c4).1.live.hs (G5 c0 c1 c2 c3 c4).2.1.base.bytes c5)⟩
  let F7 := fun (c0 : UInt8) (c1 : UInt8) (c2 : UInt8) (c3 : UInt8) (c4 : UInt8) (c5 : UInt8) (c6 : UInt8) => byteHeap (F6 c0 c1 c2 c3 c4 c5) ds pb e6 (B6 c0 c1 c2 c3 c4 c5) c6
  let B7 := fun (c0 : UInt8) (c1 : UInt8) (c2 : UInt8) (c3 : UInt8) (c4 : UInt8) (c5 : UInt8) (c6 : UInt8) => (B6 c0 c1 c2 c3 c4 c5).set! e6.pending.toNat c6
  have step6 : ∀ (c0 : UInt8) (c1 : UInt8) (c2 : UInt8) (c3 : UInt8) (c4 : UInt8) (c5 : UInt8), (∀ c, put_byte (some (.tab ds)) c (F6 c0 c1 c2 c3 c4 c5) =
      .ok ((), byteHeap (F6 c0 c1 c2 c3 c4 c5) ds pb e6 (B6 c0 c1 c2 c3 c4 c5) c)) ∧
      (∀ c, DGood (byteHeap (F6 c0 c1 c2 c3 c4 c5) ds pb e6 (B6 c0 c1 c2 c3 c4 c5) c) r ds z { e6 with pending := e6.pending + 1 } ∧
        TreesInvAt (byteHeap (F6 c0 c1 c2 c3 c4 c5) ds pb e6 (B6 c0 c1 c2 c3 c4 c5) c) ds { e6 with pending := e6.pending + 1 } pb
          ((B6 c0 c1 c2 c3 c4 c5).set! e6.pending.toNat c) ∧
        StreamBuffers (byteHeap (F6 c0 c1 c2 c3 c4 c5) ds pb e6 (B6 c0 c1 c2 c3 c4 c5) c) r ∧
        (e6.pending + 1).toNat = e6.pending.toNat + 1 ∧ ((B6 c0 c1 c2 c3 c4 c5).set! e6.pending.toNat c).size = (B6 c0 c1 c2 c3 c4 c5).size) :=
    fun (c0 : UInt8) (c1 : UInt8) (c2 : UInt8) (c3 : UInt8) (c4 : UInt8) (c5 : UInt8) => header_byte_eq (G6 c0 c1 c2 c3 c4 c5).1 (G6 c0 c1 c2 c3 c4 c5).2.1 (G6 c0 c1 c2 c3 c4 c5).2.2.1 (show e6.pending_out = e6.pending_buf from cursor)
      (by rw [pe6, (G6 c0 c1 c2 c3 c4 c5).2.2.2.1]; omega)
  have G7 : ∀ (c0 : UInt8) (c1 : UInt8) (c2 : UInt8) (c3 : UInt8) (c4 : UInt8) (c5 : UInt8) (c6 : UInt8), DGood (F7 c0 c1 c2 c3 c4 c5 c6) r ds z e7 ∧
      TreesInvAt (F7 c0 c1 c2 c3 c4 c5 c6) ds e7 pb (B7 c0 c1 c2 c3 c4 c5 c6) ∧ StreamBuffers (F7 c0 c1 c2 c3 c4 c5 c6) r ∧
      (B7 c0 c1 c2 c3 c4 c5 c6).size = buf.size ∧ HeaderFrame h (F7 c0 c1 c2 c3 c4 c5 c6) r ds pb := by
    intro c0 c1 c2 c3 c4 c5 c6
    obtain ⟨gd, tr, bu, _, sz'⟩ := (step6 c0 c1 c2 c3 c4 c5).2 c6
    exact ⟨gd, tr, bu, sz'.trans (G6 c0 c1 c2 c3 c4 c5).2.2.2.1,
      (G6 c0 c1 c2 c3 c4 c5).2.2.2.2.trans (HeaderFrame.byte pb (G6 c0 c1 c2 c3 c4 c5).1.live.hs (G6 c0 c1 c2 c3 c4 c5).2.1.base.bytes c6)⟩
  let F8 := fun (c0 : UInt8) (c1 : UInt8) (c2 : UInt8) (c3 : UInt8) (c4 : UInt8) (c5 : UInt8) (c6 : UInt8) (c7 : UInt8) => byteHeap (F7 c0 c1 c2 c3 c4 c5 c6) ds pb e7 (B7 c0 c1 c2 c3 c4 c5 c6) c7
  let B8 := fun (c0 : UInt8) (c1 : UInt8) (c2 : UInt8) (c3 : UInt8) (c4 : UInt8) (c5 : UInt8) (c6 : UInt8) (c7 : UInt8) => (B7 c0 c1 c2 c3 c4 c5 c6).set! e7.pending.toNat c7
  have step7 : ∀ (c0 : UInt8) (c1 : UInt8) (c2 : UInt8) (c3 : UInt8) (c4 : UInt8) (c5 : UInt8) (c6 : UInt8), (∀ c, put_byte (some (.tab ds)) c (F7 c0 c1 c2 c3 c4 c5 c6) =
      .ok ((), byteHeap (F7 c0 c1 c2 c3 c4 c5 c6) ds pb e7 (B7 c0 c1 c2 c3 c4 c5 c6) c)) ∧
      (∀ c, DGood (byteHeap (F7 c0 c1 c2 c3 c4 c5 c6) ds pb e7 (B7 c0 c1 c2 c3 c4 c5 c6) c) r ds z { e7 with pending := e7.pending + 1 } ∧
        TreesInvAt (byteHeap (F7 c0 c1 c2 c3 c4 c5 c6) ds pb e7 (B7 c0 c1 c2 c3 c4 c5 c6) c) ds { e7 with pending := e7.pending + 1 } pb
          ((B7 c0 c1 c2 c3 c4 c5 c6).set! e7.pending.toNat c) ∧
        StreamBuffers (byteHeap (F7 c0 c1 c2 c3 c4 c5 c6) ds pb e7 (B7 c0 c1 c2 c3 c4 c5 c6) c) r ∧
        (e7.pending + 1).toNat = e7.pending.toNat + 1 ∧ ((B7 c0 c1 c2 c3 c4 c5 c6).set! e7.pending.toNat c).size = (B7 c0 c1 c2 c3 c4 c5 c6).size) :=
    fun (c0 : UInt8) (c1 : UInt8) (c2 : UInt8) (c3 : UInt8) (c4 : UInt8) (c5 : UInt8) (c6 : UInt8) => header_byte_eq (G7 c0 c1 c2 c3 c4 c5 c6).1 (G7 c0 c1 c2 c3 c4 c5 c6).2.1 (G7 c0 c1 c2 c3 c4 c5 c6).2.2.1 (show e7.pending_out = e7.pending_buf from cursor)
      (by rw [pe7, (G7 c0 c1 c2 c3 c4 c5 c6).2.2.2.1]; omega)
  have G8 : ∀ (c0 : UInt8) (c1 : UInt8) (c2 : UInt8) (c3 : UInt8) (c4 : UInt8) (c5 : UInt8) (c6 : UInt8) (c7 : UInt8), DGood (F8 c0 c1 c2 c3 c4 c5 c6 c7) r ds z e8 ∧
      TreesInvAt (F8 c0 c1 c2 c3 c4 c5 c6 c7) ds e8 pb (B8 c0 c1 c2 c3 c4 c5 c6 c7) ∧ StreamBuffers (F8 c0 c1 c2 c3 c4 c5 c6 c7) r ∧
      (B8 c0 c1 c2 c3 c4 c5 c6 c7).size = buf.size ∧ HeaderFrame h (F8 c0 c1 c2 c3 c4 c5 c6 c7) r ds pb := by
    intro c0 c1 c2 c3 c4 c5 c6 c7
    obtain ⟨gd, tr, bu, _, sz'⟩ := (step7 c0 c1 c2 c3 c4 c5 c6).2 c7
    exact ⟨gd, tr, bu, sz'.trans (G7 c0 c1 c2 c3 c4 c5 c6).2.2.2.1,
      (G7 c0 c1 c2 c3 c4 c5 c6).2.2.2.2.trans (HeaderFrame.byte pb (G7 c0 c1 c2 c3 c4 c5 c6).1.live.hs (G7 c0 c1 c2 c3 c4 c5 c6).2.1.base.bytes c7)⟩
  have word : ∃ c0 c1 c2 c3 c4 c5 c6 c7,
      trailerBytes (some r) (some (.tab ds)) K h = K (F8 c0 c1 c2 c3 c4 c5 c6 c7) := by
    unfold trailerBytes
    simp only [bind_app, rdD_eq, good.live.hs, wrap, show ((2 : Int32) == 2) = true from rfl, ite_true, zrd_eq,
      good.live.hz]
    rw [step0.1]
    simp only []
    rw [(step1 _).1]
    simp only []
    rw [(step2 _ _).1]
    simp only []
    rw [(step3 _ _ _).1]
    simp only []
    rw [(G4 _ _ _ _).1.live.hz]
    simp only []
    rw [(step4 _ _ _ _).1]
    simp only []
    rw [(step5 _ _ _ _ _).1]
    simp only []
    rw [(step6 _ _ _ _ _ _).1]
    simp only []
    rw [(step7 _ _ _ _ _ _ _).1]
    simp only []
    exact ⟨_, _, _, _, _, _, _, _, rfl⟩
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, eq⟩ := word
  obtain ⟨g8, t8, b8, s8, f8⟩ := G8 c0 c1 c2 c3 c4 c5 c6 c7
  exact ⟨_, _, _, eq, g8, t8, s8, b8, f8, rfl, pe8⟩

theorem short_frame {h : Heap} {r : ZStreamRef} {ds : Nat} {d : DeflateState} (pb : Nat) (state : h.dstates ds = some d)
    {buf : Array UInt8} (get : h.bytes pb = some buf) (v : UInt32) : HeaderFrame h (shortHeap h ds pb d buf v) r ds pb := by
  have first := HeaderFrame.byte (r := r) pb state get (v >>> 8).toUInt8
  have state1 : (byteHeap h ds pb d buf (v >>> 8).toUInt8).dstates ds = some { d with pending := d.pending + 1 } := by
    unfold byteHeap; exact setD_dstates_same _ _ _
  have get1 : (byteHeap h ds pb d buf (v >>> 8).toUInt8).bytes pb = some (buf.set! d.pending.toNat (v >>> 8).toUInt8) := by
    simp [byteHeap, setD, Zlib.Trees.Proofs.Out.setB]
  have second := HeaderFrame.byte (r := r) pb state1 get1 (v &&& 0xff).toUInt8
  exact first.trans second

/-- **The zlib trailer bytes**: four bytes, with room. -/
theorem trailer_zlib {h : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream} {d : DeflateState}
    {buf : Array UInt8} (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) (cursor : d.pending_out = d.pending_buf)
    (room : d.pending.toNat + 4 ≤ buf.size) (wrap : d.wrap ≠ 2) (K : M Int32) :
    ∃ (after : Heap) (d1 : DeflateState) (buf1 : Array UInt8),
      trailerBytes (some r) (some (.tab ds)) K h = K after ∧ DGood after r ds z d1 ∧
      TreesInvAt after ds d1 pb buf1 ∧ buf1.size = buf.size ∧ StreamBuffers after r ∧
      HeaderFrame h after r ds pb ∧ d1 = { d with pending := d1.pending } ∧ d1.pending.toNat = d.pending.toNat + 4 := by
  obtain ⟨runs1, facts1⟩ := header_short_eq good trees buffers cursor (by omega)
  let v1 : UInt32 := (z.adler >>> 16).toUInt32
  let v2 : UInt32 := (z.adler &&& 0xffff).toUInt32
  obtain ⟨good1, trees1, buffers1, count1, size1⟩ := facts1 v1
  let d1 : DeflateState := { d with pending := d.pending + 2 }
  obtain ⟨runs2, facts2⟩ := header_short_eq good1 trees1 buffers1 (show d1.pending_out = d1.pending_buf from cursor)
    (by change (d.pending + 2).toNat + 2 ≤ _; rw [count1, size1]; omega)
  obtain ⟨good2, trees2, buffers2, count2, size2⟩ := facts2 v2
  have frame1 := short_frame (r := r) pb good.live.hs trees.base.bytes v1
  have frame2 := short_frame (r := r) pb good1.live.hs trees1.base.bytes v2
  refine ⟨_, _, _, ?_, good2, trees2, by rw [size2, size1], buffers2, frame1.trans frame2, rfl, ?_⟩
  · unfold trailerBytes
    have w : (d.wrap == 2) = false := beq_eq_false_iff_ne.mpr wrap
    simp only [bind_app, rdD_eq, good.live.hs, w, Bool.false_eq_true, ite_false, zrd_eq, good.live.hz]
    rw [runs1 v1]
    simp only []
    rw [runs2 v2]
  · rw [count2]; change (d.pending + 2).toNat + 2 = _; rw [count1]

/-- Writing `wrap` keeps the engine invariants and the caller buffers. -/
theorem wrap_engine {h : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream} {d : DeflateState}
    {buf : Array UInt8} (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) (v : Int32) (lo : -2 ≤ v.toInt) (hi : v.toInt ≤ 2) :
    DGood (setD h ds { d with wrap := v }) r ds z { d with wrap := v } ∧
      TreesInvAt (setD h ds { d with wrap := v }) ds { d with wrap := v } pb buf ∧
      StreamBuffers (setD h ds { d with wrap := v }) r ∧ HeaderFrame h (setD h ds { d with wrap := v }) r ds pb := by
  let result : DeflateState := { d with wrap := v }
  have inv : DStInv h ds result :=
    { good.inv with
      blocks := good.inv.blocks_keys rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      wrap_lo := lo
      wrap_hi := hi }
  have goodA := good.setD' (d' := result) rfl good.live.status inv (by trkeep)
  have treesA := trees_at_buffer goodA trees.base.pbuf trees.base.bytes
  have sizes := block_record_sizes good.live.hs (show result.depth = d.depth from rfl)
  have owned := stream_owned_keys good goodA rfl rfl rfl rfl
  have buffersA := stream_buffers_sizes good.live.hz goodA.live.hz buffers sizes owned (stream_accounting_zero z)
  exact ⟨goodA, treesA, buffersA, HeaderFrame.state pb good.live.hs result rfl⟩

/-- **The end of the trailer**: flush, negate a positive `wrap`, return `Z_OK` or `Z_STREAM_END`. -/
theorem trailer_end {h : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream} {d : DeflateState}
    {buf : Array UInt8} (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) (cursor : d.pending_out = d.pending_buf) (low : d.bi_valid.toInt < 8)
    (out : z.next_out ≠ .null) :
    ∃ (rc : Int32) (after : Heap) (z1 : ZStream) (d1 : DeflateState) (produced : Nat),
      trailerEnd (some r) (some (.tab ds)) h = .ok (rc, after) ∧ DGood after r ds z1 d1 ∧
      (∃ buf1, TreesInvAt after ds d1 pb buf1 ∧ buf1.size = buf.size) ∧ StreamBuffers after r ∧
      StreamAccounting z z1 0 produced ∧ (rc = Z_OK ∨ rc = Z_STREAM_END) ∧
      d1 = { d with pending := d1.pending, pending_out := d1.pending_out, wrap := d1.wrap } ∧
      d1.wrap.toInt ≤ 0 ∧ StageFrame h after r ds pb d z z1 produced ∧
      (d1.pending = 0 → d1.pending_out = d1.pending_buf) ∧ (rc = Z_STREAM_END ↔ d1.pending = 0) ∧
      (0 < d.wrap.toInt → d1.wrap.toInt = -d.wrap.toInt) := by
  obtain ⟨produced, H1, z1, d1, run1, good1, ⟨buf1, trees1, size1⟩, buffers1, account1, _copied, _left, fields1,
    empty1, _adler1, _gz1, _static1, _sizes1⟩ := header_flush good trees buffers low cursor out
  have stage1 := StageFrame.of_flush good trees buffers low cursor out run1 good1.live.hz account1
  have lo := good.inv.wrap_lo
  have hi := good.inv.wrap_hi
  have wrap1 : d1.wrap = d.wrap := by rw [fields1]
  have endZero : (if d1.pending != 0 then Z_OK else Z_STREAM_END) = Z_STREAM_END → d1.pending = 0 := by
    intro e
    by_cases p : d1.pending = 0
    · exact p
    · rw [if_pos (bne_iff_ne.mpr p)] at e; exact absurd e (by decide)
  have endIff : (if d1.pending != 0 then Z_OK else Z_STREAM_END) = Z_STREAM_END ↔ d1.pending = 0 :=
    ⟨endZero, fun p => by rw [p]; rfl⟩
  by_cases pos : d.wrap > 0
  · have posI : 0 < d.wrap.toInt := Int32.lt_iff_toInt_lt.mp pos
    have range : -2147483648 ≤ -d.wrap.toInt ∧ -d.wrap.toInt ≤ 2147483647 := by omega
    let nw : Int32 := Int32.ofInt (-d.wrap.toInt)
    have nwVal : nw.toInt = -d.wrap.toInt := Int32.toInt_ofInt_of_le range.1 (by omega)
    obtain ⟨good2, trees2, buffers2, _⟩ := wrap_engine good1 trees1 buffers1 nw (by omega) (by omega)
    refine ⟨if d1.pending != 0 then Z_OK else Z_STREAM_END, _, z1, _, produced, ?_, good2, ⟨buf1, trees2, size1⟩,
      buffers2, account1, by split <;> simp, by rw [fields1], by change nw.toInt ≤ 0; omega,
      by
        have s := StageFrame.trans stage1 (StageFrame.state good1 buffers1 trees1.base.pbuf { d1 with wrap := nw })
          (HeaderShape.owned (⟨_, _, _, _, _, _, _, _, fields1⟩ : HeaderShape d d1)) good buffers
        rwa [Nat.add_zero] at s, fun z0 => empty1 z0, endIff, fun _ => nwVal⟩
    unfold trailerEnd
    simp only [bind_app]
    rw [run1]
    simp only [rdD_eq, good1.live.hs, wrap1, pos, ite_true, ineg, chk32, range, and_self, pure_app, bind_app]
    simp only [wrD_eq, good1.live.hs, rdD_eq, setD_dstates_same, pure_app]
    rfl
  · refine ⟨if d1.pending != 0 then Z_OK else Z_STREAM_END, H1, z1, d1, produced, ?_, good1, ⟨buf1, trees1, size1⟩,
      buffers1, account1, by split <;> simp, by rw [fields1], ?_, stage1, empty1, endIff,
      fun p => by
        have := mt Int32.lt_iff_toInt_lt.mpr pos; change ¬ (0 < d.wrap.toInt) at this; exact absurd p this⟩
    · unfold trailerEnd
      simp only [bind_app]
      rw [run1]
      simp [rdD_eq, good1.live.hs, wrap1, pos]
    · rw [wrap1]; have := mt Int32.lt_iff_toInt_lt.mpr pos; change ¬ (0 < d.wrap.toInt) at this; omega

/-- **The trailer phase** from any state with room for the trailer and fewer than eight held bits:
it returns, keeping the engine invariants and the caller buffers; afterwards `wrap` is not
positive when a trailer was written. -/
theorem trailer_phase {h : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream} {d : DeflateState}
    {buf : Array UInt8} (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) (cursor : d.pending_out = d.pending_buf) (low : d.bi_valid.toInt < 8)
    (out : z.next_out ≠ .null) (room : d.pending.toNat + 8 ≤ buf.size) (flush : Int32) :
    ∃ (rc : Int32) (after : Heap) (z1 : ZStream) (d1 : DeflateState) (produced : Nat),
      trailerPhase (some r) (some (.tab ds)) flush h = .ok (rc, after) ∧ DGood after r ds z1 d1 ∧
      (∃ buf1, TreesInvAt after ds d1 pb buf1 ∧ buf1.size = buf.size) ∧ StreamBuffers after r ∧
      StreamAccounting z z1 0 produced ∧
      d1 = { d with pending := d1.pending, pending_out := d1.pending_out, wrap := d1.wrap } ∧
      StageFrame h after r ds pb d z z1 produced ∧ (rc = Z_OK ∨ rc = Z_STREAM_END) ∧
      (d1.pending = 0 → d1.pending_out = d1.pending_buf) ∧
      (rc = Z_STREAM_END → d1.pending = 0 ∨ d1.pending = d.pending) ∧
      (flush ≠ Z_FINISH → rc = Z_OK ∧ after = h ∧ d1 = d) ∧
      (d1.wrap = d.wrap ∨ (0 < d.wrap.toInt ∧ d1.wrap.toInt = -d.wrap.toInt)) ∧
      (rc = Z_STREAM_END ↔ (d.wrap.toInt ≤ 0 ∧ d1 = d ∧ flush = Z_FINISH) ∨
        (0 < d.wrap.toInt ∧ flush = Z_FINISH ∧ d1.pending = 0)) := by
  have lo := good.inv.wrap_lo
  have hi := good.inv.wrap_hi
  rw [trailer_phase_split]
  unfold trailerPhase'
  by_cases fin : flush = Z_FINISH
  · subst fin
    by_cases nonpos : d.wrap ≤ 0
    · refine ⟨Z_STREAM_END, h, z, d, 0, ?_, good, ⟨buf, trees, rfl⟩, buffers, stream_accounting_zero z, rfl,
        StageFrame.refl good buffers trees.base.pbuf, Or.inr rfl, fun _ => cursor, fun _ => Or.inr rfl,
        fun nf => absurd rfl nf, Or.inl rfl,
        ⟨fun _ => Or.inl ⟨Int32.le_iff_toInt_le.mp nonpos, rfl, rfl⟩, fun _ => rfl⟩⟩
      simp [bind_app, rdD_eq, good.live.hs, nonpos, pure_app]
    · have pos : 0 < d.wrap.toInt := by
        have := mt Int32.le_iff_toInt_le.mpr nonpos; change ¬ (d.wrap.toInt ≤ 0) at this; omega
      have pre : ∀ K : M Int32, (do
          if Z_FINISH != Z_FINISH then return Z_OK
          if (← rd (some (.tab ds)) (·.wrap)) ≤ 0 then return Z_STREAM_END
          trailerBytes (some r) (some (.tab ds)) K) h = trailerBytes (some r) (some (.tab ds)) K h := by
        intro K
        simp [bind_app, rdD_eq, good.live.hs, nonpos]
      by_cases two : d.wrap = 2
      · obtain ⟨H1, d1, buf1, run1, good1, trees1, size1, buffers1, frame1, fields1, count1⟩ :=
          trailer_gzip good trees buffers cursor room two (trailerEnd (some r) (some (.tab ds)))
        obtain ⟨rc, H2, z2, d2, produced, run2, good2, trees2, buffers2, account2, rcs2, fields2, _, stage2, cur2,
          end2, wrap2⟩ :=
          trailer_end good1 trees1 buffers1 (by rw [fields1]; exact cursor) (by rw [fields1]; exact low) out
        obtain ⟨b2, t2, s2⟩ := trees2
        refine ⟨rc, H2, z2, d2, produced, ?_, good2, ⟨b2, t2, s2.trans size1⟩, buffers2, account2, ?_, ?_, rcs2, cur2,
          fun e => Or.inl (end2.mp e), fun nf => absurd rfl nf,
          Or.inr ⟨pos, by
            have w1 : d1.wrap = d.wrap := by rw [fields1]
            rw [wrap2 (by rw [w1]; exact pos), w1]⟩,
          ⟨fun e => Or.inr ⟨pos, rfl, end2.mp e⟩, fun e => by
            rcases e with ⟨np, _, _⟩ | ⟨_, _, p⟩
            · omega
            · exact end2.mpr p⟩⟩
        · rw [pre, run1, run2]
        · rw [fields2, fields1]
        · have s := StageFrame.trans
            (StageFrame.of_header frame1 good buffers trees.base.pbuf (stream_accounting_zero z) good1.live.hz)
            stage2 (HeaderShape.owned (⟨_, _, _, _, _, _, _, _, fields1⟩ : HeaderShape d d1)) good buffers
          rwa [Nat.zero_add] at s
      · obtain ⟨H1, d1, buf1, run1, good1, trees1, size1, buffers1, frame1, fields1, count1⟩ :=
          trailer_zlib good trees buffers cursor (by omega) two (trailerEnd (some r) (some (.tab ds)))
        obtain ⟨rc, H2, z2, d2, produced, run2, good2, trees2, buffers2, account2, rcs2, fields2, _, stage2, cur2,
          end2, wrap2⟩ :=
          trailer_end good1 trees1 buffers1 (by rw [fields1]; exact cursor) (by rw [fields1]; exact low) out
        obtain ⟨b2, t2, s2⟩ := trees2
        refine ⟨rc, H2, z2, d2, produced, ?_, good2, ⟨b2, t2, s2.trans size1⟩, buffers2, account2, ?_, ?_, rcs2, cur2,
          fun e => Or.inl (end2.mp e), fun nf => absurd rfl nf,
          Or.inr ⟨pos, by
            have w1 : d1.wrap = d.wrap := by rw [fields1]
            rw [wrap2 (by rw [w1]; exact pos), w1]⟩,
          ⟨fun e => Or.inr ⟨pos, rfl, end2.mp e⟩, fun e => by
            rcases e with ⟨np, _, _⟩ | ⟨_, _, p⟩
            · omega
            · exact end2.mpr p⟩⟩
        · rw [pre, run1, run2]
        · rw [fields2, fields1]
        · have s := StageFrame.trans
            (StageFrame.of_header frame1 good buffers trees.base.pbuf (stream_accounting_zero z) good1.live.hz)
            stage2 (HeaderShape.owned (⟨_, _, _, _, _, _, _, _, fields1⟩ : HeaderShape d d1)) good buffers
          rwa [Nat.zero_add] at s
  · refine ⟨Z_OK, h, z, d, 0, ?_, good, ⟨buf, trees, rfl⟩, buffers, stream_accounting_zero z, rfl,
      StageFrame.refl good buffers trees.base.pbuf, Or.inl rfl, fun _ => cursor, fun _ => Or.inr rfl,
      fun _ => ⟨rfl, rfl, rfl⟩, Or.inl rfl,
      ⟨fun e => absurd e (by decide), fun e => by rcases e with ⟨_, _, g⟩ | ⟨_, g, _⟩ <;> exact absurd g fin⟩⟩
    simp [bind_app, bne_iff_ne.mpr fin, pure_app]

end Zlib.Deflate.Universal.Call
