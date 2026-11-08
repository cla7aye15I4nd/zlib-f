import ZlibF.Proof.«inffast.c.final»
import ZlibF.Proof.«inflate.c.base»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inffast.Spec Zlib.Inffast.Proofs
set_option autoImplicit false

/-- The translated fast-call suffix, factored at the loop exit. -/
def fastAfterLoopView (c : Zlib.Inffast.Ctx)
    (l : Zlib.Inffast.L) : M Unit := do
  let len := l.bits >>> 3
  let in_ ← Zlib.Inffast.subn l.in_ len
  let bits := l.bits - (len <<< 3)
  let hold := l.hold &&&
    ((← Zlib.Inffast.shl32 1 bits) - 1).toUInt64
  let ai : Int64 ←
    if ← Ptr.lt in_ c.last then do
      let d ← c.last.diff in_
      Zlib.Inffast.chk64 (5 + d.toInt)
    else do
      let d ← in_.diff c.last
      Zlib.Inffast.chk64 (5 - d.toInt)
  let ao : Int64 ←
    if ← Ptr.lt l.out c.end_ then do
      let d ← c.end_.diff l.out
      Zlib.Inffast.chk64 (257 + d.toInt)
    else do
      let d ← l.out.diff c.end_
      Zlib.Inffast.chk64 (257 - d.toInt)
  let sm ← ldZStream c.strm
  stZStream c.strm { sm with next_in := in_, next_out := l.out, avail_in := ai.toUInt64.toUInt32, avail_out := ao.toUInt64.toUInt32 }
  let s ← ldInflateState c.state
  stInflateState c.state { s with hold, bits }

/-- The loop and the checked writeback in their translated order. -/
def fastAfterPrefixView (c : Zlib.Inffast.Ctx)
    (initial : Zlib.Inffast.L) : M Unit := do
  let l ← cdoWhile (Zlib.Inffast.inflate_fast_body c)
    (fun l => do
      if l.broke then pure (false, l)
      else if ← Ptr.lt l.in_ c.last then
        pure (← Ptr.lt l.out c.end_, l)
      else pure (false, l)) initial
  fastAfterLoopView c l

/-- A source-order continuation cut at the fast loop entry. -/
def fastEntryWithView (strm : ZStreamPtr) (start : UInt32)
    (k : Zlib.Inffast.Ctx → Zlib.Inffast.L → M Unit) : M Unit := do
  let sm ← ldZStream strm
  let state ← castInflateState sm.state
  let in_ := sm.next_in
  let last ← in_.add (sm.avail_in - 5).toNat
  let out := sm.next_out
  let beg ← Zlib.Inffast.subn out (start - sm.avail_out)
  let end_ ← out.add (sm.avail_out - 257).toNat
  let s ← ldInflateState state
  let lmask := (← Zlib.Inffast.shl32 1 s.lenbits) - 1
  let dmask := (← Zlib.Inffast.shl32 1 s.distbits) - 1
  let c : Zlib.Inffast.Ctx := {
    strm, state, last, beg, end_, wsize := s.wsize,
    whave := s.whave, wnext := s.wnext,
    window := s.window, lcode := s.lencode,
    dcode := s.distcode, lmask, dmask }
  let l : Zlib.Inffast.L := {
    in_, out, hold := s.hold, bits := s.bits,
    here := default, op := 0, len := 0, dist := 0,
    from_ := default, broke := false,
    againL := false, againD := false }
  k c l

/-- The cut is definitionally the actual translated C function. -/
theorem inflate_fast_view_split (strm : ZStreamPtr) (start : UInt32) :
    Zlib.Inffast.inflate_fast strm start =
      fastEntryWithView strm start fastAfterPrefixView := by
  rfl

/-- The source-order stream and state stores work with arbitrary input and
output byte references, including the same reference. -/
theorem fastStoresView {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState}
    (hz : r.get h = some z) (hro : r.isRo = false)
    (hs : h.istates zs = some s)
    (input output : BPtr) (ai ao : UInt32)
    (hold : UInt64) (bits : UInt32) :
    let z' := { z with next_in := input, next_out := output, avail_in := ai, avail_out := ao }
    let h' := r.put h z'
    (do
      let sm ← ldZStream (some r)
      stZStream (some r) { sm with next_in := input, next_out := output, avail_in := ai, avail_out := ao }
      let st ← ldInflateState (some (.tab zs))
      stInflateState (some (.tab zs)) { st with hold, bits }) h =
    .ok ((), { h' with istates := upd h'.istates zs (some { s with hold, bits }) }) := by
  dsimp only
  rw [bind_ok (ldZStream_ok hz), bind_ok (stZStream_ok hz hro)]
  have hs' : (r.put h { z with next_in := input, next_out := output, avail_in := ai, avail_out := ao }).istates zs = some s := by
    rw [ZStreamRef.put_istates]
    exact hs
  rw [bind_ok (ldInflateState_tab hs'), stInflateState_tab hs']

/-- Normalizing whole buffered bytes leaves fewer than eight bits,
regardless of the bit count on a broken decoder branch. -/
theorem fastResidualBits_lt32 (bits : UInt32) :
    (bits - ((bits >>> 3) <<< 3)).toNat < 32 := by
  have whole := Zlib.Inffast.Proofs.bits_whole bits
  have shifted : ((bits >>> 3) <<< 3).toNat =
      bits.toNat / 8 * 8 := by
    rw [UInt32.toNat_shiftLeft, whole, Nat.shiftLeft_eq]
    change (bits.toNat / 8 * 8) % 4294967296 =
      bits.toNat / 8 * 8
    exact Nat.mod_eq_of_lt (by
      have width := UInt32.toNat_lt bits
      omega)
  have within : ((bits >>> 3) <<< 3).toNat ≤ bits.toNat := by
    rw [shifted]
    omega
  rw [Zlib.Inffast.Proofs.u32_toNat_sub within, shifted]
  omega

/-- Exact normalization and writeback for any represented caller byte views.
The same byte reference may be used for input and output if the caller's
interval invariant permits it. -/
theorem fastAfterLoopView_run {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState}
    {ir or_ : BRef} {ia oa : Array UInt8}
    {io last oo end_ : Nat}
    (c : Zlib.Inffast.Ctx) (l : Zlib.Inffast.L)
    (hstrm : c.strm = some r) (hstate : c.state = some (.tab zs))
    (hz : r.get h = some z) (hro : r.isRo = false)
    (hs : h.istates zs = some s)
    (hin : Space.get h ir = some ia)
    (hout : Space.get h or_ = some oa)
    (hsizeIn : ia.size < 2 ^ 63) (hsizeOut : oa.size < 2 ^ 63)
    (hinPtr : l.in_ = .ref ir io) (hlast : c.last = .ref ir last)
    (houtPtr : l.out = .ref or_ oo) (hend : c.end_ = .ref or_ end_)
    (hio : io ≤ ia.size) (hlastBound : last ≤ ia.size)
    (hoo : oo ≤ oa.size) (hendBound : end_ ≤ oa.size)
    (hbuffer : (l.bits >>> 3).toNat ≤ io)
    (hinRemain : io - (l.bits >>> 3).toNat ≤ last + 5)
    (hinRemain32 : last + 5 - (io - (l.bits >>> 3).toNat) < 2 ^ 32)
    (houtRemain : oo ≤ end_ + 257)
    (houtRemain32 : end_ + 257 - oo < 2 ^ 32) :
    let input : BPtr := .ref ir (io - (l.bits >>> 3).toNat)
    let bits := l.bits - ((l.bits >>> 3) <<< 3)
    let hold := l.hold &&& (((1 : UInt32) <<< bits) - 1).toUInt64
    let ai := UInt32.ofNat (last + 5 - (io - (l.bits >>> 3).toNat))
    let ao := UInt32.ofNat (end_ + 257 - oo)
    let z' := { z with next_in := input, next_out := l.out, avail_in := ai, avail_out := ao }
    let h' := r.put h z'
    fastAfterLoopView c l h =
      .ok ((), { h' with istates := upd h'.istates zs (some { s with hold, bits }) }) := by
  have hsmall := fastResidualBits_lt32 l.bits
  have hw : Wp (fastAfterLoopView c l) h
      (fun _ after => after =
        let input : BPtr := .ref ir (io - (l.bits >>> 3).toNat)
        let bits := l.bits - ((l.bits >>> 3) <<< 3)
        let hold := l.hold &&& (((1 : UInt32) <<< bits) - 1).toUInt64
        let ai := UInt32.ofNat (last + 5 - (io - (l.bits >>> 3).toNat))
        let ao := UInt32.ofNat (end_ + 257 - oo)
        let z' := { z with next_in := input, next_out := l.out, avail_in := ai, avail_out := ao }
        let h' := r.put h z'
        { h' with istates := upd h'.istates zs (some { s with hold, bits }) }) := by
    unfold fastAfterLoopView
    rw [hstrm, hstate, hinPtr, hlast, houtPtr, hend]
    refine Wp.bindO (Zlib.Inffast.Proofs.subn_ok hin hbuffer hio) ?_
    refine Wp.bindO (Zlib.Inffast.Proofs.shl32_ok (x := 1) hsmall) ?_
    refine Zlib.Inffast.Proofs.ptr_avail_wp hin (by omega) hlastBound hsizeIn
      hinRemain (by decide) hinRemain32 ?_
    refine Zlib.Inffast.Proofs.ptr_avail_wp hout hoo hendBound hsizeOut
      houtRemain (by decide) houtRemain32 ?_
    rw [Zlib.Inffast.Proofs.i64_to_u32_eq _ hinRemain32,
      Zlib.Inffast.Proofs.i64_to_u32_eq _ houtRemain32]
    exact Wp.of_eq (fastStoresView hz hro hs _ _ _ _ _ _) rfl
  obtain ⟨⟨⟩, after, run, post⟩ := hw
  simpa only [post] using run

end Zlib.Inflate.Proofs
