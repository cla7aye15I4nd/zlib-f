import ZlibF.Spec.PlatformMemory
import ZlibF.Spec.InflateFast

/-!
# Fast-decoder entry under the explicit platform object-size premise

The entry retains the existing table, window and buffer obligations. The
input/output size facts are derived from one named environment premise.
This remains an internal raw-block, distinct-buffer interface.
-/

namespace Zlib.Inffast.Spec
open C Zlib.Inffast.Proofs
set_option autoImplicit false

/-- Platform-scoped fast entry. Byte objects are smaller than `2^63`.
This explicit premise includes caller storage; it is not derived from the
unrestricted public history. Distinct raw input/output blocks, safe decoding
tables and the existing fast margins remain required. -/
structure PlatformEntry where
  h0 : Heap
  platform : ZlibF.PlatformMemory.ByteObjectsFit h0
  strm : ZStreamPtr
  start : UInt32
  -- the stream record and the state
  r : ZStreamRef
  sm0 : ZStream
  stid : Nat
  s0 : InflateState
  hstrm : strm = some r
  hsm : r.get h0 = some sm0
  hrw : r.isRo = false
  hstate : sm0.state = some (StateRef.inflate stid)
  hs0 : h0.istates stid = some s0
  -- the input
  ib : Nat
  i0 : Nat
  IN : Array UInt8
  hnin : sm0.next_in = .ref (BRef.blk ib) i0
  hIN : h0.bytes ib = some IN
  hai : 6 ≤ sm0.avail_in.toNat
  hINsz : i0 + sm0.avail_in.toNat ≤ IN.size
  -- the output
  ob : Nat
  o0 : Nat
  A0 : Array UInt8
  hnout : sm0.next_out = .ref (BRef.blk ob) o0
  hA0 : h0.bytes ob = some A0
  hro : h0.ro ob = false
  hao : 258 ≤ sm0.avail_out.toNat
  hAsz : o0 + sm0.avail_out.toNat ≤ A0.size
  hstart : sm0.avail_out.toNat ≤ start.toNat
  hbeg : start.toNat - sm0.avail_out.toNat ≤ o0
  hsep : ib ≠ ob
  -- the bit buffer
  hbits : s0.bits.toNat < 8
  hhold : s0.hold.toNat < 2 ^ s0.bits.toNat
  hsane : s0.sane ≠ 0
  -- the window
  hws : s0.wsize.toNat ≤ 32768
  hwh : s0.whave.toNat ≤ s0.wsize.toNat
  hwn : s0.wnext.toNat ≤ s0.wsize.toNat
  wb : Nat
  woff : Nat
  W : Array UInt8
  hwin : s0.whave ≠ 0 →
    s0.window = .ref (BRef.blk wb) woff ∧ wb ≠ ob ∧ h0.bytes wb = some W ∧ woff + s0.wsize.toNat ≤ W.size
  -- the tables
  rl : CodeRef
  ol : Nat
  LCA : Array Code
  hlc : s0.lencode = .ref rl ol
  hLCA : Space.get h0 rl = some LCA
  hlt : LenTableSafe LCA ol s0.lenbits.toNat
  rd : CodeRef
  od : Nat
  DCA : Array Code
  hdc : s0.distcode = .ref rd od
  hDCA : Space.get h0 rd = some DCA
  hdt : DistTableSafe DCA od s0.distbits.toNat

/-- Supply the two existing size fields from the platform premise. -/
def PlatformEntry.toEnv (e : PlatformEntry) : Env where
  h0 := e.h0
  strm := e.strm
  start := e.start
  r := e.r
  sm0 := e.sm0
  stid := e.stid
  s0 := e.s0
  hstrm := e.hstrm
  hsm := e.hsm
  hrw := e.hrw
  hstate := e.hstate
  hs0 := e.hs0
  ib := e.ib
  i0 := e.i0
  IN := e.IN
  hnin := e.hnin
  hIN := e.hIN
  hai := e.hai
  hINsz := e.hINsz
  hINbig := e.platform (.blk e.ib) e.IN e.hIN
  ob := e.ob
  o0 := e.o0
  A0 := e.A0
  hnout := e.hnout
  hA0 := e.hA0
  hro := e.hro
  hao := e.hao
  hAsz := e.hAsz
  hAbig := e.platform (.blk e.ob) e.A0 e.hA0
  hstart := e.hstart
  hbeg := e.hbeg
  hsep := Or.inl e.hsep
  hbits := e.hbits
  hhold := e.hhold
  hsane := e.hsane
  hws := e.hws
  hwh := e.hwh
  hwn := e.hwn
  wb := e.wb
  woff := e.woff
  W := e.W
  hwin := e.hwin
  rl := e.rl
  ol := e.ol
  LCA := e.LCA
  hlc := e.hlc
  hLCA := e.hLCA
  hlt := e.hlt
  rd := e.rd
  od := e.od
  DCA := e.DCA
  hdc := e.hdc
  hDCA := e.hDCA
  hdt := e.hdt

end Zlib.Inffast.Spec
