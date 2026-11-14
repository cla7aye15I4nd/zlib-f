import ZlibF.Spec.Public.Initialisation

namespace ZlibF.Spec.Public
open C ZlibF.Spec

def inflateResetState (i : Nat) (s : InflateState) : InflateState :=
  { s with
    total := 0, mode := HEAD, last := 0, havedict := 0, flags := -1, dmax := 32768
    head := none, hold := 0, bits := 0
    lencode := .ref (.istate_codes i) 0, distcode := .ref (.istate_codes i) 0
    next := .ref (.istate_codes i) 0, sane := 1, back := -1 }

def inflateResetStream (z : ZStream) (s : InflateState) : ZStream :=
  { z with
    total_in := 0, total_out := 0, msg := .null, data_type := 0
    adler := if s.wrap = 0 then z.adler else (s.wrap &&& 1).toInt64.toUInt64 }

def inflateResetPre (s : InflateState) : InflateState :=
  { s with
    window := if s.wbits = s.reqbits then s.window else .null
    wbits := s.reqbits, wrap := s.reqwrap, wsize := 0, whave := 0, wnext := 0 }

def InflateDictionary (h : Heap) (s : InflateState) (xs : List UInt8) : Prop :=
  (s.whave = 0 ∧ xs = []) ∨ ∃ r off a,
    s.window = .ref r off ∧ Space.get h r = some a ∧
    off + s.wsize.toNat ≤ a.size ∧
    xs = ((a.toList.drop (off + s.wnext.toNat)).take (s.whave - s.wnext).toNat ++
          (a.toList.drop off).take s.wnext.toNat)

def DeflateDictionary (h : Heap) (s : DeflateState) (xs : List UInt8) : Prop :=
  ∃ r off a, s.window = .ref r off ∧ Space.get h r = some a ∧
    off + s.strstart.toNat + s.lookahead.toNat ≤ a.size ∧
    xs = (a.toList.drop (off + s.strstart.toNat + s.lookahead.toNat -
      min s.w_size.toNat (s.strstart.toNat + s.lookahead.toNat))).take
      (min s.w_size.toNat (s.strstart.toNat + s.lookahead.toNat))

def DeflateResetContract (program : ZStreamPtr → M Int32) (keep : Bool) : Prop :=
  ∀ h r i z s, Zlib.Deflate.Spec.DGood h r i z s →
    ∃ after z' s', C.run (program (some r)) h = .ok (Z_OK, after) ∧
      Zlib.Deflate.Spec.DGood after r i z' s' ∧
      z' = { z with
        total_in := 0, total_out := 0, msg := .null, data_type := Z_UNKNOWN
        adler := if s.wrap = 2 ∨ s.wrap = -2 then 0 else 1 } ∧
      s'.wrap.toInt = s.wrap.toInt.natAbs ∧ s'.pending = 0 ∧ s'.pending_out = s.pending_buf ∧
      s'.last_flush = -2 ∧ s'.gzhead = none ∧ s'.lookahead = 0 ∧
      s'.bi_valid = 0 ∧ s'.bi_buf = 0 ∧ s'.bi_used = 0 ∧
      s'.level = s.level ∧ s'.strategy = s.strategy ∧
      s'.window = s.window ∧ s'.head = s.head ∧ s'.prev = s.prev ∧ s'.pending_buf = s.pending_buf ∧
      after.bytes = h.bytes ∧
      (keep = true → s'.strstart = s.strstart ∧ s'.block_start = s.strstart.toUInt64.toInt64 ∧
        after.words = h.words) ∧
      (keep = false → s'.strstart = 0 ∧ s'.block_start = 0 ∧ s'.insert = 0 ∧ s'.ins_h = 0 ∧
        ∀ ref off a, s.head = .ref ref off → Space.get after ref = some a →
          ∀ j, j < s.hash_size.toNat → a[off + j]? = some 0) ∧
      Frame h after (fun b => StreamRoot r b ∨ DeflateOwned i s b) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧ after.nalloc = h.nalloc

end ZlibF.Spec.Public
