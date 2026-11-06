import ZlibF.Spec.InflateTableContent
import ZlibF.Spec.Format.Huffman

/-!
# Canonical symbols in the constructed LENS and DISTS tables

This internal bridge starts with a successful independent Huffman decode.
It requires fifteen available bits so both levels can be indexed without
padding. Actual early-returning lookup with less input needs a later bridge.
The relation includes reserved symbols and identifies their invalid flag.
-/

namespace Zlib.Inftrees.Spec.DecodeSemantics
open C Zlib.Inftrees Zlib.Inftrees.Proofs

/-- The two-level table access used by the slow decoder. Link values are
offsets from the table start; the second entry's bit count excludes the root.
Only this finite access is modeled here, not input refill or bit dropping. -/
def tableRead (type : UInt32) (ca : Array Code) (offset root : Nat)
    (inp : List Bool) : Option (Code × Nat) := do
  let (i, _) ← ZlibF.Spec.readBits root inp
  let first ← ca[offset + i]?
  let link := if type = LENS then first.op != 0 && (first.op &&& 0xf0) == 0
    else (first.op &&& 0xf0) == 0
  if link then
    let (j, _) ← ZlibF.Spec.readBits first.op.toNat (inp.drop first.bits.toNat)
    let second ← ca[offset + first.val.toNat + j]?
    return (second, first.bits.toNat + second.bits.toNat)
  else return (first, first.bits.toNat)

/-- Independent DEFLATE meanings of leaf operations. Reserved symbols are
invalid, even though they have canonical codes in some accepted tables. -/
def SymbolEntry (type : UInt32) (symbol : Nat) (entry : Code) : Prop :=
  if type = LENS then
    if symbol < 256 then entry.op = 0 ∧ entry.val.toNat = symbol
    else if symbol = 256 then entry.op = 96 ∧ entry.val = 0
    else if symbol ≤ 285 then
      entry.op.toNat = 16 + ZlibF.Spec.lengthExtras.getD (symbol - 257) 0 ∧
      entry.val.toNat = ZlibF.Spec.lengthBases.getD (symbol - 257) 0
    else (entry.op &&& 64) != 0
  else
    if symbol ≤ 29 then
      entry.op.toNat = 16 + ZlibF.Spec.distExtras.getD symbol 0 ∧
      entry.val.toNat = ZlibF.Spec.distBases.getD symbol 0
    else (entry.op &&& 64) != 0

/-- The actual constructor's table selects the independent decoder's symbol,
with the exact consumed code length and the DEFLATE leaf meaning. This is
the forward direction for full-width input. It does not yet assert that
every table result is a valid independent symbol. -/
def Goal.decode_table_matches_format : Prop :=
  ∀ (h : Heap) (type : UInt32) (rl : WRef) (ol : Nat) (codes : UInt32)
    (rc : CodeRef) (oc : Nat) (bits : UInt32) (rw : WRef) (ow : Nat)
    (pre : CallPre h type rl ol codes rc oc bits rw ow),
    (type = LENS ∨ type = DISTS) →
    ∃ (r : Int32 × CodePtr × UInt32) (after : Heap),
      C.run (inflate_table type (.ref rl ol) codes (.ref rc oc) bits (.ref rw ow)) h =
        .ok (r, after) ∧
      (r.1 = 0 → ∀ (inp : List Bool) (symbol : Nat) (rest : List Bool),
        15 ≤ inp.length →
        ZlibF.Spec.decodeSym (lensOf pre.f codes.toNat) inp = some (symbol, rest) →
        ∃ (ca : Array Code) (entry : Code) (used : Nat),
          Space.get after rc = some ca ∧
          tableRead type ca oc r.2.2.toNat inp = some (entry, used) ∧
          used = (lensOf pre.f codes.toNat).getD symbol 0 ∧
          rest = inp.drop used ∧ SymbolEntry type symbol entry)

end Zlib.Inftrees.Spec.DecodeSemantics
