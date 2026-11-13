import ZlibF.Proof.«infback.c.safety-bits»
import ZlibF.Proof.«infback.c.safety-len-defs»
import ZlibF.Proof.«inffast.c.dist»

/-!
# infback.c: the lookup of one literal/length or distance symbol on the loop invariant

`symLook`: `lookup1`, and after a root link `last = here; lookup2; DROPBITS(last.bits)`. On a
table with the shape `TableSafe`, the decode invariant and query stability, `symLook_p` ends
with a leaf (`P d here`, `d` the bits of the link already dropped) whose bits are held, the input
part of the measure down by `4 d`, and fewer than 8 bits left once the leaf's bits are dropped
(from fewer than 8); or with `Z_BUF_ERROR` from `in`.
-/

namespace Zlib.Infback.Safety
open C ZlibF.Spec ZlibF.Spec.Public Zlib.Inflate Zlib.Inflate.Proofs Zlib.Infback Zlib.Infback.Proofs
open Zlib.Inftrees.Spec.DecodeSemantics (tableRead)
open Zlib.Inftrees.Spec.DecodeTableStability (StableQuery)
open Zlib.Inftrees.Proofs (PrefixQuery)
open Zlib.Inffast.Spec (TableSafe LinkOK)
open Zlib.Inffast (inflate_fast)
set_option autoImplicit false

/-- The lookup of one symbol: the root lookup, and the second level after a link. -/
def symLook (c : BCtx) (dist : Bool) (isLink : Code → Bool) (k : X Unit) : X Unit := do
  lookup1 c dist
  let here := (← get).here
  if isLink here then
    modify fun l => { l with last := here }
    lookup2 c dist
    DROPBITS (← get).last.bits.toUInt32
  k

/-- The link test of the literal/length code. -/
def lenIsLink (here : Code) : Bool := here.op != 0 && (here.op &&& 0xf0) == 0
/-- The link test of the distance code. -/
def distIsLink (here : Code) : Bool := (here.op &&& 0xf0) == 0

theorem lenDist_eq (c : BCtx) : lenDist c = symLook c true distIsLink (distSym c) := rfl

theorem back_LEN_eq' (c : BCtx) : back_LEN c = (do
    let l ← get
    if l.have_ >= 6 && l.left >= 258 then
      RESTORE c.strm c.st
      inflate_fast c.strm (← rdS c.st (·.wsize))
      LOAD c.strm c.st
      return
    symLook c false lenIsLink (lenSym c)) := rfl

theorem lenIsLink_eq (e : Code) : lenIsLink e = Zlib.Inftrees.Spec.Subtable.IsLink LENS e := by
  simp [lenIsLink, Zlib.Inftrees.Spec.Subtable.IsLink]

theorem distIsLink_eq (e : Code) : distIsLink e = Zlib.Inftrees.Spec.Subtable.IsLink DISTS e := by
  simp [distIsLink, Zlib.Inftrees.Spec.Subtable.IsLink, DISTS, LENS]

theorem lenLink_of_code : ∀ x : UInt8, (x != 0 && (x &&& 0xf0) == 0) = true →
    x ≠ 0 ∧ x &&& 16 = 0 ∧ x &&& 64 = 0 := Zlib.Inffast.Proofs.u8_forall _ (by decide +kernel)
theorem code_of_lenLink : ∀ x : UInt8, x ≠ 0 → x &&& 16 = 0 → x &&& 64 = 0 → x.toNat ≤ 15 →
    (x != 0 && (x &&& 0xf0) == 0) = true := Zlib.Inffast.Proofs.u8_forall _ (by decide +kernel)
theorem distLink_of_code : ∀ x : UInt8, ((x &&& 0xf0) == 0) = true → x &&& 16 = 0 ∧ x &&& 64 = 0 :=
  Zlib.Inffast.Proofs.u8_forall _ (by decide +kernel)
theorem code_of_distLink : ∀ x : UInt8, x.toNat ≤ 15 → ((x &&& 0xf0) == 0) = true :=
  Zlib.Inffast.Proofs.u8_forall _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- **The lookup of one symbol on the invariant.** -/
theorem symLook_p (c : BCtx) {r : ZStreamRef} {i : Nat} {window : BPtr} {n : Nat}
    (pr : Proto c r i window n) (dist : Bool) (isLink : Code → Bool) (k : X Unit) {h0 h : Heap} {l : IL}
    {log : BackLog} (I : PInv c pr h0 h l log) {s : InflateState} (hs : h.istates i = some s)
    {type : UInt32} {ref : CodeRef} {off : Nat} {ca : Array Code} {nb : UInt32}
    (tab : (if dist then s.distcode else s.lencode) = .ref ref off)
    (hnb : (if dist then s.distbits else s.lenbits) = nb) (refOk : TabRef i ref)
    (tget : Space.get h ref = some ca) {P : Nat → Code → Prop} {L : Code → Prop} [DecidablePred L]
    (safe : TableSafe P L ca off nb.toNat) (P15 : ∀ d e, P d e → e.bits.toNat + d ≤ 15)
    (linkEq : ∀ e, isLink e = Zlib.Inftrees.Spec.Subtable.IsLink type e)
    (codeL : ∀ e, isLink e = true → L e) (Lcode : ∀ e, L e → e.op.toNat ≤ 15 → isLink e = true)
    {used : Nat} {lens : List Nat}
    (inv : Zlib.Inftrees.Spec.DecodeTableInvariant.Inv type ca off nb.toNat used lens)
    (stable : StableQuery type ca off nb.toNat) (pfx : PrefixQuery type ca off nb.toNat)
    (short : l.bits.toNat < 8) :
    (∃ l' h' log', runX (symLook c dist isLink k) l h = .ok ((.error Ex.leave, l'), h') ∧
      PInv c pr h0 h' l' log' ∧ l'.ret = Z_BUF_ERROR) ∨
    (∃ l2 h2 log2 d, runX (symLook c dist isLink k) l h = runX k l2 h2 ∧ PInv c pr h0 h2 l2 log2 ∧
      h2.istates i = h.istates i ∧ l2.put = l.put ∧ l2.left = l.left ∧ P d l2.here ∧
      1 ≤ d + l2.here.bits.toNat ∧ l2.here.bits.toNat ≤ l2.bits.toNat ∧
      l2.bits.toNat - l2.here.bits.toNat < 8 ∧ baseM pr l2 log2 + 4 * d ≤ baseM pr l log) := by
  obtain ⟨R15, room, cells⟩ := safe
  obtain ⟨rootPos, -, -, rootCells⟩ := inv.rootTable
  have entries : ∀ j, j < 2 ^ nb.toNat → (ca.getD (off + j) default).bits.toNat ≤ 15 := by
    intro j hj
    have := cells j hj
    split at this
    · exact this.1
    · have := P15 _ _ this; omega
  obtain ⟨res1, l1, h1, log1, run1, I1, ist1, okc1, errc1, meas1⟩ :=
    lookup1_p c pr dist I hs tab hnb refOk tget R15 room entries
  have b1 := baseM_le meas1
  cases res1 with
  | error e =>
    obtain ⟨rfl, ret⟩ := errc1 e rfl
    left
    refine ⟨l1, h1, log1, ?_, I1, ret⟩
    unfold symLook
    rw [runX_bind, run1]
  | ok u =>
    cases u
    obtain ⟨put1, left1, here1, fit1, ext1, pull1⟩ := okc1 rfl
    have hs1 : h1.istates i = some s := ist1.trans hs
    have get1 : Space.get h1 ref = some ca := (refOk.get_eq ist1 (I.static_eq I1)).trans tget
    have hl1 : l1.hold.toNat < 2 ^ l1.bits.toNat := I1.bits.2
    have idx1 : l1.hold.toNat % 2 ^ nb.toNat < 2 ^ nb.toNat := Nat.mod_lt _ (Nat.two_pow_pos _)
    have inside1 : off + l1.hold.toNat % 2 ^ nb.toNat < ca.size := by omega
    have getE : ca[off + l1.hold.toNat % 2 ^ nb.toNat]? = some l1.here := by
      rw [here1, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem inside1]; rfl
    have cell1 := cells _ idx1
    rw [← here1] at cell1
    have rootBits : 1 ≤ l1.here.bits.toNat := by
      obtain ⟨e0, g0, p0, -⟩ := rootCells _ idx1
      rw [getE] at g0; cases g0; exact p0
    by_cases lk : isLink l1.here = true
    · -- a link: the second level
      have Lh := codeL _ lk
      rw [if_pos Lh] at cell1
      have link := cell1
      obtain ⟨bitsR, -⟩ := inv.subtables _ _ idx1 getE (by rw [← linkEq]; exact lk)
      have I1' := I1.withLast l1.here
      have sub15 : ∀ j, j < 2 ^ l1.here.op.toNat →
          l1.here.bits.toNat + (ca.getD (off + l1.here.val.toNat + j) default).bits.toNat ≤ 15 := by
        intro j hj; have := P15 _ _ (link.2.2.2.2 j hj); omega
      obtain ⟨res3, l3, h3, log3, run3, I3, ist3, okc3, errc3, meas3⟩ :=
        lookup2_p c pr dist I1' hs1 tab refOk get1 (l := { l1 with last := l1.here }) link sub15
      have b3 := baseM_le meas3
      have pre : runX (symLook c dist isLink k) l h =
          runX (do Zlib.Infback.lookup2 c dist; DROPBITS (← get).last.bits.toUInt32; k)
            { l1 with last := l1.here } h1 := by
        unfold symLook
        simp only [runX_bind, run1, runX_get, lk, ↓reduceIte, runX_modify]
      cases res3 with
      | error e =>
        obtain ⟨rfl, ret⟩ := errc3 e rfl
        left
        refine ⟨l3, h3, log3, ?_, I3, ret⟩
        rw [pre, runX_bind, run3]
      | ok u =>
        cases u
        obtain ⟨put3, left3, last3, here3, fit3, ext3, pull3⟩ := okc3 rfl
        have lb64 : l1.here.bits.toUInt32.toNat < 64 := by rw [UInt8.toNat_toUInt32]; have := link.1; omega
        have lbN : l1.here.bits.toUInt32.toNat = l1.here.bits.toNat := UInt8.toNat_toUInt32 _
        have fit3' : l1.here.bits.toNat + l3.here.bits.toNat ≤ l3.bits.toNat := fit3
        obtain ⟨B4, -, hbit4⟩ := DROPBITS_inv (bitInv_of I3) l1.here.bits.toUInt32 (by omega) lb64
        have I4 := I3.regs (l' := dropR l3 l1.here.bits.toUInt32) rfl rfl rfl rfl
          (by show (l3.bits - l1.here.bits.toUInt32).toNat ≤ 39; rw [hbit4]; have := I3.bits.1; omega)
          B4.hold_lt
        have e4 : (dropR l3 l1.here.bits.toUInt32).bits.toNat = l3.bits.toNat - l1.here.bits.toNat := by
          rw [dropR_bits (by omega), lbN]
        have hl3 : l3.hold.toNat < 2 ^ l3.bits.toNat := I3.bits.2
        have isl : Zlib.Inftrees.Spec.Subtable.IsLink type (ca.getD (off + l1.hold.toNat % 2 ^ nb.toNat) default) =
            true := by rw [← here1, ← linkEq]; exact lk
        have pull3' : Pulled2 ca off (ca.getD (off + l1.hold.toNat % 2 ^ nb.toNat) default) l1 l3 := by
          rw [← here1]; exact pull3
        have fit3'' : (ca.getD (off + l1.hold.toNat % 2 ^ nb.toNat) default).bits.toNat +
            (subVal ca off (ca.getD (off + l1.hold.toNat % 2 ^ nb.toNat) default) l3.hold.toNat).bits.toNat ≤
            l3.bits.toNat := by rw [← here1, ← here3]; exact fit3'
        have short3 := bits_after_link inv stable pfx short hl3 isl (by rw [← bitsR]; exact fit1)
          ext3 fit3'' pull1 pull3'
        rw [← here1, ← here3] at short3
        refine Or.inr ⟨dropR l3 l1.here.bits.toUInt32, h3, log3, l1.here.bits.toNat, ?_, I4,
          ist3.trans ist1, put3.trans put1, left3.trans left1, ?_, by omega, ?_, ?_, ?_⟩
        · rw [pre, runX_bind, run3]
          simp only [runX_bind, runX_get]
          rw [last3, DROPBITS_run _ _ _ lb64]
          rfl
        · show P l1.here.bits.toNat l3.here
          rw [here3]
          exact link.2.2.2.2 _ (ZlibF.Math.InflateLookup.slice_lt _ _ _)
        · show l3.here.bits.toNat ≤ (dropR l3 l1.here.bits.toUInt32).bits.toNat
          rw [e4]; omega
        · show (dropR l3 l1.here.bits.toUInt32).bits.toNat - l3.here.bits.toNat < 8
          rw [e4]; omega
        · unfold baseM at b1 b3 ⊢
          rw [e4]
          show 4 * (l3.bits.toNat - l1.here.bits.toNat + 8 * l3.have_.toNat + _) + _ ≤ _
          have e1 : ({ l1 with last := l1.here } : IL).bits.toNat = l1.bits.toNat := rfl
          have e2 : ({ l1 with last := l1.here } : IL).have_.toNat = l1.have_.toNat := rfl
          rw [e1, e2] at b3
          omega
    · -- a leaf of the root
      have nL : ¬ L l1.here := fun x => by
        rw [if_pos x] at cell1
        exact lk (Lcode _ x cell1.2.2.1)
      rw [if_neg nL] at cell1
      have lk' : isLink l1.here = false := by simpa using lk
      have leaf : Zlib.Inftrees.Spec.Subtable.IsLink type (ca.getD (off + l1.hold.toNat % 2 ^ nb.toNat) default) =
          false := by rw [← here1, ← linkEq]; exact lk'
      have short1 := bits_after_root inv stable pfx short hl1 leaf (by rw [← here1]; exact fit1) pull1
      rw [← here1] at short1
      refine Or.inr ⟨l1, h1, log1, 0, ?_, I1, ist1, put1, left1, cell1, by omega, fit1, short1, by omega⟩
      unfold symLook
      simp only [runX_bind, run1, runX_get, lk', Bool.false_eq_true, ↓reduceIte]

end Zlib.Infback.Safety
