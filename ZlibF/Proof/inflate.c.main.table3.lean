import ZlibF.Proof.«inflate.c.main.table2»

/-!
# inflate.c: `case LENLENS:` -- the loops

The two loops of `LENLENS` as local definitions (checked equal to the translation by `rfl`), their bodies and the run lemmas.
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec
open Zlib.Inftrees (inflate_table)

/-! ## Accesses to the arrays of the state record -/

theorem BitInv.tc_of_heap {h h' : Heap} {l : IL} {bs : List UInt8} (B : BitInv h l bs) (hb : h'.bytes = h.bytes)
    (hd : h'.dstates = h.dstates) (hs : h'.static = h.static) : BitInv h' l bs := by
  refine ⟨B.have_eq, ?_, B.hold_lt⟩
  rcases B.next with e | ⟨r, a, off, hn, hg, hsz, hbs⟩
  · exact Or.inl e
  · refine Or.inr ⟨r, a, off, hn, ?_, hsz, hbs⟩
    cases r <;> simpa [Space.get, hb, hd, hs] using hg

theorem BitInv.tc_setI {h : Heap} {l : IL} {bs : List UInt8} (B : BitInv h l bs) (zs : Nat) (s : InflateState) :
    BitInv (setI h zs s) l bs := B.tc_of_heap rfl rfl rfl

theorem tcStore_lens {h : Heap} {zs : Nat} {t : InflateState} {k : Nat} (v : UInt16) (ht : h.istates zs = some t)
    (hk : k < t.lens.size) :
    Ptr.store (Ptr.ref (WRef.istate_lens zs) k) v h = .ok ((), setI h zs { t with lens := t.lens.set! k v }) := by
  rw [Ptr.store_ok (WRef.get_istate_lens ht) (WRef.ro_istate_lens h zs) hk, WRef.put_istate_lens ht]
  rfl

theorem tcAdd_lens {h : Heap} {zs : Nat} {t : InflateState} {k : Nat} (ht : h.istates zs = some t)
    (hk : k ≤ t.lens.size) :
    Ptr.add (Ptr.ref (WRef.istate_lens zs) 0) (k : Int) h = .ok (Ptr.ref (WRef.istate_lens zs) k, h) := by
  have := Ptr.add_nat_ok (n := k) (off := 0) (WRef.get_istate_lens ht) (by omega)
  simpa [OkOn] using this

/-! ## The loops of `case LENLENS:` -/

/-- `while (state->have < state->ncode)` -/
def llCond (c : Ctx) : X Bool := do let s ← ldInflateState c.st; return s.«have» < s.ncode

/-- `{ NEEDBITS(3); state->lens[order[state->have++]] = (unsigned short)BITS(3); DROPBITS(3); }` -/
def llBody (c : Ctx) : X Unit := do
  NEEDBITS 3
  let s ← ldInflateState c.st
  wrS c.st fun s => { s with «have» := s.«have» + 1 }
  let o ← orderAt s.«have»
  let b ← BITS 3
  Ptr.store (← (lensP c.st).add (o.toNat : Int)) b.toUInt16
  DROPBITS 3

/-- `while (state->have < 19)` -/
def lzCond (c : Ctx) : X Bool := do let s ← ldInflateState c.st; return s.«have» < 19

/-- `state->lens[order[state->have++]] = 0;` -/
def lzBody (c : Ctx) : X Unit := do
  let s ← ldInflateState c.st
  wrS c.st fun s => { s with «have» := s.«have» + 1 }
  let o ← orderAt s.«have»
  Ptr.store (← (lensP c.st).add (o.toNat : Int)) (0 : UInt16)

/-- From `state->next = state->codes ...` to the end of the mode. -/
def llTail (c : Ctx) : X Unit := do
  wrS c.st fun s => { s with next := codesP c.st, distcode := codesP c.st, lencode := codesP c.st, lenbits := 7 }
  let s ← ldInflateState c.st
  let (r, nx, lb) ← inflate_table CODES (lensP c.st) 19 s.next s.lenbits (workP c.st)
  wrS c.st fun s => { s with next := nx, lenbits := lb }
  modify fun l => { l with ret := r }
  if r != 0 then
    badMode c "invalid code lengths set"
    return
  wrS c.st fun s => { s with «have» := 0, mode := CODELENS }
  inflate_CODELENS c

/-- The translation of `case LENLENS:` is the two loops and the tail. -/
theorem inflate_LENLENS_eq (c : Ctx) :
    inflate_LENLENS c = (do xwhile (llCond c) (llBody c); xwhile (lzCond c) (lzBody c); llTail c) := rfl

theorem tcBITS3_run (l : IL) (h : Heap) : runX (BITS 3) l h = .ok ((.ok (l.hold.toUInt32 &&& 7), l), h) := by
  rw [BITS_run l h 3 (by decide)]; rfl

theorem tcDROP3_run (l : IL) (h : Heap) :
    runX (DROPBITS 3) l h = .ok ((.ok (), { l with hold := l.hold >>> 3, bits := l.bits - 3 }), h) := by
  rw [DROPBITS_run l h 3 (by decide)]; rfl

/-- One iteration of the first loop of `LENLENS`, in a state with `have < 19` and `lens` of its declared size:
`NEEDBITS(3)`, and then either `goto inf_leave` (input ran out: nothing was written) or the next code length is stored in
`lens[order[have]]`, `have` grows by one, three bits are dropped. -/
theorem llBody_run {c : Ctx} {l : IL} {h : Heap} {zs : Nat} {t : InflateState} {bs : List UInt8}
    (hc : c.st = some (.tab zs)) (ht : h.istates zs = some t) (hsz : t.lens.size = 320) (hH : t.«have».toNat < 19)
    (B : BitInv h l bs) :
    ∃ rr l' j, runX (NEEDBITS 3) l h = .ok ((rr, l'), h) ∧ j ≤ bs.length ∧ BitInv h l' (bs.drop j) ∧
      stream l' (bs.drop j) = stream l bs ∧
      l' = { l with next := l'.next, have_ := l'.have_, hold := l'.hold, bits := l'.bits } ∧
      (rr = .error Ex.leave → l'.have_ = 0 ∧ j = bs.length ∧ l'.bits.toNat < 3 ∧
        runX (llBody c) l h = .ok ((.error Ex.leave, l'), h)) ∧
      (rr = .ok () → 3 ≤ l'.bits.toNat ∧
        runX (llBody c) l h = .ok ((.ok (), { l' with hold := l'.hold >>> 3, bits := l'.bits - 3 }),
          setI h zs { t with «have» := t.«have» + 1, lens := t.lens.set! (orderNat t.«have».toNat) (l'.hold.toUInt32 &&& 7).toUInt16 })) := by
  obtain ⟨rr, l', j, hrun, hj, B', hS', hbits, hshape, hmax, hid, hok, hleave⟩ := NEEDBITS_run B 3 (by decide)
  refine ⟨rr, l', j, hrun, hj, B', hS', hshape, ?_, ?_⟩
  · intro e
    obtain ⟨h1, h2, h3⟩ := hleave e
    refine ⟨h2, h1, h3, ?_⟩
    unfold llBody
    simp [runX_bind, hrun, e]
  · intro e
    refine ⟨hok e, ?_⟩
    have ho : orderNat t.«have».toNat < 19 := order_lt _ hH
    have hhave1 : (t.«have» + 1).toNat = t.«have».toNat + 1 := by
      rw [UInt32.toNat_add]; simp; omega
    have hoa := orderAt_run (setI h zs { t with «have» := t.«have» + 1 }) t.«have» hH
    have hadd := tcAdd_lens (h := setI h zs { t with «have» := t.«have» + 1 }) (zs := zs)
      (t := { t with «have» := t.«have» + 1 }) (k := (order[t.«have».toNat]!).toNat) (by simp)
      (by have := ho; unfold orderNat at this; simp [hsz]; omega)
    have hst := tcStore_lens (h := setI h zs { t with «have» := t.«have» + 1 }) (zs := zs)
      (t := { t with «have» := t.«have» + 1 }) (k := (order[t.«have».toNat]!).toNat) (l'.hold.toUInt32 &&& 7).toUInt16
      (by simp) (by have := ho; unfold orderNat at this; simp [hsz]; omega)
    unfold llBody
    rw [hc]
    simp at hst
    simp [runX_bind, runX_lift, ldI_eq, ht, hrun, e, wrI_eq, hoa, hadd, hst, tcBITS3_run, tcDROP3_run, lensP, orderNat]

end Zlib.Inflate.Proofs
