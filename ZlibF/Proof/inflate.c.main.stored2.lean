import ZlibF.Proof.«inflate.c.main.stored»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec

set_option maxRecDepth 100000 in
theorem lit_invalid_stored : "invalid stored block lengths" ∈ strTable :=
  Array.mem_of_getElem? (i := 122) (by rfl)

/-- The registers after `case COPY:` has moved `n` bytes: `next` is `nx`, `put` is `pt`. -/
def copyRegs (l : IL) (n : UInt32) (nx pt : BPtr) : IL :=
  { l with copy := n, have_ := l.have_ - n, next := nx, left := l.left - n, put := pt }

/-- `case COPY:` copies `n` bytes (`n` at most what the source and the destination hold; the two ranges do not overlap,
as `memcpy` requires): the heap changes in the destination block and in `state->length`. -/
theorem copyTail_run {c : Ctx} {h : Heap} {r zs z s} (E : Env c h r zs z s) (l : IL) {n : UInt32} (hn : n ≠ 0)
    {rs : BRef} {os db od : Nat} {da sa : Array UInt8}
    (hput : l.put = .ref (.blk db) od) (hnext : l.next = .ref rs os)
    (hd : h.bytes db = some da) (hsrc : (Space.get h rs : Option (Array UInt8)) = some sa)
    (hro : Space.ro h (BRef.blk db) = false) (h1 : od + n.toNat ≤ da.size) (h2 : os + n.toNat ≤ sa.size)
    (hdis : BRef.blk db ≠ rs ∨ od + n.toNat ≤ os ∨ os + n.toNat ≤ od) :
    runX (copyTail c n) l h = .ok ((.ok (), copyRegs l n (Ptr.ref rs (os + n.toNat)) (Ptr.ref (BRef.blk db) (od + n.toNat))),
      setI { h with bytes := upd h.bytes db (some (copyRange da sa od os n.toNat)) } zs { s with length := s.length - n }) := by
  have hdg : (Space.get h (BRef.blk db) : Option (Array UInt8)) = some da := hd
  have hmc : memcpyB l.put l.next n.toNat h = .ok ((), { h with bytes := upd h.bytes db (some (copyRange da sa od os n.toNat)) }) := by
    rw [hput, hnext]
    exact Ptr.memcpy_ok (rd := BRef.blk db) (rs := rs) hdg hsrc hro h1 h2 hdis
  have hsz : (copyRange da sa od os n.toNat).size = da.size := size_copyRange _ _ _ _ _
  obtain ⟨a2, ha2, hs2⟩ := get_after_put hd hsz hsrc
  obtain ⟨a3, ha3, hs3⟩ := get_after_put hd hsz hdg
  have hadd1 : OkOn { h with bytes := upd h.bytes db (some (copyRange da sa od os n.toNat)) } (l.next.add (n.toNat : Int))
      (.ref rs (os + n.toNat)) := by
    rw [hnext]; exact Ptr.add_nat_ok ha2 (by omega)
  have hadd2 : OkOn { h with bytes := upd h.bytes db (some (copyRange da sa od os n.toNat)) } (l.put.add (n.toNat : Int))
      (.ref (.blk db) (od + n.toNat)) := by
    rw [hput]; exact Ptr.add_nat_ok ha3 (by omega)
  have hs' : ({ h with bytes := upd h.bytes db (some (copyRange da sa od os n.toNat)) } : Heap).istates zs = some s := E.hs
  have E' : Env c { h with bytes := upd h.bytes db (some (copyRange da sa od os n.toNat)) } r zs z s :=
    ⟨E.strm, E.st, E.hz, hs'⟩
  have hne : (n == 0) = false := by simpa using hn
  unfold copyTail
  rw [runX_bind, runX_get]
  simp only [hne, Bool.false_eq_true, ↓reduceIte]
  rw [runX_bind, runX_lift_ok hmc]
  simp only []
  rw [runX_bind, runX_lift_ok hadd1]
  simp only []
  rw [runX_bind, runX_lift_ok hadd2]
  simp only []
  rw [runX_bind, runX_set]
  simp only []
  rw [runX_bind, runX_wrS E']
  rfl

/-- `case COPY:` with input and room: copies `copyAmt` bytes, as `copyTail_run` (the source and destination ranges inside
their blocks and not overlapping). -/
theorem inflate_COPY_run {c : Ctx} {h : Heap} {r zs z s} (E : Env c h r zs z s) (l : IL) (hnz : s.length ≠ 0)
    (hn : copyAmt s.length l.have_ l.left ≠ 0)
    {rs : BRef} {os db od : Nat} {da sa : Array UInt8}
    (hput : l.put = .ref (.blk db) od) (hnext : l.next = .ref rs os)
    (hd : h.bytes db = some da) (hsrc : (Space.get h rs : Option (Array UInt8)) = some sa)
    (hro : Space.ro h (BRef.blk db) = false)
    (h1 : od + (copyAmt s.length l.have_ l.left).toNat ≤ da.size) (h2 : os + (copyAmt s.length l.have_ l.left).toNat ≤ sa.size)
    (hdis : BRef.blk db ≠ rs ∨ od + (copyAmt s.length l.have_ l.left).toNat ≤ os ∨
      os + (copyAmt s.length l.have_ l.left).toNat ≤ od) :
    runX (inflate_COPY c) l h = .ok ((.ok (), copyRegs l (copyAmt s.length l.have_ l.left)
        (Ptr.ref rs (os + (copyAmt s.length l.have_ l.left).toNat))
        (Ptr.ref (BRef.blk db) (od + (copyAmt s.length l.have_ l.left).toNat))),
      setI { h with bytes := upd h.bytes db (some (copyRange da sa od os (copyAmt s.length l.have_ l.left).toNat)) } zs
        { s with length := s.length - copyAmt s.length l.have_ l.left }) := by
  rw [inflate_COPY_split E l hnz]
  exact copyTail_run E l hn hput hnext hd hsrc hro h1 h2 hdis

/-- `case COPY:` with `length` bytes to go but no input or no room: `goto inf_leave`. -/
theorem inflate_COPY_leave {c : Ctx} {h : Heap} {r zs z s} (E : Env c h r zs z s) (l : IL) (hnz : s.length ≠ 0)
    (hz : copyAmt s.length l.have_ l.left = 0) :
    runX (inflate_COPY c) l h = .ok ((.error Ex.leave, { l with copy := 0 }), h) := by
  rw [inflate_COPY_split E l hnz, hz]
  exact copyTail_stall c l h

/-- `case COPY_:` sets the mode `COPY` and falls into `case COPY:` (run on the updated state). -/
theorem inflate_COPY__eq {c : Ctx} {h : Heap} {r zs z s} (E : Env c h r zs z s) (l : IL) :
    runX (inflate_COPY_ c) l h = runX (inflate_COPY c) l (setI h zs { s with mode := COPY }) := by
  unfold inflate_COPY_
  rw [runX_bind, runX_setMode E]

/-- `case STORED:` when the 32 header bits are not all there (`NEEDBITS(32)` after `BYTEBITS` runs out of input). -/
theorem inflate_STORED_wait {c : Ctx} (l l1 : IL) (h : Heap) (e : Ex)
    (hN : runX (NEEDBITS 32) (bytebits l) h = .ok ((.error e, l1), h)) :
    runX (inflate_STORED c) l h = .ok ((.error e, l1), h) := by
  unfold inflate_STORED
  rw [runX_bind, BYTEBITS_run]
  simp only []
  rw [runX_bind, hN]

/-- `case STORED:` with a bad length complement: the error "invalid stored block lengths", mode `BAD`. -/
theorem inflate_STORED_bad {c : Ctx} {h : Heap} {r zs z s} (E : Env c h r zs z s) (l l1 : IL)
    (hN : runX (NEEDBITS 32) (bytebits l) h = .ok ((.ok (), l1), h))
    (hbad : (l1.hold &&& (0xffff : UInt64)) != ((l1.hold >>> 16) ^^^ (0xffff : UInt64))) :
    ∃ i, strTable[i]? = some "invalid stored block lengths" ∧
      runX (inflate_STORED c) l h = .ok ((.ok (), l1), badHeap h r zs z s i) := by
  obtain ⟨i, hi, hb⟩ := runX_badMode E (msg := "invalid stored block lengths") lit_invalid_stored l1
  refine ⟨i, hi, ?_⟩
  unfold inflate_STORED
  rw [runX_bind, BYTEBITS_run]
  simp only []
  rw [runX_bind, hN]
  simp only []
  rw [runX_bind, runX_get]
  simp only [hbad, ↓reduceIte]
  rw [runX_bind, hb]
  rfl

/-- `case STORED:` with a good header: `length` is set, the bit buffer emptied, mode `COPY_`; with `flush = Z_TREES` the
call leaves here, otherwise `case COPY_:` follows. -/
theorem inflate_STORED_ok {c : Ctx} {h : Heap} {r zs z s} (E : Env c h r zs z s) (l l1 : IL)
    (hN : runX (NEEDBITS 32) (bytebits l) h = .ok ((.ok (), l1), h))
    (hgood : ¬ ((l1.hold &&& (0xffff : UInt64)) != ((l1.hold >>> 16) ^^^ (0xffff : UInt64))) = true) :
    runX (inflate_STORED c) l h = runX (if c.flush == Z_TREES then (throw Ex.leave : X Unit) else inflate_COPY_ c)
      { l1 with hold := 0, bits := 0 }
      (setI h zs { s with length := l1.hold.toUInt32 &&& 0xffff, mode := COPY_ }) := by
  unfold inflate_STORED
  rw [runX_bind, BYTEBITS_run]
  simp only []
  rw [runX_bind, hN]
  simp only []
  rw [runX_bind, runX_get]
  simp only [hgood, Bool.false_eq_true, ↓reduceIte]
  rw [runX_bind, runX_wrS E]
  simp only []
  rw [runX_bind, runX_INITBITS]
  simp only []
  have E' : Env c (setI h zs { s with length := l1.hold.toUInt32 &&& 0xffff }) r zs z { s with length := l1.hold.toUInt32 &&& 0xffff } :=
    ⟨E.strm, E.st, by simpa using E.hz, by simp⟩
  rw [runX_bind, runX_setMode E']
  simp only [setI_setI]
  split <;> simp_all [runX_bind, runX_throw]

end Zlib.Inflate.Proofs
