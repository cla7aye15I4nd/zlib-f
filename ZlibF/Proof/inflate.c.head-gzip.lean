import ZlibF.Proof.«inflate.c.header-default»
import ZlibF.Proof.«crc32.c»
import ZlibF.Proof.«inflate.c.byte-views»

/-!
# inflate.c: `case HEAD` with any nonzero wrapper

The zlib-only proofs in `inflate.c.header-default` cover wrappers 1 and 5
with no header record. This file covers the rest of `case HEAD`: the gzip
magic bytes (`wrap & 2`), the header record's `done = -1` store, and the
zlib checks after it.
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Adler32 (adler32)
open Zlib.Crc32 (crc32)
set_option autoImplicit false

/-- The code of `case HEAD` after `NEEDBITS(16)`, as in the translation. -/
def headAfterBits (c : Ctx) : X Unit := do
  let l ← get
  let s ← ldInflateState c.st
  if (s.wrap &&& 2) != 0 && l.hold == 0x8b1f then
    if s.wbits == 0 then wrS c.st fun s => { s with wbits := 15 }
    let v ← crc32 0 .null 0
    wrS c.st fun s => { s with check := v }
    CRC2 c
    INITBITS
    setMode c.st FLAGS
    return
  if s.head != none then
    let g ← ldGzHeader s.head
    stGzHeader s.head { g with done := -1 }
  let b8 ← BITS 8
  if (s.wrap &&& 1) == 0 || ((b8 <<< 8).toUInt64 + (l.hold >>> 8)) % 31 != 0 then
    badMode c "incorrect header check"
    return
  if (← BITS 4) != i2u Z_DEFLATED then
    badMode c "unknown compression method"
    return
  DROPBITS 4
  let len := (← BITS 4) + 8
  modify fun l => { l with len := len }
  let s ← ldInflateState c.st
  if len > 15 || (s.wbits != 0 && len > s.wbits) then
    badMode c "invalid window size"
    return
  if s.wbits == 0 then wrS c.st fun s => { s with wbits := len }
  let dm ← shl32 1 len
  wrS c.st fun s => { s with dmax := dm, flags := 0 }
  let v ← adler32 0 .null 0
  wrS c.st fun s => { s with check := v }
  wrZ c.strm fun z => { z with adler := v }
  let l ← get
  setMode c.st (if (l.hold &&& 0x200) != 0 then DICTID else TYPE)
  INITBITS

theorem inflate_HEAD_split (c : Ctx) : inflate_HEAD c = (do
    if (← rdS c.st (·.wrap)) == 0 then
      setMode c.st TYPEDO
      return
    NEEDBITS 16
    headAfterBits c) := rfl

/-- `hbuf` after `CRC2(check, word)`: the low two bytes of `word`. -/
def crc2Bytes (a : Array UInt8) (word : UInt64) : Array UInt8 :=
  (a.set! 0 word.toUInt8).set! 1 (word >>> 8).toUInt8

/-- The check value after `CRC2(check, word)`. -/
def crc2Value (check word : UInt64) : UInt64 :=
  (ZlibF.Spec.crc32Update check.toUInt32 [word.toUInt8, (word >>> 8).toUInt8]).toUInt64

theorem crc2Bytes_size (a : Array UInt8) (word : UInt64) : (crc2Bytes a word).size = a.size := by
  simp [crc2Bytes]

/-- `CRC2(state->check, hold)` stores two bytes into a writable four-byte
`hbuf`, runs `crc32` over them, and stores the result in `check`. -/
theorem CRC2_run {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (E : Env c h r zs z s) (l : IL) {b : Nat} {a : Array UInt8}
    (hbufAt : c.hbuf = .ref (.blk b) 0) (bytes : h.bytes b = some a) (size : a.size = 4)
    (writable : h.ro b = false) (statics : Zlib.Crc32.Proofs.StaticsOK h) :
    runX (CRC2 c) l h = .ok ((.ok (), l),
      setI (Space.put h (BRef.blk b) (crc2Bytes a l.hold)) zs { s with check := crc2Value s.check l.hold }) := by
  let a1 := a.set! 0 l.hold.toUInt8
  let h1 := Space.put h (BRef.blk b) a1
  let h2 := Space.put h1 (BRef.blk b) (crc2Bytes a l.hold)
  have size1 : a1.size = 4 := by simp [a1, size]
  have store1 : store8 c.hbuf l.hold.toUInt8 h = .ok ((), h1) := by
    rw [hbufAt]
    exact Ptr.store_ok (R := BRef) bytes writable (by omega)
  have get1 : Space.get h1 (BRef.blk b) = some a1 := by
    simp only [h1, Space.get, Space.put, upd_same]
  have ro1 : Space.ro h1 (BRef.blk b) = false := writable
  have add1 : (Ptr.ref (BRef.blk b) 0 : BPtr).add 1 h1 = .ok (.ref (.blk b) 1, h1) := by
    have := Ptr.add_ok (R := BRef) (T := UInt8) (h := h1) (off := 0) (k := 1) get1 (by omega)
      (by rw [size1]; omega)
    exact this
  have store2 : store8 (.ref (.blk b) 1) (l.hold >>> 8).toUInt8 h1 = .ok ((), h2) := by
    have := Ptr.store_ok (R := BRef) (h := h1) (off := 1) (v := (l.hold >>> 8).toUInt8) get1 ro1
      (by rw [size1]; omega)
    have same : Space.put h1 (BRef.blk b) (a1.set! 1 (l.hold >>> 8).toUInt8) = h2 := by
      simp only [h2, h1, Space.put, upd_upd, crc2Bytes, a1]
    rw [same] at this
    exact this
  have stream2 : r.get h2 = r.get h := by cases r <;> rfl
  have env2 : Env c h2 r zs z s := ⟨E.strm, E.st, stream2.trans E.hz, E.hs⟩
  have bytes2 : h2.bytes b = some (crc2Bytes a l.hold) := by
    simp only [h2, Space.put, upd_same]
  have statics2 : Zlib.Crc32.Proofs.StaticsOK h2 := statics
  have crc := Zlib.Crc32.Proofs.crc32_correct h2 statics2 s.check b 0 (crc2Bytes a l.hold) bytes2 2
    (by rw [crc2Bytes_size, size]; decide)
  have list : ((crc2Bytes a l.hold).toList.drop 0).take (2 : UInt32).toNat =
      [l.hold.toUInt8, (l.hold >>> 8).toUInt8] := by
    have big : 2 ≤ a.size := by omega
    apply List.ext_getElem
    · simp [crc2Bytes_size, size]
    · intro n one two
      simp only [List.length_take, List.length_drop, Array.length_toList, crc2Bytes_size] at one
      have small : n = 0 ∨ n = 1 := by simp at one; omega
      rcases small with rfl | rfl <;> simp [crc2Bytes, Array.set!, Array.setIfInBounds, size]
  rw [list] at crc
  have crc' : crc32 s.check (.ref (.blk b) 0) 2 h2 = .ok (crc2Value s.check l.hold, h2) := crc
  unfold CRC2
  rw [runX_bind, runX_get]
  simp only []
  rw [runX_bind, runX_lift_ok store1]
  simp only []
  rw [hbufAt]
  rw [runX_bind, runX_lift_ok add1]
  simp only []
  rw [runX_bind, runX_lift_ok store2]
  simp only []
  rw [runX_bind, runX_rdS env2]
  simp only []
  rw [runX_bind, runX_lift_ok crc']
  simp only []
  rw [runX_wrS env2]
  have heap2 : h2 = Space.put h (BRef.blk b) (crc2Bytes a l.hold) := by
    simp only [h2, h1, Space.put, upd_upd]
  rw [heap2]

#print axioms CRC2_run

/-- The state after the gzip magic bytes: width 15 if none was set, the
CRC-32 of the two magic bytes, mode `FLAGS`. -/
def headGzipState (s : InflateState) (word : UInt64) : InflateState :=
  { s with wbits := if s.wbits = 0 then 15 else s.wbits, check := crc2Value 0 word, mode := FLAGS }

/-- The end of the gzip magic branch, from `state->check = crc32(0L, Z_NULL, 0)`. -/
theorem headGzipTail_run {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {s : InflateState} (E : Env c h r zs z s) (l : IL) {b : Nat} {a : Array UInt8}
    (hbufAt : c.hbuf = .ref (.blk b) 0) (bytes : h.bytes b = some a) (size : a.size = 4)
    (writable : h.ro b = false) (statics : Zlib.Crc32.Proofs.StaticsOK h) :
    runX (do
      let v ← (monadLift (crc32 0 .null 0) : X UInt64)
      (monadLift (wrS c.st fun s => { s with check := v }) : X Unit)
      CRC2 c
      INITBITS
      (monadLift (setMode c.st FLAGS) : X Unit)
      pure ()) l h =
      .ok ((.ok (), { l with hold := 0, bits := 0 }),
        setI (Space.put h (BRef.blk b) (crc2Bytes a l.hold)) zs
          { s with check := crc2Value 0 l.hold, mode := FLAGS }) := by
  let s1 : InflateState := { s with check := 0 }
  have env1 : Env c (setI h zs s1) r zs z s1 := ⟨E.strm, E.st, by simpa using E.hz, by simp⟩
  have null : crc32 0 .null 0 h = .ok (0, h) := Zlib.Crc32.Proofs.crc32_null h 0 0
  have crc := CRC2_run env1 l hbufAt (b := b) (a := a) bytes size writable statics
  let s2 : InflateState := { s1 with check := crc2Value s1.check l.hold }
  have env2 : Env c (setI (Space.put (setI h zs s1) (BRef.blk b) (crc2Bytes a l.hold)) zs s2) r zs z s2 :=
    ⟨E.strm, E.st, by cases r <;> exact E.hz, by simp⟩
  rw [runX_bind, runX_lift_ok null]
  simp only []
  rw [runX_bind, runX_wrS E]
  simp only []
  rw [runX_bind, crc]
  simp only []
  rw [runX_bind, runX_INITBITS]
  simp only []
  rw [runX_bind, runX_setMode env2]
  simp only [runX_pure, byte_view_put_setI, setI_setI]
  rfl

#print axioms headGzipTail_run

/-- `case HEAD` after `NEEDBITS(16)` when gzip is allowed and the magic
bytes are present. -/
theorem headAfterBits_gzip {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {s : InflateState} (E : Env c h r zs z s) (l : IL) {b : Nat} {a : Array UInt8}
    (hbufAt : c.hbuf = .ref (.blk b) 0) (bytes : h.bytes b = some a) (size : a.size = 4)
    (writable : h.ro b = false) (statics : Zlib.Crc32.Proofs.StaticsOK h)
    (gzip : (s.wrap &&& 2) ≠ 0) (magic : l.hold = 0x8b1f) :
    runX (headAfterBits c) l h = .ok ((.ok (), { l with hold := 0, bits := 0 }),
      setI (Space.put h (BRef.blk b) (crc2Bytes a l.hold)) zs (headGzipState s l.hold)) := by
  unfold headAfterBits
  rw [runX_bind, runX_get]
  simp only []
  rw [runX_bind, runX_ldS E]
  have branch : ((s.wrap &&& 2) != 0 && l.hold == 0x8b1f) = true := by simp [gzip, magic]
  simp only [branch, ↓reduceIte]
  by_cases zero : s.wbits = 0
  · simp only [zero, beq_self_eq_true, ↓reduceIte]
    rw [runX_bind, runX_wrS E]
    simp only []
    let s1 : InflateState := { s with wbits := 15 }
    have env1 : Env c (setI h zs s1) r zs z s1 := ⟨E.strm, E.st, by simpa using E.hz, by simp⟩
    rw [headGzipTail_run env1 l hbufAt bytes size writable statics]
    simp only [byte_view_put_setI, setI_setI, headGzipState, zero, ↓reduceIte]
    rfl
  · have ne : (s.wbits == 0) = false := by simpa using zero
    simp only [ne, Bool.false_eq_true, ↓reduceIte]
    rw [headGzipTail_run E l hbufAt bytes size writable statics]
    simp only [headGzipState, zero, ↓reduceIte]

#print axioms headAfterBits_gzip

/-- The heap after `if (state->head != Z_NULL) state->head->done = -1;`. -/
def headDoneHeap (h : Heap) (head : GzHeaderPtr) : Heap :=
  match head with
  | none => h
  | some (.tab i) => match h.gzheaders i with
    | some g => { h with gzheaders := upd h.gzheaders i (some { g with done := -1 }) }
    | none => h

theorem Env.headDone {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {s : InflateState} (E : Env c h r zs z s) (head : GzHeaderPtr) :
    Env c (headDoneHeap h head) r zs z s := by
  unfold headDoneHeap
  split
  · exact E
  · split
    · exact ⟨E.strm, E.st, by cases r <;> exact E.hz, E.hs⟩
    · exact E

/-- Without the gzip magic bytes, `case HEAD` marks an attached header record
as not gzip (`done = -1`) and continues with the zlib header checks. -/
theorem headAfterBits_zlib {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {s : InflateState} (E : Env c h r zs z s) (l : IL)
    (notMagic : ((s.wrap &&& 2) != 0 && l.hold == 0x8b1f) = false)
    (record : ∀ i, s.head = some (.tab i) → (h.gzheaders i).isSome) :
    runX (headAfterBits c) l h = runX (headDefaultCheck c s l) l (headDoneHeap h s.head) := by
  unfold headAfterBits
  rw [runX_bind, runX_get]
  simp only []
  rw [runX_bind, runX_ldS E]
  simp only [notMagic, Bool.false_eq_true, ↓reduceIte]
  cases hh : s.head with
  | none =>
    simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, headDoneHeap]
    rfl
  | some ref =>
    cases ref with
    | tab i =>
      obtain ⟨g, hg⟩ := Option.isSome_iff_exists.mp (record i hh)
      have attached : (some (GzHeaderRef.tab i) != none) = true := rfl
      simp only [attached, ↓reduceIte]
      rw [runX_bind, runX_lift_ok (ldGzHeader_tab hg)]
      simp only []
      rw [runX_bind, runX_lift_ok (stGzHeader_tab hg)]
      simp only [headDoneHeap, hg]
      rfl

#print axioms headAfterBits_zlib

#print axioms inflate_HEAD_split
end Zlib.Inflate.Proofs
