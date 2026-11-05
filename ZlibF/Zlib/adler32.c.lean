import ZlibF.Runtime.Reasoning

/-!
# adler32.c — faithful translation (draft)

Source: `zlib/adler32.c`, default build (`NO_DIVIDE` undefined, so
`MOD`/`MOD28` are `a %= BASE`), LP64. Translated statement by statement; the
`DO1`..`DO16` macros become `do1`/`do16` with the same expansion order.

Types: `uLong`/`unsigned long` = `UInt64`, `z_size_t` = `UInt64`,
`unsigned` = `UInt32`, `Bytef` = `UInt8`. Byte reads are promoted to `int`
and then converted to `unsigned long`, which preserves their value.

Status: translated by hand; not yet produced by a mechanical translator and not
yet differentially tested in this repository (see `docs/trusted-base.md`).
-/

namespace Zlib.Adler32
open C

def BASE : UInt64 := 65521
def NMAX : UInt64 := 5552

/-- Loop-carried locals of `adler32_z`. -/
structure Locals where
  adler : UInt64
  sum2 : UInt64
  buf : Ptr
  len : UInt64
  n : UInt32

/-- `DO1(buf,i)`: `{adler += (buf)[i]; sum2 += adler;}` -/
def do1 (s : Locals) (i : Int) : CM Locals := do
  let b ← index8 s.buf i
  let adler := s.adler + b.toUInt64
  pure { s with adler, sum2 := s.sum2 + adler }

/-- `DO16(buf)`: `DO8(buf,0); DO8(buf,8);`, i.e. `DO1(buf,0)` .. `DO1(buf,15)`. -/
def do16 (s : Locals) : CM Locals := do
  let s ← do1 s 0;  let s ← do1 s 1;  let s ← do1 s 2;  let s ← do1 s 3
  let s ← do1 s 4;  let s ← do1 s 5;  let s ← do1 s 6;  let s ← do1 s 7
  let s ← do1 s 8;  let s ← do1 s 9;  let s ← do1 s 10; let s ← do1 s 11
  let s ← do1 s 12; let s ← do1 s 13; let s ← do1 s 14; do1 s 15

/-- `adler += *buf++; sum2 += adler;` -/
def stepByte (s : Locals) : CM Locals := do
  let b ← load8 s.buf
  let buf ← s.buf.add 1
  let adler := s.adler + b.toUInt64
  pure { s with adler, buf, sum2 := s.sum2 + adler }

/-- `while (len--)` condition. -/
def lenPostDec (s : Locals) : CM (Bool × Locals) :=
  pure (s.len != 0, { s with len := s.len - 1 })

/-- `uLong ZEXPORT adler32_z(uLong adler, const Bytef *buf, z_size_t len)` -/
def adler32_z (adler : UInt64) (buf : Ptr) (len : UInt64) : CM UInt64 := do
  -- if (buf == Z_NULL) return 1L;   (upstream fix madler/zlib#1364, `patches/`)
  if buf == .null then return 1
  -- sum2 = (adler >> 16) & 0xffff; adler &= 0xffff;
  let sum2 := (adler >>> 16) &&& 0xffff
  let adler := adler &&& 0xffff
  -- if (len == 1) { ... }
  if len == 1 then
    let b ← index8 buf 0
    let mut adler := adler + b.toUInt64
    if adler >= BASE then adler := adler - BASE
    let mut sum2 := sum2 + adler
    if sum2 >= BASE then sum2 := sum2 - BASE
    return adler ||| (sum2 <<< 16)
  -- if (len < 16) { while (len--) {...} ... }
  if len < 16 then
    let s ← cwhile lenPostDec stepByte { adler, sum2, buf, len, n := 0 }
    let mut adler := s.adler
    if adler >= BASE then adler := adler - BASE
    let sum2 := s.sum2 % BASE  -- MOD28(sum2)
    return adler ||| (sum2 <<< 16)
  -- while (len >= NMAX) { ... }
  let s ← cwhile (fun s => pure (s.len >= NMAX, s))
    (fun s => do
      let s := { s with len := s.len - NMAX, n := (NMAX / 16).toUInt32 }
      -- do { DO16(buf); buf += 16; } while (--n);
      let s ← cdoWhile
        (fun s => do
          let s ← do16 s
          pure { s with buf := ← s.buf.add 16 })
        (fun s => let n := s.n - 1; pure (n != 0, { s with n }))
        s
      -- MOD(adler); MOD(sum2);
      pure { s with adler := s.adler % BASE, sum2 := s.sum2 % BASE })
    { adler, sum2, buf, len, n := 0 }
  -- if (len) { ... }
  let s ← if s.len != 0 then do
      let s ← cwhile (fun s => pure (s.len >= 16, s))
        (fun s => do
          let s := { s with len := s.len - 16 }
          let s ← do16 s
          pure { s with buf := ← s.buf.add 16 })
        s
      let s ← cwhile lenPostDec stepByte s
      pure { s with adler := s.adler % BASE, sum2 := s.sum2 % BASE }
    else pure s
  return s.adler ||| (s.sum2 <<< 16)

/-- `uLong ZEXPORT adler32(uLong adler, const Bytef *buf, uInt len)` -/
def adler32 (adler : UInt64) (buf : Ptr) (len : UInt32) : CM UInt64 :=
  adler32_z adler buf len.toUInt64

/-- `local uLong adler32_combine_(uLong adler1, uLong adler2, z_off64_t len2)`
(`z_off64_t` = signed 64-bit `long` on LP64 Linux; `MOD63` is `%=` in the
default build). -/
def adler32_combine_ (adler1 adler2 : UInt64) (len2 : Int64) : CM UInt64 := do
  -- if (len2 < 0) return 0xffffffffUL;
  if len2 < 0 then return 0xffffffff
  -- MOD63(len2);  i.e. len2 %= BASE (signed %, operands nonnegative here)
  let len2 := len2 % 65521
  -- rem = (unsigned)len2;
  -- signed -> unsigned conversion is modulo 2^32, i.e. reinterpret then truncate
  let rem : UInt32 := len2.toUInt64.toUInt32
  let sum1 := adler1 &&& (0xffff : UInt64)
  -- sum2 = rem * sum1;  (rem converted to unsigned long)
  let sum2 := rem.toUInt64 * sum1
  let sum2 := sum2 % BASE  -- MOD(sum2)
  let sum1 := sum1 + ((adler2 &&& (0xffff : UInt64)) + BASE - 1)
  let sum2 := sum2 + (((adler1 >>> 16) &&& (0xffff : UInt64)) + ((adler2 >>> 16) &&& (0xffff : UInt64)) + BASE - rem.toUInt64)
  let mut sum1 := sum1
  if sum1 >= BASE then sum1 := sum1 - BASE
  if sum1 >= BASE then sum1 := sum1 - BASE
  let mut sum2 := sum2
  if sum2 >= (BASE <<< 1) then sum2 := sum2 - (BASE <<< 1)
  if sum2 >= BASE then sum2 := sum2 - BASE
  return sum1 ||| (sum2 <<< 16)

/-- `uLong ZEXPORT adler32_combine(uLong adler1, uLong adler2, z_off_t len2)` (`z_off_t` = `long`). -/
def adler32_combine (adler1 adler2 : UInt64) (len2 : Int64) : CM UInt64 :=
  adler32_combine_ adler1 adler2 len2

/-- `uLong ZEXPORT adler32_combine64(uLong adler1, uLong adler2, z_off64_t len2)` -/
def adler32_combine64 (adler1 adler2 : UInt64) (len2 : Int64) : CM UInt64 :=
  adler32_combine_ adler1 adler2 len2

end Zlib.Adler32

/-!
# Adler-32 specification (RFC 1950 §8.2)

`spec lo hi bs`: starting from component sums `lo`, `hi` (each < 65521), feed
bytes `bs`; each byte updates `lo := (lo + b) mod 65521`, then
`hi := (hi + lo) mod 65521`. The checksum is `lo + 65536 * hi`.
This file is independent of the C translation.
-/

namespace Zlib.Adler32.Spec

def BASE : Nat := 65521

def step (st : Nat × Nat) (b : UInt8) : Nat × Nat :=
  ((st.1 + b.toNat) % BASE, (st.2 + (st.1 + b.toNat) % BASE) % BASE)

def sums (lo hi : Nat) (bs : List UInt8) : Nat × Nat := bs.foldl step (lo, hi)

/-- Adler-32 of `bs` continuing from the checksum value `adler`
(the conventional initial value is 1). -/
def adler32 (adler : Nat) (bs : List UInt8) : Nat :=
  let st := sums (adler % 65536 % BASE) (adler / 65536 % 65536 % BASE) bs
  st.1 + 65536 * st.2

theorem step_lt (st : Nat × Nat) (b : UInt8) : (step st b).1 < BASE ∧ (step st b).2 < BASE := by
  simp only [step, BASE]; omega

theorem sums_append (lo hi : Nat) (xs ys : List UInt8) :
    sums lo hi (xs ++ ys) = sums (sums lo hi xs).1 (sums lo hi xs).2 ys := by
  simp [sums, List.foldl_append]

theorem sums_lt (lo hi : Nat) (bs : List UInt8) (hlo : lo < BASE) (hhi : hi < BASE) :
    (sums lo hi bs).1 < BASE ∧ (sums lo hi bs).2 < BASE := by
  induction bs generalizing lo hi with
  | nil => exact ⟨hlo, hhi⟩
  | cons b bs ih =>
    have := step_lt (lo, hi) b
    exact ih _ _ this.1 this.2

end Zlib.Adler32.Spec


namespace Zlib.Adler32.Spec

/-! ## Combination of two Adler-32 values (RFC 1950 sums are affine in the start) -/

/-- Unreduced sums: `S1 = Σ b`, `S2 = Σ (n - i) b_i` for `bs` of length `n`. -/
def s1 (bs : List UInt8) : Nat := (bs.map UInt8.toNat).sum
def s2 : List UInt8 → Nat
  | [] => 0
  | b :: bs => (bs.length + 1) * b.toNat + s2 bs

/-- Closed form: feeding `bs` from reduced `(lo, hi)` gives
`(lo + S1, hi + n * lo + S2)` reduced modulo 65521. -/
theorem sums_closed (bs : List UInt8) : ∀ lo hi : Nat, lo < BASE → hi < BASE →
    sums lo hi bs = ((lo + s1 bs) % BASE, (hi + bs.length * lo + s2 bs) % BASE) := by
  induction bs with
  | nil =>
    intro lo hi hlo hhi
    simp [sums, s1, s2, Nat.mod_eq_of_lt hlo, Nat.mod_eq_of_lt hhi]
  | cons b bs ih =>
    intro lo hi hlo hhi
    have hst := step_lt (lo, hi) b
    have e : sums lo hi (b :: bs) = sums (step (lo, hi) b).1 (step (lo, hi) b).2 bs := rfl
    rw [e, ih _ _ hst.1 hst.2]
    simp only [step, BASE, s1, s2, List.map_cons, List.sum_cons, List.length_cons] at *
    have hm : bs.length * ((lo + b.toNat) % 65521) % 65521 = bs.length * (lo + b.toNat) % 65521 :=
      Nat.mul_mod_mod _ _ _
    rw [Nat.mul_add] at hm
    rw [Prod.mk.injEq]
    constructor
    · omega
    · rw [Nat.add_mul, Nat.add_mul, Nat.one_mul, Nat.one_mul]
      omega

/-- The Adler-32 combination identity used by `adler32_combine`: for
`x = sums 1 0 A`, `y = sums 1 0 B` and `n = |B| mod 65521`,
`sums 1 0 (A ++ B)` is `(x₁ + y₁ + 65520, (n·x₁ mod 65521) + x₂ + y₂ + 65521 − n)`
reduced modulo 65521. -/
theorem sums_combine (A B : List UInt8) :
    sums 1 0 (A ++ B) =
      (((sums 1 0 A).1 + (sums 1 0 B).1 + BASE - 1) % BASE,
       ((B.length % BASE) * (sums 1 0 A).1 % BASE + (sums 1 0 A).2 + (sums 1 0 B).2 + BASE
          - B.length % BASE) % BASE) := by
  have hx := sums_lt 1 0 A (by decide) (by decide)
  rw [sums_append, sums_closed B _ _ hx.1 hx.2, sums_closed B 1 0 (by decide) (by decide)]
  simp only [BASE] at *
  have hn : (B.length % 65521) * (sums 1 0 A).1 % 65521 = B.length * (sums 1 0 A).1 % 65521 :=
    Nat.mod_mul_mod _ _ _
  have hn' : B.length % 65521 < 65521 := Nat.mod_lt _ (by decide)
  rw [Prod.mk.injEq]
  constructor
  · omega
  · omega

end Zlib.Adler32.Spec

namespace Zlib.Adler32.Proofs
open C Zlib.Adler32

/-- Bytes `p .. p+n-1` of a block. -/
def seg (bytes : ByteArray) (p n : Nat) : List UInt8 := (List.range n).map (fun i => bytes[p + i]!)

end Zlib.Adler32.Proofs


/-!
# Arithmetic core of the adler32_z proof

Between two `MOD` reductions the C code accumulates at most `NMAX = 5552`
bytes in 64-bit `unsigned long` without reducing. `Rel j a s lo hi` says the
machine sums `a`, `s` (after `j` unreduced bytes) are congruent to the spec
sums `lo`, `hi` and bounded so that nothing wraps.
-/

namespace Zlib.Adler32.Proofs
open Zlib.Adler32.Spec

/-- One unreduced machine step: `adler += b; sum2 += adler;`. -/
def acc (st : UInt64 × UInt64) (b : UInt8) : UInt64 × UInt64 :=
  (st.1 + b.toUInt64, st.2 + (st.1 + b.toUInt64))

/-- Bound on `sum2` growth per byte while at most NMAX bytes are unreduced. -/
def C : Nat := 65535 + 255 * 5552

def Rel (j : Nat) (a s : UInt64) (lo hi : Nat) : Prop :=
  a.toNat % 65521 = lo ∧ s.toNat % 65521 = hi ∧
  a.toNat ≤ 65535 + 255 * j ∧ s.toNat ≤ 65535 + j * C

theorem acc_one (j : Nat) (a s : UInt64) (lo hi : Nat) (b : UInt8)
    (hr : Rel j a s lo hi) (hj : j + 1 ≤ 5552) :
    Rel (j + 1) (acc (a, s) b).1 (acc (a, s) b).2 (step (lo, hi) b).1 (step (lo, hi) b).2 := by
  obtain ⟨hlo, hhi, ha, hs⟩ := hr
  have hb : b.toNat < 256 := b.toNat_lt
  have ha' : (a + b.toUInt64).toNat = a.toNat + b.toNat := by
    rw [UInt64.toNat_add, UInt8.toNat_toUInt64]
    exact Nat.mod_eq_of_lt (by omega)
  have hs' : (s + (a + b.toUInt64)).toNat = s.toNat + (a.toNat + b.toNat) := by
    rw [UInt64.toNat_add, ha']
    exact Nat.mod_eq_of_lt (by simp only [C] at hs; omega)
  simp only [acc, step, Spec.BASE, Rel, ha', hs', C] at *
  omega

theorem acc_list (bs : List UInt8) : ∀ (j : Nat) (a s : UInt64) (lo hi : Nat),
    Rel j a s lo hi → j + bs.length ≤ 5552 →
    Rel (j + bs.length) (bs.foldl acc (a, s)).1 (bs.foldl acc (a, s)).2
      (sums lo hi bs).1 (sums lo hi bs).2 := by
  induction bs with
  | nil => intro j a s lo hi hr _; simpa [sums] using hr
  | cons b bs ih =>
    intro j a s lo hi hr hj
    have h1 := acc_one j a s lo hi b hr (by simp at hj; omega)
    have := ih (j + 1) _ _ _ _ h1 (by simp at hj; omega)
    simpa [sums, List.foldl, Nat.add_assoc, Nat.add_comm 1] using this

/-- `MOD(a)`: `a %= BASE` reduces exactly to the spec value and resets the bound. -/
theorem rel_mod (j : Nat) (a s : UInt64) (lo hi : Nat) (hr : Rel j a s lo hi) :
    Rel 0 (a % 65521) (s % 65521) lo hi := by
  obtain ⟨hlo, hhi, -, -⟩ := hr
  simp only [Rel, UInt64.toNat_mod]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp <;> omega

end Zlib.Adler32.Proofs

/-!
# Step lemmas for the adler32_z translation

Each lemma gives the exact resulting locals of one macro/statement group,
assuming the buffer pointer is inside a live block.
-/

namespace Zlib.Adler32.Proofs
open C Zlib.Adler32


theorem seg_length (bytes : ByteArray) (p n : Nat) : (seg bytes p n).length = n := by
  simp [seg]

theorem seg_add (bytes : ByteArray) (p m n : Nat) :
    seg bytes p (m + n) = seg bytes p m ++ seg bytes (p + m) n := by
  simp [seg, List.range_add, Nat.add_assoc]

theorem seg_one (bytes : ByteArray) (p : Nat) : seg bytes p 1 = [bytes[p]!] := by
  simp [seg]

/-- Machine sums after one byte. -/
def upd (s : Locals) (b : UInt8) : Locals :=
  { s with adler := (acc (s.adler, s.sum2) b).1, sum2 := (acc (s.adler, s.sum2) b).2 }

/-- Machine sums after a list of bytes. -/
def updL (s : Locals) (bs : List UInt8) : Locals :=
  { s with adler := (bs.foldl acc (s.adler, s.sum2)).1, sum2 := (bs.foldl acc (s.adler, s.sum2)).2 }

theorem updL_nil (s : Locals) : updL s [] = s := rfl

theorem updL_cons (s : Locals) (b : UInt8) (bs : List UInt8) :
    updL s (b :: bs) = updL (upd s b) bs := rfl

theorem updL_append (s : Locals) (xs ys : List UInt8) :
    updL s (xs ++ ys) = updL (updL s xs) ys := by
  simp [updL, List.foldl_append]

variable {h : Heap} {blk : Nat} {bytes : ByteArray}

theorem getElem_eq_bang (bytes : ByteArray) (i : Nat) (hi : i < bytes.size) :
    bytes[i] = bytes[i]! := by
  simp [getElem!_pos, hi]

theorem do1_ok (hb : h.blocks[blk]? = some (some bytes)) (s : Locals) (p i : Nat)
    (hbuf : s.buf = .ref blk p) (hlt : p + i < bytes.size) :
    OkOn h (do1 s i) (upd s bytes[p + i]!) := by
  obtain ⟨a, s2, buf, len, n⟩ := s
  simp only at hbuf
  subst hbuf
  unfold do1
  refine OkOn.bind (index8_ok hb hlt) ?_
  rw [getElem_eq_bang bytes _ hlt]
  exact OkOn.pure _ _

theorem upd_buf (t : Locals) (b : UInt8) : (upd t b).buf = t.buf := rfl

theorem do16_ok (hb : h.blocks[blk]? = some (some bytes)) (s : Locals) (p : Nat)
    (hbuf : s.buf = .ref blk p) (hlt : p + 16 ≤ bytes.size) :
    OkOn h (do16 s) (updL s (seg bytes p 16)) := by
  have st : ∀ (t : Locals) (i : Nat), t.buf = .ref blk p → i < 16 →
      OkOn h (do1 t i) (upd t bytes[p + i]!) :=
    fun t i ht hi => do1_ok hb t p i ht (by omega)
  unfold do16
  refine OkOn.bind (st _ 0 hbuf (by omega)) ?_
  refine OkOn.bind (st _ 1 (by simp only [upd_buf]; exact hbuf) (by omega)) ?_
  refine OkOn.bind (st _ 2 (by simp only [upd_buf]; exact hbuf) (by omega)) ?_
  refine OkOn.bind (st _ 3 (by simp only [upd_buf]; exact hbuf) (by omega)) ?_
  refine OkOn.bind (st _ 4 (by simp only [upd_buf]; exact hbuf) (by omega)) ?_
  refine OkOn.bind (st _ 5 (by simp only [upd_buf]; exact hbuf) (by omega)) ?_
  refine OkOn.bind (st _ 6 (by simp only [upd_buf]; exact hbuf) (by omega)) ?_
  refine OkOn.bind (st _ 7 (by simp only [upd_buf]; exact hbuf) (by omega)) ?_
  refine OkOn.bind (st _ 8 (by simp only [upd_buf]; exact hbuf) (by omega)) ?_
  refine OkOn.bind (st _ 9 (by simp only [upd_buf]; exact hbuf) (by omega)) ?_
  refine OkOn.bind (st _ 10 (by simp only [upd_buf]; exact hbuf) (by omega)) ?_
  refine OkOn.bind (st _ 11 (by simp only [upd_buf]; exact hbuf) (by omega)) ?_
  refine OkOn.bind (st _ 12 (by simp only [upd_buf]; exact hbuf) (by omega)) ?_
  refine OkOn.bind (st _ 13 (by simp only [upd_buf]; exact hbuf) (by omega)) ?_
  refine OkOn.bind (st _ 14 (by simp only [upd_buf]; exact hbuf) (by omega)) ?_
  have e : updL s (seg bytes p 16) = upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd
      (upd (upd (upd (upd (upd s bytes[p + 0]!) bytes[p + 1]!) bytes[p + 2]!) bytes[p + 3]!)
      bytes[p + 4]!) bytes[p + 5]!) bytes[p + 6]!) bytes[p + 7]!) bytes[p + 8]!) bytes[p + 9]!)
      bytes[p + 10]!) bytes[p + 11]!) bytes[p + 12]!) bytes[p + 13]!) bytes[p + 14]!) bytes[p + 15]! := rfl
  rw [e]
  exact st _ 15 (by simp only [upd_buf]; exact hbuf) (by omega)

theorem stepByte_ok (hb : h.blocks[blk]? = some (some bytes)) (s : Locals) (p : Nat)
    (hbuf : s.buf = .ref blk p) (hlt : p < bytes.size) :
    OkOn h (stepByte s) { upd s bytes[p]! with buf := .ref blk (p + 1) } := by
  obtain ⟨a, s2, buf, len, n⟩ := s
  simp only at hbuf
  subst hbuf
  unfold stepByte
  refine OkOn.bind (load8_ok hb hlt) ?_
  refine OkOn.bind (Ptr.add_ok hb (by omega) (by omega)) ?_
  rw [getElem_eq_bang bytes _ hlt]
  have : ((p : Int) + 1) = ((p + 1 : Nat) : Int) := by omega
  rw [this]
  exact OkOn.pure _ _

theorem bufAdd16_ok (hb : h.blocks[blk]? = some (some bytes)) (s : Locals) (p : Nat)
    (hbuf : s.buf = .ref blk p) (hlt : p + 16 ≤ bytes.size) :
    OkOn h (do pure { s with buf := ← s.buf.add 16 }) { s with buf := .ref blk (p + 16) } := by
  rw [hbuf]
  refine OkOn.bind (Ptr.add_ok hb (by omega) (by omega)) ?_
  have : ((p : Int) + 16) = ((p + 16 : Nat) : Int) := by omega
  rw [this]
  exact OkOn.pure _ _

end Zlib.Adler32.Proofs

/-!
# Loop lemmas for the adler32_z translation

`AccFrom s t l`: the machine sums of `t` are those of `s` after accumulating
bytes `l` without reduction. Each lemma proves a loop terminates within fuel,
stays in bounds, and computes the expected sums.
-/

namespace Zlib.Adler32.Proofs
open C Zlib.Adler32

def AccFrom (s t : Locals) (l : List UInt8) : Prop :=
  t.adler = (updL s l).adler ∧ t.sum2 = (updL s l).sum2

theorem AccFrom.refl (s : Locals) : AccFrom s s [] := ⟨rfl, rfl⟩

theorem AccFrom.updL {s t : Locals} {l : List UInt8} (hr : AccFrom s t l) (m : List UInt8) :
    AccFrom s (Proofs.updL t m) (l ++ m) := by
  obtain ⟨ha, hs⟩ := hr
  simp only [AccFrom, Proofs.updL, List.foldl_append] at *
  rw [ha, hs]
  exact ⟨rfl, rfl⟩

theorem AccFrom.upd {s t : Locals} {l : List UInt8} (hr : AccFrom s t l) (b : UInt8) :
    AccFrom s (upd t b) (l ++ [b]) := hr.updL [b]

theorem AccFrom.congr {s t t' : Locals} {l : List UInt8} (hr : AccFrom s t l)
    (ha : t'.adler = t.adler) (hs : t'.sum2 = t.sum2) : AccFrom s t' l := by
  obtain ⟨h1, h2⟩ := hr; exact ⟨ha.trans h1, hs.trans h2⟩

theorem AccFrom.trans {s t u : Locals} {l m : List UInt8} (h1 : AccFrom s t l) (h2 : AccFrom t u m) :
    AccFrom s u (l ++ m) := by
  obtain ⟨a1, s1⟩ := h1
  obtain ⟨a2, s2⟩ := h2
  simp only [AccFrom, Proofs.updL, List.foldl_append] at *
  rw [a2, s2, a1, s1]
  exact ⟨rfl, rfl⟩

theorem fuel_gt (x : UInt64) : x.toNat < fuel := by
  have := x.toNat_lt; simp only [fuel]; omega

variable {h : Heap} {blk : Nat} {bytes : ByteArray}

/-- `while (len--) { adler += *buf++; sum2 += adler; }` -/
theorem byteLoop_ok (hb : h.blocks[blk]? = some (some bytes)) (s : Locals) (p : Nat)
    (hbuf : s.buf = .ref blk p) (hfit : p + s.len.toNat ≤ bytes.size) :
    ∃ s', OkOn h (cwhile lenPostDec stepByte s) s' ∧
      s'.buf = .ref blk ((p + s.len.toNat : Nat) : Int) ∧ AccFrom s s' (seg bytes p s.len.toNat) := by
  have hk := fuel_gt s.len
  generalize hkdef : s.len.toNat = k at hfit hk ⊢
  let P : Nat → Locals → Prop := fun j t => ∃ i, i + j = k ∧ t.buf = .ref blk ((p + i : Nat) : Int) ∧
    t.len.toNat = j ∧ AccFrom s t (seg bytes p i)
  let Q : Locals → Prop := fun t => t.buf = .ref blk ((p + k : Nat) : Int) ∧ AccFrom s t (seg bytes p k)
  refine cwhile_ok (h := h) P Q ?_ ?_ (k := k) ⟨0, by omega, by simpa using hbuf, hkdef, AccFrom.refl s⟩ hk
  · intro j t ⟨i, hi, htb, htl, hacc⟩
    have hne : (t.len != 0) = true := by
      simp only [bne_iff_ne, ne_eq]; intro h0; rw [h0] at htl; simp at htl
    refine ⟨{ t with len := t.len - 1 }, { upd { t with len := t.len - 1 } bytes[p + i]! with
        buf := .ref blk ((p + i + 1 : Nat) : Int) }, ?_, stepByte_ok hb _ (p + i) htb (by omega), ?_⟩
    · show OkOn h (pure (t.len != 0, { t with len := t.len - 1 })) _
      rw [hne]; exact OkOn.pure _ _
    · refine ⟨i + 1, by omega, by simp [Nat.add_assoc], ?_, ?_⟩
      · simp only [upd]
        rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]
        simp; omega
      · rw [seg_add, seg_one]
        exact (hacc.congr rfl rfl).upd _
  · intro t ⟨i, hi, htb, htl, hacc⟩
    have he : (t.len != 0) = false := by
      simp only [bne_eq_false_iff_eq]; exact UInt64.toNat_inj.mp (by simp [htl])
    refine ⟨{ t with len := t.len - 1 }, ?_, ?_, ?_⟩
    · show OkOn h (pure (t.len != 0, { t with len := t.len - 1 })) _
      rw [he]; exact OkOn.pure _ _
    · simpa [show i = k by omega] using htb
    · exact (show i = k by omega) ▸ hacc.congr rfl rfl

/-- `while (len >= 16) { len -= 16; DO16(buf); buf += 16; }` -/
theorem chunkLoop_ok (hb : h.blocks[blk]? = some (some bytes)) (s : Locals) (p : Nat)
    (hbuf : s.buf = .ref blk p) (hfit : p + s.len.toNat ≤ bytes.size) :
    ∃ s', OkOn h (cwhile (fun s => pure (decide (s.len ≥ 16), s))
        (fun s => do
          let s ← do16 { adler := s.adler, sum2 := s.sum2, buf := s.buf, len := s.len - 16, n := s.n }
          let __do_lift ← s.buf.add 16
          pure { adler := s.adler, sum2 := s.sum2, buf := __do_lift, len := s.len, n := s.n }) s) s' ∧
      s'.buf = .ref blk ((p + 16 * (s.len.toNat / 16) : Nat) : Int) ∧ s'.len.toNat = s.len.toNat % 16 ∧
      s'.n = s.n ∧ AccFrom s s' (seg bytes p (16 * (s.len.toNat / 16))) := by
  have hk := fuel_gt s.len
  generalize hrdef : s.len.toNat = r at hfit hk ⊢
  let P : Nat → Locals → Prop := fun j t => ∃ i, i + j = r / 16 ∧
    t.buf = .ref blk ((p + 16 * i : Nat) : Int) ∧
    t.len.toNat = r - 16 * i ∧ t.n = s.n ∧ AccFrom s t (seg bytes p (16 * i))
  let Q : Locals → Prop := fun t => t.buf = .ref blk ((p + 16 * (r / 16) : Nat) : Int) ∧
    t.len.toNat = r % 16 ∧ t.n = s.n ∧ AccFrom s t (seg bytes p (16 * (r / 16)))
  refine cwhile_ok (h := h) P Q ?_ ?_ (k := r / 16)
    ⟨0, by omega, by simpa using hbuf, by simp [hrdef], rfl, AccFrom.refl s⟩ (by omega)
  · intro j t ⟨i, hi, htb, htl, htn, hacc⟩
    have hge : decide (t.len ≥ 16) = true := by
      simp only [decide_eq_true_eq, ge_iff_le, UInt64.le_iff_toNat_le]; simp; omega
    let t1 : Locals := { adler := t.adler, sum2 := t.sum2, buf := t.buf, len := t.len - 16, n := t.n }
    have ht1 : t1.buf = .ref blk ((p + 16 * i : Nat) : Int) := htb
    refine ⟨t, { updL t1 (seg bytes (p + 16 * i) 16) with
        buf := .ref blk ((p + 16 * i + 16 : Nat) : Int) }, ?_, ?_, ?_⟩
    · show OkOn h (pure (decide (t.len ≥ 16), t)) _
      rw [hge]; exact OkOn.pure _ _
    · refine OkOn.bind (do16_ok hb t1 (p + 16 * i) ht1 (by omega)) ?_
      exact bufAdd16_ok hb _ (p + 16 * i) ht1 (by omega)
    · refine ⟨i + 1, by omega, by simp [Nat.mul_add, Nat.add_assoc], ?_, htn, ?_⟩
      · show (t.len - 16).toNat = r - 16 * (i + 1)
        rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]
        simp; omega
      · rw [show 16 * (i + 1) = 16 * i + 16 by omega, seg_add]
        exact ((hacc.congr rfl rfl : AccFrom s t1 _).updL _).congr rfl rfl
  · intro t ⟨i, hi, htb, htl, htn, hacc⟩
    have hlt : decide (t.len ≥ 16) = false := by
      simp only [decide_eq_false_iff_not, ge_iff_le, UInt64.le_iff_toNat_le]; simp; omega
    refine ⟨t, ?_, ?_, ?_, htn, ?_⟩
    · show OkOn h (pure (decide (t.len ≥ 16), t)) _
      rw [hlt]; exact OkOn.pure _ _
    · simpa [show i = r / 16 by omega] using htb
    · rw [htl]; omega
    · exact (show i = r / 16 by omega) ▸ hacc

end Zlib.Adler32.Proofs

/-!
# Block-level lemmas for adler32_z: the NMAX inner loop and the outer loop
-/

namespace Zlib.Adler32.Proofs
open C Zlib.Adler32 Zlib.Adler32.Spec

variable {h : Heap} {blk : Nat} {bytes : ByteArray}

theorem nmax_div : (NMAX / 16).toUInt32 = 347 := by decide

/-- One NMAX block: `n = NMAX / 16; do { DO16(buf); buf += 16; } while (--n);` -/
theorem nmaxBlock_ok (hb : h.blocks[blk]? = some (some bytes)) (t : Locals) (p : Nat)
    (hbuf : t.buf = .ref blk p) (hfit : p + 5552 ≤ bytes.size) (ht : t.n = 347) :
    ∃ u, OkOn h (cdoWhile
        (fun s => do
          let s ← do16 s
          let __do_lift ← s.buf.add 16
          pure { adler := s.adler, sum2 := s.sum2, buf := __do_lift, len := s.len, n := s.n })
        (fun s => pure (s.n - 1 != 0, { adler := s.adler, sum2 := s.sum2, buf := s.buf, len := s.len, n := s.n - 1 }))
        t) u ∧
      u.buf = .ref blk ((p + 5552 : Nat) : Int) ∧ u.len = t.len ∧ AccFrom t u (seg bytes p 5552) := by
  let P : Nat → Locals → Prop := fun m u => ∃ i, i + m = 346 ∧ u.n.toNat = m + 1 ∧
    u.buf = .ref blk ((p + 16 * i : Nat) : Int) ∧ u.len = t.len ∧ AccFrom t u (seg bytes p (16 * i))
  let Q : Locals → Prop := fun u => u.buf = .ref blk ((p + 5552 : Nat) : Int) ∧ u.len = t.len ∧
    AccFrom t u (seg bytes p 5552)
  refine cdoWhile_ok (h := h) P Q ?_ ?_ (k := 346)
    ⟨0, rfl, by rw [ht]; rfl, by simpa using hbuf, rfl, AccFrom.refl t⟩ (by simp [fuel])
  · intro m u ⟨i, hi, hn, hub, hul, hacc⟩
    let u1 : Locals := { updL u (seg bytes (p + 16 * i) 16) with buf := .ref blk ((p + 16 * i + 16 : Nat) : Int) }
    have hne : (u1.n - 1 != 0) = true := by
      have : u1.n = u.n := rfl
      simp only [bne_iff_ne, ne_eq, this]
      intro h0
      have := congrArg UInt32.toNat h0
      rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; simp; omega)] at this
      simp at this; omega
    refine ⟨u1, { u1 with n := u1.n - 1 }, ?_, ?_, ?_⟩
    · refine OkOn.bind (do16_ok hb u (p + 16 * i) hub (by omega)) ?_
      exact bufAdd16_ok hb _ (p + 16 * i) hub (by omega)
    · show OkOn h (pure (u1.n - 1 != 0, { u1 with n := u1.n - 1 })) _
      rw [hne]; exact OkOn.pure _ _
    · refine ⟨i + 1, by omega, ?_, ?_, hul, ?_⟩
      · show (u.n - 1).toNat = m + 1
        rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; simp; omega)]
        simp; omega
      · show Ptr.ref blk ((p + 16 * i + 16 : Nat) : Int) = _
        rw [show p + 16 * i + 16 = p + 16 * (i + 1) by omega]
      · rw [show 16 * (i + 1) = 16 * i + 16 by omega, seg_add]
        exact (hacc.updL _).congr rfl rfl
  · intro u ⟨i, hi, hn, hub, hul, hacc⟩
    let u1 : Locals := { updL u (seg bytes (p + 16 * i) 16) with buf := .ref blk ((p + 16 * i + 16 : Nat) : Int) }
    have he : (u1.n - 1 != 0) = false := by
      have : u1.n = u.n := rfl
      simp only [bne_eq_false_iff_eq, this]
      apply UInt32.toNat_inj.mp
      rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; simp; omega)]
      simp; omega
    refine ⟨u1, { u1 with n := u1.n - 1 }, ?_, ?_, ?_⟩
    · refine OkOn.bind (do16_ok hb u (p + 16 * i) hub (by omega)) ?_
      exact bufAdd16_ok hb _ (p + 16 * i) hub (by omega)
    · show OkOn h (pure (u1.n - 1 != 0, { u1 with n := u1.n - 1 })) _
      rw [he]; exact OkOn.pure _ _
    · refine ⟨by simp [u1]; omega, hul, ?_⟩
      have hi' : i = 346 := by omega
      subst hi'
      rw [show 5552 = 16 * 346 + 16 by rfl, seg_add]
      exact (hacc.updL _).congr rfl rfl

/-- Low 16 and high 16 bits combine into `lo + 65536 * hi`. -/
theorem or_shift (x y : UInt64) (hx : x.toNat < 65536) (hy : y.toNat < 65536) :
    (x ||| (y <<< 16)).toNat = x.toNat + 65536 * y.toNat := by
  rw [UInt64.toNat_or, UInt64.toNat_shiftLeft]
  have hs : y.toNat <<< (16 % 64) % 2 ^ 64 = y.toNat * 65536 := by
    rw [Nat.shiftLeft_eq]; simp; omega
  rw [show (16 : UInt64).toNat = 16 from rfl, hs, Nat.or_comm,
    show y.toNat * 65536 = y.toNat <<< 16 by rw [Nat.shiftLeft_eq],
    ← Nat.shiftLeft_add_eq_or_of_lt (by omega), Nat.shiftLeft_eq]
  omega

theorem low16 (a : UInt64) : (a &&& 65535).toNat = a.toNat % 65536 := by
  rw [UInt64.toNat_and]
  exact Nat.and_two_pow_sub_one_eq_mod a.toNat 16

theorem high16 (a : UInt64) : (a >>> 16 &&& 65535).toNat = a.toNat / 65536 % 65536 := by
  rw [UInt64.toNat_and, UInt64.toNat_shiftRight]
  rw [show (65535 : UInt64).toNat = 2 ^ 16 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  simp [Nat.shiftRight_eq_div_pow]

end Zlib.Adler32.Proofs

/-!
# Main theorem for adler32_z

For every initial value `adler`, every live block, offset and length with
`off + len ≤ size`, the translation of `adler32_z` terminates without
undefined behavior, leaves the heap unchanged, and returns the RFC 1950
Adler-32 of the bytes `off .. off+len-1`, continuing from `adler` (whose
component sums are taken modulo 65521; bits above 32 are ignored, as in C).
-/

namespace Zlib.Adler32.Proofs
open C Zlib.Adler32 Zlib.Adler32.Spec

variable {h : Heap} {blk : Nat} {bytes : ByteArray}

theorem rel_init (a : UInt64) :
    Rel 0 (a &&& 65535) (a >>> 16 &&& 65535)
      ((a &&& 65535).toNat % 65521) ((a >>> 16 &&& 65535).toNat % 65521) := by
  have h1 := low16 a
  have h2 := high16 a
  refine ⟨rfl, rfl, ?_, ?_⟩ <;> simp only [Nat.mul_zero, Nat.zero_mul, Nat.add_zero] <;> omega

theorem rel_exact {a s : UInt64} {lo hi : Nat} (hr : Rel 0 a s lo hi)
    (ha : a.toNat < 65521) (hs : s.toNat < 65521) : a.toNat = lo ∧ s.toNat = hi := by
  obtain ⟨h1, h2, -, -⟩ := hr
  exact ⟨by rw [← h1, Nat.mod_eq_of_lt ha], by rw [← h2, Nat.mod_eq_of_lt hs]⟩

/-- Spec value from the final reduced component sums. -/
theorem result_value (a x y : UInt64) (bs : List UInt8)
    (hx : x.toNat = (sums ((a &&& 65535).toNat % 65521) ((a >>> 16 &&& 65535).toNat % 65521) bs).1)
    (hy : y.toNat = (sums ((a &&& 65535).toNat % 65521) ((a >>> 16 &&& 65535).toNat % 65521) bs).2) :
    (x ||| (y <<< 16)).toNat = Spec.adler32 a.toNat bs := by
  have hlt := sums_lt ((a &&& 65535).toNat % 65521) ((a >>> 16 &&& 65535).toNat % 65521) bs
    (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))
  rw [show Spec.BASE = 65521 from rfl] at hlt
  rw [or_shift x y (by omega) (by omega), hx, hy, Spec.adler32, low16, high16]
  rfl

/-- Long inputs (`len ≥ 16`): NMAX blocks, then 16-byte chunks, then bytes. -/
theorem adler32_z_long (hb : h.blocks[blk]? = some (some bytes)) (a : UInt64) (off L : Nat)
    (hfit : off + L ≤ bytes.size) (hL : L < 2 ^ 64) (h16 : 16 ≤ L) :
    ∃ r, OkOn h (adler32_z a (.ref blk off) L.toUInt64) r ∧
      r.toNat = Spec.adler32 a.toNat (seg bytes off L) := by
  have hLn : L.toUInt64.toNat = L := by simp; omega
  have hne1 : (L.toUInt64 == 1) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; intro e; have := congrArg UInt64.toNat e; simp at this; omega
  have hnull : (Ptr.ref blk off == Ptr.null) = false := rfl
  have hn16 : ¬ (L.toUInt64 < 16) := by rw [UInt64.lt_iff_toNat_lt, hLn]; simp; omega
  unfold adler32_z
  rw [ite_eq_right_of_eq_false _ _ (by simp [hnull]), ite_eq_right_of_eq_false _ _ (by simp [hne1]),
    ite_eq_right_of_eq_false _ _ (by simp [hn16])]
  let lo := (a &&& 65535).toNat % 65521
  let hi := (a >>> 16 &&& 65535).toNat % 65521
  let q := L / 5552
  let r := L % 5552
  let s0 : Locals := { adler := a &&& 65535, sum2 := a >>> 16 &&& 65535, buf := .ref blk off, len := L.toUInt64, n := 0 }
  let P : Nat → Locals → Prop := fun k t => ∃ i, i + k = q ∧ t.buf = .ref blk ((off + 5552 * i : Nat) : Int) ∧
    t.len.toNat = L - 5552 * i ∧
    Rel 0 t.adler t.sum2 (sums lo hi (seg bytes off (5552 * i))).1 (sums lo hi (seg bytes off (5552 * i))).2 ∧
    (1 ≤ i → t.adler.toNat < 65521 ∧ t.sum2.toNat < 65521)
  let Q : Locals → Prop := fun t => t.buf = .ref blk ((off + 5552 * q : Nat) : Int) ∧ t.len.toNat = r ∧
    Rel 0 t.adler t.sum2 (sums lo hi (seg bytes off (5552 * q))).1 (sums lo hi (seg bytes off (5552 * q))).2 ∧
    (1 ≤ q → t.adler.toNat < 65521 ∧ t.sum2.toNat < 65521)
  have hinit : P q s0 := ⟨0, by omega, by simp [s0], by simp [s0, hLn], rel_init a, by omega⟩
  refine OkOn.bind_ex (cwhile_ok (h := h) P Q ?_ ?_ hinit (by simp [fuel]; omega)) ?_
  · -- one NMAX block
    rintro k t ⟨i, hi_, htb, htl, hrel, -⟩
    have hge : decide (t.len ≥ NMAX) = true := by
      simp only [decide_eq_true_eq, ge_iff_le, UInt64.le_iff_toNat_le, htl]; simp [NMAX]; omega
    let t0 : Locals := { adler := t.adler, sum2 := t.sum2, buf := t.buf, len := t.len - NMAX, n := (NMAX / 16).toUInt32 }
    obtain ⟨u, hu, hub, hul, hacc⟩ := nmaxBlock_ok hb t0 (off + 5552 * i) htb (by omega) nmax_div
    refine ⟨t, { adler := u.adler % BASE, sum2 := u.sum2 % BASE, buf := u.buf, len := u.len, n := u.n }, ?_, ?_, ?_⟩
    · show OkOn h (pure (decide (t.len ≥ NMAX), t)) _
      rw [hge]; exact OkOn.pure _ _
    · exact OkOn.bind hu (OkOn.pure _ _)
    · have hacc' := acc_list (seg bytes (off + 5552 * i) 5552) 0 t0.adler t0.sum2 _ _ hrel (by simp [seg_length])
      rw [seg_length] at hacc'
      have hmod := rel_mod _ _ _ _ _ hacc'
      refine ⟨i + 1, by omega, ?_, ?_, ?_, ?_⟩
      · rw [hub, show off + 5552 * i + 5552 = off + 5552 * (i + 1) by omega]
      · show u.len.toNat = _
        rw [hul]; show (t.len - NMAX).toNat = _
        rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, htl]; simp [NMAX]; omega), htl]
        simp [NMAX]; omega
      · rw [show 5552 * (i + 1) = 5552 * i + 5552 by omega, seg_add, sums_append]
        obtain ⟨ha, hs⟩ := hacc
        simp only [updL] at ha hs
        show Rel 0 (u.adler % 65521) (u.sum2 % 65521) _ _
        rw [ha, hs]
        exact hmod
      · intro _
        simp only [UInt64.toNat_mod, BASE]
        exact ⟨Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide)⟩
  · -- loop exit
    rintro t ⟨i, hi_, htb, htl, hrel, hred⟩
    have hlt : decide (t.len ≥ NMAX) = false := by
      simp only [decide_eq_false_iff_not, ge_iff_le, UInt64.le_iff_toNat_le, htl]; simp [NMAX]; omega
    refine ⟨t, ?_, ?_⟩
    · show OkOn h (pure (decide (t.len ≥ NMAX), t)) _
      rw [hlt]; exact OkOn.pure _ _
    · have : i = q := by omega
      subst this
      exact ⟨htb, by rw [htl]; omega, hrel, hred⟩
  · -- remainder
    rintro t ⟨htb, htl, hrel, hred⟩
    by_cases hr0 : r = 0
    · have hz : (t.len != 0) = false := by
        simp only [bne_eq_false_iff_eq]; exact UInt64.toNat_inj.mp (by simp [htl, hr0])
      rw [hz]
      simp only [Bool.false_eq_true, ite_false]
      have hq : 1 ≤ q := by omega
      obtain ⟨ha, hs⟩ := hred hq
      obtain ⟨ea, es⟩ := rel_exact hrel ha hs
      refine ⟨_, OkOn.bind (OkOn.pure _ _) (OkOn.pure _ _), ?_⟩
      have hseg : seg bytes off L = seg bytes off (5552 * q) := by
        rw [show 5552 * q = L by omega]
      rw [hseg]
      exact result_value a t.adler t.sum2 _ ea es
    · have hnz : (t.len != 0) = true := by
        simp only [bne_iff_ne, ne_eq]; intro e; have := congrArg UInt64.toNat e; simp [htl] at this; omega
      rw [hnz]
      simp only [ite_true]
      obtain ⟨c, hc, hcb, hcl, -, hcacc⟩ := chunkLoop_ok hb t (off + 5552 * q) htb (by rw [htl]; omega)
      rw [htl] at hcb hcl hcacc
      obtain ⟨d, hd, hdb, hdacc⟩ := byteLoop_ok hb c _ hcb (by rw [hcl]; omega)
      rw [hcl] at hdb hdacc
      have hall := hcacc.trans hdacc
      have hlen : (seg bytes (off + 5552 * q) (16 * (r / 16)) ++ seg bytes (off + 5552 * q + 16 * (r / 16)) (r % 16)).length = r := by
        simp [seg_length]; omega
      have hrel' := acc_list _ 0 t.adler t.sum2 _ _ hrel (by rw [hlen]; omega)
      rw [hlen] at hrel'
      obtain ⟨hda, hds⟩ := hall
      simp only [updL] at hda hds
      refine ⟨_, OkOn.bind hc (OkOn.bind hd (OkOn.bind (OkOn.pure _ _) (OkOn.pure _ _))), ?_⟩
      have hseg : seg bytes off L = seg bytes off (5552 * q) ++
          (seg bytes (off + 5552 * q) (16 * (r / 16)) ++ seg bytes (off + 5552 * q + 16 * (r / 16)) (r % 16)) := by
        rw [← seg_add, ← seg_add]; congr 1; omega
      rw [hseg]
      apply result_value
      · rw [sums_append, show (d.adler % BASE).toNat = d.adler.toNat % 65521 by simp [BASE], hda]
        exact hrel'.1
      · rw [sums_append, show (d.sum2 % BASE).toNat = d.sum2.toNat % 65521 by simp [BASE], hds]
        exact hrel'.2.1

theorem add_small (x y : UInt64) (hxy : x.toNat + y.toNat < 2 ^ 64) : (x + y).toNat = x.toNat + y.toNat := by
  rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt hxy

theorem sub_small (x y : UInt64) (hyx : y.toNat ≤ x.toNat) : (x - y).toNat = x.toNat - y.toNat :=
  UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; exact hyx)

theorem base_toNat : (BASE : UInt64).toNat = 65521 := rfl

/-- Short inputs (`len < 16`, `len ≠ 1`, including `len = 0`). -/
theorem adler32_z_short (hb : h.blocks[blk]? = some (some bytes)) (a : UInt64) (off L : Nat)
    (hfit : off + L ≤ bytes.size) (h16 : L < 16) (h1 : L ≠ 1) :
    ∃ r, OkOn h (adler32_z a (.ref blk off) L.toUInt64) r ∧
      r.toNat = Spec.adler32 a.toNat (seg bytes off L) := by
  have hLn : L.toUInt64.toNat = L := by simp; omega
  have hne1 : (L.toUInt64 == 1) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; intro e; have := congrArg UInt64.toNat e; simp at this; omega
  have hnull : (Ptr.ref blk off == Ptr.null) = false := rfl
  have hy16 : L.toUInt64 < 16 := by rw [UInt64.lt_iff_toNat_lt, hLn]; simp; omega
  unfold adler32_z
  rw [ite_eq_right_of_eq_false _ _ (by simp [hnull]), ite_eq_right_of_eq_false _ _ (by simp [hne1]),
    ite_eq_left hy16]
  let s0 : Locals := { adler := a &&& 65535, sum2 := a >>> 16 &&& 65535, buf := .ref blk off, len := L.toUInt64, n := 0 }
  obtain ⟨d, hd, -, hacc⟩ := byteLoop_ok hb s0 off rfl (by simp [s0, hLn]; omega)
  have hrel := acc_list (seg bytes off s0.len.toNat) 0 s0.adler s0.sum2 _ _ (rel_init a)
    (by simp [seg_length, s0, hLn]; omega)
  obtain ⟨hda, hds⟩ := hacc
  simp only [updL] at hda hds
  rw [← hda, ← hds] at hrel
  obtain ⟨r1, r2, rb1, -⟩ := hrel
  simp only [seg_length, s0, hLn] at r1 r2 rb1
  refine OkOn.bind_ex (R := fun x => x = d) ⟨d, hd, rfl⟩ ?_
  intro x hx
  rw [hx]
  dsimp only
  have hres := result_value a (if d.adler ≥ BASE then d.adler - BASE else d.adler) (d.sum2 % BASE)
    (seg bytes off L) ?_ ?_
  · split
    · next hge => exact ⟨_, OkOn.pure _ _, by simpa [hge] using hres⟩
    · next hlt => exact ⟨_, OkOn.pure _ _, by simpa [hlt] using hres⟩
  · split
    · next hge =>
      rw [ge_iff_le, UInt64.le_iff_toNat_le, base_toNat] at hge
      rw [sub_small _ _ (by rw [base_toNat]; omega), base_toNat, ← r1]; omega
    · next hlt =>
      rw [ge_iff_le, UInt64.le_iff_toNat_le, base_toNat] at hlt
      rw [← r1]; omega
  · rw [UInt64.toNat_mod, base_toNat, r2]

/-- `len == 1`: one byte with single conditional subtractions. -/
theorem adler32_z_one (hb : h.blocks[blk]? = some (some bytes)) (a : UInt64) (off : Nat)
    (hfit : off + 1 ≤ bytes.size) (hvalid : (a >>> 16 &&& 65535).toNat < 65521) :
    ∃ r, OkOn h (adler32_z a (.ref blk off) (1 : Nat).toUInt64) r ∧
      r.toNat = Spec.adler32 a.toNat (seg bytes off 1) := by
  unfold adler32_z
  have hnull : (Ptr.ref blk off == Ptr.null) = false := rfl
  rw [ite_eq_right_of_eq_false _ _ (by simp [hnull]), ite_eq_left (by decide)]
  refine OkOn.bind_ex ⟨bytes[off + 0]!, ?_, rfl⟩ ?_
  · have := index8_ok (i := 0) hb (by omega : off + 0 < bytes.size)
    rwa [getElem_eq_bang bytes _ (by omega)] at this
  intro b hbv
  subst hbv
  have hA := low16 a
  have hH := high16 a
  have hb256 : (bytes[off + 0]!).toNat < 256 := UInt8.toNat_lt _
  have hbn : (bytes[off + 0]!).toUInt64.toNat = (bytes[off + 0]!).toNat := UInt8.toNat_toUInt64 _
  have hAm : (a &&& 65535).toNat < 65536 := by rw [hA]; omega
  have hHm : (a >>> 16 &&& 65535).toNat < 65536 := by rw [hH]; omega
  have hx : ((a &&& 65535) + (bytes[off + 0]!).toUInt64).toNat = (a &&& 65535).toNat + (bytes[off + 0]!).toNat := by
    rw [add_small _ _ (by omega), hbn]
  rw [seg_one]
  simp only [Nat.add_zero] at hx hb256 hbn ⊢
  split
  · next hge =>
    rw [ge_iff_le, UInt64.le_iff_toNat_le, base_toNat, hx] at hge
    have hx' : ((a &&& 65535) + (bytes[off]!).toUInt64 - BASE).toNat = (a &&& 65535).toNat + (bytes[off]!).toNat - 65521 := by
      rw [sub_small _ _ (by rw [base_toNat, hx]; omega), hx, base_toNat]
    have hy : ((a >>> 16 &&& 65535) + ((a &&& 65535) + (bytes[off]!).toUInt64 - BASE)).toNat =
        (a >>> 16 &&& 65535).toNat + ((a &&& 65535).toNat + (bytes[off]!).toNat - 65521) := by
      rw [add_small _ _ (by rw [hx']; omega), hx']
    split
    · next hge2 =>
      rw [ge_iff_le, UInt64.le_iff_toNat_le, base_toNat, hy] at hge2
      refine ⟨_, OkOn.pure _ _, result_value a _ _ _ ?_ ?_⟩
      · rw [hx']; simp only [sums, List.foldl, step, Spec.BASE]; omega
      · rw [sub_small _ _ (by rw [base_toNat, hy]; omega), hy, base_toNat]
        simp only [sums, List.foldl, step, Spec.BASE]; omega
    · next hlt2 =>
      rw [ge_iff_le, UInt64.le_iff_toNat_le, base_toNat, hy] at hlt2
      refine ⟨_, OkOn.pure _ _, result_value a _ _ _ ?_ ?_⟩
      · rw [hx']; simp only [sums, List.foldl, step, Spec.BASE]; omega
      · rw [hy]; simp only [sums, List.foldl, step, Spec.BASE]; omega
  · next hlt =>
    rw [ge_iff_le, UInt64.le_iff_toNat_le, base_toNat, hx] at hlt
    have hy : ((a >>> 16 &&& 65535) + ((a &&& 65535) + (bytes[off]!).toUInt64)).toNat =
        (a >>> 16 &&& 65535).toNat + ((a &&& 65535).toNat + (bytes[off]!).toNat) := by
      rw [add_small _ _ (by rw [hx]; omega), hx]
    split
    · next hge2 =>
      rw [ge_iff_le, UInt64.le_iff_toNat_le, base_toNat, hy] at hge2
      refine ⟨_, OkOn.pure _ _, result_value a _ _ _ ?_ ?_⟩
      · rw [hx]; simp only [sums, List.foldl, step, Spec.BASE]; omega
      · rw [sub_small _ _ (by rw [base_toNat, hy]; omega), hy, base_toNat]
        simp only [sums, List.foldl, step, Spec.BASE]; omega
    · next hlt2 =>
      rw [ge_iff_le, UInt64.le_iff_toNat_le, base_toNat, hy] at hlt2
      refine ⟨_, OkOn.pure _ _, result_value a _ _ _ ?_ ?_⟩
      · rw [hx]; simp only [sums, List.foldl, step, Spec.BASE]; omega
      · rw [hy]; simp only [sums, List.foldl, step, Spec.BASE]; omega

/-- `len == 1` is safe for every initial value (no validity needed). -/
theorem adler32_z_one_safe (hb : h.blocks[blk]? = some (some bytes)) (a : UInt64) (off : Nat)
    (hfit : off + 1 ≤ bytes.size) :
    ∃ r, OkOn h (adler32_z a (.ref blk off) (1 : Nat).toUInt64) r ∧ True := by
  unfold adler32_z
  have hnull : (Ptr.ref blk off == Ptr.null) = false := rfl
  rw [ite_eq_right_of_eq_false _ _ (by simp [hnull]), ite_eq_left (by decide)]
  refine OkOn.bind_ex (index8_ok (i := 0) hb (by omega : off + 0 < bytes.size)).bind_ex_pure ?_
  intro b _
  dsimp only
  split <;> split <;> exact ⟨_, OkOn.pure _ _, trivial⟩


end Zlib.Adler32.Proofs

/-! ## Main theorems

They state Theorems A1 (safety) and A2 (correctness) of `docs/proof/adler32.md`. -/

namespace Zlib.Adler32.Proofs
open C Zlib.Adler32 Zlib.Adler32.Spec

/-- **Main theorem.** For every live block, offset and length that fits in the
block, and every initial value whose high component sum is canonical
(`< 65521`, true of any value adler32 itself returns), `adler32_z` runs
without undefined behavior, terminates, leaves the heap unchanged and returns
the Adler-32 of the bytes. -/
theorem adler32_z_correct (h : Heap) (blk : Nat) (bytes : ByteArray)
    (hb : h.blocks[blk]? = some (some bytes)) (a : UInt64) (off L : Nat)
    (hfit : off + L ≤ bytes.size) (hL : L < 2 ^ 64) (hvalid : (a >>> 16 &&& 65535).toNat < 65521) :
    ∃ r, C.run (adler32_z a (.ref blk off) L.toUInt64) h = .ok (r, h) ∧
      r.toNat = Spec.adler32 a.toNat (seg bytes off L) := by
  by_cases h1 : L = 1
  · subst h1; exact adler32_z_one hb a off hfit hvalid
  · by_cases h16 : L < 16
    · exact adler32_z_short hb a off L hfit h16 h1
    · exact adler32_z_long hb a off L hfit hL (by omega)

/-- For `len ≠ 1` the result is the Adler-32 for **every** initial value. -/
theorem adler32_z_correct_ne_one (h : Heap) (blk : Nat) (bytes : ByteArray)
    (hb : h.blocks[blk]? = some (some bytes)) (a : UInt64) (off L : Nat)
    (hfit : off + L ≤ bytes.size) (hL : L < 2 ^ 64) (h1 : L ≠ 1) :
    ∃ r, C.run (adler32_z a (.ref blk off) L.toUInt64) h = .ok (r, h) ∧
      r.toNat = Spec.adler32 a.toNat (seg bytes off L) := by
  by_cases h16 : L < 16
  · exact adler32_z_short hb a off L hfit h16 h1
  · exact adler32_z_long hb a off L hfit hL (by omega)

/-- **Safety.** For every initial value, `adler32_z` on an in-bounds buffer
terminates without undefined behavior and leaves the heap unchanged. -/
theorem adler32_z_safe (h : Heap) (blk : Nat) (bytes : ByteArray)
    (hb : h.blocks[blk]? = some (some bytes)) (a : UInt64) (off L : Nat)
    (hfit : off + L ≤ bytes.size) (hL : L < 2 ^ 64) :
    ∃ r, C.run (adler32_z a (.ref blk off) L.toUInt64) h = .ok (r, h) := by
  by_cases h1 : L = 1
  · subst h1; obtain ⟨r, hr, -⟩ := adler32_z_one_safe hb a off hfit; exact ⟨r, hr⟩
  · obtain ⟨r, hr, -⟩ := adler32_z_correct_ne_one h blk bytes hb a off L hfit hL h1; exact ⟨r, hr⟩

end Zlib.Adler32.Proofs

namespace Zlib.Adler32.Proofs
open C Zlib.Adler32 Zlib.Adler32.Spec

variable {h : Heap}

theorem len2_rem (x : Int64) (h0 : 0 ≤ x) :
    (x % 65521).toUInt64.toUInt32.toUInt64.toNat = x.toInt.toNat % 65521 := by
  have hx : 0 ≤ x.toInt := Int64.le_iff_toInt_le.mp h0
  have hm : (x % 65521).toInt = x.toInt.tmod 65521 := Int64.toInt_mod x 65521
  have hm0 : 0 ≤ x % 65521 := by
    rw [Int64.le_iff_toInt_le, hm]; simp; exact Int.tmod_nonneg _ hx
  rw [UInt32.toNat_toUInt64, UInt64.toNat_toUInt32, Int64.toNat_toUInt64_of_le hm0,
    ← Int64.toNat_toInt, hm, Int.tmod_eq_emod_of_nonneg hx]
  omega

theorem toNat_sub' (x y : UInt64) : (x - y).toNat = (x.toNat + (2 ^ 64 - y.toNat)) % 2 ^ 64 := by
  rw [UInt64.toNat_sub]; have := y.toNat_lt; omega

/-- `if (x >= c) x -= c;` -/
def csub (x c : UInt64) : UInt64 := if x ≥ c then x - c else x

theorem csub_toNat (x c : UInt64) :
    (csub x c).toNat = if c.toNat ≤ x.toNat then x.toNat - c.toNat else x.toNat := by
  unfold csub
  by_cases hc : c.toNat ≤ x.toNat
  · have : x ≥ c := UInt64.le_iff_toNat_le.mpr hc
    rw [ite_eq_left this, ite_eq_left hc, sub_small _ _ hc]
  · have : ¬ x ≥ c := fun h' => hc (UInt64.le_iff_toNat_le.mp h')
    rw [ite_eq_right this, ite_eq_right hc]

/-- Value of `adler32_combine_` on canonical inputs (all four halves `< 65521`). -/
theorem combine_value (a1 a2 : UInt64) (len2 : Int64) (h0 : 0 ≤ len2)
    (hl1 : (a1 &&& 65535).toNat < 65521) (hh1 : (a1 >>> 16 &&& 65535).toNat < 65521)
    (hl2 : (a2 &&& 65535).toNat < 65521) (hh2 : (a2 >>> 16 &&& 65535).toNat < 65521) :
    ∃ r, OkOn h (adler32_combine_ a1 a2 len2) r ∧
      r.toNat = ((a1 &&& 65535).toNat + (a2 &&& 65535).toNat + 65521 - 1) % 65521 +
        65536 * (((len2.toInt.toNat % 65521) * (a1 &&& 65535).toNat % 65521 +
          (a1 >>> 16 &&& 65535).toNat + (a2 >>> 16 &&& 65535).toNat + 65521 -
          len2.toInt.toNat % 65521) % 65521) := by
  unfold adler32_combine_
  have hz : (0 : Int64).toInt = 0 := rfl
  rw [ite_eq_right (by
    intro hneg
    have a := Int64.lt_iff_toInt_lt.mp hneg
    have b := Int64.le_iff_toInt_le.mp h0
    rw [hz] at a b; omega)]
  dsimp only
  have hm := len2_rem len2 h0
  have hn : len2.toInt.toNat % 65521 < 65521 := Nat.mod_lt _ (by decide)
  generalize len2.toInt.toNat % 65521 = n at hm hn ⊢
  generalize (len2 % 65521).toUInt64.toUInt32.toUInt64 = M at hm ⊢
  generalize hA1 : a1 &&& 65535 = A1 at hl1 ⊢
  generalize hH1 : a1 >>> 16 &&& 65535 = H1 at hh1 ⊢
  generalize hA2 : a2 &&& 65535 = A2 at hl2 ⊢
  generalize hH2 : a2 >>> 16 &&& 65535 = H2 at hh2 ⊢
  have hprod : n * A1.toNat < 65521 * 65521 := Nat.mul_lt_mul'' hn hl1
  have hP : (M * A1).toNat = n * A1.toNat := by
    rw [UInt64.toNat_mul, hm]; exact Nat.mod_eq_of_lt (by omega)
  generalize M * A1 = P at hP ⊢
  have hB : (BASE : UInt64).toNat = 65521 := rfl
  have hB2 : (BASE <<< 1 : UInt64).toNat = 131042 := rfl
  have hpm : (P % BASE).toNat = n * A1.toNat % 65521 := by rw [UInt64.toNat_mod, hP, hB]
  generalize P % BASE = Pm at hpm ⊢
  have hpmlt : Pm.toNat < 65521 := by rw [hpm]; exact Nat.mod_lt _ (by decide)
  -- The two accumulated sums never wrap: compute them exactly, then abstract.
  have hS1 : (A1 + (A2 + BASE - 1)).toNat = A1.toNat + A2.toNat + 65520 := by
    have e1 : (A2 + BASE).toNat = A2.toNat + 65521 := by rw [add_small _ _ (by rw [hB]; omega), hB]
    have e2 : (A2 + BASE - 1).toNat = A2.toNat + 65520 := by
      rw [sub_small _ _ (by rw [e1]; simp), e1]; simp
    rw [add_small _ _ (by rw [e2]; omega), e2]; omega
  have hS2 : (Pm + (H1 + H2 + BASE - M)).toNat = Pm.toNat + H1.toNat + H2.toNat + 65521 - n := by
    have e1 : (H1 + H2).toNat = H1.toNat + H2.toNat := add_small _ _ (by omega)
    have e2 : (H1 + H2 + BASE).toNat = H1.toNat + H2.toNat + 65521 := by
      rw [add_small _ _ (by rw [e1, hB]; omega), e1, hB]
    have e3 : (H1 + H2 + BASE - M).toNat = H1.toNat + H2.toNat + 65521 - n := by
      rw [sub_small _ _ (by rw [e2, hm]; omega), e2, hm]
    rw [add_small _ _ (by rw [e3]; omega), e3]; omega
  generalize A1 + (A2 + BASE - 1) = S1 at hS1 ⊢
  generalize Pm + (H1 + H2 + BASE - M) = S2 at hS2 ⊢
  have sub' : ∀ x y : UInt64, y.toNat ≤ x.toNat → (x - y).toNat = x.toNat - y.toNat := sub_small
  have key : ∀ v : UInt64,
      v = csub (csub S1 BASE) BASE ||| csub (csub S2 (BASE <<< 1)) BASE <<< 16 →
      ∃ r, OkOn h (pure v) r ∧ r.toNat = (A1.toNat + A2.toNat + 65521 - 1) % 65521 +
        65536 * ((n * A1.toNat % 65521 + H1.toNat + H2.toNat + 65521 - n) % 65521) := by
    intro v hv
    refine ⟨v, OkOn.pure _ _, ?_⟩
    have c1 : (csub (csub S1 BASE) BASE).toNat = (A1.toNat + A2.toNat + 65521 - 1) % 65521 := by
      rw [csub_toNat, csub_toNat, hB, hS1]
      split <;> (try split) <;> omega
    have c2 : (csub (csub S2 (BASE <<< 1)) BASE).toNat =
        (n * A1.toNat % 65521 + H1.toNat + H2.toNat + 65521 - n) % 65521 := by
      rw [csub_toNat, csub_toNat, hB, hB2, hS2, hpm]
      split <;> (try split) <;> omega
    rw [hv, or_shift _ _ (by rw [c1]; omega) (by rw [c2]; omega), c1, c2]
  repeat' split
  all_goals
    apply key
    simp only [csub]
    repeat' split
    all_goals first
      | rfl
      | (exfalso; simp only [ge_iff_le, UInt64.le_iff_toNat_le, Nat.not_le] at *; omega)

theorem halves (st : Nat × Nat) (h1 : st.1 < 65521) (h2 : st.2 < 65521) :
    ((st.1 + 65536 * st.2).toUInt64 &&& 65535).toNat = st.1 ∧
    ((st.1 + 65536 * st.2).toUInt64 >>> 16 &&& 65535).toNat = st.2 := by
  have hv : (st.1 + 65536 * st.2).toUInt64.toNat = st.1 + 65536 * st.2 := by simp; omega
  rw [low16, high16, hv]
  omega

end Zlib.Adler32.Proofs

/-! ## Theorems for `adler32_combine`, `adler32_combine64` and `adler32`

The combination theorem says that `adler32_combine64` of the checksums of `A` and `B`, with `len2` the length of `B`, is the checksum of `A ++ B`. -/

namespace Zlib.Adler32.Proofs
open C Zlib.Adler32 Zlib.Adler32.Spec

variable {h : Heap}

/-- `adler32_combine_` never faults and leaves the heap unchanged. -/
theorem adler32_combine_safe (a1 a2 : UInt64) (len2 : Int64) :
    ∃ r, OkOn h (adler32_combine_ a1 a2 len2) r := by
  unfold adler32_combine_
  split
  · exact ⟨_, OkOn.pure _ _⟩
  · try dsimp only
    repeat' split
    all_goals exact ⟨_, OkOn.pure _ _⟩

/-- **Combination theorem.** For byte strings `A` and `B` (with `|B| < 2^63`),
`adler32_combine64(adler32(A), adler32(B), |B|) = adler32(A ++ B)`, where
`adler32` starts from the conventional initial value 1. -/
theorem adler32_combine_correct (A B : List UInt8) (hB : B.length < 2 ^ 63) :
    ∃ r, OkOn h (adler32_combine64 (Spec.adler32 1 A).toUInt64 (Spec.adler32 1 B).toUInt64
        (Int64.ofNat B.length)) r ∧ r.toNat = Spec.adler32 1 (A ++ B) := by
  have hx := sums_lt 1 0 A (by decide) (by decide)
  have hy := sums_lt 1 0 B (by decide) (by decide)
  simp only [Spec.BASE] at hx hy
  have e1 : Spec.adler32 1 A = (sums 1 0 A).1 + 65536 * (sums 1 0 A).2 := rfl
  have e2 : Spec.adler32 1 B = (sums 1 0 B).1 + 65536 * (sums 1 0 B).2 := rfl
  have e3 : Spec.adler32 1 (A ++ B) = (sums 1 0 (A ++ B)).1 + 65536 * (sums 1 0 (A ++ B)).2 := rfl
  obtain ⟨l1, h1⟩ := halves (sums 1 0 A) hx.1 hx.2
  obtain ⟨l2, h2⟩ := halves (sums 1 0 B) hy.1 hy.2
  have hlen0 : (0 : Int64) ≤ Int64.ofNat B.length := by
    rw [Int64.le_iff_toInt_le, Int64.toInt_ofNat_of_lt (by omega : B.length < 2 ^ 63)]
    exact Int.natCast_nonneg _
  have hlen : (Int64.ofNat B.length).toInt.toNat = B.length := by
    rw [Int64.toInt_ofNat_of_lt (by omega)]; simp
  rw [e1, e2] at *
  obtain ⟨r, hr, hv⟩ := combine_value (h := h) _ _ _ hlen0 (by rw [l1]; exact hx.1) (by rw [h1]; exact hx.2)
    (by rw [l2]; exact hy.1) (by rw [h2]; exact hy.2)
  refine ⟨r, hr, ?_⟩
  rw [hv, l1, h1, l2, h2, hlen, e3, sums_combine]
  simp only [Spec.BASE]

/-- `adler32_combine64` is `adler32_combine_`: it never faults. -/
theorem adler32_combine64_safe (a1 a2 : UInt64) (len2 : Int64) :
    ∃ r, OkOn h (adler32_combine64 a1 a2 len2) r := by
  exact adler32_combine_safe a1 a2 len2

/-- `adler32_combine` is `adler32_combine_`: it never faults. -/
theorem adler32_combine_c_safe (a1 a2 : UInt64) (len2 : Int64) :
    ∃ r, OkOn h (adler32_combine a1 a2 len2) r := by
  exact adler32_combine_safe a1 a2 len2

/-- `adler32` is `adler32_z` with a 32-bit length: it never faults on an in-bounds buffer. -/
theorem adler32_safe (h : Heap) (blk : Nat) (bytes : ByteArray)
    (hb : h.blocks[blk]? = some (some bytes)) (a : UInt64) (off L : Nat)
    (hfit : off + L ≤ bytes.size) (hL : L < 2 ^ 32) :
    ∃ r, C.run (adler32 a (.ref blk off) L.toUInt32) h = .ok (r, h) := by
  have hL' : L < 2 ^ 64 := by omega
  have e : L.toUInt32.toUInt64 = L.toUInt64 := by
    apply UInt64.toNat_inj.mp
    simp [Nat.mod_eq_of_lt hL, Nat.mod_eq_of_lt hL']
  unfold adler32
  rw [e]
  exact adler32_z_safe h blk bytes hb a off L hfit hL'

end Zlib.Adler32.Proofs


namespace Zlib.Adler32.Proofs
open C Zlib.Adler32

/-- Result value of a run, if it returns. -/
def resultOf {α} (r : Except Fault (α × Heap)) : Option α :=
  match r with
  | .ok (x, _) => some x
  | .error _ => none

/-- The `hvalid` precondition of `adler32_z_correct` is necessary: with initial
value `0xFFFFFFF0` (high half 65535, not canonical) and the single byte 0, the
C code subtracts BASE only once and returns `sum2 = 65534`, while the Adler-32
spec gives 13. -/
theorem adler32_z_one_noncanonical :
    resultOf (C.run (adler32_z 0xFFFFFFF0 (.ref 0 0) 1) { blocks := #[some (ByteArray.mk #[0])] }) =
      some (65520 + 65536 * 65534) ∧
    Spec.adler32 (0xFFFFFFF0 : UInt64).toNat [0] = 65520 + 65536 * 13 := by
  constructor <;> decide

end Zlib.Adler32.Proofs

