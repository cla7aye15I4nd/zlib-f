import ZlibF.Proof.«deflate.c.base»

/-!
# deflate.c: `deflateBound_z` and `deflateBound`

The bound is a closed formula of `w_bits`, `hash_bits`, `level`, the length of the wrapper and the source length. The
wrapper length depends on the state: 0 for a raw stream, 6 or 10 for a zlib stream (10 once a dictionary was loaded:
`strstart` is not 0), 18 plus the lengths of the user's header parts for a gzip stream.
-/

namespace Zlib.Deflate.Spec
open C

/-- `fixedlen` of `deflateBound_z`: an upper bound for the fixed-code deflate size (wraps to the maximum). -/
def fixedLen (n : UInt64) : UInt64 :=
  if n + (n >>> 3) + (n >>> 8) + (n >>> 9) + 4 < n then 0xffffffffffffffff else n + (n >>> 3) + (n >>> 8) + (n >>> 9) + 4

/-- `storelen` of `deflateBound_z`: an upper bound for the stored-block size. -/
def storeLen (n : UInt64) : UInt64 :=
  if n + (n >>> 5) + (n >>> 7) + (n >>> 11) + 7 < n then 0xffffffffffffffff else n + (n >>> 5) + (n >>> 7) + (n >>> 11) + 7

/-- The bound for a stream with no usable state (the check refuses it): the larger of the two plus 18. -/
def boundNoStateP (fx st : UInt64) : UInt64 :=
  let bound := if fx > st then fx else st
  if bound + 18 < bound then 0xffffffffffffffff else bound + 18

def boundNoState (n : UInt64) : UInt64 := boundNoStateP (fixedLen n) (storeLen n)

/-- The bound of a valid stream with the window bits, the hash bits, the level and the wrapper length `wl`, from the
values `fx` (`fixedlen`) and `st` (`storelen`). -/
def boundTailP (w_bits hash_bits : UInt32) (level : Int32) (wl : UInt64) (fx st n : UInt64) : UInt64 :=
  if w_bits != 15 || hash_bits != 15 then
    let bound := if w_bits ≤ hash_bits && level != 0 then fx else st
    if bound + wl < bound then 0xffffffffffffffff else bound + wl
  else
    let bound := n + (n >>> 12) + (n >>> 14) + (n >>> 25) + 13 - 6 + wl
    if bound < n then 0xffffffffffffffff else bound

def boundTail (w_bits hash_bits : UInt32) (level : Int32) (wl : UInt64) (n : UInt64) : UInt64 :=
  boundTailP w_bits hash_bits level wl (fixedLen n) (storeLen n) n

/-- The NUL-terminated string of length `len` starts at the pointer `p`: the bytes `p[0 .. len)` are not 0, `p[len]`
is 0, all inside one live array (a heap block or a string literal). The length is below `2^64`, the loop fuel of the
model (an array of `2^64` elements does not exist; Lean cannot prove it). -/
def GzStr (h : Heap) (p : BPtr) (len : Nat) : Prop :=
  ∃ r off a, p = .ref r off ∧ Space.get h r = some a ∧ off + len < a.size ∧ a[off + len]? = some 0 ∧
    (∀ i, i < len → a[off + i]? ≠ some 0) ∧ len < 2 ^ 64

/-- `p` is `NULL` or the start of a NUL-terminated string. -/
def StrOk (h : Heap) (p : BPtr) : Prop := p = .null ∨ ∃ len, GzStr h p len

/-- The number of bytes `deflate` writes for the string at `p`: 0 for `NULL`, else its length and the terminating zero. -/
def StrPart (h : Heap) (p : BPtr) (k : UInt64) : Prop :=
  (p = .null ∧ k = 0) ∨ ∃ len, GzStr h p len ∧ k = UInt64.ofNat (len + 1)

/-- `wl` is the length of the wrapper of the state record `d`: raw 0; zlib 6, plus 4 when `strstart` is not 0; gzip 18,
plus the parts of the user's header when there is one: the extra field (two length bytes and the field), the name, the
comment and the header CRC (two bytes). The wrapper is read from the absolute value of `wrap`. -/
def WrapLen (h : Heap) (d : DeflateState) (wl : UInt64) : Prop :=
  (d.wrap = 0 ∧ wl = 0) ∨ ((d.wrap = 1 ∨ d.wrap = -1) ∧ wl = 6 + (if d.strstart != 0 then 4 else 0)) ∨
  ((d.wrap = 2 ∨ d.wrap = -2) ∧ ((d.gzhead = none ∧ wl = 18) ∨
    ∃ g gh kn kc, d.gzhead = some (.tab g) ∧ h.gzheaders g = some gh ∧ StrPart h gh.name kn ∧ StrPart h gh.comment kc ∧
      wl = 18 + (if gh.extra = .null then 0 else ((2 : UInt32) + gh.extra_len).toUInt64) + kn + kc +
        (if gh.hcrc != 0 then 2 else 0)))

/-- The user's header, if there is one, has NUL-terminated `name` and `comment` (or `NULL`), as `zlib.h` requires. -/
def HdrStrOk (h : Heap) (d : DeflateState) : Prop :=
  d.gzhead = none ∨ ∃ g gh, d.gzhead = some (.tab g) ∧ h.gzheaders g = some gh ∧ StrOk h gh.name ∧ StrOk h gh.comment

end Zlib.Deflate.Spec

namespace Zlib.Deflate.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec

/-- The loop `do { wraplen++; } while (*str++);` over a string of length `len` adds `len + 1` to `wraplen` and leaves the
pointer one past the terminating zero; it reads the heap only. -/
theorem strLoop_run {h : Heap} {p : BPtr} {len : Nat} (hs : GzStr h p len) (w : UInt64) :
    OkOn h (cdoWhile (fun (s : UInt64 × BPtr) => (pure (s.1 + 1, s.2) : M (UInt64 × BPtr)))
      (fun (s : UInt64 × BPtr) => do
        let b ← load8 s.2
        pure (b != 0, (s.1, ← padd s.2 1)))
      (w, p)) (w + UInt64.ofNat (len + 1), (match p with | .ref r off => .ref r (off + len + 1) | .null => .null)) := by
  obtain ⟨r, off, a, rfl, hg, hlt, hz, hnz, hlen⟩ := hs
  simp only
  obtain ⟨k0, hk0⟩ : ∃ k, k = len := ⟨_, rfl⟩
  have key := cdoWhile_ok (h := h)
    (body := fun (s : UInt64 × BPtr) => (pure (s.1 + 1, s.2) : M (UInt64 × BPtr)))
    (cond := fun (s : UInt64 × BPtr) => do
        let b ← load8 s.2
        pure (b != 0, (s.1, ← padd s.2 1)))
    (P := fun k s => ∃ i, i + k = len ∧ s = (w + UInt64.ofNat i, (Ptr.ref r (off + i) : BPtr)))
    (Q := fun s => s = (w + UInt64.ofNat (len + 1), (Ptr.ref r (off + len + 1) : BPtr)))
    ?_ ?_ (k := len) (s := (w, (Ptr.ref r off : BPtr))) ⟨0, by omega, by simp⟩ (by unfold fuel; omega)
  · obtain ⟨s', hs', rfl⟩ := key
    exact hs'
  · rintro k s ⟨i, hi, rfl⟩
    have hlt' : off + i < a.size := by omega
    have hnz' : a[off + i]? ≠ some 0 := hnz i (by omega)
    have hne : a[off + i] ≠ 0 := by
      intro h0; apply hnz'; simp [hlt', h0]
    refine ⟨(w + UInt64.ofNat i + 1, Ptr.ref r (off + i)), (w + UInt64.ofNat (i + 1), Ptr.ref r (off + (i + 1))), rfl, ?_, i + 1, by omega, ?_⟩
    · have e1 := Ptr.load_ok (r := r) (off := off + i) hg hlt'
      have e2 := Ptr.add_nat_ok (r := r) (off := off + i) (n := 1) hg (by omega)
      show OkOn h (do let b ← load8 (Ptr.ref r (off + i)); pure (b != 0, (w + UInt64.ofNat i + 1, ← padd (Ptr.ref r (off + i)) 1))) _
      refine OkOn.bind (x := a[off + i]) e1 ?_
      refine OkOn.bind (x := Ptr.ref r (off + i + 1)) e2 ?_
      have hb : (a[off + i] != 0) = true := by simpa using hne
      have e3 : w + UInt64.ofNat i + 1 = w + UInt64.ofNat (i + 1) := by
        rw [UInt64.ofNat_add]; simp [UInt64.add_assoc]
      unfold OkOn
      simp [hb, e3, Nat.add_assoc]
    · simp [Nat.add_assoc]
  · rintro s ⟨i, hi, rfl⟩
    have hi' : i = len := by omega
    subst hi'
    have hlt' : off + i < a.size := hlt
    have hz' : a[off + i] = 0 := by
      have := hz; simp [hlt'] at this; exact this
    refine ⟨(w + UInt64.ofNat i + 1, Ptr.ref r (off + i)), (w + UInt64.ofNat i + 1, Ptr.ref r (off + i + 1)), rfl, ?_, ?_⟩
    · have e1 := Ptr.load_ok (r := r) (off := off + i) hg hlt'
      have e2 := Ptr.add_nat_ok (r := r) (off := off + i) (n := 1) hg (by omega)
      show OkOn h (do let b ← load8 (Ptr.ref r (off + i)); pure (b != 0, (w + UInt64.ofNat i + 1, ← padd (Ptr.ref r (off + i)) 1))) _
      refine OkOn.bind (x := a[off + i]) e1 ?_
      refine OkOn.bind (x := Ptr.ref r (off + i + 1)) e2 ?_
      unfold OkOn
      simp [hz']
    · have e3 : w + UInt64.ofNat i + 1 = w + UInt64.ofNat (i + 1) := by
        rw [UInt64.ofNat_add]; simp [UInt64.add_assoc]
      simp [e3]


theorem wrap_cases {w : Int32} (h1 : -2 ≤ w.toInt) (h2 : w.toInt ≤ 2) :
    w = 0 ∨ w = 1 ∨ w = -1 ∨ w = 2 ∨ w = -2 := by
  have : w.toInt = 0 ∨ w.toInt = 1 ∨ w.toInt = -1 ∨ w.toInt = 2 ∨ w.toInt = -2 := by omega
  rcases this with e | e | e | e | e
  · exact Or.inl (Int32.toInt_inj.mp (e.trans (by decide)))
  · exact Or.inr (Or.inl (Int32.toInt_inj.mp (e.trans (by decide))))
  · exact Or.inr (Or.inr (Or.inl (Int32.toInt_inj.mp (e.trans (by decide)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (Int32.toInt_inj.mp (e.trans (by decide))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Int32.toInt_inj.mp (e.trans (by decide))))))

/-- `deflateBound_z` after `fixedlen` and `storelen` are computed, as a function of the two values. -/
def boundBody (strm : ZStreamPtr) (fixedlen storelen : UInt64) (sourceLen : UInt64) : M UInt64 := do
  if (← deflateStateCheck strm) != 0 then
    let bound := if fixedlen > storelen then fixedlen else storelen
    return if bound + 18 < bound then 0xffffffffffffffff else bound + 18
  let s ← castDeflateState (← zrd strm (·.state))
  let d ← ldDeflateState s
  let w ← if d.wrap < 0 then ineg d.wrap else pure d.wrap
  let mut wraplen : UInt64 := 18
  if w == 0 then
    wraplen := 0
  else if w == 1 then
    wraplen := 6 + (if d.strstart != 0 then 4 else 0)
  else if w == 2 then
    wraplen := 18
    if d.gzhead != none then
      let gh ← ldGzHeader d.gzhead
      if gh.extra != .null then wraplen := wraplen + ((2 : UInt32) + gh.extra_len).toUInt64
      if gh.name != .null then
        let (wl, _) ← cdoWhile
          (fun (wl, str) => pure (wl + 1, str))
          (fun (wl, str) => do
            let b ← load8 str
            pure (b != 0, (wl, ← padd str 1)))
          (wraplen, gh.name)
        wraplen := wl
      if gh.comment != .null then
        let (wl, _) ← cdoWhile
          (fun (wl, str) => pure (wl + 1, str))
          (fun (wl, str) => do
            let b ← load8 str
            pure (b != 0, (wl, ← padd str 1)))
          (wraplen, gh.comment)
        wraplen := wl
      if gh.hcrc != 0 then wraplen := wraplen + 2
  else
    wraplen := 18
  if d.w_bits != 15 || d.hash_bits != 15 then
    let bound := if d.w_bits ≤ d.hash_bits && d.level != 0 then fixedlen else storelen
    return if bound + wraplen < bound then 0xffffffffffffffff else bound + wraplen
  let bound : UInt64 := sourceLen + (sourceLen >>> 12) + (sourceLen >>> 14) + (sourceLen >>> 25) + 13 - 6 + wraplen
  return if bound < sourceLen then 0xffffffffffffffff else bound

theorem deflateBound_z_eq (strm : ZStreamPtr) (n : UInt64) :
    deflateBound_z strm n = boundBody strm (fixedLen n) (storeLen n) n := by
  unfold deflateBound_z boundBody fixedLen storeLen
  by_cases c1 : n + (n >>> 3) + (n >>> 8) + (n >>> 9) + 4 < n <;>
    by_cases c2 : n + (n >>> 5) + (n >>> 7) + (n >>> 11) + 7 < n <;>
    simp only [c1, c2, ↓reduceIte] <;> rfl

theorem ineg_m2 : ineg (-2) = (pure 2 : M Int32) := by
  unfold ineg chk32
  simp

theorem ineg_m1 : ineg (-1) = (pure 1 : M Int32) := by
  unfold ineg chk32
  simp

theorem boundBody_nostate {h : Heap} {strm : ZStreamPtr} (hD : StreamDom h strm) (hN : ¬ DInitialised h strm)
    (fx st n : UInt64) : boundBody strm fx st n h = .ok (boundNoStateP fx st, h) := by
  unfold boundBody
  simp [bind_app, notInit_check hD hN, boundNoStateP]

theorem boundBody_raw {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (hL : DLive h r ds z d) (hw : d.wrap = 0) (fx st n : UInt64) :
    boundBody (some r) fx st n h = .ok (boundTailP d.w_bits d.hash_bits d.level 0 fx st n, h) := by
  unfold boundBody
  dsimp' [stateCheck_live hL, hL.zst, hL.hz, hL.hs, hw]
  by_cases c : ¬d.w_bits = 15 ∨ ¬d.hash_bits = 15 <;> simp [boundTailP, c]

theorem boundBody_zlib {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (hL : DLive h r ds z d) (hw : d.wrap = 1 ∨ d.wrap = -1) (fx st n : UInt64) :
    boundBody (some r) fx st n h =
      .ok (boundTailP d.w_bits d.hash_bits d.level (6 + (if d.strstart != 0 then 4 else 0)) fx st n, h) := by
  unfold boundBody
  rcases hw with hw | hw
  · dsimp' [stateCheck_live hL, hL.zst, hL.hz, hL.hs, hw]
    by_cases c : ¬d.w_bits = 15 ∨ ¬d.hash_bits = 15 <;> simp [boundTailP, c]
  · dsimp' [stateCheck_live hL, hL.zst, hL.hz, hL.hs, hw, ineg_m1]
    by_cases c : ¬d.w_bits = 15 ∨ ¬d.hash_bits = 15 <;> simp [boundTailP, c]


theorem boundBody_gz_nohead {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (hL : DLive h r ds z d) (hw : d.wrap = 2 ∨ d.wrap = -2) (hg : d.gzhead = none) (fx st n : UInt64) :
    boundBody (some r) fx st n h = .ok (boundTailP d.w_bits d.hash_bits d.level 18 fx st n, h) := by
  unfold boundBody
  rcases hw with hw | hw
  · dsimp' [stateCheck_live hL, hL.zst, hL.hz, hL.hs, hw, hg]
    by_cases c : ¬d.w_bits = 15 ∨ ¬d.hash_bits = 15 <;> simp [boundTailP, c]
  · dsimp' [stateCheck_live hL, hL.zst, hL.hz, hL.hs, hw, hg, ineg_m2]
    by_cases c : ¬d.w_bits = 15 ∨ ¬d.hash_bits = 15 <;> simp [boundTailP, c]

theorem GzStr.ne_null {h : Heap} {p : BPtr} {len : Nat} (hs : GzStr h p len) : p ≠ .null := by
  obtain ⟨r, off, a, rfl, -⟩ := hs
  intro e; cases e

theorem strLoop_eq {h : Heap} {p : BPtr} {len : Nat} (hs : GzStr h p len) (w : UInt64) :
    cdoWhile (fun (s : UInt64 × BPtr) => (pure (s.1 + 1, s.2) : M (UInt64 × BPtr)))
      (fun (s : UInt64 × BPtr) => do
        let b ← load8 s.2
        pure (b != 0, (s.1, ← padd s.2 1)))
      (w, p) h = .ok ((w + UInt64.ofNat (len + 1), (match p with | .ref r off => .ref r (off + len + 1) | .null => .null)), h) :=
  strLoop_run hs w

set_option maxHeartbeats 1600000 in
theorem boundBody_gz_head {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (hL : DLive h r ds z d) (hw : d.wrap = 2 ∨ d.wrap = -2) {g : Nat} {gh : GzHeader}
    (hg : d.gzhead = some (.tab g)) (hgh : h.gzheaders g = some gh) {kn kc : UInt64}
    (hn : StrPart h gh.name kn) (hc : StrPart h gh.comment kc) (fx st n : UInt64) :
    boundBody (some r) fx st n h = .ok (boundTailP d.w_bits d.hash_bits d.level
      (18 + (if gh.extra = .null then 0 else ((2 : UInt32) + gh.extra_len).toUInt64) + kn + kc +
        (if gh.hcrc != 0 then 2 else 0)) fx st n, h) := by
  unfold boundBody
  rcases hw with hw | hw
  · rcases hn with ⟨hn0, rfl⟩ | ⟨ln, hs1, rfl⟩ <;> rcases hc with ⟨hc0, rfl⟩ | ⟨lc, hs2, rfl⟩ <;>
      by_cases he : gh.extra = .null <;> by_cases hh : gh.hcrc = 0 <;> by_cases c : ¬d.w_bits = 15 ∨ ¬d.hash_bits = 15 <;>
      (try have := GzStr.ne_null ‹GzStr h gh.name _›) <;> (try have := GzStr.ne_null ‹GzStr h gh.comment _›) <;>
      dsimp' [stateCheck_live hL, hL.zst, hL.hz, hL.hs, hw, hg, ldGzHeader_tab hgh] <;>
      simp (disch := assumption) [boundTailP, c, he, hh, *, strLoop_eq]
  · rcases hn with ⟨hn0, rfl⟩ | ⟨ln, hs1, rfl⟩ <;> rcases hc with ⟨hc0, rfl⟩ | ⟨lc, hs2, rfl⟩ <;>
      by_cases he : gh.extra = .null <;> by_cases hh : gh.hcrc = 0 <;> by_cases c : ¬d.w_bits = 15 ∨ ¬d.hash_bits = 15 <;>
      (try have := GzStr.ne_null ‹GzStr h gh.name _›) <;> (try have := GzStr.ne_null ‹GzStr h gh.comment _›) <;>
      dsimp' [stateCheck_live hL, hL.zst, hL.hz, hL.hs, hw, hg, ldGzHeader_tab hgh, ineg_m2] <;>
      simp (disch := assumption) [boundTailP, c, he, hh, *, strLoop_eq]



theorem StrOk.part {h : Heap} {p : BPtr} (hs : StrOk h p) : ∃ k, StrPart h p k := by
  rcases hs with rfl | ⟨len, hl⟩
  · exact ⟨0, Or.inl ⟨rfl, rfl⟩⟩
  · exact ⟨_, Or.inr ⟨len, hl, rfl⟩⟩

theorem _root_.Zlib.Deflate.Spec.DStInv.wrapLen {h : Heap} {ds : Nat} {d : DeflateState} (hI : DStInv h ds d) (hs : HdrStrOk h d) :
    ∃ wl, WrapLen h d wl := by
  have hw := wrap_cases (w := d.wrap) hI.wrap_lo hI.wrap_hi
  rcases hw with hw | hw | hw | hw | hw
  · exact ⟨0, Or.inl ⟨hw, rfl⟩⟩
  · exact ⟨_, Or.inr (Or.inl ⟨Or.inl hw, rfl⟩)⟩
  · exact ⟨_, Or.inr (Or.inl ⟨Or.inr hw, rfl⟩)⟩
  all_goals
    rcases hs with hg | ⟨g, gh, hg, hgh, hn, hc⟩
    · exact ⟨18, Or.inr (Or.inr ⟨by simp [hw], Or.inl ⟨hg, rfl⟩⟩)⟩
    · obtain ⟨kn, hkn⟩ := StrOk.part hn
      obtain ⟨kc, hkc⟩ := StrOk.part hc
      exact ⟨_, Or.inr (Or.inr ⟨by simp [hw], Or.inr ⟨g, gh, kn, kc, hg, hgh, hkn, hkc, rfl⟩⟩)⟩

theorem boundBody_wl {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (hL : DLive h r ds z d) {wl : UInt64} (hwl : WrapLen h d wl) (fx st n : UInt64) :
    boundBody (some r) fx st n h = .ok (boundTailP d.w_bits d.hash_bits d.level wl fx st n, h) := by
  rcases hwl with ⟨hw, rfl⟩ | ⟨hw, rfl⟩ | ⟨hw, ⟨hg, rfl⟩ | ⟨g, gh, kn, kc, hg, hgh, hn, hc, rfl⟩⟩
  · exact boundBody_raw hL hw fx st n
  · exact boundBody_zlib hL hw fx st n
  · exact boundBody_gz_nohead hL hw hg fx st n
  · exact boundBody_gz_head hL hw hg hgh hn hc fx st n

/-- **deflateBound_z, safety and specification.** On an initialised stream with the invariant, and a user gzip header
(if there is one) whose `name` and `comment` are `NULL` or NUL-terminated strings (`zlib.h` requires it; the
precondition `HdrStrOk`), the call never faults and leaves the heap unchanged. Its value is the closed formula
`boundTail` of `w_bits`, `hash_bits`, `level`, the wrapper length `wl` (`WrapLen`: 0 for raw, 6 or 10 for zlib, 18 and the
parts of the header for gzip) and the source length. -/
theorem deflateBound_z_safe {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (hG : DGood h r ds z d) (hs : HdrStrOk h d) (n : UInt64) :
    ∃ wl, WrapLen h d wl ∧
      C.run (deflateBound_z (some r) n) h = .ok (boundTail d.w_bits d.hash_bits d.level wl n, h) := by
  obtain ⟨wl, hwl⟩ := hG.inv.wrapLen hs
  refine ⟨wl, hwl, ?_⟩
  rw [C.run, deflateBound_z_eq, boundBody_wl hG.live hwl]
  rfl

/-- **deflateBound_z on a stream the check refuses** (including `NULL`): the value `boundNoState`, the heap unchanged. -/
theorem deflateBound_z_nostate {h : Heap} {strm : ZStreamPtr} (hD : StreamDom h strm) (hN : ¬ DInitialised h strm)
    (n : UInt64) : C.run (deflateBound_z strm n) h = .ok (boundNoState n, h) := by
  rw [C.run, deflateBound_z_eq, boundBody_nostate hD hN]
  rfl

/-- **deflateBound, safety and specification.** `deflateBound` is `deflateBound_z` (on this target `uLong` and
`z_size_t` are both 64 bits, so the final saturation never applies). -/
theorem deflateBound_safe {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (hG : DGood h r ds z d) (hs : HdrStrOk h d) (n : UInt64) :
    ∃ wl, WrapLen h d wl ∧
      C.run (deflateBound (some r) n) h = .ok (boundTail d.w_bits d.hash_bits d.level wl n, h) := by
  obtain ⟨wl, hwl, e⟩ := deflateBound_z_safe hG hs n
  refine ⟨wl, hwl, ?_⟩
  unfold deflateBound
  simp [C.run, bind_app] at e ⊢
  simp [e]

/-- **deflateBound on a stream the check refuses**: `boundNoState`, the heap unchanged. -/
theorem deflateBound_nostate {h : Heap} {strm : ZStreamPtr} (hD : StreamDom h strm) (hN : ¬ DInitialised h strm)
    (n : UInt64) : C.run (deflateBound strm n) h = .ok (boundNoState n, h) := by
  have e := deflateBound_z_nostate hD hN n
  unfold deflateBound
  simp [C.run, bind_app] at e ⊢
  simp [e]

end Zlib.Deflate.Proofs
