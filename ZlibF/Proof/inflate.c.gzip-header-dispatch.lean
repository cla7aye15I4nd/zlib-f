import ZlibF.Proof.«inflate.c.gzip-header-modes»

/-!
# inflate.c: one dispatch from a gzip header mode

`inflate_dispatch_gzip_header_rank`: one dispatch from `FLAGS` .. `HCRC` runs
under the representation invariant, keeps the caller packet and the header
record, writes only the gzip header fields and its footprint, and either leaves
or decreases the dispatch rank. The statement is the inflate owner's interface
(`skeleton/inflate`). Two premises are narrower than zlib.h; both come from real
C undefined behaviour reproduced under AddressSanitizer: the caller's `extra`
buffer is separate from the unread input (`ExtraApart`; EXTRA copies with
`memcpy`), and in `EXTRA` the record's `extra_len` is not below the remaining
length (`zmemcpy` past `extra_max` after a 32-bit wrap otherwise).
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Each caller region the header record names after a step is the region
it named before, or its pointer was set to `Z_NULL` (the header has no extra
field, name or comment), with the same maximum length. -/
def RegionsKept : List Region → List Region → Prop
  | [], [] => True
  | a :: after, b :: before =>
    (a = b ∨ (a.pointer = .null ∧ a.length = b.length)) ∧ RegionsKept after before
  | _, _ => False

theorem RegionsKept.mem {after before : List Region} (kept : RegionsKept after before) {region : Region}
    (member : region ∈ after) (nonnull : region.pointer ≠ .null) : region ∈ before := by
  induction after generalizing before with
  | nil => cases member
  | cons a rest ih =>
    cases before with
    | nil => cases kept
    | cons b others =>
      obtain ⟨first, tail⟩ := kept
      rcases List.mem_cons.mp member with head | inRest
      · subst head
        rcases first with same | ⟨null, _⟩
        · rw [same]; exact List.mem_cons_self
        · exact absurd null nonnull
      · exact List.mem_cons_of_mem _ (ih tail inRest)

/-! ## The dispatch selects the mode -/

section select
variable {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}

theorem inflate_dispatch_FLAGS (E : Env c h r zs z s) (l : IL) (mode : s.mode = FLAGS) :
    runX (inflate_dispatch c) l h = runX (inflate_FLAGS c) l h := by
  unfold inflate_dispatch
  rw [runX_bind, runX_rdS E]
  with_reducible simp [mode, HEAD, FLAGS]

theorem inflate_dispatch_TIME (E : Env c h r zs z s) (l : IL) (mode : s.mode = TIME) :
    runX (inflate_dispatch c) l h = runX (inflate_TIME c) l h := by
  unfold inflate_dispatch
  rw [runX_bind, runX_rdS E]
  with_reducible simp [mode, HEAD, FLAGS, TIME]

theorem inflate_dispatch_OS (E : Env c h r zs z s) (l : IL) (mode : s.mode = OS) :
    runX (inflate_dispatch c) l h = runX (inflate_OS c) l h := by
  unfold inflate_dispatch
  rw [runX_bind, runX_rdS E]
  with_reducible simp [mode, HEAD, FLAGS, TIME, OS]

theorem inflate_dispatch_EXLEN (E : Env c h r zs z s) (l : IL) (mode : s.mode = EXLEN) :
    runX (inflate_dispatch c) l h = runX (inflate_EXLEN c) l h := by
  unfold inflate_dispatch
  rw [runX_bind, runX_rdS E]
  with_reducible simp [mode, HEAD, FLAGS, TIME, OS, EXLEN]

theorem inflate_dispatch_EXTRA (E : Env c h r zs z s) (l : IL) (mode : s.mode = EXTRA) :
    runX (inflate_dispatch c) l h = runX (inflate_EXTRA c) l h := by
  unfold inflate_dispatch
  rw [runX_bind, runX_rdS E]
  with_reducible simp [mode, HEAD, FLAGS, TIME, OS, EXLEN, EXTRA]

theorem inflate_dispatch_NAME (E : Env c h r zs z s) (l : IL) (mode : s.mode = NAME) :
    runX (inflate_dispatch c) l h = runX (inflate_NAME c) l h := by
  unfold inflate_dispatch
  rw [runX_bind, runX_rdS E]
  with_reducible simp [mode, HEAD, FLAGS, TIME, OS, EXLEN, EXTRA, NAME]

theorem inflate_dispatch_COMMENT (E : Env c h r zs z s) (l : IL) (mode : s.mode = COMMENT) :
    runX (inflate_dispatch c) l h = runX (inflate_COMMENT c) l h := by
  unfold inflate_dispatch
  rw [runX_bind, runX_rdS E]
  with_reducible simp [mode, HEAD, FLAGS, TIME, OS, EXLEN, EXTRA, NAME, COMMENT]

theorem inflate_dispatch_HCRC (E : Env c h r zs z s) (l : IL) (mode : s.mode = HCRC) :
    runX (inflate_dispatch c) l h = runX (inflate_HCRC c) l h := by
  unfold inflate_dispatch
  rw [runX_bind, runX_rdS E]
  with_reducible simp [mode, HEAD, FLAGS, TIME, OS, EXLEN, EXTRA, NAME, COMMENT, HCRC]

end select

/-- The eight gzip header modes. -/
theorem gzip_header_mode_cases {m : UInt32} (range : FLAGS ≤ m ∧ m ≤ HCRC) :
    m = FLAGS ∨ m = TIME ∨ m = OS ∨ m = EXLEN ∨ m = EXTRA ∨ m = NAME ∨ m = COMMENT ∨ m = HCRC := by
  have lo := UInt32.le_iff_toNat_le.mp range.1
  have hi := UInt32.le_iff_toNat_le.mp range.2
  have lo' : FLAGS.toNat = 16181 := rfl
  have hi' : HCRC.toNat = 16188 := rfl
  have cases : m.toNat = 16181 ∨ m.toNat = 16182 ∨ m.toNat = 16183 ∨ m.toNat = 16184 ∨
      m.toNat = 16185 ∨ m.toNat = 16186 ∨ m.toNat = 16187 ∨ m.toNat = 16188 := by omega
  rcases cases with k | k | k | k | k | k | k | k
  · exact Or.inl (UInt32.toNat_inj.mp (by rw [k]; rfl))
  · exact Or.inr (Or.inl (UInt32.toNat_inj.mp (by rw [k]; rfl)))
  · exact Or.inr (Or.inr (Or.inl (UInt32.toNat_inj.mp (by rw [k]; rfl))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (UInt32.toNat_inj.mp (by rw [k]; rfl)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (UInt32.toNat_inj.mp (by rw [k]; rfl))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (UInt32.toNat_inj.mp (by rw [k]; rfl)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (UInt32.toNat_inj.mp (by rw [k]; rfl))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (UInt32.toNat_inj.mp (by rw [k]; rfl))))))))

/-- A gzip header mode has the default dispatch credit. -/
theorem dispatchCredit_gzip_header {m : UInt32} (range : FLAGS ≤ m ∧ m ≤ HCRC) : dispatchCredit m = 61 := by
  rcases gzip_header_mode_cases range with k | k | k | k | k | k | k | k <;> subst k <;> decide

/-- One gzip header dispatch from the entry `e`. -/
theorem gz_dispatch {e : GzEntry} (valid : e.Valid) (mode : FLAGS ≤ e.s.mode ∧ e.s.mode ≤ HCRC)
    (flags : FLAGS < e.s.mode → e.s.flags ≠ -1 ∧ e.s.flags ≠ 0) (lenOk : ExtraLenOk e.h e.s) :
    GzRuns e (inflate_dispatch e.c) e.l e.h := by
  have inv := GzInv.refl valid
  have E := valid.env
  have later : ∀ {m : UInt32}, e.s.mode = m → FLAGS < m → e.s.flags ≠ -1 ∧ e.s.flags ≠ 0 :=
    fun k lt => flags (by rw [k]; exact lt)
  unfold GzRuns
  rcases gzip_header_mode_cases mode with k | k | k | k | k | k | k | k
  · rw [inflate_dispatch_FLAGS E e.l k]; exact gz_FLAGS valid inv k
  · rw [inflate_dispatch_TIME E e.l k]; exact gz_TIME valid inv k (later k (by decide))
  · rw [inflate_dispatch_OS E e.l k]; exact gz_OS valid inv k (later k (by decide))
  · rw [inflate_dispatch_EXLEN E e.l k]; exact gz_EXLEN valid inv k (later k (by decide))
  · rw [inflate_dispatch_EXTRA E e.l k]; exact gz_EXTRA valid inv k (later k (by decide)) (fun _ => lenOk)
  · rw [inflate_dispatch_NAME E e.l k]; exact gz_NAME valid inv k (later k (by decide))
  · rw [inflate_dispatch_COMMENT E e.l k]; exact gz_COMMENT valid inv k (later k (by decide))
  · rw [inflate_dispatch_HCRC E e.l k]; exact gz_HCRC valid inv k (later k (by decide))

/-! ## From the step invariant to the interface -/

/-- The caller packet after the dispatch, from the entry packet: consumed input,
the same output registers, sizes and read-only flags kept. -/
theorem DispatchBuffers.of_entry {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z stream : ZStream} {s state : InflateState} {l regs : IL} {bs rest : List UInt8} {used : Nat}
    (buffers : DispatchBuffers h r l bs) (before : Good h r zs z s)
    (current : Good after r zs stream state) (window : state.window = s.window)
    (sizes : ByteViewSizes h after) (readonly : ∀ ref : BRef, Space.ro after ref = Space.ro h ref)
    (next : regs.next = inputAdvance l.next used) (count : regs.have_.toNat + used = l.have_.toNat)
    (put : regs.put = l.put) (left : regs.left = l.left) (total : regs.out_ = l.out_)
    (bits : BitInv after regs rest) : DispatchBuffers after r regs rest := by
  have input := callerRange_capacity before current window sizes readonly buffers.input
  have inputBound : used ≤ l.have_.toNat := by omega
  have advanced := callerRange_advance input inputBound
  have nextCount : regs.have_.toNat = l.have_.toNat - used := by omega
  have output := buffers.output.emit before current window sizes readonly (regs := regs) (made := 0)
    (by rw [put, inputAdvance_zero]) (by rw [left]; rfl) total
  have separate := inputAdvance_separate l.next l.put l.have_.toNat l.left.toNat used inputBound buffers.separate
  refine ⟨?_, output, ?_, bits⟩
  · rw [next, nextCount]; exact advanced
  · rw [next, put, left, nextCount]; exact separate

section final
variable {e : GzEntry} {l : IL} {h : Heap} {z : ZStream} {s : InflateState} {used : Nat}

/-- The header record's regions after the dispatch are the entry regions, or NULL. -/
theorem GzInv.regionsKept (inv : GzInv e l h z s used) (valid : e.Valid) :
    RegionsKept (HeaderRegions h s.head) (HeaderRegions e.h e.s.head) := by
  rw [inv.head]
  cases head : e.s.head with
  | none => trivial
  | some ref =>
    cases ref with
    | tab i =>
      obtain ⟨g0, get0, _⟩ := valid.entryRecord head
      obtain ⟨g, get, xm, nm, cm, xp, np, cp⟩ := inv.links i head g0 get0
      simp only [HeaderRegions, get, get0, RegionsKept]
      refine ⟨?_, ?_, ?_, trivial⟩
      · rcases xp with same | null
        · exact Or.inl (by rw [same, xm])
        · exact Or.inr ⟨null, by rw [xm]⟩
      · rcases np with same | null
        · exact Or.inl (by rw [same, nm])
        · exact Or.inr ⟨null, by rw [nm]⟩
      · rcases cp with same | null
        · exact Or.inl (by rw [same, cm])
        · exact Or.inr ⟨null, by rw [cm]⟩

theorem GzInv.hbufApart (inv : GzInv e l h z s used) (valid : e.Valid) : HbufApart e.c h s.head := by
  intro b ptr region member ref off rptr
  have nonnull : region.pointer ≠ .null := by rw [rptr]; exact fun h => by cases h
  exact valid.apart b ptr region ((inv.regionsKept valid).mem member nonnull) ref off rptr

theorem GzInv.headerMemory (inv : GzInv e l h z s used) (valid : e.Valid) :
    HeaderMemory h e.r s.head true := by
  rw [inv.head]
  cases head : e.s.head with
  | none => exact Or.inl rfl
  | some ref =>
    cases ref with
    | tab i =>
      rcases valid.record with none | ⟨j, g0, ptr, get0, owned0, extra0, name0, comment0⟩
      · rw [head] at none; cases none
      rw [head] at ptr
      cases ptr
      obtain ⟨g, get, xm, nm, cm, xp, np, cp⟩ := inv.links i head g0 get0
      have capacity : ∀ {p : BPtr} {n : Nat}, CallerRange e.h e.r p n true → CallerRange h e.r p n true :=
        fun range => callerRange_capacity valid.good inv.good inv.window inv.sizes inv.readonly range
      refine Or.inr ⟨i, g, rfl, get, ?_, ?_, ?_, ?_⟩
      · intro owned
        apply owned0
        rw [valid.good.streamOwned_iff]
        have now := (inv.good.streamOwned_iff i).mp owned
        unfold InflateOwned at now ⊢
        rw [inv.window] at now
        exact now
      · intro nonnull
        have same : g.extra = g0.extra := xp.resolve_right nonnull
        have range := extra0 (by rw [← same]; exact nonnull)
        simp only [if_true] at range ⊢
        rw [same, xm]; exact capacity range
      · intro nonnull
        have same : g.name = g0.name := np.resolve_right nonnull
        have range := name0 (by rw [← same]; exact nonnull)
        simp only [if_true] at range ⊢
        rw [same, nm]; exact capacity range
      · intro nonnull
        have same : g.comment = g0.comment := cp.resolve_right nonnull
        have range := comment0 (by rw [← same]; exact nonnull)
        simp only [if_true] at range ⊢
        rw [same, cm]; exact capacity range

end final

/-- One dispatch from a gzip header mode returns, keeps the representation,
the caller packet and the header record, writes only the gzip header fields
and its footprint, and either leaves or decreases the dispatch rank. A
completed header (HCRC done) is in `TYPE`; past `FLAGS` the gzip flags are read
(nonzero, since the method byte is 8). The header record's buffers may
overlap the unread input (zlib.h does not forbid it), so only the length of
the remaining input is fixed, not its bytes. Two premises are narrower than
zlib.h (`docs/deviations.md`): `extraApart` (the `extra` buffer is separate from
the unread input) and `extraLen` (in `EXTRA`, `extra_len` is not below the
remaining length); the real C has undefined behaviour without them
(`tests/regression/inflate-gzip-extra`). -/
theorem inflate_dispatch_gzip_header_rank {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (good : Good h r zs z s) (pending : DataPendingInvariant s)
    (buffers : DispatchBuffers h r l bs) (hbuf : LocalHbuf c h) (apart : HbufApart c h s.head)
    (record : HeaderMemory h r s.head true) (globals : LibraryGlobals h)
    (extraApart : ExtraApart h s.head l)
    (extraLen : s.mode = EXTRA → ∀ i g, s.head = some (.tab i) → h.gzheaders i = some g →
      s.length ≤ g.extra_len)
    (mode : FLAGS ≤ s.mode ∧ s.mode ≤ HCRC) (gzip : GzipAllowed s.wrap)
    (flags : FLAGS < s.mode → s.flags ≠ -1 ∧ s.flags ≠ 0)
    (incoming : l.bits.toNat ≤ 39) :
    ∃ outcome regs after stream state used, used ≤ bs.length ∧
      runX (inflate_dispatch c) l h = .ok ((outcome, regs), after) ∧
      Good after r zs stream state ∧ DataPendingInvariant state ∧
      (∃ rest, rest.length = bs.length - used ∧ DispatchBuffers after r regs rest) ∧
      ByteViewSizes h after ∧
      regs.next = inputAdvance l.next used ∧ regs.have_.toNat + used = l.have_.toNat ∧
      regs.put = l.put ∧ regs.left = l.left ∧ regs.out_ = l.out_ ∧ regs.bits.toNat ≤ 39 ∧
      after.static = h.static ∧ LocalHbuf c after ∧ HbufApart c after state.head ∧
      GzipHeaderStateFrame s state ∧ HeaderStreamFrame z stream ∧
      GzipHeaderFootprint c r zs s h after ∧ HeaderMemory after r state.head true ∧
      RegionsKept (HeaderRegions after state.head) (HeaderRegions h s.head) ∧
      (state.mode = EXTRA → ∀ i g, state.head = some (.tab i) → after.gzheaders i = some g →
        state.length ≤ g.extra_len) ∧
      ((FLAGS ≤ state.mode ∧ state.mode ≤ HCRC) ∨ state.mode = TYPE ∨ state.mode = BAD) ∧
      (state.mode ≠ BAD → state.mode ≠ FLAGS → state.flags ≠ -1 ∧ state.flags ≠ 0) ∧
      (outcome = .error Ex.leave ∨
        (outcome = .ok () ∧ dispatchRank regs state.mode < dispatchRank l s.mode)) := by
  let e : GzEntry := ⟨c, r, zs, h, z, s, l, bs⟩
  have valid : e.Valid := ⟨E, good, buffers, hbuf, apart, record, globals, extraApart, incoming⟩
  obtain ⟨outcome, regs, after, run, stream, state, used, inv, ends, flagsAfter, lenAfter⟩ :=
    gz_dispatch (e := e) valid mode flags extraLen
  obtain ⟨rest, len, bits⟩ := inv.bits
  obtain ⟨b, a, ptr, get, size, ro, _, _⟩ := inv.hbuf valid
  have modes : (FLAGS ≤ state.mode ∧ state.mode ≤ HCRC) ∨ state.mode = TYPE ∨ state.mode = BAD := by
    rcases ends with ⟨_, range⟩ | ⟨_, final⟩
    · exact Or.inl range
    · exact Or.inr final
  have pendingAfter : DataPendingInvariant state := by
    have sane : state.sane = 1 := by rw [inv.state]; exact pending.sane
    apply dataPendingInvariant_idle sane
    rcases modes with ⟨lo, hi⟩ | m | m
    · have hi' := UInt32.le_iff_toNat_le.mp hi
      have hiN : HCRC.toNat = 16188 := rfl
      refine ⟨?_, ?_, ?_, ?_⟩ <;> intro eq <;> rw [eq] at hi' <;> revert hi' <;> decide
    · rw [m]; decide
    · rw [m]; decide
  refine ⟨outcome, regs, after, stream, state, used, inv.usedLe, run, inv.good, pendingAfter,
    ⟨rest, len, DispatchBuffers.of_entry buffers good inv.good inv.window inv.sizes inv.readonly
      inv.next inv.count inv.put inv.left inv.out bits⟩,
    inv.sizes, inv.next, inv.count, inv.put, inv.left, inv.out, inv.bound, inv.static,
    ⟨b, a, ptr, get, size, ro⟩, ?_, inv.state, inv.stream, ⟨inv.foot.bufferFrame, inv.foot.live⟩,
    ?_, ?_, lenAfter, modes, flagsAfter, ?_⟩
  · rw [inv.head]; exact (inv.head ▸ inv.hbufApart valid)
  · rw [inv.head]; exact (inv.head ▸ inv.headerMemory valid)
  · rw [inv.head]; exact (inv.head ▸ inv.regionsKept valid)
  · rcases ends with ⟨leave, _⟩ | ⟨ok, final⟩
    · exact Or.inl leave
    · refine Or.inr ⟨ok, ?_⟩
      have credit : dispatchCredit state.mode ≤ 8 := by
        rcases final with m | m <;> rw [m] <;> decide
      have start : dispatchCredit s.mode = 61 := dispatchCredit_gzip_header mode
      have mass : regs.bits.toNat ≤ l.bits.toNat + 8 * used := inv.mass
      have count : regs.have_.toNat + used = l.have_.toNat := inv.count
      have left : regs.left = l.left := inv.left
      unfold dispatchRank dispatchMass
      rw [start, left]
      omega

end Zlib.Inflate.Proofs
