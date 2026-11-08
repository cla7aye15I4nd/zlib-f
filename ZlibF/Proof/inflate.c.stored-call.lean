import ZlibF.Proof.«inflate.c.main.stored2»
import ZlibF.Proof.«inflate.c.main.check0»
import ZlibF.Proof.«inflate.c.sync3»
import ZlibF.Proof.«inflate.c.ring»

/-!
# inflate.c: complete raw stored-block calls

Execution lemmas connect the actual dispatch loop and exit to the stored-copy
proof. The restricted raw-stream domain is explicit in each statement.
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec

set_option maxRecDepth 100000

/-- `case CHECK:` in a raw stream skips checksum computation and reaches LENGTH. -/
theorem inflate_CHECK_raw_skip {c : Ctx} {l : IL} {h : Heap} {zs : Nat} {s : InflateState}
    (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s) (hw : s.wrap = 0) :
    runX (inflate_CHECK c) l h = runX (inflate_LENGTH c) l (setI h zs { s with mode := LENGTH }) := by
  unfold inflate_CHECK
  rw [hc]
  simp [runX_bind, runX_lift, ldI_eq, hs, hw, setMode, wrI_eq, runX_pure]

/-- `case LENGTH:` in a raw stream reaches the actual DONE exit directly. -/
theorem inflate_LENGTH_raw_skip {c : Ctx} {l : IL} {h : Heap} {zs : Nat} {s : InflateState}
    (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s) (hw : s.wrap = 0) :
    runX (inflate_LENGTH c) l h =
      .ok ((.error Ex.leave, { l with ret := Z_STREAM_END }), setI h zs { s with mode := DONE }) := by
  unfold inflate_LENGTH
  rw [hc]
  simp [runX_bind, runX_lift, ldI_eq, hs, hw, runX_pure, setMode, wrI_eq,
    inflate_DONE, runX_modify, runX_throw]

/-- A finite sequence of actual mode executions, ending in an exception,
executes within the translated dispatch loop's fuel. -/
theorem xwhile_run_chain (body : X Unit) (locals : Nat → IL) (heaps : Nat → Heap)
    (n : Nat) (hn : n + 1 < fuel) (e : Ex) (final : IL) (after : Heap)
    (steps : ∀ j, j < n → runX body (locals j) (heaps j) =
      .ok ((.ok (), locals (j + 1)), heaps (j + 1)))
    (stop : runX body (locals n) (heaps n) = .ok ((.error e, final), after)) :
    runX (xwhile (pure true) body) (locals 0) (heaps 0) = .ok ((.error e, final), after) := by
  let P : Nat → IL → Heap → Prop := fun k l h =>
    ∃ j, j ≤ n ∧ k = n + 1 - j ∧ l = locals j ∧ h = heaps j
  let Q : Except Ex Unit → IL → Heap → Prop := fun result l h =>
    result = .error e ∧ l = final ∧ h = after
  have step : ∀ k l h, P (k + 1) l h → ∃ l1 h1,
      runX (pure true : X Bool) l h = .ok ((.ok true, l1), h1) ∧
      ∃ result l2 h2, runX (do body; pure false) l1 h1 = .ok ((result, l2), h2) ∧
        (match result with
        | .ok true => Q (.ok ()) l2 h2
        | .ok false => P k l2 h2
        | .error ex => Q (.error ex) l2 h2) := by
    rintro k l h ⟨j, hj, hk, rfl, rfl⟩
    refine ⟨locals j, heaps j, rfl, ?_⟩
    by_cases he : j = n
    · subst j
      exact ⟨.error e, final, after, by rw [runX_bind, stop], rfl, rfl, rfl⟩
    · have hjn : j < n := by omega
      refine ⟨.ok false, locals (j + 1), heaps (j + 1), ?_, j + 1, by omega, by omega, rfl, rfl⟩
      rw [runX_bind, steps j hjn]
      rfl
  obtain ⟨result, l, h, run, hQ⟩ := xwhileBrk_run P Q step
    (by rintro l h ⟨j, hj, hk, _, _⟩; omega)
    (k := n + 1) (l := locals 0) (h := heaps 0) ⟨0, by omega, by omega, rfl, rfl⟩ hn
  obtain ⟨rfl, rfl, rfl⟩ := hQ
  exact run

/-- `int inflate(z_streamp strm, int flush)`.
The raw finished exit with Z_FINISH needs no window allocation. It writes the actual
cursors, wrapping totals and terminal data-type flag before returning. -/
theorem inflate_leave_raw_finish_done {c : Ctx} {h : Heap} {r zs z s}
    (E : Env c h r zs z s) (l : IL) (hm : s.mode = DONE)
    (hf : c.flush = Z_FINISH)
    (hw : s.wrap = 0) (hws : s.wsize = 0) (hlast : s.last ≠ 0)
    (hb : l.bits = 0) (hh : l.hold = 0) (hr : l.ret = Z_STREAM_END) :
    inflate_leave c l h = .ok (Z_STREAM_END,
      setI (r.put h { z with
        next_out := l.put, avail_out := l.left,
        next_in := l.next, avail_in := l.have_,
        total_in := z.total_in + (l.in_ - l.have_).toUInt64,
        total_out := z.total_out + (l.out_ - l.left).toUInt64, data_type := 64 }) zs
        { s with hold := 0, bits := 0, total := s.total + (l.out_ - l.left).toUInt64 }) := by
  unfold inflate_leave
  rw [E.strm, E.st]
  isimp [E.hz, E.hs, hm, hf, hw, hws, hlast, hb, hh, hr, DONE, CHECK, BAD, TYPE, LEN_, COPY_, Z_STREAM_END, Z_OK,
    ZStreamRef.get_put_same E.hz, ZStreamRef.put_put, ZStreamRef.put_setI, setI_setI,
    chkI32, u2i]

/-- `int inflate(z_streamp strm, int flush)`.
Starting at COPY in the final raw block, sufficient input and output complete
the actual dispatch loop. The copied bytes and all returned registers are exact.
This is an internal continuation result, not the unrestricted public target. -/
theorem inflate_raw_copy_loop {c : Ctx} {h : Heap} {r zs z s}
    (E : Env c h r zs z s) (l : IL) (hm : s.mode = COPY)
    (hf : c.flush = Z_FINISH) (hw : s.wrap = 0) (hlast : s.last ≠ 0)
    (hb : l.bits = 0) (hh : l.hold = 0) (hn : s.length ≠ 0)
    (hin : s.length.toNat ≤ l.have_.toNat) (hout : s.length.toNat ≤ l.left.toNat)
    {rs : BRef} {os db od : Nat} {da sa : Array UInt8}
    (hput : l.put = .ref (.blk db) od) (hnext : l.next = .ref rs os)
    (hd : h.bytes db = some da) (hsrc : (Space.get h rs : Option (Array UInt8)) = some sa)
    (hro : Space.ro h (BRef.blk db) = false)
    (h1 : od + s.length.toNat ≤ da.size) (h2 : os + s.length.toNat ≤ sa.size)
    (hdis : BRef.blk db ≠ rs ∨ od + s.length.toNat ≤ os ∨ os + s.length.toNat ≤ od) :
    runX (xwhile (pure true) (inflate_dispatch c)) l h =
      .ok ((.error Ex.leave,
        { copyRegs l s.length (.ref rs (os + s.length.toNat)) (.ref (.blk db) (od + s.length.toNat)) with
          copy := 0, ret := Z_STREAM_END }),
        setI { h with bytes := upd h.bytes db (some (copyRange da sa od os s.length.toNat)) }
          zs { s with length := 0, mode := DONE }) := by
  let base := { h with bytes := upd h.bytes db (some (copyRange da sa od os s.length.toNat)) }
  let l1 := copyRegs l s.length (.ref rs (os + s.length.toNat)) (.ref (.blk db) (od + s.length.toNat))
  let l2 := { l1 with copy := 0 }
  let s1 := { s with length := 0 }
  let s2 := { s1 with mode := TYPE }
  let s3 := { s1 with mode := CHECK }
  have hzbase : r.get base = some z := by cases r <;> exact E.hz
  have E1 : Env c (setI base zs s1) r zs z s1 :=
    ⟨E.strm, E.st, by simpa only [ZStreamRef.get_setI] using hzbase, by simp⟩
  have E2 : Env c (setI base zs s2) r zs z s2 :=
    ⟨E.strm, E.st, by simpa only [ZStreamRef.get_setI] using hzbase, by simp⟩
  have E3 : Env c (setI base zs s3) r zs z s3 :=
    ⟨E.strm, E.st, by simpa only [ZStreamRef.get_setI] using hzbase, by simp⟩
  have hamt : copyAmt s.length l.have_ l.left = s.length := by
    unfold copyAmt
    simp only [gt_iff_lt, UInt32.lt_iff_toNat_lt, show ¬ l.have_.toNat < s.length.toNat by omega,
      show ¬ l.left.toNat < s.length.toNat by omega, ite_false]
  have step0 : runX (inflate_dispatch c) l h = .ok ((.ok (), l1), setI base zs s1) := by
    unfold inflate_dispatch
    rw [runX_bind, runX_rdS E]
    simp only [hm]
    change runX (inflate_COPY c) l h = _
    simpa only [hamt, UInt32.sub_self] using
      inflate_COPY_run E l hn (by simpa only [hamt] using hn) hput hnext hd hsrc hro
        (by simpa only [hamt] using h1) (by simpa only [hamt] using h2) (by simpa only [hamt] using hdis)
  have step1 : runX (inflate_dispatch c) l1 (setI base zs s1) = .ok ((.ok (), l2), setI base zs s2) := by
    unfold inflate_dispatch
    rw [runX_bind, runX_rdS E1]
    simp only [show s1.mode = COPY from hm]
    change runX (inflate_COPY c) l1 (setI base zs s1) = _
    simpa only [setI_setI] using inflate_COPY_done E1 l1 rfl
  have step2 : runX (inflate_dispatch c) l2 (setI base zs s2) = .ok ((.ok (), l2), setI base zs s3) := by
    unfold inflate_dispatch
    rw [runX_bind, runX_rdS E2]
    change runX (inflate_TYPE c) l2 (setI base zs s2) = _
    rw [inflate_TYPE_go c l2 _ (by simp [hf, Z_FINISH, Z_BLOCK, Z_TREES])]
    have run := inflate_TYPEDO_last E2 l2 (by simpa [s2, s1] using hlast)
    simpa [bytebits, l2, l1, copyRegs, hb, hh, s3, s2, s1, setI_setI] using run
  have stop : runX (inflate_dispatch c) l2 (setI base zs s3) =
      .ok ((.error Ex.leave, { l2 with ret := Z_STREAM_END }), setI base zs { s with length := 0, mode := DONE }) := by
    unfold inflate_dispatch
    rw [runX_bind, runX_rdS E3]
    change runX (inflate_CHECK c) l2 (setI base zs s3) = _
    rw [inflate_CHECK_raw_skip (s := s3) E.st E3.hs (by simpa [s3, s1] using hw)]
    rw [inflate_LENGTH_raw_skip (s := { s3 with mode := LENGTH }) E.st (by simp)
      (by simpa [s3, s1] using hw)]
    simp [s3, s1, setI_setI]
  let locals : Nat → IL := fun j => if j = 0 then l else if j = 1 then l1 else l2
  let heaps : Nat → Heap := fun j => if j = 0 then h else if j = 1 then setI base zs s1
    else if j = 2 then setI base zs s2 else setI base zs s3
  have steps : ∀ j, j < 3 → runX (inflate_dispatch c) (locals j) (heaps j) =
      .ok ((.ok (), locals (j + 1)), heaps (j + 1)) := by
    intro j hj
    have cases : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases cases with rfl | rfl | rfl
    · exact step0
    · exact step1
    · exact step2
  exact xwhile_run_chain (inflate_dispatch c) locals heaps 3 (by decide) Ex.leave _ _ steps stop

/-- `int inflate(z_streamp strm, int flush)`.
LOAD copies the actual boundary fields into the local registers. -/
theorem LOAD_run {c : Ctx} {h : Heap} {r zs z s}
    (E : Env c h r zs z s) (l : IL) :
    runX (LOAD c.strm c.st) l h = .ok ((.ok (),
      { l with
        put := z.next_out, left := z.avail_out, next := z.next_in,
        have_ := z.avail_in, hold := s.hold, bits := s.bits }), h) := by
  unfold LOAD
  have hz : ldZStream c.strm h = .ok (z, h) := by rw [E.strm]; exact ldZStream_ok E.hz
  rw [runX_bind, runX_lift_ok hz]
  simp only []
  rw [runX_bind, runX_ldS E]
  rfl

/-- `int inflate(z_streamp strm, int flush)`.
The full LOAD and dispatch computation for the final raw stored copy.
No result about a previous call is assumed. -/
theorem inflate_run_raw_copy {c : Ctx} {h : Heap} {r zs z s}
    (E : Env c h r zs z s) (hm : s.mode = COPY)
    (hf : c.flush = Z_FINISH) (hw : s.wrap = 0) (hlast : s.last ≠ 0)
    (hb : s.bits = 0) (hh : s.hold = 0) (hn : s.length ≠ 0)
    (hin : s.length.toNat ≤ z.avail_in.toNat) (hout : s.length.toNat ≤ z.avail_out.toNat)
    {rs : BRef} {os db od : Nat} {da sa : Array UInt8}
    (hput : z.next_out = .ref (.blk db) od) (hnext : z.next_in = .ref rs os)
    (hd : h.bytes db = some da) (hsrc : (Space.get h rs : Option (Array UInt8)) = some sa)
    (hro : Space.ro h (BRef.blk db) = false)
    (h1 : od + s.length.toNat ≤ da.size) (h2 : os + s.length.toNat ≤ sa.size)
    (hdis : BRef.blk db ≠ rs ∨ od + s.length.toNat ≤ os ∨ os + s.length.toNat ≤ od) :
    let l : IL := { IL.init with
      put := z.next_out, left := z.avail_out, next := z.next_in, have_ := z.avail_in,
      hold := s.hold, bits := s.bits, in_ := z.avail_in, out_ := z.avail_out, ret := Z_OK }
    runX (inflate_run c) IL.init h =
      .ok ((.error Ex.leave,
        { copyRegs l s.length (.ref rs (os + s.length.toNat)) (.ref (.blk db) (od + s.length.toNat)) with
          copy := 0, ret := Z_STREAM_END }),
        setI { h with bytes := upd h.bytes db (some (copyRange da sa od os s.length.toNat)) }
          zs { s with length := 0, mode := DONE }) := by
  dsimp only
  unfold inflate_run
  rw [runX_bind, runX_rdS E]
  simp only [hm]
  change runX (do
    LOAD c.strm c.st
    modify fun l => { l with in_ := l.have_, out_ := l.left, ret := Z_OK }
    xwhile (pure true) (inflate_dispatch c)) IL.init h = _
  rw [runX_bind, LOAD_run E]
  simp only []
  rw [runX_bind, runX_modify]
  exact inflate_raw_copy_loop E _ hm hf hw hlast hb hh hn hin hout hput hnext hd hsrc hro h1 h2 hdis

/-- Cancellation for the actual unsigned remaining-byte counters. -/
theorem u32_used_of_remaining (a b : UInt32) (hle : b.toNat ≤ a.toNat) : a - (a - b) = b := by
  have hab : (a - b).toNat = a.toNat - b.toNat :=
    UInt32.toNat_sub_of_le a b (UInt32.le_iff_toNat_le.mpr hle)
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_sub_of_le a (a - b) (UInt32.le_iff_toNat_le.mpr (by rw [hab]; omega)), hab]
  omega

/-- `int inflate(z_streamp strm, int flush)`.
The actual public call at Z_FINISH completes a nonempty final raw stored copy.
Input/output ranges are readable/writable and nonoverlapping, the final block
is already in COPY, and no history window is in use. This internal domain does
not replace Goal.inflate. The result includes allocation and freeing of the
automatic header array, with no allocator-oracle assumption. -/
theorem inflate_raw_copy_finish_run {h : Heap} {r zs z s}
    (G : Good h r zs z s) (hm : s.mode = COPY) (hw : s.wrap = 0)
    (hws : s.wsize = 0) (hlast : s.last ≠ 0) (hb : s.bits = 0) (hh : s.hold = 0)
    (hn : s.length ≠ 0) (hin : s.length.toNat ≤ z.avail_in.toNat) (hout : s.length.toNat ≤ z.avail_out.toNat)
    {rs : BRef} {os db od : Nat} {da sa : Array UInt8}
    (hput : z.next_out = .ref (.blk db) od) (hnext : z.next_in = .ref rs os)
    (hd : h.bytes db = some da) (hsrc : (Space.get h rs : Option (Array UInt8)) = some sa)
    (hro : Space.ro h (BRef.blk db) = false)
    (h1 : od + s.length.toNat ≤ da.size) (h2 : os + s.length.toNat ≤ sa.size)
    (hdis : BRef.blk db ≠ rs ∨ od + s.length.toNat ≤ os ∨ os + s.length.toNat ≤ od) :
    let z' := { z with
      next_in := .ref rs (os + s.length.toNat), avail_in := z.avail_in - s.length,
      next_out := .ref (.blk db) (od + s.length.toNat), avail_out := z.avail_out - s.length,
      total_in := z.total_in + s.length.toUInt64, total_out := z.total_out + s.length.toUInt64, data_type := 64 }
    let s' := { s with length := 0, mode := DONE, hold := 0, bits := 0, total := s.total + s.length.toUInt64 }
    C.run (inflate (some r) Z_FINISH) h = .ok (Z_STREAM_END,
      freeWin (setI (r.put { syncAlloc h with
        bytes := upd (syncAlloc h).bytes db (some (copyRange da sa od os s.length.toNat)) } z') zs s') (syncBuf h)) := by
  dsimp only
  have GA := good_syncAlloc G
  have hdb : db ≠ h.nextBlk := by
    intro he
    have hf := (fresh_dead G.fresh (Nat.le_refl _)).1
    rw [← he, hd] at hf
    cases hf
  have hdA : (syncAlloc h).bytes db = some da := by rw [syncAlloc_bytes_ne h hdb]; exact hd
  have hsrcA : (Space.get (syncAlloc h) rs : Option (Array UInt8)) = some sa := by
    cases rs with
    | blk b =>
      have hbne : b ≠ h.nextBlk := by
        intro he
        have hf := (fresh_dead G.fresh (Nat.le_refl _)).1
        change h.bytes b = some sa at hsrc
        rw [← he, hsrc] at hf
        cases hf
      exact (syncAlloc_bytes_ne h hbne).trans hsrc
    | _ => exact hsrc
  have hroA : Space.ro (syncAlloc h) (BRef.blk db) = false := by
    simpa [Space.ro, syncAlloc, upd_ne _ _ _ _ hdb] using hro
  let c : Ctx := ⟨some r, some (.tab zs), syncBuf h, Z_FINISH⟩
  have E : Env c (syncAlloc h) r zs z s := ⟨rfl, rfl, GA.live.hz, GA.live.hs⟩
  let l : IL := { IL.init with
    put := z.next_out, left := z.avail_out, next := z.next_in, have_ := z.avail_in,
    hold := s.hold, bits := s.bits, in_ := z.avail_in, out_ := z.avail_out, ret := Z_OK }
  let final := { copyRegs l s.length (.ref rs (os + s.length.toNat)) (.ref (.blk db) (od + s.length.toNat)) with
    copy := 0, ret := Z_STREAM_END }
  let copied := { syncAlloc h with
    bytes := upd (syncAlloc h).bytes db (some (copyRange da sa od os s.length.toNat)) }
  let state := { s with length := 0, mode := DONE }
  have run : runX (inflate_run c) IL.init (syncAlloc h) =
      .ok ((.error Ex.leave, final), setI copied zs state) :=
    inflate_run_raw_copy E hm rfl hw hlast hb hh hn hin hout hput hnext hdA hsrcA hroA h1 h2 hdis
  have hzcopy : r.get copied = some z := by cases r <;> exact GA.live.hz
  have EE : Env c (setI copied zs state) r zs z state :=
    ⟨rfl, rfl, by simpa only [ZStreamRef.get_setI] using hzcopy, by simp⟩
  have leave := inflate_leave_raw_finish_done EE final rfl rfl hw hws hlast hb hh rfl
  have htmp : (setI (r.put copied { z with
      next_in := .ref rs (os + s.length.toNat), avail_in := z.avail_in - s.length,
      next_out := .ref (.blk db) (od + s.length.toNat), avail_out := z.avail_out - s.length,
      total_in := z.total_in + s.length.toUInt64, total_out := z.total_out + s.length.toUInt64,
      data_type := 64 }) zs { s with
        length := 0, mode := DONE, hold := 0, bits := 0,
        total := s.total + s.length.toUInt64 }).bytes h.nextBlk = some (syncJunk h) := by
    simp [copied, upd_ne _ _ _ _ (Ne.symm hdb), syncAlloc_bytes_buf]
  have htmpro : (setI (r.put copied { z with
      next_in := .ref rs (os + s.length.toNat), avail_in := z.avail_in - s.length,
      next_out := .ref (.blk db) (od + s.length.toNat), avail_out := z.avail_out - s.length,
      total_in := z.total_in + s.length.toUInt64, total_out := z.total_out + s.length.toUInt64,
      data_type := 64 }) zs { s with
        length := 0, mode := DONE, hold := 0, bits := 0,
        total := s.total + s.length.toUInt64 }).ro h.nextBlk = false := by simp [copied, syncAlloc]
  unfold C.run inflate
  rw [bind_app, allocLocalB_run h G.fresh]
  simp only []
  rw [bind_app]
  have hnout : z.next_out ≠ .null := by rw [hput]; simp
  have hnin : z.next_in ≠ .null := by rw [hnext]; simp
  have hobuf : (z.next_out == .null) = false := by simp [hput]
  have hibuf : (z.next_in == .null) = false := by simp [hnext]
  simp only [bind_app, stateCheck_live GA.live, bne_self_eq_false, Bool.false_eq_true, ite_false,
    ldZStream_ok GA.live.hz, hobuf, hibuf, Bool.false_and, Bool.false_or, GA.live.zst, castI]
  unfold runX at run
  rw [run]
  simp only []
  rw [leave]
  simp only [final, l, copyRegs, u32_used_of_remaining _ _ hin, u32_used_of_remaining _ _ hout,
    ZStreamRef.put_setI, setI_setI]
  erw [freeBuf_run htmp htmpro]
  simp only [pure_app, GA.live.zst]
  rfl

/-- `int inflate(z_streamp strm, int flush)`.
For a nonempty final raw stored copy with no saved window and enough separated
input/output storage, the public call returns STREAM_END, preserves Good,
copies exactly the input bytes, accounts for both wrapping totals, and leaves
the live allocation set unchanged. The COPY-entry restriction is internal. -/
theorem inflate_raw_copy_finish_safe {h : Heap} {r zs z s}
    (G : Good h r zs z s) (hm : s.mode = COPY) (hw : s.wrap = 0)
    (hwindow : s.window = .null) (hlast : s.last ≠ 0) (hb : s.bits = 0) (hh : s.hold = 0)
    (hn : s.length ≠ 0) (hin : s.length.toNat ≤ z.avail_in.toNat) (hout : s.length.toNat ≤ z.avail_out.toNat)
    {rs : BRef} {os db od : Nat} {da sa : Array UInt8}
    (hput : z.next_out = .ref (.blk db) od) (hnext : z.next_in = .ref rs os)
    (hd : h.bytes db = some da) (hsrc : (Space.get h rs : Option (Array UInt8)) = some sa)
    (hro : Space.ro h (BRef.blk db) = false)
    (h1 : od + s.length.toNat ≤ da.size) (h2 : os + s.length.toNat ≤ sa.size)
    (hdis : BRef.blk db ≠ rs ∨ od + s.length.toNat ≤ os ∨ os + s.length.toNat ≤ od) :
    ∃ after z' s' output,
      C.run (inflate (some r) Z_FINISH) h = .ok (Z_STREAM_END, after) ∧
      Good after r zs z' s' ∧ s'.mode = DONE ∧ s'.length = 0 ∧ s'.window = .null ∧
      z'.next_in = .ref rs (os + s.length.toNat) ∧ z'.avail_in = z.avail_in - s.length ∧
      z'.next_out = .ref (.blk db) (od + s.length.toNat) ∧ z'.avail_out = z.avail_out - s.length ∧
      z'.total_in = z.total_in + s.length.toUInt64 ∧ z'.total_out = z.total_out + s.length.toUInt64 ∧
      after.nalloc = h.nalloc ∧ (∀ b, after.live b ↔ h.live b) ∧
      after.bytes db = some output ∧ output.size = da.size ∧
      (∀ j, j < s.length.toNat → output[od + j]? = sa[os + j]?) ∧
      (∀ j, j < od ∨ od + s.length.toNat ≤ j → output[j]? = da[j]?) := by
  let output := copyRange da sa od os s.length.toNat
  let copied := { syncAlloc h with bytes := upd (syncAlloc h).bytes db (some output) }
  let z' := { z with
    next_in := .ref rs (os + s.length.toNat), avail_in := z.avail_in - s.length,
    next_out := .ref (.blk db) (od + s.length.toNat), avail_out := z.avail_out - s.length,
    total_in := z.total_in + s.length.toUInt64, total_out := z.total_out + s.length.toUInt64, data_type := 64 }
  let s' := { s with length := 0, mode := DONE, hold := 0, bits := 0, total := s.total + s.length.toUInt64 }
  let mid := setI (r.put copied z') zs s'
  let after := freeWin mid (syncBuf h)
  have GA := good_syncAlloc G
  have hdb : db ≠ h.nextBlk := by
    intro he
    have hf := (fresh_dead G.fresh (Nat.le_refl _)).1
    rw [← he, hd] at hf
    cases hf
  have hdA : (syncAlloc h).bytes db = some da := (syncAlloc_bytes_ne h hdb).trans hd
  have SC : Shape (syncAlloc h) copied := shape_setB hdA output
  have hzC : r.get copied = some z := by cases r <;> exact GA.live.hz
  have GC : Good copied r zs z s := by
    refine ⟨⟨hzC, GA.live.hs, GA.live.zst, GA.live.back, GA.live.mode, GA.live.zalloc, GA.live.zfree⟩,
      ⟨GA.inv.wf, ?_, GA.inv.reqbits, GA.inv.bits, GA.inv.ptr⟩,
      SC.uniq GA.uniq, SC.fresh rfl GA.fresh⟩
    exact ⟨GA.inv.win.wbits, Or.inl hwindow, GA.inv.win.nullws, GA.inv.win.ws,
      GA.inv.win.hv, GA.inv.win.wn, GA.inv.win.eq⟩
  have GM : Good mid r zs z' s' := GC.setZI rfl GC.live.zalloc GC.live.zfree rfl
    (by change HEAD ≤ DONE ∧ DONE ≤ SYNC; constructor <;> decide)
    (GC.inv.of_fields rfl rfl rfl rfl rfl rfl rfl rfl rfl
      (by change (0 : UInt32).toNat ≤ 39; decide) rfl rfl rfl)
  have GF : Good after r zs z' s' := good_freeBuf GM (by intro w he; simp [s', hwindow] at he)
  have SM : Shape (syncAlloc h) mid := SC.trans
    ((shape_put hzC z').trans (shape_setI (by simpa using GC.live.hs) s'))
  have htmp : mid.bytes h.nextBlk = some (syncJunk h) := by
    simp [mid, copied, upd_ne _ _ _ _ (Ne.symm hdb), syncAlloc_bytes_buf]
  have ownM : mid.Owns (fun b => h.live b ∨ b = h.nextBlk) := fun b =>
    (SM.live b).trans (live_syncAlloc b)
  have ownF := owns_freeWin GM.uniq htmp ownM
  have live : ∀ b, after.live b ↔ h.live b := by
    intro b
    change (freeWin mid (.ref (.blk h.nextBlk) 0)).live b ↔ h.live b
    rw [ownF b]
    have hf : h.live b → b ≠ h.nextBlk := by
      intro hl he
      subst b
      exact G.fresh h.nextBlk (Nat.le_refl _) hl
    constructor
    · rintro ⟨hb | rfl, hn⟩
      · exact hb
      · exact (hn rfl).elim
    · intro hl
      exact ⟨Or.inl hl, hf hl⟩
  have houtarray : after.bytes db = some output := by
    simp [after, mid, copied, freeWin, syncBuf, upd_ne _ _ _ _ hdb]
  refine ⟨after, z', s', output,
    inflate_raw_copy_finish_run G hm hw (G.inv.win.nullws hwindow) hlast hb hh hn hin hout
      hput hnext hd hsrc hro h1 h2 hdis,
    GF, rfl, rfl, hwindow, rfl, rfl, rfl, rfl, rfl, rfl, ?_, live, houtarray,
    size_copyRange .., ?_, ?_⟩
  · change (r.put copied z').nalloc = h.nalloc
    rw [ZStreamRef.put_nalloc]
    rfl
  · intro j hj
    rw [copyRange_getElem? da sa od os s.length.toNat h1 h2]
    simp [show od ≤ od + j ∧ od + j < od + s.length.toNat by omega]
  · intro j hj
    rw [copyRange_getElem? da sa od os s.length.toNat h1 h2]
    rw [if_neg (by omega)]

end Zlib.Inflate.Proofs
