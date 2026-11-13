import ZlibF.Proof.«gzread.c.load-errno»
import ZlibF.Proof.«gzlib.c.error-keeps-x»

/-!
# gzread.c: `gz_fetch` in `COPY` mode sets `x.next` before it loads (upstream PR 1363)

With the patch, `case COPY` writes `x.next = out` and then calls `gz_load`. So whatever `gz_load`
returns, `x.next` is the start of the bytes it counted in `x.have`. Here: a refused first read on
the regular branch of the read oracle returns `-1` with `x.have = 0` and `x.next = out`. Under the
unpatched order `x.next` keeps its old value on this path; this theorem is false for it.
-/

namespace Zlib.Gzread.FetchCopy
open C Zlib.Gzguts Zlib.GzFs Zlib.Gzlib Zlib.Gzread
open Zlib.Gzlib.Spec Zlib.Gzlib.Proofs Zlib.Gzlib.ErrnoLifetime Zlib.Gzread.LoadErrno Zlib.Gzlib.KeepsX
set_option autoImplicit false

private theorem g_bind_app {α β : Type} (m : G α) (f : α → G β) (fs : Fs) (h : Heap) :
    (m >>= f) fs h = match m fs h with
      | .ok ((a, fs1), h1) => f a fs1 h1 | .error e => .error e := by
  simp only [bind, StateT.bind]
  cases he : m fs h with
  | error e => rfl
  | ok result => obtain ⟨⟨a, fs1⟩, h1⟩ := result; rfl

private theorem g_lift_app {α : Type} (m : M α) (fs : Fs) (h : Heap) :
    (StateT.lift m : G α) fs h = match m h with
      | .ok (a, h1) => .ok ((a, fs), h1) | .error e => .error e := rfl

private theorem g_pure_app {α : Type} (a : α) (fs : Fs) (h : Heap) :
    (pure a : G α) fs h = .ok ((a, fs), h) := rfl

/-- `gz_room` (patch 0004) reads the record and returns a count; it changes nothing. -/
theorem gz_room_run (h : Heap) (i : Nat) (s : GzState) (hs : h.gzstates i = some s) (m : UInt32) :
    ∃ room, gz_room (some (.tab i)) m h = .ok (room, h) := by
  unfold gz_room
  simp only [bind_app, ldS_eq, hs]
  split
  · rename_i pos
    have hp : 0 < s.x.pos.toInt := by
      have := Int64.lt_iff_toInt_lt.mp pos
      simpa using this
    have hb := s.x.pos.toInt_lt
    have hmax : GZ_OFF_MAX.toInt = 9223372036854775807 := by decide
    rw [bind_app, i64sub_run _ _ (by rw [hmax]; omega) (by rw [hmax]; omega)]
    dsimp only
    split
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

theorem fetch_copy_refusal_next (h : Heap) (fs : Fs) (i : Nat) (s : GzState) (r : BRef)
    (a : Array UInt8) (e : Int32)
    (hs : h.gzstates i = some s) (how : s.how = GZ_COPY) (err : s.err = Z_OK)
    (out : s.out = .ref r 0) (ha : Space.get h r = some a)
    (hc : fs.readChoice fs.nos = .regular) (he : ReadRefusal s.fd fs e)
    {res : Int32} {fs' : Fs} {after : Heap}
    (run : gz_fetch (some (.tab i)) fs h = .ok ((res, fs'), after)) :
    res = -1 ∧ ∃ s', after.gzstates i = some s' ∧ s'.x.next = s.out ∧ s'.x.«have» = 0 := by
  obtain ⟨room, hroom⟩ := gz_room_run h i s hs (s.size <<< 1)
  have hs1 : (setS h i { s with x := { «have» := s.x.«have», next := s.out, pos := s.x.pos } }).gzstates i =
      some { s with x := { «have» := s.x.«have», next := s.out, pos := s.x.pos } } := setS_gz_same _ _ _
  have ha1 : Space.get (setS h i { s with x := { «have» := s.x.«have», next := s.out, pos := s.x.pos } }) r = some a := by
    have : Space.get (setS h i { s with x := { «have» := s.x.«have», next := s.out, pos := s.x.pos } }) r = Space.get h r := by
      cases r <;> rfl
    rw [this, ha]
  have load : gz_load (some (.tab i)) s.out (if room != 0 then room else 1) fs
      (setS h i { s with x := { «have» := s.x.«have», next := s.out, pos := s.x.pos } }) =
      loadReport i { tickW fs with errno := e } (loadPrefixHeap (setS h i { s with x := { «have» := s.x.«have», next := s.out, pos := s.x.pos } }) i { s with x := { «have» := s.x.«have», next := s.out, pos := s.x.pos } }) := by
    have := gz_load_refusal_source _ fs i _ r 0 a (if room != 0 then room else 1) e hs1 ha1 (Nat.zero_le _) hc he
    rwa [← out] at this
  rw [load_report_source] at load
  -- the record that `gz_error` starts from
  have hs2 : (errnoHeap (loadPrefixHeap (setS h i { s with x := { «have» := s.x.«have», next := s.out, pos := s.x.pos } }) i
      { s with x := { «have» := s.x.«have», next := s.out, pos := s.x.pos } }) { tickW fs with errno := e }).gzstates i =
      some { s with x := { «have» := s.x.«have», next := s.out, pos := s.x.pos }, again := 0 } := by
    simp [errnoHeap, loadPrefixHeap]
  have hlook : (s.how == LOOK) = false := by rw [how]; decide
  have hcopy : (s.how == GZ_COPY) = true := by rw [how]; decide
  have hz : (Z_OK != Z_OK) = false := by decide
  unfold gz_fetch at run
  simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, g_bind_app, g_lift_app,
    g_pure_app, ldS_eq, hs, err, hz, Bool.false_and, Bool.false_eq_true, ite_false] at run
  unfold gdoWhile at run
  rw [show fuel = 18446744073709551615 + 1 by rfl, gdoWhile.go] at run
  simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, g_bind_app, g_lift_app,
    g_pure_app, ldS_eq, updX, updS_eq, hs, hlook, hcopy, hroom, setS_gz_same, Bool.false_eq_true,
    ite_false, ite_true] at run
  rw [load] at run
  cases hg : gz_error (some (.tab i)) Z_ERRNO
      (errnoPointer (loadPrefixHeap (setS h i { s with x := { «have» := s.x.«have», next := s.out, pos := s.x.pos } }) i
        { s with x := { «have» := s.x.«have», next := s.out, pos := s.x.pos } }) { tickW fs with errno := e })
      (errnoHeap (loadPrefixHeap (setS h i { s with x := { «have» := s.x.«have», next := s.out, pos := s.x.pos } }) i
        { s with x := { «have» := s.x.«have», next := s.out, pos := s.x.pos } }) { tickW fs with errno := e }) with
  | error err' => simp [hg] at run
  | ok result =>
    rcases result with ⟨u, h3⟩
    obtain ⟨s3, hs3, x3⟩ := gz_error_keepsX i i _ _ _ _ _ hg _ hs2
    simp only [hg, hs3, g_pure_app, g_bind_app, g_lift_app, ldS_eq, setS_gz_same] at run
    simp (config := { decide := true }) only [ite_true, g_pure_app, Option.isSome_some, Bool.true_eq_false,
      ite_false, Option.getD_some] at run
    simp only [Except.ok.injEq, Prod.mk.injEq] at run
    obtain ⟨⟨rfl, -⟩, rfl⟩ := run
    refine ⟨rfl, _, setS_gz_same _ _ _, ?_, rfl⟩
    show s3.x.next = s.out
    rw [x3]

end Zlib.Gzread.FetchCopy
