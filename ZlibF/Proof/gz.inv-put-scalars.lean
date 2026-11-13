import ZlibF.Proof.«gz.inv-model»
import ZlibF.Proof.«gzlib.c.base»

/-!
# gz safety: a scalar write of the handle record keeps `GzInv`

`putGz h i s'` replaces the record of handle `i` and nothing else. When the pointer fields, the sizes, the mode,
`direct`, the embedded stream and `x.next` are unchanged, and the new scalars satisfy the clauses that mention
them, the invariant holds of the new record.

The embedded stream lives in the record, so the codec history (`StreamReachable`) is carried by a rebuffer whose
frame must allow the record block to change: that needs `¬ StreamOwned h (gzStrm i) i` (the codec does not own
the record block), the clause `GzCommon.recordFree`. `GzInv.put_scalars_of` takes it as a premise;
`GzInv.put_scalars` (the skeleton statement) supplies it from the invariant.
-/

namespace ZlibF.Spec.Public
open C Zlib.GzFs
set_option autoImplicit false

section put
variable {h : Heap} {i : Nat} {s s' : GzState}

theorem putGz_live (hs : h.gzstates i = some s) (b : Nat) : (putGz h i s').live b ↔ h.live b := by
  by_cases hb : b = i
  · subst hb
    simp [Heap.live, putGz, hs]
  · simp [Heap.live, putGz, upd_ne _ _ _ _ hb]

theorem putGz_fresh (hs : h.gzstates i = some s) (f : Fresh h) : Fresh (putGz h i s') :=
  fun b hb hl => f b hb ((putGz_live hs b).1 hl)

theorem putGz_uniq (hs : h.gzstates i = some s) (u : Zlib.Gzlib.Spec.Uniq h) :
    Zlib.Gzlib.Spec.Uniq (putGz h i s') := by
  intro b
  have hb := u b
  by_cases e : b = i
  · subst e
    simpa [putGz, hs] using hb
  · simpa [putGz, upd_ne _ _ _ _ e] using hb

theorem putGz_space (r : BRef) : Space.get (putGz h i s') r = Space.get h r := by
  cases r <;> rfl

theorem putGz_fit (fit : ZlibF.PlatformMemory.ByteObjectsFit h) :
    ZlibF.PlatformMemory.ByteObjectsFit (putGz h i s') := by
  intro r a e
  rw [putGz_space] at e
  exact fit r a e

theorem putGz_cstring (p : BPtr) (xs : List UInt8) : CString (putGz h i s') p xs ↔ CString h p xs := by
  unfold CString Bytes
  simp only [putGz_space]

theorem putGz_streamOwned (hs : h.gzstates i = some s) (hz : s'.strm = s.strm) (b : Nat) :
    StreamOwned (putGz h i s') (.in_gzstate_strm i) b = StreamOwned h (.in_gzstate_strm i) b := by
  have hget : ZStreamRef.get (putGz h i s') (.in_gzstate_strm i) = ZStreamRef.get h (.in_gzstate_strm i) := by
    simp [ZStreamRef.get, putGz, hs, hz]
  unfold StreamOwned
  rw [hget]
  rfl

theorem putGz_get (hs : h.gzstates i = some s) (hz : s'.strm = s.strm) :
    ZStreamRef.get (putGz h i s') (gzStrm i) = ZStreamRef.get h (gzStrm i) := by
  simp [ZStreamRef.get, gzStrm, putGz, hs, hz]

/-- The record write is a rebuffer of the embedded codec when the codec does not own the record block. -/
theorem putGz_rebuffer (inv : GzInv h i s) (hz : s'.strm = s.strm) (hrec : ¬ StreamOwned h (gzStrm i) i) :
    Rebuffer h (putGz h i s') (gzStrm i) := by
  have hs := inv.common.record
  refine ⟨putGz_fresh hs inv.common.fresh, putGz_uniq hs inv.common.uniq, inv.common.globals, ?_,
    s.strm, s.strm, ?_, ?_, rfl⟩
  · refine ⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _, ?_⟩
    intro b _ hb
    have hbi : b ≠ i := by
      intro e
      subst e
      exact hb hrec
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, by simp [putGz, upd_ne _ _ _ _ hbi], rfl⟩
  · simp [ZStreamRef.get, gzStrm, hs]
  · simp [ZStreamRef.get, gzStrm, putGz, hz]

/-- The scalar fields that `GzOwned` reads are unchanged, so the handle owns the same blocks. -/
theorem putGz_owned (hs : h.gzstates i = some s)
    (same : s'.path = s.path ∧ s'.msg = s.msg ∧ s'.«in» = s.«in» ∧ s'.out = s.out ∧ s'.size = s.size ∧
      s'.mode = s.mode ∧ s'.direct = s.direct ∧ s'.strm = s.strm) (b : Nat) :
    GzOwned (putGz h i s') i s' b ↔ GzOwned h i s b := by
  obtain ⟨hpath, hmsg, hin, hout, hsize, hmode, hdirect, hstrm⟩ := same
  unfold GzOwned
  rw [hpath, hmsg, hin, hout, hsize, hmode, hdirect, putGz_streamOwned hs hstrm]

end put

/-- **A scalar write of the record keeps `GzInv`**, given that the codec does not own the record block (`hrec`).
The other premises are those of the skeleton's `GzInv.put_scalars`. -/
theorem GzInv.put_scalars_of {h : Heap} {i : Nat} {s s' : GzState} (inv : GzInv h i s)
    (hrec : ¬ StreamOwned h (gzStrm i) i)
    (same : s'.path = s.path ∧ s'.msg = s.msg ∧ s'.«in» = s.«in» ∧ s'.out = s.out ∧ s'.size = s.size ∧
      s'.mode = s.mode ∧ s'.direct = s.direct ∧ s'.strm = s.strm ∧ s'.x.next = s.x.next ∧ s'.err = s.err)
    (want : 8 ≤ s'.want.toNat ∧ s'.want.toNat < 2 ^ 31 ∧ (s.size = 0 ∨ s'.want = s.want))
    (pos : 0 ≤ s'.skip.toInt ∧ s'.x.pos.toInt + s'.skip.toInt ≤ 9223372036854775807 ∧
      0 ≤ s'.x.pos.toInt + s'.x.have.toNat)
    (have_le : s'.x.have.toNat ≤ s.x.have.toNat)
    (rd : s.mode = GZ_READ → (s'.how = LOOK ∨ s'.how = GZ_COPY ∨ s'.how = GZIP) ∧ (s'.how = GZ_COPY → s'.direct = 1) ∧
      (s'.how = GZIP → s'.direct = 0) ∧ (s'.junk = -1 ∨ s'.junk = 0 ∨ s'.junk = 1) ∧
      (s'.eof = 0 ∨ s'.eof = 1) ∧ (s'.past = 0 ∨ s'.past = 1) ∧ (s'.again = 0 ∨ s'.again = 1) ∧
      (s.size = 0 → s'.how = LOOK) ∧ (s.size = 0 → s'.again = 0) ∧
      s'.x.pos.toInt + s'.x.have.toNat ≤ 9223372036854775807)
    (wr : s.mode = GZ_WRITE → s'.reset = 0 ∨ s'.reset = 1) :
    GzInv (putGz h i s') i s' := by
  obtain ⟨hpath, hmsg, hin, hout, hsize, hmode, hdirect, hstrm, hnext, herr⟩ := same
  have c := inv.common
  have hs := c.record
  have hso : ∀ b, StreamOwned (putGz h i s') (gzStrm i) b = StreamOwned h (gzStrm i) b :=
    putGz_streamOwned hs hstrm
  have hown : ∀ b, GzOwned (putGz h i s') i s' b ↔ GzOwned h i s b :=
    putGz_owned hs ⟨hpath, hmsg, hin, hout, hsize, hmode, hdirect, hstrm⟩
  have hptrs : ownedPtrs s' = ownedPtrs s := by
    unfold ownedPtrs
    rw [hpath, hmsg, hsize, hin, hmode, hdirect, hout]
  have hzero : s.x.have = 0 → s'.x.have = 0 := by
    intro e
    have h0 : s'.x.have.toNat = 0 := by
      have := have_le
      rw [e] at this
      exact Nat.le_zero.mp this
    exact UInt32.toNat_inj.mp (by rw [h0]; rfl)
  have hget := putGz_get (s' := s') hs hstrm
  refine ⟨?_, ?_, ?_⟩
  · exact {
      record := by simp [putGz]
      mode := by rw [hmode]; exact c.mode
      fresh := putGz_fresh hs c.fresh
      uniq := putGz_uniq hs c.uniq
      globals := c.globals
      fit := putGz_fit c.fit
      path := by
        obtain ⟨p, hp, hm⟩ := c.path
        exact ⟨p, by rw [hpath, putGz_cstring]; exact hp, by rw [hpath]; exact hm⟩
      msg := by
        rcases c.msg with hn | ⟨m, hm, hb⟩
        · exact Or.inl (by rw [hmsg]; exact hn)
        · exact Or.inr ⟨m, by rw [hmsg, putGz_cstring]; exact hm, by rw [hmsg]; exact hb⟩
      memerr := by rw [herr, hmsg]; exact c.memerr
      want := ⟨want.1, want.2.1⟩
      size := by
        rcases c.size with e | e
        · exact Or.inl (by rw [hsize]; exact e)
        · rcases want.2.2 with z | w
          · exact Or.inl (by rw [hsize]; exact z)
          · exact Or.inr (by rw [hsize, e, w])
      distinct := by
        rw [hptrs]
        simp only [hso]
        exact c.distinct
      live := fun b hb => (putGz_live hs b).2 (c.live b ((hown b).1 hb))
      pos := pos
      next := by
        rcases c.next with hn | ⟨b, off, a, hx, hbi, ho, hmb, hb, hle⟩
        · exact Or.inl (by rw [hnext]; exact hn)
        · exact Or.inr ⟨b, off, a, by rw [hnext]; exact hx, hbi, (hown b).2 ho, by rw [hmsg]; exact hmb, hb,
            by have := have_le; omega⟩
      nullHave := fun hn => hzero (c.nullHave (by rw [← hnext]; exact hn))
      recordFree := by rw [hso]; exact c.recordFree }
  · intro hm'
    have hm : s.mode = GZ_READ := by rw [← hmode]; exact hm'
    have r := inv.reader hm
    obtain ⟨hhow, hcopy, hgzip, hjunk, heof, hpast, hagain, hlook, hagz, hph⟩ := rd hm
    exact {
      how := hhow
      copyDirect := hcopy
      gzipDirect := hgzip
      direct := by rw [hdirect]; exact r.direct
      junk := hjunk
      flags := ⟨heof, hpast, hagain⟩
      unalloc := fun hz => by
        have hz0 : s.size = 0 := by rw [← hsize]; exact hz
        obtain ⟨hh, ha, _, hn⟩ := r.unalloc hz0
        exact ⟨hzero hh, by rw [hstrm]; exact ha, hlook hz0, by rw [hstrm]; exact hn⟩
      bufs := fun hz => by
        rw [hin, hout, hsize]
        exact r.bufs (by rw [← hsize]; exact hz)
      input := by
        rw [hstrm, hin, hsize]
        exact r.input
      output := fun hh => by
        have hh' : s.x.have ≠ 0 := fun e => hh (hzero e)
        obtain ⟨c0, hx, hle⟩ := r.output hh'
        exact ⟨c0, by rw [hnext, hout]; exact hx, by rw [hsize]; have := have_le; omega⟩
      codec := fun hz => by
        have hz0 : s.size ≠ 0 := by rw [← hsize]; exact hz
        obtain ⟨reach, z, k, st, hzget, hzst, hk, hhead⟩ := r.codec hz0
        exact ⟨StreamReachable.rebuffer reach (putGz_rebuffer inv hstrm hrec) (fun _ => putGz_fit c.fit),
          z, k, st, by rw [hget]; exact hzget, hzst, hk, hhead⟩
      posHave := hph
      againSize := fun hz => hagz (by rw [← hsize]; exact hz) }
  · intro hm'
    have hm : s.mode = GZ_WRITE := by rw [← hmode]; exact hm'
    have w := inv.writer hm
    exact {
      have0 := hzero w.have0
      direct := by rw [hdirect]; exact w.direct
      reset := wr hm
      unalloc := fun hz => by
        rw [hstrm]
        exact w.unalloc (by rw [← hsize]; exact hz)
      bufs := fun hz => by
        rw [hin, hout, hsize, hdirect]
        exact w.bufs (by rw [← hsize]; exact hz)
      input := by
        rw [hstrm, hin, hsize]
        exact w.input
      output := fun hd hz => by
        rw [hstrm, hout, hsize, hnext]
        exact w.output (by rw [← hdirect]; exact hd) (by rw [← hsize]; exact hz)
      codec := fun hd hz => by
        obtain ⟨reach, z, k, d, hzget, hzst, hk, hhead⟩ :=
          w.codec (by rw [← hdirect]; exact hd) (by rw [← hsize]; exact hz)
        exact ⟨StreamReachable.rebuffer reach (putGz_rebuffer inv hstrm hrec) (fun e => nomatch e),
          z, k, d, by rw [hget]; exact hzget, hzst, hk, hhead⟩
      transparent := fun hd => by
        rw [hstrm]
        exact w.transparent (by rw [← hdirect]; exact hd) }

/-- With no codec set up (`size = 0`) the codec owns no block, so the record write needs no premise about it. -/
theorem GzInv.no_codec_record {h : Heap} {i : Nat} {s : GzState} (inv : GzInv h i s) (hz : s.size = 0) :
    ¬ StreamOwned h (gzStrm i) i := by
  rcases inv.common.mode with hm | hm
  · exact noCodec_owned inv.common.record ((inv.reader hm).unalloc hz).2.2.2 i
  · exact noCodec_owned inv.common.record ((inv.writer hm).unalloc hz) i

/-- Interface: a write of scalar fields of the record that keeps every clause of the invariant over the new
values keeps it (the caller of this lemma proves the clause conditions for the fields it changes). -/
theorem GzInv.put_scalars {h : Heap} {i : Nat} {s s' : GzState} (inv : GzInv h i s)
    (same : s'.path = s.path ∧ s'.msg = s.msg ∧ s'.«in» = s.«in» ∧ s'.out = s.out ∧ s'.size = s.size ∧
      s'.mode = s.mode ∧ s'.direct = s.direct ∧ s'.strm = s.strm ∧ s'.x.next = s.x.next ∧ s'.err = s.err)
    (want : 8 ≤ s'.want.toNat ∧ s'.want.toNat < 2 ^ 31 ∧ (s.size = 0 ∨ s'.want = s.want))
    (pos : 0 ≤ s'.skip.toInt ∧ s'.x.pos.toInt + s'.skip.toInt ≤ 9223372036854775807 ∧
      0 ≤ s'.x.pos.toInt + s'.x.have.toNat)
    (have_le : s'.x.have.toNat ≤ s.x.have.toNat)
    (rd : s.mode = GZ_READ → (s'.how = LOOK ∨ s'.how = GZ_COPY ∨ s'.how = GZIP) ∧ (s'.how = GZ_COPY → s'.direct = 1) ∧
      (s'.how = GZIP → s'.direct = 0) ∧ (s'.junk = -1 ∨ s'.junk = 0 ∨ s'.junk = 1) ∧
      (s'.eof = 0 ∨ s'.eof = 1) ∧ (s'.past = 0 ∨ s'.past = 1) ∧ (s'.again = 0 ∨ s'.again = 1) ∧
      (s.size = 0 → s'.how = LOOK) ∧ (s.size = 0 → s'.again = 0) ∧
      s'.x.pos.toInt + s'.x.have.toNat ≤ 9223372036854775807)
    (wr : s.mode = GZ_WRITE → s'.reset = 0 ∨ s'.reset = 1) :
    GzInv (putGz h i s') i s' :=
  inv.put_scalars_of inv.common.recordFree same want pos have_le rd wr

end ZlibF.Spec.Public
