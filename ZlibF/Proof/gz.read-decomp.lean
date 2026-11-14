import ZlibF.Proof.«gz.read-budget»
import ZlibF.Proof.«public-inflate»
import ZlibF.Proof.«inflate.c.completes-percall»
import ZlibF.Proof.«inflate.c.region-frame-compose»
import ZlibF.Proof.«gzread.c.skip-gets»
import ZlibF.Proof.«inflate.c.completes-blocked»
import ZlibF.Proof.«inflate.c.leave-ret-codes»
import ZlibF.Proof.«inflate.c.completes-gzip-fields»
import ZlibF.Proof.«inflate.c.public-need-dict-sourcecut»

/-!
# gz read side: `gz_decomp` is safe

`gz_decomp(state)` runs `inflate(strm, Z_NO_FLUSH)` on the embedded stream until the output is full, the member
ends, the input ends or an error occurs.

1. `inflate_step`: one `inflate` call on the embedded stream of a reader in `GzInvUpToOutput`. Its premises come
   from the invariant (`GzReadInv.codec`, `GzReadInv.input`) and from the output window (caller memory the handle
   does not own, or the handle's `out` buffer). The record changes only in its stream (`KeepsCall.gz`, the record
   fact of the whole `inflate` run), so the invariant holds after it.
2. The loop: an invariant over the accumulated post-condition, with the measure `inputLeft + avail_out` under
   `ReadsFinite`.
3. The tail: `x.have` and `x.next` describe the output written into `out`.

`gz_decomp_safe_of` takes two premises, facts of `inflate` that are open: `InflateHeadUsesInput` (a call from mode
`HEAD` with no held bits and `last = 0` and pending input uses input) and `InflateStuckNoOutput` (a call from `BAD` or
`MEM` moves neither buffer and returns `Z_DATA_ERROR` or `Z_MEM_ERROR`). Two proved facts of `inflate` serve the
clauses on a bad error: a `Z_OK` call with input left has filled the output (`blocked_leave`), and a `Z_NEED_DICT`
call makes no output (`public_need_dictionary_zero`). The message of the embedded stream (`MsgLit`) is kept by the
`Keeps` clause on stream messages (`inflate.c.completes-keep`).
-/

namespace ZlibF.Spec.Public.GzRead
open C Zlib.GzFs Zlib.Gzguts Zlib.Gzlib.Spec Zlib.Gzlib.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-! ## The open functional fact -/

/-- **The HEAD fact, a premise** (a functional fact of `inflate`, open). An `inflate` call from mode `HEAD` with no
held bits, `last = 0` and pending input takes input or refuses the stream. From `HEAD` every path pulls a byte
(`NEEDBITS(16)` of the header with `wrap ≠ 0`, or, with `wrap = 0`, `TYPEDO` and then `NEEDBITS(3)` since `last = 0`)
before the mode can change; no later step of the call gives input back, and `inf_leave` writes the remaining input
back before `updatewindow`. -/
def InflateHeadUsesInput : Prop :=
  ∀ {h : Heap} {r : ZStreamRef} {k : Nat} {z : ZStream} {st : InflateState},
    Zlib.Inflate.Spec.Good h r k z st → st.mode = HEAD → st.bits = 0 → st.last = 0 → z.avail_in ≠ 0 →
    ∀ {rc : Int32} {after : Heap} {z' : ZStream},
      C.run (Zlib.Inflate.inflate (some r) Z_NO_FLUSH) h = .ok (rc, after) → r.get after = some z' →
      z'.avail_in.toNat < z.avail_in.toNat ∨ rc = Z_STREAM_ERROR

/-- **The stuck fact, a premise** (a fact of `inflate`, **open**). An `inflate` call from mode `BAD` or `MEM` returns
`Z_DATA_ERROR` or `Z_MEM_ERROR` and leaves `avail_in` and `avail_out` unchanged. `inflate.c`, `inflate()`:
`case BAD: ret = Z_DATA_ERROR; goto inf_leave;` (`inf_leave` restores the registers, which no step of the call moved;
`updatewindow` then copies no output and can only fail, into `MEM` with `Z_MEM_ERROR`) and
`case MEM: return Z_MEM_ERROR;`. -/
def InflateStuckNoOutput : Prop :=
  ∀ {h : Heap} {r : ZStreamRef} {k : Nat} {z : ZStream} {st : InflateState},
    Zlib.Inflate.Spec.Good h r k z st → (st.mode = BAD ∨ st.mode = MEM) →
    ∀ {rc : Int32} {after : Heap} {z' : ZStream},
      C.run (Zlib.Inflate.inflate (some r) Z_NO_FLUSH) h = .ok (rc, after) → r.get after = some z' →
      z'.avail_in = z.avail_in ∧ z'.avail_out = z.avail_out ∧ (rc = Z_DATA_ERROR ∨ rc = Z_MEM_ERROR)

/-- Every literal of the sources is a C string with no NUL inside. -/
theorem table_no_nul : ∀ j : Fin strTable.size,
    0 ∉ (strTable[j]).toUTF8.data.toList ∧ (strTable[j]).toUTF8.data.toList.length < 2 ^ 64 := by
  decide +kernel

/-- A literal of the sources as a C string that no block roots. -/
theorem lit_cstring (h : Heap) {j : Nat} (hj : j < strTable.size) :
    ∃ t, CString h (.ref (.str j) 0) t ∧ ∀ b, ¬ ByteRoot (.ref (.str j) 0) b := by
  obtain ⟨hz, hl⟩ := table_no_nul ⟨j, hj⟩
  have hb : strBytes strTable[j] = ((strTable[j]).toUTF8.data.toList ++ [0]).toArray :=
    Array.ext' (by simp [strBytes])
  have hg : Space.get h (BRef.str j) = some ((strTable[j]).toUTF8.data.toList ++ [0]).toArray := by
    show staticStringBytes h j = _
    simp only [staticStringBytes, if_pos hj, Array.getElem?_eq_getElem hj, Option.map_some]
    rw [hb]
  refine ⟨_, ⟨Or.inr ⟨.str j, 0, _, rfl, hg, by simp, (List.take_of_length_le (by simp)).symm⟩, hz, hl⟩,
    fun b hb' => ?_⟩
  simp [ByteRoot] at hb'

/-! ## Frames -/

theorem bytes_of_writable' {h : Heap} {p : BPtr} {n : Nat} (w : Writable h p n) : ∃ xs, Bytes h p n xs := by
  rcases w with ⟨null, zero⟩ | ⟨ref, off, a, ptr, get, -, room⟩
  · exact ⟨[], Or.inl ⟨null, zero, rfl⟩⟩
  · exact ⟨(a.toList.drop off).take n, Or.inr ⟨ref, off, a, ptr, get, room, rfl⟩⟩

/-- A live block outside the changed set keeps its tables other than the bytes (only byte views are restored). -/
theorem bf_tables {h a : Heap} {C : Nat → Prop} {R : List Region} (bf : BufferFrame h a C R) {b : Nat}
    (hl : h.live b) (hc : ¬ C b) :
    a.ro b = h.ro b ∧ a.istates b = h.istates b ∧ a.gzstates b = h.gzstates b ∧ a.streams b = h.streams b ∧
      a.words b = h.words b ∧ a.gzheaders b = h.gzheaders b := by
  obtain ⟨-, e2, e3, e4, -, e6, e7, e8⟩ := bf.1.2.2.2.2.2 b hl hc
  have o := Zlib.Inflate.Proofs.restoreRegions_other h a R
  dsimp only at o
  obtain ⟨-, -, -, -, -, ew, es, egh, ei, eg, ero⟩ := o
  exact ⟨by rw [← ero]; exact e8, by rw [← ei]; exact e6, by rw [← eg]; exact e7, by rw [← es]; exact e3,
    by rw [← ew]; exact e2, by rw [← egh]; exact e4⟩

/-- A live block outside the changed set and outside the regions keeps its bytes. -/
theorem bf_bytes {h a : Heap} {C : Nat → Prop} {R : List Region} (bf : BufferFrame h a C R) {b : Nat}
    (hl : h.live b) (hc : ¬ C b) (hr : ¬ Zlib.Inflate.Proofs.RegionRoot R (.blk b)) :
    a.bytes b = h.bytes b := by
  obtain ⟨e1, -⟩ := bf.1.2.2.2.2.2 b hl hc
  rw [Zlib.Inflate.Proofs.restoreRegions_bytes, if_neg (fun hh => hr hh.1)] at e1
  exact e1

/-- A byte block outside the changed set keeps its size and its flag. -/
theorem bf_size {h a : Heap} {C : Nat → Prop} {R : List Region} (bf : BufferFrame h a C R) {b : Nat}
    {x : Array UInt8} (hx : h.bytes b = some x) (hc : ¬ C b) :
    ∃ y, a.bytes b = some y ∧ y.size = x.size ∧ a.ro b = h.ro b := by
  have hl : h.live b := Or.inl (by rw [hx]; intro e; cases e)
  have ro := (bf_tables bf hl hc).1
  by_cases hr : Zlib.Inflate.Proofs.RegionRoot R (.blk b)
  · obtain ⟨region, mem, off, hp⟩ := hr
    obtain ⟨y, hy, hsz, -⟩ := bf.2 region mem (.blk b) off x hp hx
    exact ⟨y, hy, hsz, ro⟩
  · exact ⟨x, by rw [bf_bytes bf hl hc hr]; exact hx, rfl, ro⟩

/-! ## The reader's blocks -/

/-- Two different owned blocks of a reader with buffers: the `in` and `out` buffers are different blocks. -/
theorem GzInv.in_ne_out {h : Heap} {i : Nat} {s : GzState} (inv : GzInv h i s) (hm : s.mode = GZ_READ)
    (hsz : s.size ≠ 0) {inb ob : Nat} (hin : s.«in» = .ref (.blk inb) 0) (hout : s.out = .ref (.blk ob) 0) :
    inb ≠ ob := by
  intro e
  subst e
  have nd := inv.common.distinct.1
  simp only [ownedPtrs, if_pos hsz, if_pos (Or.inl hm : s.mode = GZ_READ ∨ s.direct = 0), List.cons_append,
    List.nil_append] at nd
  exact absurd (nd.sublist (List.Sublist.filterMap blkOf
    (List.Sublist.cons _ (List.Sublist.cons _ (List.Sublist.cons₂ _ (List.Sublist.cons₂ _ (List.nil_sublist _)))))))
    (by simp [hin, hout, blkOf])

/-- The facts of a reader with buffers that an `inflate` call needs, on the actual heap. -/
def ReaderBlocks (h : Heap) (i : Nat) (s : GzState) : Prop :=
  h.gzstates i = some s ∧ ∃ (inb : Nat) (arr : Array UInt8), s.«in» = .ref (.blk inb) 0 ∧ h.bytes inb = some arr ∧
    h.ro inb = false ∧ arr.size = s.size.toNat ∧ ∃ (ob : Nat) (oarr : Array UInt8), s.out = .ref (.blk ob) 0 ∧
    h.bytes ob = some oarr ∧ h.ro ob = false ∧ oarr.size = 2 * s.size.toNat ∧ inb ≠ ob ∧
    (inb ≠ i ∧ ¬ StreamOwned h (gzStrm i) inb ∧ s.path ≠ .ref (.blk inb) 0 ∧ s.msg ≠ .ref (.blk inb) 0) ∧
    (ob ≠ i ∧ ¬ StreamOwned h (gzStrm i) ob ∧ s.path ≠ .ref (.blk ob) 0 ∧ s.msg ≠ .ref (.blk ob) 0) ∧
    ∃ (k : Nat) (st : InflateState), s.strm.state = some (.inflate k) ∧ h.istates k = some st ∧ st.head = none

theorem readerBlocks {h : Heap} {i : Nat} {s : GzState} (hu : GzInvUpToOutput h i s) (hm : s.mode = GZ_READ)
    (hsz : s.size ≠ 0) : ReaderBlocks h i s := by
  obtain ⟨hs, inv⟩ := hu
  have rd := inv.reader hm
  have hso : ∀ b, StreamOwned (putGz h i (clearOut s)) (gzStrm i) b ↔ StreamOwned h (gzStrm i) b := fun b =>
    Iff.of_eq (putGz_streamOwned (s' := clearOut s) hs rfl b)
  obtain ⟨inb, arr, hin, hinb, hinro, hinsz⟩ := (rd.bufs hsz).1
  obtain ⟨ob, oarr, hout, houtb, houtro, houtsz⟩ := (rd.bufs hsz).2
  have din : DataBuf (clearOut s) inb := ⟨hsz, Or.inl hin⟩
  have dout : DataBuf (clearOut s) ob := ⟨hsz, Or.inr ⟨Or.inl hm, hout⟩⟩
  obtain ⟨i1, i2, i3, i4⟩ := GzInv.data_separate inv din
  obtain ⟨o1, o2, o3, o4⟩ := GzInv.data_separate inv dout
  obtain ⟨-, z, k, st, hzget, hzst, hk, hhead⟩ := rd.codec hsz
  have hz : z = s.strm := by
    simp [ZStreamRef.get, gzStrm, putGz] at hzget
    exact hzget.symm
  subst hz
  exact ⟨hs, inb, arr, hin, hinb, hinro, hinsz, ob, oarr, hout, houtb, houtro, houtsz,
    GzInv.in_ne_out inv hm hsz hin hout, ⟨i1, fun x => i2 ((hso inb).2 x), i3, i4⟩,
    ⟨o1, fun x => o2 ((hso ob).2 x), o3, o4⟩,
    k, st, hzst, hk, hhead⟩

/-! ## One `inflate` call on the embedded stream -/

/-- Where the output pointer of the embedded stream points: caller memory the handle does not own, or `out`. -/
def OutSide (h : Heap) (i : Nat) (s : GzState) (p : BPtr) : Prop :=
  (∀ b, ByteRoot p b → ¬ GzOwned h i s b) ∨ ∃ c, p = padv s.out c

theorem ne_nil_length {α : Type} {l : List α} (hl : l ≠ []) : l.length ≠ 0 := fun e => hl (List.eq_nil_of_length_eq_zero e)

/-- **One `inflate(strm, Z_NO_FLUSH)` call on the embedded stream** of a reader with buffers and pending input,
into a writable output window. It returns, the record changes only in its stream, the invariant up to the
buffered output holds after it, and the post-condition holds over the output written. -/
theorem inflate_step (head : InflateHeadUsesInput) (stuck : InflateStuckNoOutput) {h : Heap} {i : Nat} {s : GzState} (fs : Fs) (hfs : FileSystem fs)
    (hu : GzInvUpToOutput h i s) (hm : s.mode = GZ_READ)
    (hsz : s.size ≠ 0) (hav : s.strm.avail_in ≠ 0)
    (hw : Writable h s.strm.next_out s.strm.avail_out.toNat) (hside : OutSide h i s s.strm.next_out) :
    ∃ rc after z' used produced,
      C.run (Zlib.Inflate.inflate (some (gzStrm i)) Z_NO_FLUSH) h = .ok (rc, after) ∧
      after.gzstates i = some { s with strm := z' } ∧
      StreamAccounting s.strm z' used produced ∧
      (rc = Z_OK ∨ rc = Z_STREAM_END ∨ rc = Z_NEED_DICT ∨ rc = Z_STREAM_ERROR ∨
        rc = Z_DATA_ERROR ∨ rc = Z_MEM_ERROR ∨ rc = Z_BUF_ERROR) ∧
      (rc = Z_OK → used ≠ 0 ∨ produced ≠ 0) ∧
      (rc = Z_BUF_ERROR → s.strm.avail_out ≠ 0 → False) ∧
      (InflateAtHead h s → s.strm.avail_out ≠ 0 → used ≠ 0) ∧
      (rc = Z_OK → z'.avail_in ≠ 0 → z'.avail_out = 0) ∧
      (rc = Z_NEED_DICT ∨ rc = Z_STREAM_ERROR → produced = 0) ∧
      (Stuck h s → produced = 0 ∧ (rc = Z_DATA_ERROR ∨ rc = Z_MEM_ERROR)) ∧
      (rc = Z_DATA_ERROR ∨ rc = Z_MEM_ERROR → Stuck after { s with strm := z' }) ∧
      (MsgLit s → MsgLit { s with strm := z' }) ∧
      GzPost h i s [⟨s.strm.next_out, produced⟩] fs after GzInvUpToOutput := by
  have hs : h.gzstates i = some s := hu.1
  have inv := hu.2
  have rd := inv.reader hm
  have c0 := inv.common
  obtain ⟨-, inb, arr, hin, hinb, hinro, hinsz, ob, oarr, hout, houtb, houtro, houtsz, hne, inSep, outSep,
    k, st, hstate, hk, hhead⟩ := readerBlocks hu hm hsz
  have hso0 : ∀ b, StreamOwned (putGz h i (clearOut s)) (gzStrm i) b ↔ StreamOwned h (gzStrm i) b := fun b =>
    Iff.of_eq (putGz_streamOwned (s' := clearOut s) hs rfl b)
  have hlive0 : ∀ b, (putGz h i (clearOut s)).live b ↔ h.live b := fun b => putGz_live hs b
  have hgetH : (gzStrm i).get h = some s.strm := by simp [ZStreamRef.get, gzStrm, hs]
  obtain ⟨a, hnin, hale⟩ : ∃ a, s.strm.next_in = .ref (.blk inb) a ∧ a + s.strm.avail_in.toNat ≤ s.size.toNat := by
    rcases rd.input with z | ⟨a, hq, hle⟩
    · exact absurd z hav
    · refine ⟨a, ?_, hle⟩
      have hq' : s.strm.next_in = padv s.«in» a := hq
      rw [hq', hin]; simp [padv]
  -- the codec history on the actual heap
  have hH0 : putGz (putGz h i (clearOut s)) i s = h := by rw [putGz_putGz']; exact upd_self_heap hs
  have reach0 := (rd.codec hsz).1
  have hreb : Rebuffer (putGz h i (clearOut s)) h (gzStrm i) := by
    have := putGz_rebuffer (s' := s) inv rfl c0.recordFree
    rwa [hH0] at this
  have fitH : ZlibF.PlatformMemory.ByteObjectsFit h := by
    have := putGz_fit (h := putGz h i (clearOut s)) (i := i) (s' := s) c0.fit
    rwa [hH0] at this
  have reach : StreamReachable .inflate h (gzStrm i) := StreamReachable.rebuffer reach0 hreb (fun _ => fitH)
  obtain ⟨k1, z1, st1, iinv, -⟩ := Zlib.Inflate.Proofs.reachable_invariant_kind reach rfl
  have ez : z1 = s.strm := Option.some.inj (iinv.good.live.hz.symm.trans hgetH)
  subst ez
  have ek : k1 = k := by
    have e := iinv.good.live.zst.symm.trans hstate
    cases e; rfl
  rw [ek] at iinv
  have est : st1 = st := Option.some.inj (iinv.good.live.hs.symm.trans hk)
  rw [est] at iinv
  have good1 := iinv.good
  -- the blocks of the handle and the output window
  have soOwned : ∀ b, StreamOwned h (gzStrm i) b → GzOwned h i s b := fun b e =>
    Or.inr (Or.inr (Or.inr ⟨hsz, Or.inr ⟨Or.inl hm, Or.inr e⟩⟩))
  have hroot : ∀ b, ByteRoot s.strm.next_out b → b ≠ i ∧ ¬ StreamOwned h (gzStrm i) b ∧ b ≠ inb ∧
      s.path ≠ .ref (.blk b) 0 ∧ s.msg ≠ .ref (.blk b) 0 := by
    intro b hb
    rcases hside with hA | ⟨c, hc⟩
    · have hn := hA b hb
      refine ⟨fun e => hn (Or.inl e), fun e => hn (soOwned b e),
        fun e => hn (Or.inr (Or.inr (Or.inr ⟨hsz, Or.inl (by rw [hin, e])⟩))), fun e => hn (Or.inr (Or.inl e)),
        fun e => hn (Or.inr (Or.inr (Or.inl e)))⟩
    · rw [hc, hout] at hb
      have hb' : b = ob := hb
      subst hb'
      exact ⟨outSep.1, outSep.2.1, fun e => hne e.symm, outSep.2.2.1, outSep.2.2.2⟩
  have bufs : StreamBuffers h (gzStrm i) := by
    refine ⟨s.strm, hgetH, Or.inr ⟨⟨_, Or.inr ⟨.blk inb, a, arr, hnin, hinb, by omega, rfl⟩⟩, (fun e => by cases e),
      fun b hb => ?_⟩, Or.inr ⟨bytes_of_writable' hw, fun _ => hw, fun b hb => (hroot b hb).2.1⟩, ?_⟩
    · rw [hnin] at hb
      have hb' : b = inb := hb
      subst hb'
      exact inSep.2.1
    · right; right
      rw [hnin]
      cases hq : s.strm.next_out with
      | null => trivial
      | ref r' j =>
        left
        intro e
        subst e
        exact (hroot inb (by rw [hq]; rfl)).2.2.1 rfl
  have act : ActiveHeader h (gzStrm i) := by
    refine ⟨s.strm, hgetH, fun k2 st2 hk2 hst2 => ?_, fun k2 d hk2 _ => by rw [hstate] at hk2; cases hk2⟩
    rw [hstate] at hk2
    cases hk2
    rw [hk] at hst2
    cases hst2
    exact ⟨Or.inl hhead, fun _ _ j g hh _ => by rw [hhead] at hh; cases hh⟩
  -- the call
  obtain ⟨rc, after, z', st', used, outb, run, good', acct, -, codes, progOK, serr, sEq, bufE, progBUF, -, -, dataM,
    memM, -, frame, ledger⟩ :=
    Zlib.Inflate.Proofs.inflate_public h (gzStrm i) k s.strm st Z_NO_FLUSH reach good1 fitH iinv.alloc bufs act
  have ctl := Zlib.Inflate.Proofs.call_keeps_control h (gzStrm i) k s.strm st Z_NO_FLUSH rc after z' st' reach
    good1 run good'
  have kc := Zlib.Inflate.KeepProofs.call_inflate (some (gzStrm i)) Z_NO_FLUSH h rc after run
  obtain ⟨g', hg', eg'⟩ := kc.gz i s hs
  have hzg : g'.strm = z' := by
    have := good'.live.hz
    simp only [ZStreamRef.get, gzStrm, hg', Option.map_some, Option.some.injEq] at this
    exact this
  have hrec' : after.gzstates i = some { s with strm := z' } := by rw [hg', eg', hzg]
  have hstate' : z'.state = some (.inflate k) := by rw [acct.2.2.2.2.2.2.1, hstate]
  have frame' : BufferFrame h after
      (fun b => StreamRoot (gzStrm i) b ∨ InflateOwned k st b ∨ st.head = some (.tab b))
      [⟨s.strm.next_out, outb.length⟩] := by
    have e : HeaderRegions h st.head = [] := by rw [hhead]; rfl
    have := frame
    rw [e] at this
    exact this
  have notC : ∀ b, b ≠ i → ¬ StreamOwned h (gzStrm i) b →
      ¬ (StreamRoot (gzStrm i) b ∨ InflateOwned k st b ∨ st.head = some (.tab b)) := by
    rintro b hbi hso (e | io | hh)
    · exact hbi e
    · exact hso ⟨s.strm, hgetH, Or.inl ⟨k, st, hstate, hk, io⟩⟩
    · rw [hhead] at hh; cases hh
  have notRoot : ∀ b, ¬ ByteRoot s.strm.next_out b →
      ¬ Zlib.Inflate.Proofs.RegionRoot [⟨s.strm.next_out, outb.length⟩] (.blk b) := by
    rintro b hn ⟨region, mem, off, hp⟩
    rw [List.mem_singleton] at mem
    subst mem
    apply hn
    simp only at hp
    rw [hp]
    rfl
  have sownH : ∀ b, StreamOwned h (gzStrm i) b → InflateOwned k st b := by
    rintro b ⟨z2, hz2, ⟨k2, st2, hk2, hst2, io⟩ | ⟨k2, d2, hk2, -, -⟩⟩
    · have ez2 : z2 = s.strm := Option.some.inj (hz2.symm.trans hgetH)
      subst ez2
      rw [hstate] at hk2
      have ek2 : k2 = k := by injection hk2 with e1; injection e1 with e2; exact e2.symm
      rw [ek2, hk] at hst2
      have es2 : st2 = st := (Option.some.inj hst2).symm
      rw [ek2, es2] at io
      exact io
    · have ez2 : z2 = s.strm := Option.some.inj (hz2.symm.trans hgetH)
      subst ez2
      rw [hstate] at hk2
      injection hk2 with e1
      injection e1
  have sownAfter : ∀ b, StreamOwned after (gzStrm i) b →
      (StreamOwned h (gzStrm i) b ∨ ¬ h.live b) ∧ after.live b ∧ InflateOwned k st' b := by
    rintro b ⟨z2, hz2, ⟨k2, st2, hk2, hst2, io⟩ | ⟨k2, d2, hk2, -, -⟩⟩
    · have ez2 : z2 = z' := Option.some.inj (hz2.symm.trans good'.live.hz)
      subst ez2
      rw [hstate'] at hk2
      have ek2 : k2 = k := by injection hk2 with e1; injection e1 with e2; exact e2.symm
      rw [ek2, good'.live.hs] at hst2
      have es2 : st2 = st' := (Option.some.inj hst2).symm
      rw [ek2, es2] at io
      refine ⟨?_, ?_, io⟩
      · rcases ctl.2.2.2.2 b io with io0 | nl
        · exact Or.inl ⟨s.strm, hgetH, Or.inl ⟨k, st, hstate, hk, io0⟩⟩
        · exact Or.inr nl
      · rcases io with e | w
        · subst e
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by rw [good'.live.hs]; intro x; cases x))))))
        · rcases good'.inv.win.block with wn | ⟨w', a', hw', hb', -, -⟩
          · rw [wn] at w; cases w
          · rw [hw'] at w
            cases w
            exact Or.inl (by rw [hb']; intro x; cases x)
    · exfalso
      have ez2 : z2 = z' := Option.some.inj (hz2.symm.trans good'.live.hz)
      subst ez2
      rw [hstate'] at hk2
      injection hk2 with e1
      injection e1
  have ownAfter : ∀ b, InflateOwned k st' b → StreamOwned after (gzStrm i) b := fun b io =>
    ⟨z', good'.live.hz, Or.inl ⟨k, st', hstate', good'.live.hs, io⟩⟩
  -- the pointer blocks are kept
  have keptB : ∀ b, b ≠ i → ¬ StreamOwned h (gzStrm i) b → ¬ ByteRoot s.strm.next_out b → h.live b →
      after.bytes b = h.bytes b ∧ after.ro b = h.ro b := fun b h1 h2 h3 hl =>
    ⟨bf_bytes frame' hl (notC b h1 h2) (notRoot b h3), (bf_tables frame' hl (notC b h1 h2)).1⟩
  have notRootOf : ∀ b, (s.path = .ref (.blk b) 0 ∨ s.msg = .ref (.blk b) 0 ∨ b = inb) →
      ¬ ByteRoot s.strm.next_out b := by
    intro b hb hr
    obtain ⟨-, -, h3, h4, h5⟩ := hroot b hr
    rcases hb with e | e | e
    · exact h4 e
    · exact h5 e
    · exact h3 e
  have ptrSep : ∀ p, p ∈ ownedPtrs (clearOut s) → ∀ b, blkOf p = some b → b ≠ i ∧ ¬ StreamOwned h (gzStrm i) b :=
    fun p hp b hb => ⟨(c0.distinct.2 p hp b hb).1, fun x => (c0.distinct.2 p hp b hb).2 ((hso0 b).2 x)⟩
  have pathKept : ∀ pb, s.path = .ref (.blk pb) 0 → after.bytes pb = h.bytes pb ∧ after.ro pb = h.ro pb := by
    intro pb hp
    have sep := ptrSep s.path (by simp [ownedPtrs, clearOut]) pb (by rw [hp]; rfl)
    have hl : h.live pb := (hlive0 pb).1 (GzInv.ptr_live inv (p := s.path) (by simp [ownedPtrs, clearOut])
      (by rw [hp]; rfl))
    exact keptB pb sep.1 sep.2 (notRootOf pb (Or.inl hp)) hl
  have msgKept : ∀ mb, s.msg = .ref (.blk mb) 0 → after.bytes mb = h.bytes mb ∧ after.ro mb = h.ro mb := by
    intro mb hp
    have sep := ptrSep s.msg (by simp [ownedPtrs, clearOut]) mb (by rw [hp]; rfl)
    have hl : h.live mb := (hlive0 mb).1 (GzInv.ptr_live inv (p := s.msg) (by simp [ownedPtrs, clearOut])
      (by rw [hp]; rfl))
    exact keptB mb sep.1 sep.2 (notRootOf mb (Or.inr (Or.inl hp))) hl
  obtain ⟨arr', hinb', hinsz', hinro'⟩ := bf_size frame' hinb (notC inb inSep.1 inSep.2.1)
  obtain ⟨oarr', houtb', houtsz', houtro'⟩ := bf_size frame' houtb (notC ob outSep.1 outSep.2.1)
  -- the record after the call
  let s' : GzState := { s with strm := z' }
  have hrecA : (putGz after i (clearOut s')).gzstates i = some (clearOut s') := by simp [putGz]
  have hsoA : ∀ b, StreamOwned (putGz after i (clearOut s')) (gzStrm i) b ↔ StreamOwned after (gzStrm i) b :=
    fun b => Iff.of_eq (putGz_streamOwned (s' := clearOut s') hrec' rfl b)
  have recFreeAfter : ¬ StreamOwned after (gzStrm i) i := by
    intro ho
    rcases (sownAfter i ho).1 with so | nl
    · exact c0.recordFree ((hso0 i).2 so)
    · exact nl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by rw [hs]; intro x; cases x)))))))
  have staticEq : after.static = h.static := by
    have o := Zlib.Inflate.Proofs.restoreRegions_other h after [⟨s.strm.next_out, outb.length⟩]
    dsimp only at o
    rw [← o.1]; exact frame'.1.1.symm
  have freshA : Fresh (putGz after i (clearOut s')) := putGz_fresh hrec' good'.fresh
  have uniqA : Zlib.Gzlib.Spec.Uniq (putGz after i (clearOut s')) := putGz_uniq hrec' good'.uniq
  have globalsA : LibraryGlobals (putGz after i (clearOut s')) := by
    show after.static = _
    rw [staticEq]; exact c0.globals
  have fitAfter : ZlibF.PlatformMemory.ByteObjectsFit after :=
    Zlib.Inflate.Proofs.inflate_keeps_object_size h (gzStrm i) k s.strm st Z_NO_FLUSH rc after reach good1 fitH
      bufs act run
  have fitA : ZlibF.PlatformMemory.ByteObjectsFit (putGz after i (clearOut s')) := putGz_fit fitAfter
  have exec : Call.execute (.inflate (some (gzStrm i)) Z_NO_FLUSH) default h = .ok ((rc, default), after) := by
    show heapCall (Zlib.Inflate.inflate (some (gzStrm i)) Z_NO_FLUSH) default h = _
    unfold heapCall
    rw [show Zlib.Inflate.inflate (some (gzStrm i)) Z_NO_FLUSH h = .ok (rc, after) from run]
    rfl
  have reachAfter : StreamReachable .inflate after (gzStrm i) :=
    StreamReachable.step (call := .inflate (some (gzStrm i)) Z_NO_FLUSH) reach (fun _ => fitH) ⟨rfl, rfl⟩
      ⟨bufs, act⟩ exec
  have hrebA : Rebuffer after (putGz after i (clearOut s')) (gzStrm i) := by
    refine ⟨freshA, uniqA, globalsA, ⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _, fun b _ hb => ?_⟩, z', z', ?_,
      ?_, rfl⟩
    · have hbi : b ≠ i := fun e => hb (by rw [e]; exact recFreeAfter)
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, by simp [putGz, upd_ne _ _ _ _ hbi], rfl⟩
    · simp [ZStreamRef.get, gzStrm, hrec']
    · simp [ZStreamRef.get, gzStrm, putGz, clearOut, s']
  have reachA : StreamReachable .inflate (putGz after i (clearOut s')) (gzStrm i) :=
    StreamReachable.rebuffer reachAfter hrebA (fun _ => fitA)
  have liveA : ∀ b, (putGz after i (clearOut s')).live b ↔ after.live b := fun b => putGz_live hrec' b
  have liveOfBytes : ∀ (H : Heap) b (x : Array UInt8), H.bytes b = some x → H.live b := fun H b x e =>
    Or.inl (by rw [e]; intro y; cases y)
  have invA : GzInv (putGz after i (clearOut s')) i (clearOut s') := by
    refine ⟨?_, fun _ => ?_, fun hw => absurd (hm.symm.trans hw) (by decide)⟩
    · exact {
        record := hrecA
        mode := c0.mode
        fresh := freshA
        uniq := uniqA
        globals := globalsA
        fit := fitA
        path := by
          obtain ⟨p, hc, hmb⟩ := c0.path
          obtain ⟨pb, x, hp, hb, hr, hn⟩ := hmb
          have hp' : s.path = .ref (.blk pb) 0 := hp
          obtain ⟨e1, e2⟩ := pathKept pb hp'
          refine ⟨p, ?_, pb, x, hp, by show after.bytes pb = _; rw [e1]; exact hb,
            by show after.ro pb = _; rw [e2]; exact hr, hn⟩
          have hc0 : CString (putGz h i (clearOut s)) s.path p := hc
          show CString (putGz after i (clearOut s')) s.path p
          rw [hp'] at hc0 ⊢
          exact (cstring_blk_congr (h := putGz h i (clearOut s)) (by exact e1)).2 hc0
        msg := by
          rcases c0.msg with hn | ⟨m, hc, hmb⟩
          · exact Or.inl hn
          · obtain ⟨mb, x, hp, hb, hr, hn⟩ := hmb
            have hp' : s.msg = .ref (.blk mb) 0 := hp
            obtain ⟨e1, e2⟩ := msgKept mb hp'
            refine Or.inr ⟨m, ?_, mb, x, hp, by show after.bytes mb = _; rw [e1]; exact hb,
              by show after.ro mb = _; rw [e2]; exact hr, hn⟩
            have hc0 : CString (putGz h i (clearOut s)) s.msg m := hc
            show CString (putGz after i (clearOut s')) s.msg m
            rw [hp'] at hc0 ⊢
            exact (cstring_blk_congr (h := putGz h i (clearOut s)) (by exact e1)).2 hc0
        memerr := c0.memerr
        want := c0.want
        size := c0.size
        distinct := ⟨c0.distinct.1, fun p hp b hb => ⟨(c0.distinct.2 p hp b hb).1, fun ho => by
          rcases (sownAfter b ((hsoA b).1 ho)).1 with so | nl
          · exact (ptrSep p hp b hb).2 so
          · exact nl ((hlive0 b).1 (GzInv.ptr_live inv hp hb))⟩⟩
        live := by
          intro b ho
          rw [liveA]
          rcases ho with e | e | e | ⟨-, e | ⟨-, e | e⟩⟩
          · rw [e]; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by rw [hrec']; intro x; cases x))))))
          · obtain ⟨-, -, pb, x, hp, hb, -, -⟩ := c0.path
            have hp' : s.path = .ref (.blk pb) 0 := hp
            have e' : s.path = .ref (.blk b) 0 := e
            rw [hp'] at e'
            have epb : b = pb := by injection e' with e1 e2; injection e1 with e3; exact e3.symm
            rw [epb]
            exact liveOfBytes after pb x (by rw [(pathKept pb hp').1]; exact hb)
          · rcases c0.msg with hn | ⟨_, _, mb, x, hp, hb, -, -⟩
            · have e' : s.msg = .ref (.blk b) 0 := e
              have hn' : s.msg = .null := hn
              rw [hn'] at e'; cases e'
            · have hp' : s.msg = .ref (.blk mb) 0 := hp
              have e' : s.msg = .ref (.blk b) 0 := e
              rw [hp'] at e'
              have emb : b = mb := by injection e' with e1 e2; injection e1 with e3; exact e3.symm
              rw [emb]
              exact liveOfBytes after mb x (by rw [(msgKept mb hp').1]; exact hb)
          · have e' : s.«in» = .ref (.blk b) 0 := e
            rw [hin] at e'
            have eb : b = inb := by injection e' with e1 e2; injection e1 with e3; exact e3.symm
            rw [eb]
            exact liveOfBytes after inb arr' hinb'
          · have e' : s.out = .ref (.blk b) 0 := e
            rw [hout] at e'
            have eb : b = ob := by injection e' with e1 e2; injection e1 with e3; exact e3.symm
            rw [eb]
            exact liveOfBytes after ob oarr' houtb'
          · exact (sownAfter b ((hsoA b).1 e)).2.1
        pos := c0.pos
        next := fun hh => absurd rfl hh
        nullHave := fun _ => rfl
        recordFree := fun ho => recFreeAfter ((hsoA i).1 ho) }
    · exact {
        how := rd.how
        copyDirect := rd.copyDirect
        gzipDirect := rd.gzipDirect
        direct := rd.direct
        junk := rd.junk
        flags := rd.flags
        unalloc := fun hz => absurd hz hsz
        bufs := fun _ => ⟨⟨inb, arr', hin, hinb', by show after.ro inb = _; rw [hinro']; exact hinro,
            by rw [hinsz']; exact hinsz⟩,
          ⟨ob, oarr', hout, houtb', by show after.ro ob = _; rw [houtro']; exact houtro,
            by rw [houtsz']; exact houtsz⟩⟩
        input := by
          right
          refine ⟨a + used, ?_, ?_⟩
          · show z'.next_in = padv s.«in» (a + used)
            rw [acct.2.2.2.2.1, hnin, hin]
            simp [advance, padv]
          · show a + used + z'.avail_in.toNat ≤ s.size.toNat
            have := acct.2.2.1
            omega
        output := fun hh => absurd rfl hh
        codec := fun _ => ⟨reachA, z', k, st', by simp [ZStreamRef.get, gzStrm, putGz, clearOut, s'],
          hstate', good'.live.hs, by rw [ctl.2.2.1]; exact hhead⟩
        posHave := rd.posHave
        againSize := rd.againSize
        haveSkip := rd.haveSkip
        againEof := fun ha he => by
          have h1 : s.strm.avail_in = 0 := rd.againEof ha he
          have h0 : s.strm.avail_in.toNat = 0 := by rw [h1]; rfl
          have := acct.2.2.1
          show z'.avail_in = 0
          apply UInt32.toNat_inj.mp
          show z'.avail_in.toNat = 0
          omega
        errEnd := rd.errEnd
        copyIn := fun hc => absurd (rd.copyIn hc) hav
        msgLit := fun hz => by
          obtain ⟨z2, g2, m2⟩ := kc.msgs (gzStrm i) s.strm hgetH
          have ez : z2 = z' := Option.some.inj (g2.symm.trans good'.live.hz)
          subst ez
          rcases m2 with e | e | e
          · have hm := rd.msgLit hz
            change s.strm.msg = .null ∨ ∃ j, j < strTable.size ∧ s.strm.msg = .ref (.str j) 0 at hm
            change z2.msg = .null ∨ ∃ j, j < strTable.size ∧ z2.msg = .ref (.str j) 0
            rw [e]
            exact hm
          · exact Or.inl e
          · exact Or.inr e }
  -- ownership across the call
  have ownA : ∀ b, GzOwned (putGz after i (clearOut s')) i (clearOut s') b ↔ GzOwned after i s' b :=
    putGz_owned (s' := clearOut s') hrec' ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have O1 : ∀ b, GzOwned h i s b → GzOwned after i s' b := by
    rintro b (e | e | e | ⟨hz, e | ⟨hmd, e | so⟩⟩)
    · exact Or.inl e
    · exact Or.inr (Or.inl e)
    · exact Or.inr (Or.inr (Or.inl e))
    · exact Or.inr (Or.inr (Or.inr ⟨hz, Or.inl e⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨hz, Or.inr ⟨hmd, Or.inl e⟩⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨hz, Or.inr ⟨hmd, Or.inr (ownAfter b (ctl.2.2.2.1 b (sownH b so)))⟩⟩))
  have O2 : ∀ b, GzOwned after i s' b → GzOwned h i s b ∨ ¬ h.live b := by
    rintro b (e | e | e | ⟨hz, e | ⟨hmd, e | so⟩⟩)
    · exact Or.inl (Or.inl e)
    · exact Or.inl (Or.inr (Or.inl e))
    · exact Or.inl (Or.inr (Or.inr (Or.inl e)))
    · exact Or.inl (Or.inr (Or.inr (Or.inr ⟨hz, Or.inl e⟩)))
    · exact Or.inl (Or.inr (Or.inr (Or.inr ⟨hz, Or.inr ⟨hmd, Or.inl e⟩⟩)))
    · rcases (sownAfter b so).1 with so0 | nl
      · exact Or.inl (soOwned b so0)
      · exact Or.inr nl
  have Al : ∀ b, GzOwned after i s' b → after.live b := fun b ho =>
    (liveA b).1 (invA.common.live b ((ownA b).2 ho))
  have msgOk : Zlib.Inflate.KeepProofs.MsgOk s.strm z' := by
    obtain ⟨z2, g2, m2⟩ := kc.msgs (gzStrm i) s.strm hgetH
    have ez : z2 = z' := Option.some.inj (g2.symm.trans good'.live.hz)
    rw [← ez]
    exact m2
  refine ⟨rc, after, z', used, outb.length, run, hrec', acct, codes, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e
    rcases (progOK e).1 with u | o
    · exact Or.inl u
    · exact Or.inr (ne_nil_length o)
  · intro e hao
    rcases bufE e with ⟨u0, o0⟩ | ff
    · rcases progBUF hav hao (by decide) (by decide) e with u | o
      · exact u u0
      · exact o o0
    · exact absurd ff (by decide)
  · rintro ⟨k2, st2, hk2, hst2, hmode, hbits, hlast⟩ hao
    rw [hstate] at hk2
    cases hk2
    rw [hk] at hst2
    cases hst2
    rcases head good1 hmode hbits hlast hav run good'.live.hz with lt | e
    · have := acct.2.2.1
      omega
    · exfalso
      rcases serr.1 e with hn | ⟨hn, -⟩ | hsy
      · rcases hw with ⟨-, hz0⟩ | ⟨r', off', a', hp', -, -, -⟩
        · exact hao (UInt32.toNat_inj.mp (by rw [hz0]; rfl))
        · rw [hp'] at hn; cases hn
      · rw [hnin] at hn; cases hn
      · rw [hmode] at hsy; exact absurd hsy (by decide)
  · intro e ha
    exact (Zlib.Inflate.Proofs.blocked_leave Zlib.Inflate.Proofs.leave_ret_codes Zlib.Inflate.Proofs.gzip_field_leaves
      h (gzStrm i) k s.strm st Z_NO_FLUSH rc after z' iinv fitH bufs act run good'.live.hz (by decide) (by decide)
      (Or.inl e) ha).1
  · rintro (e | e)
    · subst e
      obtain ⟨stream, state, dj, -, -, -, hao', -⟩ :=
        Zlib.Inflate.Proofs.ActiveSourceCut.public_need_dictionary_zero (iinv.to_origin fitH).toDefaultStateJ iinv.alloc
          bufs (Zlib.Inflate.Proofs.ActiveHeader.entry act iinv.good.live) run
      have ez : stream = z' := Option.some.inj (dj.good.live.hz.symm.trans good'.live.hz)
      subst ez
      have := acct.2.2.2.1
      rw [hao'] at this
      omega
    · obtain ⟨-, -, -, hnil⟩ := sEq e
      rw [hnil]; rfl
  · rintro ⟨k2, st2, hk2, hst2, hmode⟩
    rw [hstate] at hk2
    cases hk2
    rw [hk] at hst2
    cases hst2
    obtain ⟨-, hao', hrc⟩ := stuck good1 hmode run good'.live.hz
    refine ⟨?_, hrc⟩
    have := acct.2.2.2.1
    rw [hao'] at this
    omega
  · rintro (e | e)
    · exact ⟨k, st', hstate', good'.live.hs, Or.inl (dataM e)⟩
    · exact ⟨k, st', hstate', good'.live.hs, Or.inr (memM e).1⟩
  · intro ml hz
    rcases msgOk with e | e | e
    · show z'.msg = _ ∨ _
      rw [e]
      exact ml hz
    · exact Or.inl e
    · exact Or.inr e
  · refine ⟨hfs, s', ⟨hrec', invA⟩, rfl, rfl, ?_, ?_, ?_⟩
    · refine Zlib.Inflate.Proofs.BufferFrame.mono_changed frame' ?_
      rintro b (e | io | hh)
      · exact Or.inl e
      · exact soOwned b ⟨s.strm, hgetH, Or.inl ⟨k, st, hstate, hk, io⟩⟩
      · rw [hhead] at hh; cases hh
    · intro b
      have L := ledger b
      constructor
      · intro hl
        rcases L.1 hl with ⟨hl0, -⟩ | ⟨io, nl⟩
        · exact Or.inl ⟨hl0, fun ⟨o, no⟩ => no (O1 b o)⟩
        · exact Or.inr ⟨Or.inr (Or.inr (Or.inr ⟨hsz, Or.inr ⟨Or.inl hm, Or.inr (ownAfter b io)⟩⟩)), nl⟩
      · rintro (⟨hl0, -⟩ | ⟨o, -⟩)
        · exact L.2 (Or.inl ⟨hl0, fun x => x⟩)
        · exact Al b o
    · exact O2

/-! ## Open facts outside this module -/

/-! ## The source, split -/

/-- What follows the `inflate` call: the error checks. -/
def decompErrs (i : Nat) (l : Zlib.Gzread.DecompLoop) (ret : Int32) : G Zlib.Gzread.DecompLoop :=
  if (ret == Z_STREAM_ERROR || ret == Z_NEED_DICT) = true then do
    let m ← StateT.lift (strLit "internal error: inflate stream corrupt")
    StateT.lift (Zlib.Gzlib.gz_error (gzSt i) Z_STREAM_ERROR m)
    pure { ret, brk := true }
  else if (ret == Z_MEM_ERROR) = true then do
    let m ← StateT.lift (strLit "out of memory")
    StateT.lift (Zlib.Gzlib.gz_error (gzSt i) Z_MEM_ERROR m)
    pure { ret, brk := true }
  else if (ret == Z_DATA_ERROR) = true then do
    let s ← StateT.lift (ldS (gzSt i))
    if (s.junk == 1) = true then do
      StateT.lift (updZ (strmOf (gzSt i)) fun z => { z with avail_in := 0 })
      StateT.lift (updS (gzSt i) fun s => { s with eof := 1, how := LOOK })
      pure { ret := Z_OK, brk := true }
    else do
      let z ← StateT.lift (ldZ (strmOf (gzSt i)))
      let msg ← if (z.msg == .null) = true then StateT.lift (strLit "compressed data error") else pure z.msg
      StateT.lift (Zlib.Gzlib.gz_error (gzSt i) Z_DATA_ERROR msg)
      pure { ret, brk := true }
  else pure { l with ret }

/-- The `inflate` call and the `junk` update. -/
def decompRun (i : Nat) (had : UInt32) (l : Zlib.Gzread.DecompLoop) : G Zlib.Gzread.DecompLoop := do
  let ret ← StateT.lift (Zlib.Inflate.inflate (strmOf (gzSt i)) Z_NO_FLUSH)
  let z ← StateT.lift (ldZ (strmOf (gzSt i)))
  if z.avail_out < had then do
    StateT.lift (updS (gzSt i) fun s => { s with junk := 0 })
    decompErrs i l ret
  else decompErrs i l ret

/-- The second input check. -/
def decompMid (i : Nat) (had : UInt32) (l : Zlib.Gzread.DecompLoop) : G Zlib.Gzread.DecompLoop := do
  let z ← StateT.lift (ldZ (strmOf (gzSt i)))
  if (z.avail_in == 0) = true then do
    let s ← StateT.lift (ldS (gzSt i))
    if (s.again == 0) = true then do
      let m ← StateT.lift (strLit "unexpected end of file")
      StateT.lift (Zlib.Gzlib.gz_error (gzSt i) Z_BUF_ERROR m)
      pure { l with brk := true }
    else pure { l with brk := true }
  else decompRun i had l

/-- The body of the loop. -/
def decompBody (i : Nat) (had : UInt32) (l : Zlib.Gzread.DecompLoop) : G Zlib.Gzread.DecompLoop := do
  let z ← StateT.lift (ldZ (strmOf (gzSt i)))
  if (z.avail_in == 0) = true then do
    let r ← Zlib.Gzread.gz_avail (gzSt i)
    if (r == -1) = true then do
      let s ← StateT.lift (ldS (gzSt i))
      pure { ret := s.err, brk := true }
    else decompMid i had l
  else decompMid i had l

/-- The condition of the loop. -/
def decompCond (i : Nat) (l : Zlib.Gzread.DecompLoop) : G (Bool × Zlib.Gzread.DecompLoop) := do
  let z ← StateT.lift (ldZ (strmOf (gzSt i)))
  pure (!l.brk && z.avail_out != 0 && l.ret != Z_STREAM_END, l)

/-- After the loop. -/
def decompTail (i : Nat) (had : UInt32) (l : Zlib.Gzread.DecompLoop) : G Int32 := do
  let z ← StateT.lift (ldZ (strmOf (gzSt i)))
  StateT.lift (updX (gzSt i) fun x => { x with «have» := had - z.avail_out })
  let nx ← StateT.lift (z.next_out.add (-((had - z.avail_out).toNat : Int)))
  StateT.lift (updX (gzSt i) fun x => { x with next := nx })
  if (l.ret == Z_STREAM_END) = true then do
    StateT.lift (updS (gzSt i) fun s => { s with junk := 0, how := LOOK })
    pure 0
  else pure (if l.ret != Z_OK then -1 else 0)

theorem gz_decomp_source (i : Nat) : Zlib.Gzread.gz_decomp (gzSt i) = (do
    let z ← StateT.lift (ldZ (strmOf (gzSt i)))
    let l ← gdoWhile (decompBody i z.avail_out) (decompCond i) { ret := Z_OK, brk := false }
    decompTail i z.avail_out l) := rfl

/-! ## Composing post-conditions -/

theorem live_logic (a a1 a2 o o1 o2 : Prop) (L1 : a1 ↔ (a ∧ ¬ (o ∧ ¬ o1)) ∨ (o1 ∧ ¬ a))
    (L2 : a2 ↔ (a1 ∧ ¬ (o1 ∧ ¬ o2)) ∨ (o2 ∧ ¬ a1)) (N1 : o1 → o ∨ ¬ a) (N2 : o2 → o1 ∨ ¬ a1) :
    (a2 ↔ (a ∧ ¬ (o ∧ ¬ o2)) ∨ (o2 ∧ ¬ a)) ∧ (o2 → o ∨ ¬ a) := by
  rcases Classical.em a with ha | ha <;> rcases Classical.em o with ho | ho <;>
    rcases Classical.em o1 with ho1 | ho1 <;> rcases Classical.em o2 with ho2 | ho2 <;> simp_all

/-- **Two post-conditions compose**, when the second step's regions lie within the first's and the first's
regions are views of blocks the composed frame does not change. -/
theorem post_compose {h0 h1 h2 : Heap} {i : Nat} {s0 s1 : GzState} {fs1 fs2 : Fs} {R S : List Region}
    (p1 : GzPost h0 i s0 R fs1 h1 GzInvUpToOutput) (hs1 : h1.gzstates i = some s1)
    (p2 : GzPost h1 i s1 S fs2 h2 GzInvUpToOutput)
    (within : Zlib.Inflate.Proofs.RegionsWithin S R)
    (views : Zlib.Inflate.Proofs.RegionViews (StartChanged h0 i s0) R) :
    GzPost h0 i s0 R fs2 h2 GzInvUpToOutput := by
  classical
  obtain ⟨-, t1, inv1, m1, f1, bf1, lc1, g1⟩ := p1
  have e : t1 = s1 := Option.some.inj (inv1.1.symm.trans hs1)
  subst e
  obtain ⟨hfs2, t2, inv2, m2, f2, bf2, lc2, g2⟩ := p2
  have n1 : ∀ b, GzOwned h1 i t1 b → h0.live b → GzOwned h0 i s0 b := fun b hb hl =>
    (g1 b hb).elim id (fun hn => absurd hl hn)
  have ntc : ∀ b, GzOwned h1 i t1 b → StartChanged h0 i s0 b := fun b hb =>
    (Classical.em (h0.live b)).elim (fun hl => Or.inl (n1 b hb hl)) Or.inr
  have l := Zlib.Inflate.Proofs.BufferFrame.mono_changed (wider := StartChanged h0 i s0) bf1 (fun b hb => Or.inl hb)
  have r := Zlib.Inflate.Proofs.BufferFrame.mono_changed (wider := StartChanged h0 i s0) bf2 ntc
  have c := Zlib.Infback.Safety.BufferFrame.trans_within' l r within views
  have key : ∀ b, (h2.live b ↔ (h0.live b ∧ ¬ (GzOwned h0 i s0 b ∧ ¬ GzOwned h2 i t2 b)) ∨
      (GzOwned h2 i t2 b ∧ ¬ h0.live b)) ∧ (GzOwned h2 i t2 b → GzOwned h0 i s0 b ∨ ¬ h0.live b) :=
    fun b => live_logic _ _ _ _ _ _ (lc1 b) (lc2 b) (g1 b) (g2 b)
  exact ⟨hfs2, t2, inv2, m2.trans m1, f2.trans f1, ⟨⟨c.1.1, c.1.2.1, c.1.2.2.1, c.1.2.2.2.1, c.1.2.2.2.2.1,
      fun b hl hn => c.1.2.2.2.2.2 b hl (fun hc => hc.elim hn (fun x => x hl))⟩, c.2⟩,
    fun b => (key b).1, fun b => (key b).2⟩

/-- A region list with no regions. -/
theorem views_nil' (C : Nat → Prop) : Zlib.Inflate.Proofs.RegionViews C [] := by
  intro ref ⟨region, hm, _⟩
  cases hm

/-- A region inside `[p, p + n)`. -/
theorem within_one (p : BPtr) (n d m : Nat) (hle : d + m ≤ n) :
    Zlib.Inflate.Proofs.RegionsWithin [⟨padv p d, m⟩] [⟨p, n⟩] := by
  refine ⟨?_, ?_⟩
  · rintro ref ⟨region, mem, off, hp⟩
    rw [List.mem_singleton] at mem
    subst mem
    cases p with
    | null => cases hp
    | ref r o =>
      simp only [padv] at hp
      cases hp
      exact ⟨_, List.mem_singleton_self _, o, rfl⟩
  · rintro ref j ⟨region, mem, off, hp, lo, hi⟩
    rw [List.mem_singleton] at mem
    subst mem
    cases p with
    | null => cases hp
    | ref r o =>
      simp only [padv] at hp
      cases hp
      have hi' : j < o + d + m := hi
      refine ⟨_, List.mem_singleton_self _, o, rfl, by omega, ?_⟩
      show j < o + n
      omega

/-- The embedded codec owns the same blocks after a record write that keeps its state pointer. -/
theorem streamOwned_put {h : Heap} {i : Nat} {s s' : GzState} (hs : h.gzstates i = some s)
    (hz : s'.strm.state = s.strm.state) (b : Nat) :
    StreamOwned (putGz h i s') (.in_gzstate_strm i) b ↔ StreamOwned h (.in_gzstate_strm i) b := by
  have g1 : ZStreamRef.get (putGz h i s') (.in_gzstate_strm i) = some s'.strm := by
    simp [ZStreamRef.get, putGz]
  have g0 : ZStreamRef.get h (.in_gzstate_strm i) = some s.strm := by simp [ZStreamRef.get, hs]
  constructor
  · rintro ⟨z, hz1, rest⟩
    rw [g1] at hz1
    cases hz1
    refine ⟨s.strm, g0, ?_⟩
    rw [← hz]
    exact rest
  · rintro ⟨z, hz1, rest⟩
    rw [g0] at hz1
    cases hz1
    refine ⟨s'.strm, g1, ?_⟩
    rw [hz]
    exact rest

theorem owned_put {h : Heap} {i : Nat} {s s' : GzState} (hs : h.gzstates i = some s)
    (same : s'.path = s.path ∧ s'.msg = s.msg ∧ s'.«in» = s.«in» ∧ s'.out = s.out ∧ s'.size = s.size ∧
      s'.mode = s.mode ∧ s'.direct = s.direct ∧ s'.strm.state = s.strm.state) (b : Nat) :
    GzOwned (putGz h i s') i s' b ↔ GzOwned h i s b := by
  obtain ⟨hpath, hmsg, hin, hout, hsize, hmode, hdirect, hst⟩ := same
  unfold GzOwned
  rw [hpath, hmsg, hin, hout, hsize, hmode, hdirect, streamOwned_put hs hst b]

/-- A record write is a step with no caller region. -/
theorem post_put_rec {h1 : Heap} {i : Nat} {s1 s2 : GzState} {fs : Fs} (hu1 : GzInvUpToOutput h1 i s1)
    (hu2 : GzInvUpToOutput (putGz h1 i s2) i s2) (hfs : FileSystem fs)
    (same : s2.path = s1.path ∧ s2.msg = s1.msg ∧ s2.«in» = s1.«in» ∧ s2.out = s1.out ∧ s2.size = s1.size ∧
      s2.mode = s1.mode ∧ s2.direct = s1.direct ∧ s2.strm.state = s1.strm.state) (hfd : s2.fd = s1.fd) :
    GzPost h1 i s1 [] fs (putGz h1 i s2) GzInvUpToOutput :=
  post_put (post_refl hu1 hfs) hu1.1 hu2 (owned_put hu1.1 same) same.2.2.2.2.2.1 hfd

/-- A frame between two record writes of the same handle is a frame between the heaps, when the changed set has
the record block. -/
theorem frame_unput {A B : Heap} {i : Nat} {u v sa : GzState} (hA : A.gzstates i = some sa) {C : Nat → Prop}
    (hi : C i) (fr : Frame (putGz A i u) (putGz B i v) C) : Frame A B C := by
  refine ⟨fr.1, fr.2.1, fr.2.2.1, fr.2.2.2.1, fr.2.2.2.2.1, fun b hl hc => ?_⟩
  have hbi : b ≠ i := fun e => hc (e ▸ hi)
  have hl' : (putGz A i u).live b := (putGz_live hA b).2 hl
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ := fr.2.2.2.2.2 b hl' hc
  refine ⟨e1, e2, e3, e4, e5, e6, ?_, e8⟩
  have e7' : upd B.gzstates i (some v) b = upd A.gzstates i (some u) b := e7
  rw [upd_ne _ _ _ _ hbi, upd_ne _ _ _ _ hbi] at e7'
  exact e7'

/-- The codec record of the stream is kept from `H` to `after`. -/
def CodecKept (H after : Heap) (s : GzState) : Prop :=
  ∀ k st, s.strm.state = some (.inflate k) → H.istates k = some st → after.istates k = some st

theorem atHead_kept {H after : Heap} {s s' : GzState} (kc : CodecKept H after s) (hst : s'.strm.state = s.strm.state)
    (hd : InflateAtHead H s) : InflateAtHead after s' := by
  obtain ⟨k, st, a, b, c, d, e⟩ := hd
  exact ⟨k, st, by rw [hst]; exact a, kc k st a b, c, d, e⟩

theorem stuck_kept {H after : Heap} {s s' : GzState} (kc : CodecKept H after s) (hst : s'.strm.state = s.strm.state)
    (hd : Stuck H s) : Stuck after s' := by
  obtain ⟨k, st, a, b, c⟩ := hd
  exact ⟨k, st, by rw [hst]; exact a, kc k st a b, c⟩

theorem stuck_put {h : Heap} {i : Nat} {s s' : GzState} (hd : Stuck h s) (hst : s'.strm.state = s.strm.state) :
    Stuck (putGz h i s') s' := by
  obtain ⟨k, st, a, b, c⟩ := hd
  exact ⟨k, st, by rw [hst]; exact a, b, c⟩

theorem stuck_of_put {h : Heap} {i : Nat} {s s' : GzState} (hd : Stuck (putGz h i s') s')
    (hst : s'.strm.state = s.strm.state) : Stuck h s := by
  obtain ⟨k, st, a, b, c⟩ := hd
  exact ⟨k, st, by rw [← hst]; exact a, b, c⟩

/-- **`gz_error` inside a reading call** as a step: the run, the record (error and message changed), and the
post-condition with no caller region. -/
theorem post_gz_error {H : Heap} {i : Nat} {s : GzState} {fs : Fs} (hu : GzInvUpToOutput H i s)
    (hfs : FileSystem fs) (err : Int32) (msg : BPtr)
    (hmsg : msg = .null ∨ ∃ t, CString H msg t ∧ ∀ b, ¬ ByteRoot msg b) (he : err ≠ Z_STREAM_END) :
    ∃ after s', C.run (Zlib.Gzlib.gz_error (gzSt i) err msg) H = .ok ((), after) ∧ after.gzstates i = some s' ∧
      s' = { s with err := s'.err, msg := s'.msg } ∧ (s'.err = err ∨ s'.err = Z_MEM_ERROR) ∧
      CodecKept H after s ∧
      GzPost H i s [] fs after GzInvUpToOutput := by
  have hmsg' : msg = .null ∨ ∃ t, CString H msg t ∧
      ∀ b, ByteRoot msg b → ¬ GzOwned (putGz H i (clearOut s)) i (clearOut s) b := by
    rcases hmsg with hn | ⟨t, ct, hno⟩
    · exact Or.inl hn
    · exact Or.inr ⟨t, ct, fun b hb => absurd hb (hno b)⟩
  obtain ⟨after, s', run, hs', shape, inv', -, errs, fr, lc, -, -, ng, keep⟩ := gz_error_upToOutput hu err msg hmsg' he
  have hs := hu.1
  have inv := hu.2
  have ownA : ∀ b, GzOwned (putGz after i (clearOut s')) i (clearOut s') b ↔ GzOwned after i s' b :=
    putGz_owned (s' := clearOut s') hs' ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have ownH : ∀ b, GzOwned (putGz H i (clearOut s)) i (clearOut s) b ↔ GzOwned H i s b :=
    putGz_owned (s' := clearOut s) hs ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have liveA : ∀ b, (putGz after i (clearOut s')).live b ↔ after.live b := fun b => putGz_live hs' b
  have liveH : ∀ b, (putGz H i (clearOut s)).live b ↔ H.live b := fun b => putGz_live hs b
  have msgOwned : ∀ b, blkOf s.msg = some b → GzOwned H i s b := fun b hb =>
    (ownH b).1 (GzInv.msg_owned inv hb)
  have msgOwned' : ∀ b, blkOf s'.msg = some b → GzOwned after i s' b := fun b hb =>
    (ownA b).1 (GzInv.msg_owned inv' hb)
  have fr' : Frame H after (fun b => b = i ∨ blkOf s.msg = some b) := frame_unput hs (Or.inl rfl) fr
  refine ⟨after, s', run, hs', shape, errs.imp id (fun e => e.1), ?_, hfs, s', ⟨hs', inv'⟩, by rw [shape],
    by rw [shape],
    BufferFrame.nil_of_frame (Frame.mono' fr' ?_), ?_, ?_⟩
  · intro k st hst hk
    have hlk : H.live k := Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by rw [hk]; intro x; cases x))))))
    have so : StreamOwned H (gzStrm i) k :=
      ⟨s.strm, by simp [ZStreamRef.get, gzStrm, hs], Or.inl ⟨k, st, hst, hk, Or.inl rfl⟩⟩
    have so' : StreamOwned (putGz H i (clearOut s)) (gzStrm i) k :=
      (Iff.of_eq (putGz_streamOwned (s' := clearOut s) hs rfl k)).2 so
    have nc : ¬ (k = i ∨ blkOf s.msg = some k) := by
      rintro (e | e)
      · subst e; exact inv.common.recordFree so'
      · exact (inv.common.distinct.2 s.msg (by simp [ownedPtrs, clearOut]) k e).2 so'
    obtain ⟨-, -, -, -, -, e6, -⟩ := fr'.2.2.2.2.2 k hlk nc
    rw [e6]; exact hk
  · rintro b (e | e)
    · exact Or.inl e
    · exact msgOwned b e
  · intro b
    have L' : after.live b ↔ (H.live b ∧ ¬ blkOf s.msg = some b) ∨ (blkOf s'.msg = some b ∧ ¬ H.live b) := by
      have L := lc b
      simp only [] at L
      rw [liveA, liveH] at L
      exact L
    have o2l : GzOwned after i s' b → after.live b := fun ho => (liveA b).1 (inv'.common.live b ((ownA b).2 ho))
    have k1 : GzOwned H i s b → ¬ blkOf s.msg = some b → GzOwned after i s' b := fun ho hn =>
      (ownA b).1 (keep b ((ownH b).2 ho) hn)
    constructor
    · intro hl
      rcases L'.1 hl with ⟨hl0, hnm⟩ | ⟨hm, nl⟩
      · exact Or.inl ⟨hl0, fun ⟨o, no⟩ => no (k1 o hnm)⟩
      · exact Or.inr ⟨msgOwned' b hm, nl⟩
    · rintro (⟨hl0, hno⟩ | ⟨o, nl⟩)
      · by_cases hm : blkOf s.msg = some b
        · exact o2l (Classical.byContradiction fun no => hno ⟨msgOwned b hm, no⟩)
        · exact L'.2 (Or.inl ⟨hl0, hm⟩)
      · exact o2l o
  · intro b hb
    rcases ng b ((ownA b).2 hb) with e | e
    · exact Or.inl ((ownH b).1 e)
    · exact Or.inr (fun hl => e ((liveH b).2 hl))

/-- An owned block of a handle in `GzInvUpToOutput` is live. -/
theorem upTo_live {h : Heap} {i : Nat} {s : GzState} (hu : GzInvUpToOutput h i s) (b : Nat) (ho : GzOwned h i s b) :
    h.live b :=
  (putGz_live hu.1 b).1 (hu.2.common.live b
    ((putGz_owned (s' := clearOut s) hu.1 ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ b).2 ho))

/-! ## The state of the loop -/

/-- The regions of `gz_decomp`'s post-condition. -/
def outRegions (out : Region) (s0 : GzState) : List Region := if out.pointer = s0.out then [] else [out]

/-- The loop state: the record, the invariant, the effect so far, the kept fields, the output window, the
input left and the read budget. -/
structure Base (i : Nat) (out : Region) (h0 : Heap) (fs0 : Fs) (s0 : GzState) (fs : Fs) (h : Heap) (s : GzState) :
    Prop where
  rcd : h.gzstates i = some s
  inv : GzInvUpToOutput h i s
  kept : FdsKept fs0 fs
  post : GzPost h0 i s0 (outRegions out s0) fs h GzInvUpToOutput
  keep : s.mode = s0.mode ∧ s.fd = s0.fd ∧ s.skip = s0.skip ∧ s.x.pos = s0.x.pos ∧ s.size = s0.size ∧
    s.out = s0.out ∧ s.«in» = s0.«in»
  pos : ∃ d, s.strm.next_out = padv out.pointer d ∧ d + s.strm.avail_out.toNat = out.length
  wr : Writable h out.pointer out.length
  side : (∀ b, ByteRoot out.pointer b → ¬ GzOwned h i s b) ∨ out.pointer = s0.out
  rf : HasBudget fs0 s0.fd → HasBudget fs s0.fd ∧ inputLeft fs s ≤ inputLeft fs0 s0
  rb : ReadsFinite fs0 s0.fd → ReadsFinite fs s0.fd
  err : s0.err ≠ Z_STREAM_END → s.err ≠ Z_STREAM_END
  ml : MsgLit s
  bud : BudgetAcc s0.fd fs0 fs 0

/-- The view of a writable range keeps its size across a frame that does not change its block. -/
theorem bf_view {h a : Heap} {C : Nat → Prop} {R : List Region} (bf : BufferFrame h a C R) {r : BRef}
    {x : Array UInt8} (hx : Space.get h r = some x)
    (kind : (∃ b, r = .blk b ∧ ¬ C b) ∨ (∃ b, r = .dstate_depth b ∧ ¬ C b)) :
    ∃ y, Space.get a r = some y ∧ y.size = x.size := by
  by_cases hr : Zlib.Inflate.Proofs.RegionRoot R r
  · obtain ⟨region, mem, off, hp⟩ := hr
    obtain ⟨y, hy, hsz, -⟩ := bf.2 region mem r off x hp hx
    exact ⟨y, hy, hsz⟩
  · exact ⟨x, Zlib.Inflate.Proofs.BufferFrame.view_kept bf hr kind hx, rfl⟩

/-- A writable range whose block the step does not change stays writable. -/
theorem writable_step {h a : Heap} {C : Nat → Prop} {R : List Region} (bf : BufferFrame h a C R) {p : BPtr}
    {n : Nat} (w : Writable h p n) (hn : n ≠ 0) (hc : ∀ b, ByteRoot p b → ¬ C b) : Writable a p n := by
  rcases w with ⟨-, hz⟩ | ⟨r, off, x, hp, hx, hro, hfit⟩
  · exact absurd hz hn
  subst hp
  cases r with
  | blk b =>
    have hcb : ¬ C b := hc b rfl
    obtain ⟨y, hy, hsz⟩ := bf_view bf hx (Or.inl ⟨b, rfl, hcb⟩)
    have hl : h.live b := Or.inl (by have : h.bytes b = some x := hx; rw [this]; intro e; cases e)
    have ro := (bf_tables bf hl hcb).1
    exact Or.inr ⟨.blk b, off, y, rfl, hy, by show a.ro b = false; rw [ro]; exact hro, by omega⟩
  | dstate_depth b =>
    obtain ⟨y, hy, hsz⟩ := bf_view bf hx (Or.inr ⟨b, rfl, hc b rfl⟩)
    exact Or.inr ⟨.dstate_depth b, off, y, rfl, hy, rfl, by omega⟩
  | str j => simp [Space.ro] at hro
  | st_dist_code => simp [Space.ro] at hro
  | st_length_code => simp [Space.ro] at hro

/-- The root of a writable nonempty range is live. -/
theorem writable_live {h : Heap} {p : BPtr} {n : Nat} (w : Writable h p n) (hn : n ≠ 0) {b : Nat}
    (hb : ByteRoot p b) : h.live b := by
  rcases w with ⟨-, hz⟩ | ⟨r, off, x, hp, hx, -, -⟩
  · exact absurd hz hn
  subst hp
  cases r with
  | blk c =>
    have e : b = c := hb
    subst e
    exact Or.inl (by have : h.bytes b = some x := hx; rw [this]; intro e; cases e)
  | dstate_depth c =>
    have e : b = c := hb
    subst e
    have : (h.dstates b).map (·.depth) = some x := hx
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
    intro e; rw [e] at this; cases this
  | str j => cases hb
  | st_dist_code => cases hb
  | st_length_code => cases hb

/-- **One step of the loop keeps its state**: a step with no caller region, or with a region inside the output
window. -/
theorem Base.step {i : Nat} {out : Region} {h0 : Heap} {fs0 : Fs} {s0 : GzState} {fs fs' : Fs} {h h' : Heap}
    {s s' : GzState} (B : Base i out h0 fs0 s0 fs h s) {S : List Region}
    (p : GzPost h i s S fs' h' GzInvUpToOutput) (hs' : h'.gzstates i = some s') (kept : FdsKept fs fs')
    (within : S = [] ∨ ∃ d m, S = [⟨padv out.pointer d, m⟩] ∧ d + m ≤ out.length)
    (keep : s'.mode = s.mode ∧ s'.fd = s.fd ∧ s'.skip = s.skip ∧ s'.x.pos = s.x.pos ∧ s'.size = s.size ∧
      s'.out = s.out ∧ s'.«in» = s.«in»)
    (pos : ∃ d, s'.strm.next_out = padv out.pointer d ∧ d + s'.strm.avail_out.toNat = out.length)
    (rf : HasBudget fs0 s0.fd → HasBudget fs' s0.fd ∧ inputLeft fs' s' ≤ inputLeft fs0 s0)
    (rb : ReadsFinite fs0 s0.fd → ReadsFinite fs' s0.fd)
    (err : s0.err ≠ Z_STREAM_END → s'.err ≠ Z_STREAM_END) (ml : MsgLit s')
    (hlen : out.length ≠ 0) (hm0 : s0.mode = GZ_READ) (hsz0 : s0.size ≠ 0)
    (outLen : out.pointer = s0.out → out.length ≤ 2 * s0.size.toNat)
    (views : Zlib.Inflate.Proofs.RegionViews (StartChanged h0 i s0) (outRegions out s0))
    (bud : BudgetAcc s0.fd fs fs' 0) :
    Base i out h0 fs0 s0 fs' h' s' := by
  obtain ⟨hfs', t, inv', hmo, hfdp, bf, lc, ng⟩ := p
  have et : t = s' := Option.some.inj (inv'.1.symm.trans hs')
  rw [et] at inv' ng lc hmo hfdp
  obtain ⟨em, efd, esk, epos, esz, eout, ein⟩ := keep
  obtain ⟨em0, efd0, esk0, epos0, esz0, eout0, ein0⟩ := B.keep
  have hm : s.mode = GZ_READ := em0.trans hm0
  have hsz : s.size ≠ 0 := by rw [esz0]; exact hsz0
  -- the out block is owned when the window is `out`
  have post' : GzPost h i s (if out.pointer = s0.out then [] else S) fs' h' GzInvUpToOutput := by
    by_cases hB : out.pointer = s0.out
    · rw [if_pos hB]
      rcases within with hS | ⟨d, m, hS, -⟩
      · rw [← hS]; exact ⟨hfs', s', inv', hmo, hfdp, bf, lc, ng⟩
      · subst hS
        obtain ⟨ob, oarr, hob, -, -, -⟩ := ((B.inv.2.reader hm).bufs hsz).2
        have hob' : s.out = .ref (.blk ob) 0 := hob
        have hp : padv out.pointer d = .ref (.blk ob) (0 + d) := by rw [hB, ← eout0, hob']; rfl
        rw [hp] at bf
        have own : GzOwned h i s ob := Or.inr (Or.inr (Or.inr ⟨hsz, Or.inr ⟨Or.inl hm, Or.inl hob'⟩⟩))
        exact ⟨hfs', s', inv', hmo, hfdp, BufferFrame.nil_of_frame (frame_of_bf_blk bf own), lc, ng⟩
    · rw [if_neg hB]
      exact ⟨hfs', s', inv', hmo, hfdp, bf, lc, ng⟩
  have within' : Zlib.Inflate.Proofs.RegionsWithin (if out.pointer = s0.out then [] else S) (outRegions out s0) := by
    unfold outRegions
    by_cases hB : out.pointer = s0.out
    · rw [if_pos hB, if_pos hB]; exact Zlib.Inflate.Proofs.RegionsWithin.nil _
    · rw [if_neg hB, if_neg hB]
      rcases within with hS | ⟨d, m, hS, hle⟩
      · rw [hS]; exact Zlib.Inflate.Proofs.RegionsWithin.nil _
      · rw [hS]; exact within_one out.pointer out.length d m hle
  -- the window stays writable
  have wr' : Writable h' out.pointer out.length := by
    rcases B.side with hA | hB
    · exact writable_step bf B.wr hlen (fun b hb ho => hA b hb ho)
    · obtain ⟨ob, oarr, hob, hb, hro, hn⟩ := ((inv'.2.reader (em.trans hm)).bufs
        (by show s'.size ≠ 0; rw [esz]; exact hsz)).2
      have hob' : s'.out = .ref (.blk ob) 0 := hob
      rw [hB, ← eout0, ← eout, hob']
      refine Or.inr ⟨.blk ob, 0, oarr, rfl, hb, hro, ?_⟩
      have hn' : oarr.size = 2 * s'.size.toNat := hn
      have := outLen hB
      rw [hn', esz, esz0]
      omega
  refine ⟨hs', ⟨hs', inv'.2⟩, fun j => (kept j).trans (B.kept j),
    post_compose B.post B.rcd post' within' views,
    ⟨em.trans em0, efd.trans efd0, esk.trans esk0, epos.trans epos0, esz.trans esz0, eout.trans eout0,
      ein.trans ein0⟩, pos, wr', ?_, rf, rb, err, ml, (B.bud.trans bud).mono (Nat.zero_le _)⟩
  rcases B.side with hA | hB
  · left
    intro b hb ho
    rcases ng b ho with o | nl
    · exact hA b hb o
    · exact nl (writable_live B.wr hlen hb)
  · exact Or.inr hB

theorem GzInv.zero_input {h : Heap} {i : Nat} {s : GzState} (inv : GzInv h i s) (hm0 : s.mode = GZ_READ)
    (hz0 : s.size ≠ 0) :
    GzInv (putGz h i { s with strm := { s.strm with avail_in := 0 } }) i
      { s with strm := { s.strm with avail_in := 0 } } ∧
    (∀ b, GzOwned (putGz h i { s with strm := { s.strm with avail_in := 0 } }) i
      { s with strm := { s.strm with avail_in := 0 } } b ↔ GzOwned h i s b) := by
  have c := inv.common
  have hs := c.record
  have gH : ZStreamRef.get (putGz h i { s with strm := { s.strm with avail_in := 0 } }) (gzStrm i) =
      some { s.strm with avail_in := 0 } := by
    simp [ZStreamRef.get, gzStrm, putGz]
  have gh : ZStreamRef.get h (gzStrm i) = some s.strm := by simp [ZStreamRef.get, gzStrm, hs]
  have hso : ∀ b, StreamOwned (putGz h i { s with strm := { s.strm with avail_in := 0 } }) (gzStrm i) b ↔
      StreamOwned h (gzStrm i) b := by
    intro b
    unfold StreamOwned
    rw [gH, gh]
    simp only [Option.some.injEq, exists_eq_left']
    try rfl
  have hso' : ∀ b, StreamOwned (putGz h i { s with strm := { s.strm with avail_in := 0 } })
      (.in_gzstate_strm i) b ↔ StreamOwned h (.in_gzstate_strm i) b := hso
  have hown : ∀ b, GzOwned (putGz h i { s with strm := { s.strm with avail_in := 0 } }) i
      { s with strm := { s.strm with avail_in := 0 } } b ↔ GzOwned h i s b := by
    intro b
    unfold GzOwned
    dsimp only
    rw [hso']
  have hreb : Rebuffer h (putGz h i { s with strm := { s.strm with avail_in := 0 } }) (gzStrm i) := by
    refine ⟨putGz_fresh hs c.fresh, putGz_uniq hs c.uniq, c.globals, ?_, s.strm,
      { s.strm with avail_in := 0 }, gh, gH, rfl⟩
    refine ⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _, ?_⟩
    intro b _ hb
    have hbi : b ≠ i := by
      intro e
      subst e
      exact hb c.recordFree
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, by simp [putGz, upd_ne _ _ _ _ hbi], rfl⟩
  have fitH := putGz_fit (s' := { s with strm := { s.strm with avail_in := 0 } }) (i := i) c.fit
  refine ⟨⟨?_, ?_, ?_⟩, hown⟩
  · exact {
      record := by simp [putGz]
      mode := c.mode
      fresh := putGz_fresh hs c.fresh
      uniq := putGz_uniq hs c.uniq
      globals := c.globals
      fit := fitH
      path := by
        obtain ⟨p, hp, hm⟩ := c.path
        exact ⟨p, (putGz_cstring _ _).2 hp, hm⟩
      msg := by
        rcases c.msg with hn | ⟨m, hm, hb⟩
        · exact Or.inl hn
        · exact Or.inr ⟨m, (putGz_cstring _ _).2 hm, hb⟩
      memerr := c.memerr
      want := c.want
      size := c.size
      distinct := ⟨c.distinct.1, fun p hp b hb =>
        ⟨(c.distinct.2 p hp b hb).1, by rw [hso]; exact (c.distinct.2 p hp b hb).2⟩⟩
      live := fun b hb => (putGz_live hs b).2 (c.live b ((hown b).1 hb))
      pos := c.pos
      next := fun hh => by
        obtain ⟨b, off, a, hx, hbi, ho, hmb, hb, hle⟩ := c.next hh
        exact ⟨b, off, a, hx, hbi, (hown b).2 ho, hmb, hb, hle⟩
      nullHave := c.nullHave
      recordFree := by rw [hso]; exact c.recordFree }
  · intro hm
    have r := inv.reader hm
    exact {
      how := r.how
      copyDirect := r.copyDirect
      gzipDirect := r.gzipDirect
      direct := r.direct
      junk := r.junk
      flags := r.flags
      unalloc := fun hz => absurd hz hz0
      bufs := r.bufs
      input := Or.inl rfl
      output := r.output
      codec := fun hz => by
        obtain ⟨reach, z, k, st, hzget, hzst, hk, hhead⟩ := r.codec hz
        have hz' : z = s.strm := by rw [gh] at hzget; exact (Option.some.inj hzget).symm
        subst hz'
        exact ⟨StreamReachable.rebuffer reach hreb (fun _ => fitH), _, k, st, gH, hzst, hk, hhead⟩
      posHave := r.posHave
      againSize := r.againSize
      haveSkip := r.haveSkip
      againEof := fun _ _ => rfl
      errEnd := r.errEnd
      copyIn := fun _ => rfl
      msgLit := r.msgLit }
  · intro hm
    exact absurd (hm0.symm.trans hm) (by decide)



/-- `avail_in = 0` inside a reading call. -/
theorem upto_zero_input {h : Heap} {i : Nat} {s : GzState} (hu : GzInvUpToOutput h i s) (hm : s.mode = GZ_READ)
    (hz0 : s.size ≠ 0) :
    GzInvUpToOutput (putGz h i { s with strm := { s.strm with avail_in := 0 } }) i
      { s with strm := { s.strm with avail_in := 0 } } := by
  obtain ⟨hs, inv⟩ := hu
  have r := (GzInv.zero_input inv hm hz0).1
  refine ⟨by simp [putGz], ?_⟩
  have e : putGz (putGz h i { s with strm := { s.strm with avail_in := 0 } }) i
      (clearOut { s with strm := { s.strm with avail_in := 0 } }) =
      putGz (putGz h i (clearOut s)) i { clearOut s with strm := { (clearOut s).strm with avail_in := 0 } } := by
    simp only [putGz, upd_upd]; rfl
  rw [e]
  exact r

/-- A scalar write of the record inside a reading call. -/
theorem upto_put {h : Heap} {i : Nat} {s s2 : GzState} (hu : GzInvUpToOutput h i s) (hm : s.mode = GZ_READ)
    (same : s2.path = s.path ∧ s2.msg = s.msg ∧ s2.«in» = s.«in» ∧ s2.out = s.out ∧ s2.size = s.size ∧
      s2.mode = s.mode ∧ s2.direct = s.direct ∧ s2.strm = s.strm ∧ s2.err = s.err ∧ s2.want = s.want ∧
      s2.x.pos = s.x.pos ∧ s2.skip = s.skip)
    (rd : (s2.how = LOOK ∨ s2.how = GZ_COPY ∨ s2.how = GZIP) ∧ (s2.how = GZ_COPY → s2.direct = 0 ∨ s2.direct = 1) ∧
      (s2.how = GZIP → s2.direct = 0) ∧ (s2.junk = -1 ∨ s2.junk = 0 ∨ s2.junk = 1) ∧
      (s2.eof = 0 ∨ s2.eof = 1) ∧ (s2.past = 0 ∨ s2.past = 1) ∧ (s2.again = 0 ∨ s2.again = 1) ∧
      (s.size = 0 → s2.how = LOOK) ∧ (s.size = 0 → s2.again = 0) ∧
      (s2.again ≠ 0 → s2.eof ≠ 0 → s2.strm.avail_in = 0))
    (hcp : s2.how = GZ_COPY → s2.strm.avail_in = 0) :
    GzInvUpToOutput (putGz h i s2) i s2 := by
  obtain ⟨hs, inv⟩ := hu
  have c := inv.common
  have rr := inv.reader hm
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12⟩ := same
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10⟩ := rd
  refine ⟨by simp [putGz], ?_⟩
  have e : putGz (putGz h i s2) i (clearOut s2) = putGz (putGz h i (clearOut s)) i (clearOut s2) := by
    simp only [putGz, upd_upd]
  rw [e]
  have p := c.pos
  have ph := rr.posHave
  simp only [clearOut] at p ph
  refine GzInv.put_scalars inv ⟨e1, e2, e3, e4, e5, e6, e7, e8, rfl, e9⟩
    ⟨by show 8 ≤ s2.want.toNat; rw [e10]; exact c.want.1, by show s2.want.toNat < 2 ^ 31; rw [e10]; exact c.want.2,
      Or.inr e10⟩ ?_ (Nat.le_refl _) ?_ (fun hw => absurd (hm.symm.trans hw) (by decide)) (fun _ => hcp)
  · show 0 ≤ s2.skip.toInt ∧ s2.x.pos.toInt + s2.skip.toInt ≤ 9223372036854775807 ∧ 0 ≤ s2.x.pos.toInt + (0 : UInt32).toNat
    rw [e11, e12]
    exact p
  · intro _
    refine ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, ?_, fun hh => absurd rfl hh, r10⟩
    show s2.x.pos.toInt + (0 : UInt32).toNat ≤ 9223372036854775807
    rw [e11]
    exact ph

/-- A write of `x.have` and `x.next` inside a reading call: the invariant up to the buffered output ignores them. -/
theorem upto_x {h : Heap} {i : Nat} {s : GzState} (hu : GzInvUpToOutput h i s) (hv : UInt32) (nx : BPtr) :
    GzInvUpToOutput (putGz h i { s with x := { s.x with «have» := hv, next := nx } }) i
      { s with x := { s.x with «have» := hv, next := nx } } := by
  obtain ⟨hs, inv⟩ := hu
  refine ⟨by simp [putGz], ?_⟩
  have ec : clearOut { s with x := { s.x with «have» := hv, next := nx } } = clearOut s := rfl
  rw [ec, putGz_putGz']
  exact inv

/-! ## The transitions of the loop -/

/-- The static facts of a `gz_decomp` call. -/
structure Stat (i : Nat) (out : Region) (h0 : Heap) (s0 : GzState) : Prop where
  hlen : out.length ≠ 0
  hm0 : s0.mode = GZ_READ
  hsz0 : s0.size ≠ 0
  outLen : out.pointer = s0.out → out.length ≤ 2 * s0.size.toNat
  views : Zlib.Inflate.Proofs.RegionViews (StartChanged h0 i s0) (outRegions out s0)

theorem writable_suffix {h : Heap} {p : BPtr} {n d m : Nat} (w : Writable h p n) (hdm : d + m = n) (hm : m ≠ 0) :
    Writable h (padv p d) m := by
  rcases w with ⟨-, hz⟩ | ⟨r, off, a, hp, ha, hro, hfit⟩
  · omega
  · subst hp
    exact Or.inr ⟨r, off + d, a, rfl, ha, hro, by omega⟩

theorem byteRoot_padv {p : BPtr} {d b : Nat} (hb : ByteRoot (padv p d) b) : ByteRoot p b := by
  cases p with
  | null => cases hb
  | ref r o => cases r <;> exact hb

theorem advance_padv (p : BPtr) (d m : Nat) : advance (padv p d) m = padv p (d + m) := by
  cases p with
  | null => rfl
  | ref r o => simp [advance, padv, Nat.add_assoc]

theorem inputLeft_strm (fs : Fs) (s : GzState) (z : ZStream) :
    inputLeft fs { s with strm := z } = inputLeft fs s - s.strm.avail_in.toNat + z.avail_in.toNat := by
  unfold inputLeft
  simp only
  omega

section trans
variable {i : Nat} {out : Region} {h0 : Heap} {fs0 : Fs} {s0 : GzState}

theorem Base.mode (St : Stat i out h0 s0) {fs : Fs} {h : Heap} {s : GzState} (B : Base i out h0 fs0 s0 fs h s) :
    s.mode = GZ_READ := B.keep.1.trans St.hm0

theorem Base.size (St : Stat i out h0 s0) {fs : Fs} {h : Heap} {s : GzState} (B : Base i out h0 fs0 s0 fs h s) :
    s.size ≠ 0 := by rw [B.keep.2.2.2.2.1]; exact St.hsz0

/-- **`gz_avail`** as a transition. -/
theorem avail_trans (St : Stat i out h0 s0) {fs : Fs} {h : Heap} {s : GzState} (B : Base i out h0 fs0 s0 fs h s)
    (hnc : s.how ≠ GZ_COPY) :
    ∃ r fs' h' s', Zlib.Gzread.gz_avail (gzSt i) fs h = .ok ((r, fs'), h') ∧ (r = 0 ∨ r = -1) ∧
      h'.gzstates i = some s' ∧ Base i out h0 fs0 s0 fs' h' s' ∧ AvailRec s s' ∧ AvailFlags r s s' ∧
      (∀ k, h'.istates k = h.istates k) ∧ (HasBudget fs0 s0.fd → inputLeft fs' s' ≤ inputLeft fs s) := by
  have hm := B.mode St
  have hsz := B.size St
  have hfs : FileSystem fs := B.post.1
  obtain ⟨-, ex, post⟩ := gz_avail_safe i h fs s B.inv hm hfs hsz hnc
  obtain ⟨r, fs', h', run⟩ := ex trivial
  obtain ⟨hr, kept, p, s', hs', hrec, hafs, hflags, hist⟩ := post _ _ _ run
  obtain ⟨bud1, bud2, bud3⟩ := gz_avail_budget i h fs s B.inv hm hfs hsz hnc run s' hs'
  have e := hrec
  simp only [AvailRec] at e
  have hfd : s.fd = s0.fd := B.keep.2.1
  rw [hfd] at bud1 bud2
  refine ⟨r, fs', h', s', run, hr, hs', ?_, hrec, hflags, hist,
    fun h0f => (bud1 (B.rf h0f).1).2⟩
  refine Base.step B p hs' kept (Or.inl rfl)
    ⟨by rw [e], by rw [e], by rw [e], by rw [e], by rw [e], by rw [e], by rw [e]⟩ ?_ ?_ ?_ ?_
    (by rw [e]; exact B.ml) St.hlen St.hm0 St.hsz0 St.outLen St.views
    (by rw [← hfd]; exact hafs.1.mono (Nat.zero_le _))
  · obtain ⟨d, hd, hdl⟩ := B.pos
    exact ⟨d, by rw [e]; exact hd, by rw [e]; exact hdl⟩
  · intro h0f
    obtain ⟨f1, l1⟩ := B.rf h0f
    obtain ⟨f2, l2⟩ := bud1 f1
    exact ⟨f2, Nat.le_trans l2 l1⟩
  · exact fun h0b => bud2 (B.rb h0b)
  · exact fun he => bud3 (B.err he)

/-- **One `inflate` call** as a transition. -/
theorem inflate_trans (head : InflateHeadUsesInput) (stuck : InflateStuckNoOutput) (St : Stat i out h0 s0) {fs : Fs} {h : Heap} {s : GzState} (B : Base i out h0 fs0 s0 fs h s)
    (hav : s.strm.avail_in ≠ 0) (hao : s.strm.avail_out ≠ 0) :
    ∃ rc after z' used produced,
      C.run (Zlib.Inflate.inflate (some (gzStrm i)) Z_NO_FLUSH) h = .ok (rc, after) ∧
      after.gzstates i = some { s with strm := z' } ∧ Base i out h0 fs0 s0 fs after { s with strm := z' } ∧
      StreamAccounting s.strm z' used produced ∧
      (rc = Z_OK ∨ rc = Z_STREAM_END ∨ rc = Z_NEED_DICT ∨ rc = Z_STREAM_ERROR ∨
        rc = Z_DATA_ERROR ∨ rc = Z_MEM_ERROR ∨ rc = Z_BUF_ERROR) ∧
      (rc = Z_OK → used ≠ 0 ∨ produced ≠ 0) ∧ rc ≠ Z_BUF_ERROR ∧
      (InflateAtHead h s → used ≠ 0) ∧
      (rc = Z_OK → z'.avail_in ≠ 0 → z'.avail_out = 0) ∧
      (rc = Z_NEED_DICT ∨ rc = Z_STREAM_ERROR → produced = 0) ∧
      (Stuck h s → produced = 0 ∧ (rc = Z_DATA_ERROR ∨ rc = Z_MEM_ERROR)) ∧
      (rc = Z_DATA_ERROR ∨ rc = Z_MEM_ERROR → Stuck after { s with strm := z' }) := by
  have hm := B.mode St
  have hsz := B.size St
  have hfs : FileSystem fs := B.post.1
  obtain ⟨d, hd, hdl⟩ := B.pos
  have hw : Writable h s.strm.next_out s.strm.avail_out.toNat := by
    rw [hd]
    exact writable_suffix B.wr hdl (fun e => hao (UInt32.toNat_inj.mp (by rw [e]; rfl)))
  have side : OutSide h i s s.strm.next_out := by
    rcases B.side with hA | hB
    · left
      intro b hb
      rw [hd] at hb
      exact hA b (byteRoot_padv hb)
    · right
      exact ⟨d, by rw [hd, hB, ← B.keep.2.2.2.2.2.1]⟩
  obtain ⟨rc, after, z', used, produced, run, hrec', acct, codes, pOK, pBUF, pHead, pFull, pDict, pStuck, pStuck',
    pMsg, post⟩ := inflate_step head stuck fs hfs B.inv hm hsz hav hw side
  rw [hd] at post
  refine ⟨rc, after, z', used, produced, run, hrec', ?_, acct, codes, pOK, fun e => pBUF e hao,
    fun hd => pHead hd hao, pFull, pDict, pStuck, pStuck'⟩
  refine Base.step B post hrec' (fun _ => Iff.rfl) (Or.inr ⟨d, produced, rfl, by have := acct.2.1; omega⟩)
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ ?_ ?_ B.rb B.err (pMsg B.ml) St.hlen St.hm0 St.hsz0 St.outLen St.views
    (BudgetAcc.refl _ _)
  · refine ⟨d + produced, ?_, ?_⟩
    · show z'.next_out = _
      rw [acct.2.2.2.2.2.1, hd, advance_padv]
    · show d + produced + z'.avail_out.toNat = out.length
      have := acct.2.2.2.1
      omega
  · intro h0f
    obtain ⟨f1, l1⟩ := B.rf h0f
    refine ⟨f1, ?_⟩
    rw [inputLeft_strm]
    have := acct.2.2.1
    have : s.strm.avail_in.toNat ≤ inputLeft fs s := by unfold inputLeft; omega
    omega

/-- **A record write** as a transition. -/
theorem put_trans (St : Stat i out h0 s0) {fs : Fs} {h : Heap} {s s2 : GzState} (B : Base i out h0 fs0 s0 fs h s)
    (hu2 : GzInvUpToOutput (putGz h i s2) i s2)
    (same : s2.path = s.path ∧ s2.msg = s.msg ∧ s2.«in» = s.«in» ∧ s2.out = s.out ∧ s2.size = s.size ∧
      s2.mode = s.mode ∧ s2.direct = s.direct ∧ s2.strm.state = s.strm.state)
    (keep : s2.fd = s.fd ∧ s2.skip = s.skip ∧ s2.x.pos = s.x.pos)
    (hno : s2.strm.next_out = s.strm.next_out) (hao : s2.strm.avail_out = s.strm.avail_out)
    (hai : s2.strm.avail_in.toNat ≤ s.strm.avail_in.toNat) (herr : s2.err = s.err) (hml : MsgLit s2) :
    Base i out h0 fs0 s0 fs (putGz h i s2) s2 := by
  obtain ⟨d, hd, hdl⟩ := B.pos
  refine Base.step B (post_put_rec B.inv hu2 B.post.1 same keep.1) (by simp [putGz]) (fun _ => Iff.rfl)
    (Or.inl rfl) ⟨same.2.2.2.2.2.1, keep.1, keep.2.1, keep.2.2, same.2.2.2.2.1, same.2.2.2.1, same.2.2.1⟩
    ⟨d, by rw [hno]; exact hd, by rw [hao]; exact hdl⟩ ?_ B.rb (fun he => by rw [herr]; exact B.err he) hml
    St.hlen St.hm0 St.hsz0 St.outLen St.views (BudgetAcc.refl _ _)
  intro h0f
  obtain ⟨f1, l1⟩ := B.rf h0f
  refine ⟨f1, Nat.le_trans ?_ l1⟩
  unfold inputLeft
  rw [keep.1]
  omega

/-- **`gz_error`** as a transition. -/
theorem err_trans (St : Stat i out h0 s0) {fs : Fs} {h : Heap} {s : GzState} (B : Base i out h0 fs0 s0 fs h s)
    (err : Int32) (herr : err ≠ Z_STREAM_END) (msg : BPtr)
    (hmsg : msg = .null ∨ ∃ t, CString h msg t ∧ ∀ b, ¬ ByteRoot msg b) :
    ∃ after s', C.run (Zlib.Gzlib.gz_error (gzSt i) err msg) h = .ok ((), after) ∧ after.gzstates i = some s' ∧
      s' = { s with err := s'.err, msg := s'.msg } ∧ (s'.err = err ∨ s'.err = Z_MEM_ERROR) ∧
      CodecKept h after s ∧ inputLeft fs s' = inputLeft fs s ∧
      Base i out h0 fs0 s0 fs after s' := by
  obtain ⟨after, s', run, hs', shape, errs, ahd, post⟩ := post_gz_error B.inv B.post.1 err msg hmsg herr
  refine ⟨after, s', run, hs', shape, errs, ahd, by rw [shape]; rfl, ?_⟩
  obtain ⟨d, hd, hdl⟩ := B.pos
  refine Base.step B post hs' (fun _ => Iff.rfl) (Or.inl rfl)
    ⟨by rw [shape], by rw [shape], by rw [shape], by rw [shape], by rw [shape], by rw [shape], by rw [shape]⟩
    ⟨d, by rw [shape]; exact hd, by rw [shape]; exact hdl⟩ ?_ B.rb ?_ (by rw [shape]; exact B.ml) St.hlen St.hm0
    St.hsz0 St.outLen St.views (BudgetAcc.refl _ _)
  · intro h0f
    obtain ⟨f1, l1⟩ := B.rf h0f
    refine ⟨f1, ?_⟩
    have e : inputLeft fs s' = inputLeft fs s := by rw [shape]; rfl
    rw [e]; exact l1
  · intro _
    rcases errs with e | e
    · rw [e]; exact herr
    · rw [e]; decide

end trans

/-! ## The loop: invariant, body and condition -/

/-- A literal of the sources as a message for `gz_error`. -/
theorem lit_msg (str : String) (hs : str ∈ strTable) (hz : 0 ∉ str.toUTF8.data.toList)
    (hl : str.toUTF8.data.toList.length < 2 ^ 64) (h : Heap) :
    ∃ p, strLit str h = .ok (p, h) ∧ (p = .null ∨ ∃ t, CString h p t ∧ ∀ b, ¬ ByteRoot p b) := by
  obtain ⟨p, e, c, n⟩ := lit_run str _ hs (Array.ext' (by simp [strBytes])) hz hl h
  exact ⟨p, e, Or.inr ⟨_, c, n⟩⟩

/-- An error other than `Z_OK` and `Z_BUF_ERROR`: `gz_avail` refuses to read. -/
def BadErr (s : GzState) : Prop := s.err ≠ Z_OK ∧ s.err ≠ Z_BUF_ERROR

/-- `gz_avail` with a bad error returns `-1` at once. -/
theorem gz_avail_bad {h : Heap} {i : Nat} {s : GzState} (hs : h.gzstates i = some s) (fs : Fs) (hb : BadErr s) :
    Zlib.Gzread.gz_avail (gzSt i) fs h = .ok ((-1, fs), h) := by
  rw [gz_avail_source]
  have hld : (StateT.lift (ldS (some (.tab i))) : G GzState) fs h = .ok ((s, fs), h) := by
    rw [g_lift_app, ldS_eq, hs]
  simp only [g_bind_app, hld]
  have hc : (s.err != Z_OK && s.err != Z_BUF_ERROR) = true := by
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq]
    exact hb
  rw [if_pos hc]
  rfl

section loop
variable (i : Nat) (out : Region) (h0 : Heap) (fs0 : Fs) (s0 : GzState)

/-- At a member start, the first call takes input, or the input left has already dropped. -/
def Hd (fs : Fs) (h : Heap) (s : GzState) : Prop :=
  HasBudget fs0 s0.fd → InflateAtHead h0 s0 → s0.err ≠ Z_STREAM_END →
    InflateAtHead h s ∨ inputLeft fs s < inputLeft fs0 s0

/-- The input left has dropped (when the call started at a member start). -/
def Strict (fs : Fs) (s : GzState) : Prop :=
  HasBudget fs0 s0.fd → InflateAtHead h0 s0 → s0.err ≠ Z_STREAM_END → inputLeft fs s < inputLeft fs0 s0

/-- The measure of the loop. -/
def meas (fs : Fs) (s : GzState) : Nat := inputLeft fs s + s.strm.avail_out.toNat

/-- The input left has dropped. -/
def StrictB (fs : Fs) (s : GzState) : Prop :=
  HasBudget fs0 s0.fd → s0.err ≠ Z_STREAM_END → inputLeft fs s < inputLeft fs0 s0

/-- After the loop. -/
def LQ (l : Zlib.Gzread.DecompLoop) (fs : Fs) (h : Heap) : Prop :=
  ∃ s, Base i out h0 fs0 s0 fs h s ∧ (s.how = GZIP ∨ s.how = LOOK) ∧
    (l.ret = Z_OK → s.strm.avail_out = 0 ∨ (s.eof ≠ 0 ∧ s.strm.avail_in = 0)) ∧
    (l.ret = Z_STREAM_END → Strict h0 fs0 s0 fs s) ∧
    (s.how = GZIP → Hd h0 fs0 s0 fs h s) ∧ (l.ret ≠ Z_OK → l.ret ≠ Z_STREAM_END → BadErr s) ∧
    (BadErr s0 → BadErr s) ∧
    (BadErr s0 → s.strm.avail_out.toNat ≠ out.length → s.strm.avail_out = 0 ∨ (s.eof ≠ 0 ∧ s.strm.avail_in = 0) ∨
      StrictB fs0 s0 fs s ∨ l.ret = Z_STREAM_END ∨
      (s.how = GZIP ∧ Stuck h s ∧ ¬ Stuck h0 s0 ∧ ¬ InflateAtHead h0 s0)) ∧
    (BadErr s0 → s0.err ≠ Z_STREAM_END → Stuck h0 s0 → s.strm.avail_out.toNat = out.length ∧
      ((l.ret ≠ Z_OK ∧ l.ret ≠ Z_STREAM_END) ∨ (s.eof ≠ 0 ∧ s.strm.avail_in = 0)))

/-- Before a round. -/
def LI (k : Nat) (l : Zlib.Gzread.DecompLoop) (fs : Fs) (h : Heap) : Prop :=
  l.brk = false ∧ l.ret = Z_OK ∧ ∃ s, Base i out h0 fs0 s0 fs h s ∧ s.how = GZIP ∧
    s.strm.avail_out ≠ 0 ∧ Hd h0 fs0 s0 fs h s ∧ k = meas fs s ∧ s.err = s0.err ∧
    (BadErr s0 → s.strm.avail_out.toNat = out.length ∨ (s.strm.avail_in = 0 ∧ StrictB fs0 s0 fs s)) ∧
    (Stuck h0 s0 → Stuck h s ∧ s.strm.avail_out.toNat = out.length)

/-- After a round. -/
def LJ (k : Nat) (y : Zlib.Gzread.DecompLoop) (fs : Fs) (h : Heap) : Prop :=
  (y.brk = false ∧ ∃ s, Base i out h0 fs0 s0 fs h s ∧ s.how = GZIP ∧ Hd h0 fs0 s0 fs h s ∧
    (y.ret = Z_OK ∨ y.ret = Z_STREAM_END) ∧ (y.ret = Z_STREAM_END → Strict h0 fs0 s0 fs s) ∧
    (y.ret ≠ Z_STREAM_END → ReadsFinite fs0 s0.fd → meas fs s < k) ∧ s.err = s0.err ∧
    (y.ret = Z_OK → BadErr s0 → s.strm.avail_out = 0 ∨ s.strm.avail_out.toNat = out.length ∨
      (s.strm.avail_in = 0 ∧ StrictB fs0 s0 fs s)) ∧ ¬ Stuck h0 s0) ∨
  (y.brk = true ∧ LQ i out h0 fs0 s0 y fs h)

end loop

section body
variable {i : Nat} {out : Region} {h0 : Heap} {fs0 : Fs} {s0 : GzState}

theorem lift_ok {α : Type} {m : M α} {fs : Fs} {h h' : Heap} {a : α} (e : m h = .ok (a, h')) :
    (StateT.lift m : G α) fs h = .ok ((a, fs), h') := by rw [g_lift_app, e]

theorem hd_of_strict {fs : Fs} {h : Heap} {s : GzState} (st : Strict h0 fs0 s0 fs s) : Hd h0 fs0 s0 fs h s :=
  fun a b c => Or.inr (st a b c)

theorem strict_eq {fs : Fs} {s s' : GzState} (e : inputLeft fs s' = inputLeft fs s) (st : Strict h0 fs0 s0 fs s) :
    Strict h0 fs0 s0 fs s' := fun a b c => by rw [e]; exact st a b c

theorem bad_code {e : Int32} (h : e = Z_STREAM_ERROR ∨ e = Z_MEM_ERROR ∨ e = Z_DATA_ERROR) :
    e ≠ Z_OK ∧ e ≠ Z_BUF_ERROR := by
  rcases h with h | h | h <;> (subst h; exact ⟨by decide, by decide⟩)

/-- A report of `gz_error` with a bad code, after an `inflate` error: the post of the loop. -/
theorem errs_post (St : Stat i out h0 s0) {fs : Fs} {h after : Heap} {s s' : GzState}
    (B' : Base i out h0 fs0 s0 fs after s') (hgz : s.how = GZIP) (shape : s' = { s with err := s'.err, msg := s'.msg })
    (kc : CodecKept h after s) (hil : inputLeft fs s' = inputLeft fs s) (hstr : Strict h0 fs0 s0 fs s)
    (rc : Int32) (hbad : s'.err ≠ Z_OK ∧ s'.err ≠ Z_BUF_ERROR) (hrc : rc ≠ Z_OK ∧ rc ≠ Z_STREAM_END)
    (hcodes : (rc = Z_NEED_DICT ∨ rc = Z_STREAM_ERROR) ∨ (rc = Z_DATA_ERROR ∨ rc = Z_MEM_ERROR))
    (e3 : rc = Z_NEED_DICT ∨ rc = Z_STREAM_ERROR → BadErr s0 → s.strm.avail_out.toNat = out.length)
    (e4 : Stuck h0 s0 → s.strm.avail_out.toNat = out.length ∧ (rc = Z_DATA_ERROR ∨ rc = Z_MEM_ERROR))
    (e5 : rc = Z_DATA_ERROR ∨ rc = Z_MEM_ERROR → Stuck h s) :
    LQ i out h0 fs0 s0 { ret := rc, brk := true } fs after := by
  have hst : s'.strm = s.strm := by rw [shape]
  refine ⟨s', B', Or.inl (by rw [shape]; exact hgz), fun e => absurd e hrc.1, fun e => absurd e hrc.2,
    fun _ => hd_of_strict (strict_eq hil hstr), fun _ _ => hbad, fun _ => hbad, fun hb hne => ?_,
    fun hb _ hs => ⟨by rw [hst]; exact (e4 hs).1, Or.inl hrc⟩⟩
  have hne' : s.strm.avail_out.toNat ≠ out.length := by rw [← hst]; exact hne
  rcases hcodes with hk | hdm
  · exact absurd (e3 hk hb) hne'
  by_cases a0 : InflateAtHead h0 s0
  · exact Or.inr (Or.inr (Or.inl fun hb0 hse => by rw [hil]; exact hstr hb0 a0 hse))
  · refine Or.inr (Or.inr (Or.inr (Or.inr ⟨by rw [shape]; exact hgz, stuck_kept kc (by rw [hst]) (e5 hdm),
      fun hs => hne' (e4 hs).1, a0⟩)))

/-- The error checks after the call. -/
theorem errs_run (St : Stat i out h0 s0) {fs : Fs} {h : Heap} {s : GzState} (B : Base i out h0 fs0 s0 fs h s)
    (hgz : s.how = GZIP) (k : Nat) (l : Zlib.Gzread.DecompLoop) (hl : l.brk = false) (rc : Int32)
    (codes : rc = Z_OK ∨ rc = Z_STREAM_END ∨ rc = Z_NEED_DICT ∨ rc = Z_STREAM_ERROR ∨
      rc = Z_DATA_ERROR ∨ rc = Z_MEM_ERROR ∨ rc = Z_BUF_ERROR) (hbuf : rc ≠ Z_BUF_ERROR)
    (hstr : Strict h0 fs0 s0 fs s)
    (hmeas : rc = Z_OK → ReadsFinite fs0 s0.fd → meas fs s < k)
    (e1 : s.err = s0.err)
    (e2 : rc = Z_OK → s.strm.avail_out ≠ 0 → s.strm.avail_in = 0 ∧ StrictB fs0 s0 fs s)
    (e3 : rc = Z_NEED_DICT ∨ rc = Z_STREAM_ERROR → BadErr s0 → s.strm.avail_out.toNat = out.length)
    (e4 : Stuck h0 s0 → s.strm.avail_out.toNat = out.length ∧ (rc = Z_DATA_ERROR ∨ rc = Z_MEM_ERROR))
    (e5 : rc = Z_DATA_ERROR ∨ rc = Z_MEM_ERROR → Stuck h s) :
    ∃ y fs' h', decompErrs i l rc fs h = .ok ((y, fs'), h') ∧ LJ i out h0 fs0 s0 k y fs' h' := by
  have hm := B.mode St
  have hsz := B.size St
  unfold decompErrs
  by_cases c1 : (rc == Z_STREAM_ERROR || rc == Z_NEED_DICT) = true
  · rw [if_pos c1]
    obtain ⟨p, hp, hmsg⟩ := lit_msg "internal error: inflate stream corrupt" (by decide +kernel)
      (by decide +kernel) (by decide +kernel) h
    obtain ⟨after, s', run, hs', shape, errs, kc, hil, B'⟩ := err_trans St B Z_STREAM_ERROR (by decide) p hmsg
    have run' : Zlib.Gzlib.gz_error (gzSt i) Z_STREAM_ERROR p h = .ok ((), after) := run
    simp only [Bool.or_eq_true, beq_iff_eq] at c1
    have hrc : rc ≠ Z_OK ∧ rc ≠ Z_STREAM_END := by
      rcases c1 with c | c <;> (rw [c]; exact ⟨by decide, by decide⟩)
    refine ⟨{ ret := rc, brk := true }, fs, after, by simp only [g_bind_app, lift_ok hp, lift_ok run', g_pure_app],
      Or.inr ⟨rfl, errs_post St B' hgz shape kc hil hstr rc
        (bad_code (errs.elim (fun e => Or.inl e) (fun e => Or.inr (Or.inl e)))) hrc
        (Or.inl (c1.elim Or.inr Or.inl)) e3 e4 e5⟩⟩
  rw [if_neg c1]
  by_cases c2 : (rc == Z_MEM_ERROR) = true
  · rw [if_pos c2]
    obtain ⟨p, hp, hmsg⟩ := lit_msg "out of memory" (by decide +kernel) (by decide +kernel) (by decide +kernel) h
    obtain ⟨after, s', run, hs', shape, errs, kc, hil, B'⟩ := err_trans St B Z_MEM_ERROR (by decide) p hmsg
    have run' : Zlib.Gzlib.gz_error (gzSt i) Z_MEM_ERROR p h = .ok ((), after) := run
    have c : rc = Z_MEM_ERROR := by simpa using c2
    subst c
    refine ⟨{ ret := Z_MEM_ERROR, brk := true }, fs, after,
      by simp only [g_bind_app, lift_ok hp, lift_ok run', g_pure_app], Or.inr ⟨rfl, errs_post St B' hgz shape kc hil
        hstr _ (bad_code (errs.elim (fun e => Or.inr (Or.inl e)) (fun e => Or.inr (Or.inl e))))
        ⟨by decide, by decide⟩ (Or.inr (Or.inr rfl)) e3 e4 e5⟩⟩
  rw [if_neg c2]
  by_cases c3 : (rc == Z_DATA_ERROR) = true
  · rw [if_pos c3]
    have c : rc = Z_DATA_ERROR := by simpa using c3
    subst c
    have hld : (StateT.lift (ldS (gzSt i)) : G GzState) fs h = .ok ((s, fs), h) := lift_ok (ldS_run B.rcd)
    simp only [g_bind_app, hld]
    by_cases cj : (s.junk == 1) = true
    · rw [if_pos cj]
      -- `avail_in = 0`, then `eof = 1, how = LOOK`
      let s2 : GzState := { s with strm := { s.strm with avail_in := 0 } }
      have hu2 : GzInvUpToOutput (putGz h i s2) i s2 := upto_zero_input B.inv hm hsz
      have B2 : Base i out h0 fs0 s0 fs (putGz h i s2) s2 :=
        put_trans St B hu2 ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl⟩ rfl rfl (by simp [s2]) rfl B.ml
      have hz : (StateT.lift (updZ (strmOf (gzSt i)) fun z => { z with avail_in := 0 }) : G Unit) fs h =
          .ok (((), fs), putGz h i s2) := lift_ok (updZ_run B.rcd _)
      let s3 : GzState := { s2 with eof := 1, how := LOOK }
      have rd := (B.inv.2.reader hm)
      have hu3 : GzInvUpToOutput (putGz (putGz h i s2) i s3) i s3 :=
        upto_put hu2 hm ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
          ⟨Or.inl rfl, (fun e => absurd (show LOOK = GZ_COPY from e) (by decide)),
            (fun e => absurd (show LOOK = GZIP from e) (by decide)), rd.junk, Or.inr rfl, rd.flags.2.1, rd.flags.2.2,
            fun hz => absurd hz hsz, fun hz => absurd hz hsz, fun _ _ => rfl⟩ (fun hc => absurd hc (by show ¬ (LOOK = GZ_COPY); decide))
      have B3 : Base i out h0 fs0 s0 fs (putGz (putGz h i s2) i s3) s3 :=
        put_trans St B2 hu3 ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl⟩ rfl rfl (Nat.le_refl _) rfl B2.ml
      have hs2 : (putGz h i s2).gzstates i = some s2 := by simp [putGz]
      have hu : (StateT.lift (updS (gzSt i) fun s => { s with eof := 1, how := LOOK }) : G Unit) fs (putGz h i s2) =
          .ok (((), fs), putGz (putGz h i s2) i s3) := lift_ok (updS_run hs2 _)
      have heof : s3.eof ≠ 0 ∧ s3.strm.avail_in = 0 := ⟨show (1 : Int32) ≠ 0 by decide, rfl⟩
      refine ⟨{ ret := Z_OK, brk := true }, fs, _, by simp only [g_bind_app, hz, hu, g_pure_app], Or.inr ⟨rfl, s3, B3,
        Or.inr rfl, fun _ => Or.inr heof, fun e => absurd e (by decide),
        fun e => absurd (show LOOK = GZIP from e) (by decide), fun hne => absurd rfl hne,
        fun hb => by show s.err ≠ Z_OK ∧ s.err ≠ Z_BUF_ERROR; rw [e1]; exact hb,
        fun _ _ => Or.inr (Or.inl heof), fun _ _ hs => ⟨(e4 hs).1, Or.inr heof⟩⟩⟩
    · rw [if_neg cj]
      have hz : (StateT.lift (ldZ (strmOf (gzSt i))) : G ZStream) fs h = .ok ((s.strm, fs), h) :=
        lift_ok (ldZ_run B.rcd)
      simp only [g_bind_app, hz]
      -- the message
      have hmsgOk : s.strm.msg = .null ∨ ∃ t, CString h s.strm.msg t ∧ ∀ b, ¬ ByteRoot s.strm.msg b := by
        rcases B.ml hsz with e | ⟨j, hj, e⟩
        · exact Or.inl e
        · rw [e]
          exact Or.inr (lit_cstring h hj)
      by_cases cm : (s.strm.msg == .null) = true
      · obtain ⟨p, hp, hmsg⟩ := lit_msg "compressed data error" (by decide +kernel) (by decide +kernel)
          (by decide +kernel) h
        obtain ⟨after, s', run, hs', shape, errs, kc, hil, B'⟩ := err_trans St B Z_DATA_ERROR (by decide) p hmsg
        have run' : Zlib.Gzlib.gz_error (gzSt i) Z_DATA_ERROR p h = .ok ((), after) := run
        refine ⟨{ ret := Z_DATA_ERROR, brk := true }, fs, after, ?_, Or.inr ⟨rfl, errs_post St B' hgz shape kc hil
          hstr _ (bad_code (errs.elim (fun e => Or.inr (Or.inr e)) (fun e => Or.inr (Or.inl e))))
          ⟨by decide, by decide⟩ (Or.inr (Or.inl rfl)) e3 e4 e5⟩⟩
        rw [if_pos cm]
        simp only [g_bind_app, lift_ok hp, lift_ok run', g_pure_app]
      · obtain ⟨after, s', run, hs', shape, errs, kc, hil, B'⟩ :=
          err_trans St B Z_DATA_ERROR (by decide) s.strm.msg hmsgOk
        have run' : Zlib.Gzlib.gz_error (gzSt i) Z_DATA_ERROR s.strm.msg h = .ok ((), after) := run
        refine ⟨{ ret := Z_DATA_ERROR, brk := true }, fs, after, ?_, Or.inr ⟨rfl, errs_post St B' hgz shape kc hil
          hstr _ (bad_code (errs.elim (fun e => Or.inr (Or.inr e)) (fun e => Or.inr (Or.inl e))))
          ⟨by decide, by decide⟩ (Or.inr (Or.inl rfl)) e3 e4 e5⟩⟩
        rw [if_neg cm]
        simp only [g_bind_app, g_pure_app, lift_ok run']
  rw [if_neg c3]
  -- `Z_OK` or `Z_STREAM_END`: the loop goes on, or stops at the end of a member
  have hcode : rc = Z_OK ∨ rc = Z_STREAM_END := by
    simp only [Bool.or_eq_true, beq_iff_eq, not_or] at c1 c2 c3
    rcases codes with e | e | e | e | e | e | e
    · exact Or.inl e
    · exact Or.inr e
    · exact absurd e c1.2
    · exact absurd e c1.1
    · exact absurd e c3
    · exact absurd e c2
    · exact absurd e hbuf
  have nst : ¬ Stuck h0 s0 := fun hs => by
    rcases (e4 hs).2 with e | e <;> rcases hcode with c | c <;> (rw [c] at e; exact absurd e (by decide))
  refine ⟨{ l with ret := rc }, fs, h, rfl, Or.inl ⟨hl, s, B, hgz, hd_of_strict hstr, hcode, fun _ => hstr,
    fun hse hb => ?_, e1, fun hok _ => ?_, nst⟩⟩
  · rcases hcode with e | e
    · exact hmeas e hb
    · exact absurd e hse
  · by_cases h0' : s.strm.avail_out = 0
    · exact Or.inl h0'
    · exact Or.inr (Or.inr (e2 hok h0'))

end body

section body2
variable {i : Nat} {out : Region} {h0 : Heap} {fs0 : Fs} {s0 : GzState}

/-- The `inflate` call, the `junk` update and the error checks. -/
theorem run_run (head : InflateHeadUsesInput) (stuck : InflateStuckNoOutput) (St : Stat i out h0 s0) (had : UInt32)
    (hhad : had.toNat = out.length) {fs : Fs} {h : Heap}
    {s : GzState} (B : Base i out h0 fs0 s0 fs h s) (hgz : s.how = GZIP) (hav : s.strm.avail_in ≠ 0)
    (hao : s.strm.avail_out ≠ 0) (hd : Hd h0 fs0 s0 fs h s) (k : Nat)
    (hk : ReadsFinite fs0 s0.fd → meas fs s ≤ k) (l : Zlib.Gzread.DecompLoop) (hl : l.brk = false)
    (r1 : s.err = s0.err)
    (r2 : BadErr s0 → s.strm.avail_out.toNat = out.length ∨ (s.strm.avail_in = 0 ∧ StrictB fs0 s0 fs s))
    (r3 : Stuck h0 s0 → Stuck h s ∧ s.strm.avail_out.toNat = out.length) :
    ∃ y fs' h', decompRun i had l fs h = .ok ((y, fs'), h') ∧ LJ i out h0 fs0 s0 k y fs' h' := by
  have hm := B.mode St
  have hsz := B.size St
  obtain ⟨rc, h2, z', used, produced, run, hrec2, B2, acct, codes, pOK, pBUF, pHead, pFull, pDict, pStuck, pStuck'⟩ :=
    inflate_trans head stuck St B hav hao
  let s2 : GzState := { s with strm := z' }
  have hrun : (StateT.lift (Zlib.Inflate.inflate (strmOf (gzSt i)) Z_NO_FLUSH) : G Int32) fs h =
      .ok ((rc, fs), h2) := lift_ok run
  have hz : (StateT.lift (ldZ (strmOf (gzSt i))) : G ZStream) fs h2 = .ok ((z', fs), h2) := lift_ok (ldZ_run hrec2)
  -- the input left after the call
  have hleft : inputLeft fs s2 + used = inputLeft fs s := by
    unfold inputLeft
    simp only [s2]
    have := acct.2.2.1
    omega
  have hstr : Strict h0 fs0 s0 fs s2 := by
    intro h1 h2' h3
    have l1 := (B.rf h1).2
    rcases hd h1 h2' h3 with ah | lt
    · have := pHead ah
      omega
    · omega
  have hmeas : rc = Z_OK → ReadsFinite fs0 s0.fd → meas fs s2 < k := by
    intro hc hb
    have hk' := hk hb
    have p : used ≠ 0 ∨ produced ≠ 0 := pOK hc
    unfold meas at hk' ⊢
    have a1 : s2.strm.avail_out.toNat + produced = s.strm.avail_out.toNat := acct.2.2.2.1
    omega
  have hao0 : s2.strm.avail_out.toNat + produced = s.strm.avail_out.toNat := acct.2.2.2.1
  have e2 : rc = Z_OK → s2.strm.avail_out ≠ 0 → s2.strm.avail_in = 0 ∧ StrictB fs0 s0 fs s2 := by
    intro hok ha
    have ha0 : s2.strm.avail_in = 0 := Classical.byContradiction fun hn => ha (pFull hok hn)
    refine ⟨ha0, fun hb hse => ?_⟩
    have l1 := (B.rf hb).2
    have a1 : z'.avail_in.toNat + used = s.strm.avail_in.toNat := acct.2.2.1
    have a2 : z'.avail_in.toNat = 0 := by
      have : z'.avail_in = 0 := ha0
      rw [this]; rfl
    have a3 : s.strm.avail_in.toNat ≠ 0 := fun e => hav (UInt32.toNat_inj.mp (by rw [e]; rfl))
    omega
  have e3 : rc = Z_NEED_DICT ∨ rc = Z_STREAM_ERROR → BadErr s0 → s2.strm.avail_out.toNat = out.length := by
    intro hc hb
    have p0 := pDict hc
    rcases r2 hb with e | ⟨e, -⟩
    · omega
    · exact absurd e hav
  have e4 : Stuck h0 s0 → s2.strm.avail_out.toNat = out.length ∧ (rc = Z_DATA_ERROR ∨ rc = Z_MEM_ERROR) := by
    intro hs
    obtain ⟨hs1, hl1⟩ := r3 hs
    obtain ⟨p0, hrc⟩ := pStuck hs1
    exact ⟨by omega, hrc⟩
  unfold decompRun
  simp only [g_bind_app, hrun, hz]
  by_cases cj : z'.avail_out < had
  · rw [if_pos cj]
    let s3 : GzState := { s2 with junk := 0 }
    have rd := (B2.inv.2.reader hm)
    have hu3 : GzInvUpToOutput (putGz h2 i s3) i s3 :=
      upto_put B2.inv hm ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        ⟨rd.how, rd.copyDirect, rd.gzipDirect, Or.inr (Or.inl rfl), rd.flags.1, rd.flags.2.1, rd.flags.2.2,
          fun hz => absurd hz hsz, fun hz => absurd hz hsz, rd.againEof⟩
        (fun hc => rd.copyIn hc)
    have B3 : Base i out h0 fs0 s0 fs (putGz h2 i s3) s3 :=
      put_trans St B2 hu3 ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl⟩ rfl rfl (Nat.le_refl _) rfl B2.ml
    have hu : (StateT.lift (updS (gzSt i) fun s => { s with junk := 0 }) : G Unit) fs h2 =
        .ok (((), fs), putGz h2 i s3) := lift_ok (updS_run hrec2 _)
    simp only [g_bind_app, hu]
    exact errs_run St B3 hgz k l hl rc codes pBUF hstr hmeas r1 e2 e3 e4
      (fun hc => stuck_put (pStuck' hc) rfl)
  · rw [if_neg cj]
    exact errs_run St B2 hgz k l hl rc codes pBUF hstr hmeas r1 e2 e3 e4 pStuck'

/-- The second input check. -/
theorem mid_run (head : InflateHeadUsesInput) (stuck : InflateStuckNoOutput) (St : Stat i out h0 s0) (had : UInt32)
    (hhad : had.toNat = out.length) {fs : Fs} {h : Heap}
    {s : GzState} (B : Base i out h0 fs0 s0 fs h s) (hgz : s.how = GZIP) (hao : s.strm.avail_out ≠ 0)
    (heof : s.strm.avail_in = 0 → s.eof ≠ 0) (hd : Hd h0 fs0 s0 fs h s) (k : Nat)
    (hk : ReadsFinite fs0 s0.fd → meas fs s ≤ k) (l : Zlib.Gzread.DecompLoop) (hl : l.brk = false)
    (hret : l.ret = Z_OK)
    (r1 : s.err = s0.err)
    (r2 : BadErr s0 → s.strm.avail_out.toNat = out.length ∨ (s.strm.avail_in = 0 ∧ StrictB fs0 s0 fs s))
    (r3 : Stuck h0 s0 → Stuck h s ∧ s.strm.avail_out.toNat = out.length)
    (hbad : BadErr s0 → s.strm.avail_in ≠ 0) :
    ∃ y fs' h', decompMid i had l fs h = .ok ((y, fs'), h') ∧ LJ i out h0 fs0 s0 k y fs' h' := by
  have hz : (StateT.lift (ldZ (strmOf (gzSt i))) : G ZStream) fs h = .ok ((s.strm, fs), h) := lift_ok (ldZ_run B.rcd)
  unfold decompMid
  simp only [g_bind_app, hz]
  by_cases c0 : (s.strm.avail_in == 0) = true
  · rw [if_pos c0]
    have hav : s.strm.avail_in = 0 := by simpa using c0
    have nb : ¬ BadErr s0 := fun hb => hbad hb hav
    have hld : (StateT.lift (ldS (gzSt i)) : G GzState) fs h = .ok ((s, fs), h) := lift_ok (ldS_run B.rcd)
    simp only [g_bind_app, hld]
    have post : ∀ (h' : Heap) (s' : GzState), Base i out h0 fs0 s0 fs h' s' → s'.how = GZIP → s'.eof = s.eof →
        s'.strm = s.strm → Hd h0 fs0 s0 fs h' s' → LJ i out h0 fs0 s0 k { l with brk := true } fs h' := by
      intro h' s' B' hg he hst hd'
      refine Or.inr ⟨rfl, s', B', Or.inl hg, fun e => Or.inr ⟨by rw [he]; exact heof hav, by rw [hst]; exact hav⟩,
        fun e => ?_, fun _ => hd', fun hne => absurd hret hne, fun hb => absurd hb nb, fun hb => absurd hb nb,
        fun hb => absurd hb nb⟩
      exfalso
      have e' : l.ret = Z_STREAM_END := e
      rw [hret] at e'; exact absurd e' (by decide)
    by_cases ca : (s.again == 0) = true
    · rw [if_pos ca]
      obtain ⟨p, hp, hmsg⟩ := lit_msg "unexpected end of file" (by decide +kernel) (by decide +kernel)
        (by decide +kernel) h
      obtain ⟨after, s', run, hs', shape, -, kc, hil, B'⟩ := err_trans St B Z_BUF_ERROR (by decide) p hmsg
      have run' : Zlib.Gzlib.gz_error (gzSt i) Z_BUF_ERROR p h = .ok ((), after) := run
      refine ⟨{ l with brk := true }, fs, after, by simp only [g_bind_app, lift_ok hp, lift_ok run', g_pure_app],
        post after s' B' (by rw [shape]; exact hgz) (by rw [shape]) (by rw [shape]) ?_⟩
      intro a b c
      rcases hd a b c with x | x
      · exact Or.inl (atHead_kept kc (by rw [shape]) x)
      · exact Or.inr (by rw [hil]; exact x)
    · rw [if_neg ca]
      exact ⟨{ l with brk := true }, fs, h, rfl, post h s B hgz rfl rfl hd⟩
  · rw [if_neg c0]
    have hav : s.strm.avail_in ≠ 0 := by simpa using c0
    exact run_run head stuck St had hhad B hgz hav hao hd k hk l hl r1 r2 r3

/-- **The body of the loop.** -/
theorem body_run (head : InflateHeadUsesInput) (stuck : InflateStuckNoOutput) (St : Stat i out h0 s0) (had : UInt32)
    (hhad : had.toNat = out.length) (k : Nat)
    (l : Zlib.Gzread.DecompLoop) {fs : Fs} {h : Heap} (hI : LI i out h0 fs0 s0 k l fs h) :
    ∃ y fs' h', decompBody i had l fs h = .ok ((y, fs'), h') ∧ LJ i out h0 fs0 s0 k y fs' h' := by
  obtain ⟨hl, hret, s, B, hgz, hao, hd, hk, i1, i2, i3⟩ := hI
  have hz : (StateT.lift (ldZ (strmOf (gzSt i))) : G ZStream) fs h = .ok ((s.strm, fs), h) := lift_ok (ldZ_run B.rcd)
  unfold decompBody
  simp only [g_bind_app, hz]
  by_cases c0 : (s.strm.avail_in == 0) = true
  · rw [if_pos c0]
    have hav0 : s.strm.avail_in = 0 := by simpa using c0
    obtain ⟨r, fs1, h1, s1, run, hr, hs1, B1, hrec, hflags, hist, hle⟩ := avail_trans St B (by rw [hgz]; decide)
    have e := hrec
    simp only [AvailRec] at e
    simp only [g_bind_app, run]
    have hd1 : Hd h0 fs0 s0 fs1 h1 s1 := by
      intro a b c
      rcases hd a b c with ah | lt
      · left
        obtain ⟨k2, st2, hk2, hst2, hmode, hbits, hlast⟩ := ah
        exact ⟨k2, st2, by rw [e]; exact hk2, by rw [hist k2]; exact hst2, hmode, hbits, hlast⟩
      · right
        exact Nat.lt_of_le_of_lt (hle a) lt
    have hstk : Stuck h s → Stuck h1 s1 := by
      rintro ⟨k2, st2, hk2, hst2, hmode⟩
      exact ⟨k2, st2, by rw [e]; exact hk2, by rw [hist k2]; exact hst2, hmode⟩
    have hao1 : s1.strm.avail_out = s.strm.avail_out := by rw [e]
    by_cases c1 : (r == -1) = true
    · rw [if_pos c1]
      have rm : r = -1 := by simpa using c1
      have hb1 := hflags.1 rm
      have hld : (StateT.lift (ldS (gzSt i)) : G GzState) fs1 h1 = .ok ((s1, fs1), h1) := lift_ok (ldS_run hs1)
      refine ⟨{ ret := s1.err, brk := true }, fs1, h1, by simp only [g_bind_app, hld, g_pure_app], Or.inr ⟨rfl, s1, B1,
        Or.inl (by rw [e]; exact hgz), fun he => absurd he hb1.1, fun he => ?_, fun _ => hd1,
        fun _ _ => hb1, fun _ => hb1, fun hb hne => ?_, fun _ hse hs => ⟨by rw [hao1]; exact (i3 hs).2,
          Or.inl ⟨hb1.1, B1.err hse⟩⟩⟩⟩
      · intro _ _ hne
        exact absurd he (B1.err hne)
      · rw [hao1] at hne
        rcases i2 hb with x | ⟨-, x⟩
        · exact absurd x hne
        · exact Or.inr (Or.inr (Or.inl fun a b => Nat.lt_of_le_of_lt (hle a) (x a b)))
    · rw [if_neg c1]
      have r0 : r = 0 := hr.resolve_right (by simpa using c1)
      have nb : ¬ BadErr s0 := fun hb => by
        have hb' : BadErr s := by show s.err ≠ Z_OK ∧ s.err ≠ Z_BUF_ERROR; rw [i1]; exact hb
        have hrun := gz_avail_bad B.rcd fs hb'
        rw [hrun] at run
        have e2 := Except.ok.inj run
        have hr' : (-1 : Int32) = r := congrArg (fun p => p.1.1) e2
        rw [r0] at hr'
        exact absurd hr' (by decide)
      refine mid_run head stuck St had hhad B1 (by rw [e]; exact hgz) (by rw [e]; exact hao) (hflags.2.2.1 r0) hd1 k
        ?_ l hl hret ((hflags.2.1 r0).trans i1) (fun hb => absurd hb nb)
        (fun hs => ⟨hstk (i3 hs).1, by rw [hao1]; exact (i3 hs).2⟩) (fun hb => absurd hb nb)
      intro hb
      have := hle hb.1
      rw [hk]
      unfold meas
      rw [hao1]
      omega
  · rw [if_neg c0]
    exact mid_run head stuck St had hhad B hgz hao (fun e => absurd (by simp [e]) c0) hd k (fun _ => by omega) l hl hret
      i1 i2 i3 (fun _ e => c0 (by simp [e]))

/-- **The condition of the loop.** -/
theorem cond_run (k : Nat) (y : Zlib.Gzread.DecompLoop) {fs : Fs} {h : Heap}
    (hJ : LJ i out h0 fs0 s0 k y fs h) :
    ∃ c z fs' h', decompCond i y fs h = .ok (((c, z), fs'), h') ∧
      (c = true → ∃ k', (ReadsFinite fs0 s0.fd → k' < k) ∧ LI i out h0 fs0 s0 k' z fs' h') ∧
      (c = false → LQ i out h0 fs0 s0 z fs' h') := by
  rcases hJ with ⟨hb, s, B, hgz, hd, hret, hse, hmeas, j1, j2, j3⟩ | ⟨hb, hq⟩
  · have hz : (StateT.lift (ldZ (strmOf (gzSt i))) : G ZStream) fs h = .ok ((s.strm, fs), h) :=
      lift_ok (ldZ_run B.rcd)
    refine ⟨!y.brk && s.strm.avail_out != 0 && y.ret != Z_STREAM_END, y, fs, h,
      by simp only [decompCond, g_bind_app, hz, g_pure_app], fun hc => ?_, fun hc => ?_⟩
    · have hao : s.strm.avail_out ≠ 0 := by intro e; rw [e] at hc; simp at hc
      have hne : y.ret ≠ Z_STREAM_END := by intro e; rw [e] at hc; simp at hc
      have hok : y.ret = Z_OK := hret.resolve_right hne
      refine ⟨meas fs s, fun hfin => hmeas hne hfin, hb, hok, s, B, hgz, hao, hd, rfl, j1, fun hbad => ?_,
        fun hs => absurd hs j3⟩
      rcases j2 hok hbad with x | x | x
      · exact absurd x hao
      · exact Or.inl x
      · exact Or.inr x
    · have stop : s.strm.avail_out = 0 ∨ y.ret = Z_STREAM_END := by
        by_cases ha : s.strm.avail_out = 0
        · exact Or.inl ha
        · right
          apply Classical.byContradiction
          intro hne
          rw [hb] at hc
          simp (config := { decide := true }) [ha, hne] at hc
      refine ⟨s, B, Or.inl hgz, fun hok => Or.inl (stop.resolve_right (by rw [hok]; decide)), hse, fun _ => hd,
        fun h1 h2 => ?_, fun hbad => by show s.err ≠ Z_OK ∧ s.err ≠ Z_BUF_ERROR; rw [j1]; exact hbad, fun _ _ => ?_, fun _ _ hs => absurd hs j3⟩
      · rcases hret with r | r
        · exact absurd r h1
        · exact absurd r h2
      · rcases stop with x | x
        · exact Or.inl x
        · exact Or.inr (Or.inr (Or.inr (Or.inl x)))
  · obtain ⟨s, B, -⟩ := id hq
    have hz : (StateT.lift (ldZ (strmOf (gzSt i))) : G ZStream) fs h = .ok ((s.strm, fs), h) :=
      lift_ok (ldZ_run B.rcd)
    refine ⟨!y.brk && s.strm.avail_out != 0 && y.ret != Z_STREAM_END, y, fs, h,
      by simp only [decompCond, g_bind_app, hz, g_pure_app], fun hc => ?_, fun _ => hq⟩
    simp [hb] at hc

end body2

/-! ## After the loop -/

theorem padv_zero (p : BPtr) : padv p 0 = p := by
  cases p <;> rfl

theorem runSafe_of_ok {α : Type} {m : G α} {fs fs' : Fs} {h h' : Heap} {a : α} {fin : Prop}
    {P : α → Fs → Heap → Prop} (e : m fs h = .ok ((a, fs'), h')) (p : P a fs' h') : RunSafe m fs h fin P := by
  refine ⟨fun x hx => ?_, fun _ => ⟨a, fs', h', e⟩, fun a2 fs2 h2 hx => ?_⟩
  · rw [e] at hx
    cases hx
  · rw [e] at hx
    cases hx
    exact p

/-- The post-condition of `gz_decomp`. -/
def DecompPost (i : Nat) (out : Region) (h : Heap) (fs : Fs) (s : GzState) (r : Int32) (fs' : Fs) (after : Heap) :
    Prop :=
  (r = 0 ∨ r = -1) ∧ FdsKept fs fs' ∧
      GzPost h i s (if out.pointer = s.out then [] else [out]) fs' after GzInvUpToOutput ∧
      (HasBudget fs s.fd → HasBudget fs' s.fd) ∧ (ReadsFinite fs s.fd → ReadsFinite fs' s.fd) ∧
      BudgetAcc s.fd fs fs' 0 ∧
      ∃ s', after.gzstates i = some s' ∧ FetchKeeps s s' ∧ MsgLit s' ∧
        (HasBudget fs s.fd → inputLeft fs' s' ≤ inputLeft fs s) ∧
        (s.err ≠ Z_STREAM_END → s'.err ≠ Z_STREAM_END) ∧
        (s'.x.have ≠ 0 → ∃ c, s'.x.next = padv out.pointer c ∧ c + s'.x.have.toNat ≤ out.length) ∧
        (s'.how = GZIP ∨ s'.how = LOOK) ∧ (r = -1 → s'.err ≠ Z_OK) ∧
        (r = 0 → s'.x.have ≠ 0 ∨ (s'.eof ≠ 0 ∧ s'.strm.avail_in = 0) ∨
          (s'.how = LOOK ∧ (HasBudget fs s.fd → InflateAtHead h s → s.err ≠ Z_STREAM_END →
            inputLeft fs' s' < inputLeft fs s))) ∧
        (HasBudget fs s.fd → s.err ≠ Z_STREAM_END → fetchRank fs' after s' ≤ fetchRank fs h s) ∧
        (HasBudget fs s.fd → s.err ≠ Z_STREAM_END → s'.x.have.toNat = out.length ∨ r = -1 ∨
          (s'.eof ≠ 0 ∧ s'.strm.avail_in = 0) ∨ fetchRank fs' after s' + 2 ≤ fetchRank fs h s) ∧
        (s.err ≠ Z_OK → s.err ≠ Z_BUF_ERROR → s'.err ≠ Z_OK ∧ s'.err ≠ Z_BUF_ERROR) ∧
        (r = -1 → s'.err ≠ Z_OK ∧ s'.err ≠ Z_BUF_ERROR) ∧
        (HasBudget fs s.fd → s.err ≠ Z_STREAM_END → s.err ≠ Z_OK → s.err ≠ Z_BUF_ERROR → s'.x.have ≠ 0 →
          s'.x.have.toNat = out.length ∨ (s'.eof ≠ 0 ∧ s'.strm.avail_in = 0) ∨
          fetchRank fs' after s' + 2 ≤ fetchRank fs h s ∨
          (s'.how = GZIP ∧ Stuck after s' ∧ ¬ Stuck h s ∧ ¬ InflateAtHead h s)) ∧
        (s.err ≠ Z_OK → s.err ≠ Z_BUF_ERROR → s.err ≠ Z_STREAM_END → Stuck h s →
          s'.x.have = 0 ∧ (r = -1 ∨ (s'.eof ≠ 0 ∧ s'.strm.avail_in = 0)))

/-- The rank falls by 2 when the input left fell. -/
theorem rank_strict {fs0 fs : Fs} {h0 h : Heap} {s0 s : GzState} (g0 : s0.how = GZIP) (hb0 : HasBudget fs0 s0.fd)
    (hfd : s.fd = s0.fd) (hbud : BudgetAcc s0.fd fs0 fs 0) (hw : s.how = GZIP ∨ s.how = LOOK)
    (hil : inputLeft fs s < inputLeft fs0 s0) : fetchRank fs h s + 2 ≤ fetchRank fs0 h0 s0 := by
  have b := budOf_acc hbud hb0
  rw [fetchRank_eq, fetchRank_eq, hfd, flagW_gzip g0]
  have fw : flagW s = 2 := by
    rcases hw with e | e
    · exact flagW_gzip e
    · exact flagW_look e
  rw [fw]
  have f0 := flagF_le h s
  omega

/-- The rank at the end of `gz_decomp`: it does not rise, and it falls by 2 at a member end. -/
theorem rank_tail {fs0 fs : Fs} {h0 h : Heap} {s0 s : GzState} (g0 : s0.how = GZIP) (hb0 : HasBudget fs0 s0.fd)
    (hfd : s.fd = s0.fd) (hil : inputLeft fs s ≤ inputLeft fs0 s0) (hbud : BudgetAcc s0.fd fs0 fs 0)
    (hw : s.how = GZIP ∨ s.how = LOOK)
    (hd : InflateAtHead h0 s0 → (s.how = GZIP → InflateAtHead h s) ∨ inputLeft fs s < inputLeft fs0 s0) :
    fetchRank fs h s ≤ fetchRank fs0 h0 s0 ∧
      (s.how = LOOK → (InflateAtHead h0 s0 → inputLeft fs s < inputLeft fs0 s0) →
        fetchRank fs h s + 2 ≤ fetchRank fs0 h0 s0) := by
  have b := budOf_acc hbud hb0
  rw [fetchRank_eq, fetchRank_eq, hfd, flagW_gzip g0]
  have fw : flagW s = 2 := by
    rcases hw with e | e
    · exact flagW_gzip e
    · exact flagW_look e
  rw [fw]
  have f0 := flagF_le h s
  refine ⟨?_, fun hl hs => ?_⟩
  · by_cases a0 : InflateAtHead h0 s0
    · rw [flagF_head a0]
      rcases hd a0 with x | x
      · rcases hw with e | e
        · rw [flagF_head (x e)]; omega
        · rw [flagF_look e]; omega
      · omega
    · rw [flagF_gzip g0 a0]; omega
  · rw [flagF_look hl]
    by_cases a0 : InflateAtHead h0 s0
    · rw [flagF_head a0]; have := hs a0; omega
    · rw [flagF_gzip g0 a0]; omega

section tail
variable {i : Nat} {out : Region} {h0 : Heap} {fs0 : Fs} {s0 : GzState}

/-- The final state gives the post-condition. -/
theorem final_post {fs : Fs} {h : Heap} {s : GzState} (B : Base i out h0 fs0 s0 fs h s) (r : Int32)
    (hr : r = 0 ∨ r = -1) (hgl : s.how = GZIP ∨ s.how = LOOK)
    (hx : s.x.have ≠ 0 → ∃ c, s.x.next = padv out.pointer c ∧ c + s.x.have.toNat ≤ out.length)
    (herr1 : r = -1 → s.err ≠ Z_OK)
    (prog : r = 0 → s.x.have ≠ 0 ∨ (s.eof ≠ 0 ∧ s.strm.avail_in = 0) ∨ (s.how = LOOK ∧ Strict h0 fs0 s0 fs s))
    (rkA : HasBudget fs0 s0.fd → s0.err ≠ Z_STREAM_END → fetchRank fs h s ≤ fetchRank fs0 h0 s0)
    (rkB : HasBudget fs0 s0.fd → s0.err ≠ Z_STREAM_END → s.x.have.toNat = out.length ∨ r = -1 ∨
      (s.eof ≠ 0 ∧ s.strm.avail_in = 0) ∨ fetchRank fs h s + 2 ≤ fetchRank fs0 h0 s0)
    (dA : s0.err ≠ Z_OK → s0.err ≠ Z_BUF_ERROR → s.err ≠ Z_OK ∧ s.err ≠ Z_BUF_ERROR)
    (dB : r = -1 → s.err ≠ Z_OK ∧ s.err ≠ Z_BUF_ERROR)
    (dC : HasBudget fs0 s0.fd → s0.err ≠ Z_STREAM_END → s0.err ≠ Z_OK → s0.err ≠ Z_BUF_ERROR → s.x.have ≠ 0 →
      s.x.have.toNat = out.length ∨ (s.eof ≠ 0 ∧ s.strm.avail_in = 0) ∨
      fetchRank fs h s + 2 ≤ fetchRank fs0 h0 s0 ∨
      (s.how = GZIP ∧ Stuck h s ∧ ¬ Stuck h0 s0 ∧ ¬ InflateAtHead h0 s0))
    (dD : s0.err ≠ Z_OK → s0.err ≠ Z_BUF_ERROR → s0.err ≠ Z_STREAM_END → Stuck h0 s0 →
      s.x.have = 0 ∧ (r = -1 ∨ (s.eof ≠ 0 ∧ s.strm.avail_in = 0))) :
    DecompPost i out h0 fs0 s0 r fs h := by
  obtain ⟨em, efd, esk, epos, esz, eout, ein⟩ := B.keep
  refine ⟨hr, B.kept, B.post, fun f => (B.rf f).1, B.rb, B.bud, s, B.rcd, ⟨em, efd, esk, epos, fun _ => ⟨esz, eout, ein⟩⟩,
    B.ml, fun f => (B.rf f).2, B.err, hx, hgl, herr1, ?_, rkA, rkB, dA, dB, dC, dD⟩
  intro r0
  rcases prog r0 with a | a | ⟨hl, st⟩
  · exact Or.inl a
  · exact Or.inr (Or.inl a)
  · exact Or.inr (Or.inr ⟨hl, fun a b c => st a b c⟩)

/-- **After the loop**: `x.have`, `x.next`, and at a member end `junk` and `how`. -/
theorem tail_run (St : Stat i out h0 s0) (g0 : s0.how = GZIP) (had : UInt32) (hhad : had.toNat = out.length)
    (l : Zlib.Gzread.DecompLoop) {fs : Fs} {h : Heap} (hq : LQ i out h0 fs0 s0 l fs h) :
    ∃ r fs' h', decompTail i had l fs h = .ok ((r, fs'), h') ∧ DecompPost i out h0 fs0 s0 r fs' h' := by
  obtain ⟨s, B, hgl, hok, hse, hhd, herr, hbb, hq3, hq4⟩ := hq
  have hm := B.mode St
  have hsz := B.size St
  obtain ⟨d, hd, hdl⟩ := B.pos
  have hz : (StateT.lift (ldZ (strmOf (gzSt i))) : G ZStream) fs h = .ok ((s.strm, fs), h) := lift_ok (ldZ_run B.rcd)
  have hv : (had - s.strm.avail_out).toNat = d := by
    rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; omega)]
    omega
  have hzero : s.strm.avail_out.toNat = out.length → (had - s.strm.avail_out) = 0 := fun e =>
    UInt32.toNat_inj.mp (by rw [hv]; show d = 0; omega)
  -- `x.have`
  let s1 : GzState := { s with x := { s.x with «have» := had - s.strm.avail_out } }
  have B1 : Base i out h0 fs0 s0 fs (putGz h i s1) s1 :=
    put_trans St B (upto_x B.inv (had - s.strm.avail_out) s.x.next) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      ⟨rfl, rfl, rfl⟩ rfl rfl (Nat.le_refl _) rfl B.ml
  have hu1 : (StateT.lift (updX (gzSt i) fun x => { x with «have» := had - s.strm.avail_out }) : G Unit) fs h =
      .ok (((), fs), putGz h i s1) := lift_ok (updX_run B.rcd _)
  -- `next_out - have`
  obtain ⟨r, off, a, hp, ha, -, hfit⟩ : ∃ r off a, out.pointer = .ref r off ∧ Space.get h r = some a ∧
      Space.ro h r = false ∧ off + out.length ≤ a.size := by
    rcases B.wr with ⟨-, hz0⟩ | ⟨r, off, a, hp, ha, hro, hfit⟩
    · exact absurd hz0 St.hlen
    · exact ⟨r, off, a, hp, ha, hro, hfit⟩
  have hadd : (StateT.lift (s.strm.next_out.add (-((had - s.strm.avail_out).toNat : Int))) : G BPtr) fs
      (putGz h i s1) = .ok ((out.pointer, fs), putGz h i s1) := by
    apply lift_ok
    rw [hd, hp, hv]
    show Ptr.add (Ptr.ref r (off + d)) (-(d : Int)) (putGz h i s1) = _
    have := Ptr.add_ok (h := putGz h i s1) (r := r) (a := a) (off := off + d) (k := -(d : Int))
      (by rw [putGz_space]; exact ha) (by omega) (by omega)
    unfold OkOn at this
    rw [this]
    have e2 : (((off + d : Nat) : Int) + -(d : Int)).toNat = off := by omega
    rw [e2]
  -- `x.next`
  let s2 : GzState := { s1 with x := { s1.x with next := out.pointer } }
  have hs1 : (putGz h i s1).gzstates i = some s1 := by simp [putGz]
  have B2 : Base i out h0 fs0 s0 fs (putGz (putGz h i s1) i s2) s2 :=
    put_trans St B1 (upto_x B1.inv (had - s.strm.avail_out) out.pointer) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      ⟨rfl, rfl, rfl⟩ rfl rfl (Nat.le_refl _) rfl B1.ml
  have hu2 : (StateT.lift (updX (gzSt i) fun x => { x with next := out.pointer }) : G Unit) fs (putGz h i s1) =
      .ok (((), fs), putGz (putGz h i s1) i s2) := lift_ok (updX_run hs1 _)
  have hxc : s2.x.have ≠ 0 → ∃ c, s2.x.next = padv out.pointer c ∧ c + s2.x.have.toNat ≤ out.length := by
    intro _
    refine ⟨0, (padv_zero _).symm, ?_⟩
    show 0 + (had - s.strm.avail_out).toNat ≤ out.length
    omega
  unfold decompTail
  simp only [g_bind_app, hz, hu1, hadd, hu2]
  by_cases ce : (l.ret == Z_STREAM_END) = true
  · rw [if_pos ce]
    have ret : l.ret = Z_STREAM_END := by simpa using ce
    let s3 : GzState := { s2 with junk := 0, how := LOOK }
    have hs2 : (putGz (putGz h i s1) i s2).gzstates i = some s2 := by simp [putGz]
    have rd := (B2.inv.2.reader hm)
    have hu3 : GzInvUpToOutput (putGz (putGz (putGz h i s1) i s2) i s3) i s3 :=
      upto_put B2.inv hm ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        ⟨Or.inl rfl, (fun e => absurd (show LOOK = GZ_COPY from e) (by decide)),
          (fun e => absurd (show LOOK = GZIP from e) (by decide)), Or.inr (Or.inl rfl), rd.flags.1, rd.flags.2.1,
          rd.flags.2.2, fun hz => absurd hz hsz, fun hz => absurd hz hsz, rd.againEof⟩ (fun hc => absurd hc (by show ¬ (LOOK = GZ_COPY); decide))
    have B3 := put_trans St B2 hu3 ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl⟩ rfl rfl (Nat.le_refl _) rfl B2.ml
    have hu4 : (StateT.lift (updS (gzSt i) fun s => { s with junk := 0, how := LOOK }) : G Unit) fs
        (putGz (putGz h i s1) i s2) = .ok (((), fs), putGz (putGz (putGz h i s1) i s2) i s3) := lift_ok (updS_run hs2 _)
    have rk := fun (hb : HasBudget fs0 s0.fd) (hse0 : s0.err ≠ Z_STREAM_END) =>
      rank_tail (h := putGz (putGz (putGz h i s1) i s2) i s3) g0 hb B3.keep.2.1 (B3.rf hb).2 B3.bud (Or.inr rfl)
        (fun a0 => Or.inr (hse ret hb a0 hse0))
    refine ⟨0, fs, _, by simp only [g_bind_app, hu4, g_pure_app], final_post B3 0 (Or.inl rfl) (Or.inr rfl) hxc
      (fun e => absurd e (by decide)) ?_ (fun hb hse0 => (rk hb hse0).1)
      (fun hb hse0 => Or.inr (Or.inr (Or.inr ((rk hb hse0).2 rfl (fun a0 => hse ret hb a0 hse0)))))
      (fun a b => hbb ⟨a, b⟩) (fun e => absurd e (by decide))
      (fun hb hse0 _ _ _ => Or.inr (Or.inr (Or.inl ((rk hb hse0).2 rfl (fun a0 => hse ret hb a0 hse0)))))
      (fun a b c hs => ?_)⟩
    · intro _
      exact Or.inr (Or.inr ⟨rfl, hse ret⟩)
    · obtain ⟨ho, hx⟩ := hq4 ⟨a, b⟩ c hs
      refine ⟨hzero ho, Or.inr ?_⟩
      rcases hx with ⟨-, x⟩ | x
      · exact absurd ret x
      · exact x
  · rw [if_neg ce]
    have ret : l.ret ≠ Z_STREAM_END := by simpa using ce
    have hdF : HasBudget fs0 s0.fd → s0.err ≠ Z_STREAM_END → InflateAtHead h0 s0 →
        (s2.how = GZIP → InflateAtHead (putGz (putGz h i s1) i s2) s2) ∨ inputLeft fs s2 < inputLeft fs0 s0 := by
      intro hb hse0 a0
      by_cases g : s.how = GZIP
      · rcases hhd g hb a0 hse0 with x | x
        · exact Or.inl (fun _ => atHead_put (atHead_put x rfl) rfl)
        · exact Or.inr x
      · exact Or.inl (fun g' => absurd g' g)
    have rkA : HasBudget fs0 s0.fd → s0.err ≠ Z_STREAM_END →
        fetchRank fs (putGz (putGz h i s1) i s2) s2 ≤ fetchRank fs0 h0 s0 := fun hb hse0 =>
      (rank_tail g0 hb B2.keep.2.1 (B2.rf hb).2 B2.bud hgl (hdF hb hse0)).1
    have dC : HasBudget fs0 s0.fd → s0.err ≠ Z_STREAM_END → s0.err ≠ Z_OK → s0.err ≠ Z_BUF_ERROR →
        s2.x.have ≠ 0 → s2.x.have.toNat = out.length ∨ (s2.eof ≠ 0 ∧ s2.strm.avail_in = 0) ∨
        fetchRank fs (putGz (putGz h i s1) i s2) s2 + 2 ≤ fetchRank fs0 h0 s0 ∨
        (s2.how = GZIP ∧ Stuck (putGz (putGz h i s1) i s2) s2 ∧ ¬ Stuck h0 s0 ∧ ¬ InflateAtHead h0 s0) := by
      intro hb hse0 a b hne
      have hne' : s.strm.avail_out.toNat ≠ out.length := fun e => hne (hzero e)
      rcases hq3 ⟨a, b⟩ hne' with x | x | x | x | ⟨g, st, ns, na⟩
      · left
        show (had - s.strm.avail_out).toNat = out.length
        have : s.strm.avail_out.toNat = 0 := by rw [x]; rfl
        omega
      · exact Or.inr (Or.inl x)
      · exact Or.inr (Or.inr (Or.inl (rank_strict g0 hb B2.keep.2.1 B2.bud hgl (x hb hse0))))
      · exact absurd x ret
      · exact Or.inr (Or.inr (Or.inr ⟨g, stuck_put (stuck_put st rfl) rfl, ns, na⟩))
    by_cases c : (l.ret != Z_OK) = true
    · refine ⟨_, fs, _, rfl, ?_⟩
      rw [if_pos c]
      have hne : l.ret ≠ Z_OK := by simpa using c
      exact final_post B2 (-1) (Or.inr rfl) hgl hxc (fun _ => (herr hne ret).1) (fun e => absurd e (by decide)) rkA
        (fun _ _ => Or.inr (Or.inl rfl)) (fun a b => hbb ⟨a, b⟩) (fun _ => herr hne ret) dC
        (fun a b c hs => ⟨hzero (hq4 ⟨a, b⟩ c hs).1, Or.inl rfl⟩)
    · refine ⟨_, fs, _, rfl, ?_⟩
      rw [if_neg c]
      have e : l.ret = Z_OK := by simpa using c
      have hav0 : s2.x.have ≠ 0 ∨ (s2.eof ≠ 0 ∧ s2.strm.avail_in = 0) := by
        rcases hok e with a0 | a0
        · left
          show (had - s.strm.avail_out) ≠ 0
          rw [a0]
          intro z
          have z' : had = 0 := by simpa using z
          have : had.toNat = 0 := by rw [z']; rfl
          exact St.hlen (by omega)
        · exact Or.inr a0
      refine final_post B2 0 (Or.inl rfl) hgl hxc (fun e => absurd e (by decide))
        (fun _ => hav0.elim Or.inl (fun a => Or.inr (Or.inl a))) rkA (fun _ _ => ?_) (fun a b => hbb ⟨a, b⟩)
        (fun e => absurd e (by decide)) dC (fun a b c hs => ?_)
      · rcases hok e with a0 | a0
        · left
          show (had - s.strm.avail_out).toNat = out.length
          have : s.strm.avail_out.toNat = 0 := by rw [a0]; rfl
          omega
        · exact Or.inr (Or.inr (Or.inl a0))
      · obtain ⟨ho, hx⟩ := hq4 ⟨a, b⟩ c hs
        refine ⟨hzero ho, Or.inr ?_⟩
        rcases hx with ⟨x, -⟩ | x
        · exact absurd e x
        · exact x

end tail

/-! ## `gz_decomp` -/

/-- **`gz_decomp` is safe** (`GzDecompSpec`), given the HEAD fact of `inflate`. -/
theorem gz_decomp_safe_of (head : InflateHeadUsesInput) (stuck : InflateStuckNoOutput) : GzDecompSpec := by
  intro i out h fs s hu hfs hm hgz hml ⟨hno, hao, hlen, hw⟩ hside
  have rd := hu.2.reader hm
  have hsz : s.size ≠ 0 := fun hz => by
    have h1 : s.how = LOOK := (rd.unalloc hz).2.2.1
    rw [hgz] at h1
    exact absurd h1 (by decide)
  have hs := hu.1
  -- the static facts
  have St : Stat i out h s := by
    refine ⟨hlen, hm, hsz, fun hB => ?_, ?_⟩
    · obtain ⟨ob, oarr, hob, hb, -, hn⟩ := (rd.bufs hsz).2
      have hob' : s.out = .ref (.blk ob) 0 := hob
      rcases hw with ⟨-, hz0⟩ | ⟨r, off, a, hp, ha, -, hfit⟩
      · exact absurd hz0 hlen
      · rw [hB, hob'] at hp
        cases hp
        have ha' : h.bytes ob = some a := ha
        have hb' : h.bytes ob = some oarr := hb
        rw [ha'] at hb'
        cases hb'
        have hn' : oarr.size = 2 * s.size.toNat := hn
        omega
    · unfold outRegions
      by_cases hB : out.pointer = s.out
      · rw [if_pos hB]; exact views_nil' _
      · rw [if_neg hB]
        have hA := hside.resolve_right hB
        rintro ref ⟨region, mem, off, hp⟩
        rw [List.mem_singleton] at mem
        subst mem
        rcases hw with ⟨hn, _⟩ | ⟨r, off', a, hp', ha, hro, hfit⟩
        · rw [hn] at hp; cases hp
        rw [hp] at hp'
        cases hp'
        cases ref with
        | blk b =>
          left
          refine ⟨b, rfl, ?_⟩
          rintro (o | nl)
          · exact hA b (by rw [hp]; rfl) o
          · exact nl (writable_live (Or.inr ⟨.blk b, off, a, hp, ha, hro, by omega⟩) hlen (by rw [hp]; rfl))
        | dstate_depth b =>
          right
          refine ⟨b, rfl, ?_⟩
          rintro (o | nl)
          · exact hA b (by rw [hp]; rfl) o
          · exact nl (writable_live (Or.inr ⟨.dstate_depth b, off, a, hp, ha, hro, by omega⟩) hlen (by rw [hp]; rfl))
        | str j => simp [Space.ro] at hro
        | st_dist_code => simp [Space.ro] at hro
        | st_length_code => simp [Space.ro] at hro
  -- the start of the loop
  have B0 : Base i out h fs s fs h s := by
    refine ⟨hs, hu, fun _ => Iff.rfl, ⟨hfs, s, hu, rfl, rfl, Zlib.Infback.Safety.BufferFrame.refl h _ _, ?_,
      fun b hb => Or.inl hb⟩, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ⟨0, by rw [hno, padv_zero], by omega⟩, hw, ?_,
      fun f => ⟨f, Nat.le_refl _⟩, id, id, hml, BudgetAcc.refl _ _⟩
    · intro b
      constructor
      · intro hl; exact Or.inl ⟨hl, fun hh => hh.2 hh.1⟩
      · rintro (⟨hl, _⟩ | ⟨ho, hn⟩)
        · exact hl
        · exact absurd (upTo_live hu b ho) hn
    · exact hside
  have I0 : LI i out h fs s (meas fs s) { ret := Z_OK, brk := false } fs h :=
    ⟨rfl, rfl, s, B0, hgz, fun e => hlen (by rw [← hao, e]; rfl), fun _ head _ => Or.inl head, rfl, rfl,
      fun _ => Or.inl hao, fun hs => ⟨hs, hao⟩⟩
  have hhad : s.strm.avail_out.toNat = out.length := hao
  -- the run
  have hz : (StateT.lift (ldZ (strmOf (gzSt i))) : G ZStream) fs h = .ok ((s.strm, fs), h) := lift_ok (ldZ_run hs)
  have e0 : Zlib.Gzread.gz_decomp (gzSt i) fs h = (gdoWhile (decompBody i s.strm.avail_out) (decompCond i)
      { ret := Z_OK, brk := false } >>= decompTail i s.strm.avail_out) fs h := by
    rw [gz_decomp_source, g_bind_app, hz]
  have loop : RunSafe (gdoWhile (decompBody i s.strm.avail_out) (decompCond i) { ret := Z_OK, brk := false }) fs h
      (ReadsFinite fs s.fd) (LQ i out h fs s) := by
    refine RunSafe.doWhile (LI i out h fs s) (LJ i out h fs s) (LQ i out h fs s) ?_ ?_ (k := meas fs s) ?_ I0
    · intro k x fs1 h1 hI
      obtain ⟨y, fs2, h2, e, hJ⟩ := body_run head stuck St s.strm.avail_out hhad k x hI
      exact runSafe_of_ok e hJ
    · intro k y fs1 h1 hJ
      obtain ⟨c, z, fs2, h2, e, ht, hf⟩ := cond_run k y hJ
      exact runSafe_of_ok e ⟨ht, hf⟩
    · intro hb
      unfold meas inputLeft
      have b1 := hb.2
      have b2 := s.strm.avail_in.toNat_lt
      have b3 := s.strm.avail_out.toNat_lt
      split <;> omega
  have key : RunSafe (gdoWhile (decompBody i s.strm.avail_out) (decompCond i) { ret := Z_OK, brk := false } >>=
      decompTail i s.strm.avail_out) fs h (ReadsFinite fs s.fd) (DecompPost i out h fs s) := by
    refine RunSafe.bind loop ?_
    intro l fs1 h1 hq
    obtain ⟨r, fs2, h2, e, post⟩ := tail_run St hgz s.strm.avail_out hhad l hq
    exact runSafe_of_ok e post
  unfold RunSafe
  rw [e0]
  exact key

#print axioms gz_decomp_safe_of

end ZlibF.Spec.Public.GzRead
