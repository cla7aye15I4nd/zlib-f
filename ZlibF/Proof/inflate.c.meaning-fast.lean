import ZlibF.Proof.«inflate.c.meaning-fast-loop»
import ZlibF.Proof.«inflate.c.meaning-length»
import ZlibF.Proof.«inflate.c.fast-entry»
import ZlibF.Proof.«inflate.c.window-physical-history»
import ZlibF.Proof.«inflate.c.meaning-frame»

/-!
# inflate.c: the fast branch of `LEN` keeps the format meaning

With at least 6 input bytes, 258 bytes of output room and fewer than 8 held
bits, `case LEN` runs `RESTORE; inflate_fast(strm, out); LOAD` and returns to
the mode loop. `fast_call_tokens` gives the tokens of the whole fast call; this
file places them in the format grammar and rebuilds `LoopMatches`:

* the window and the call's output before the fast call are the history of
  every match (`Token.Step.rebase`, with `window_have_le`);
* each token of the fast call is a `DeflateParsed.token` step
  (`Token.Step.strip`);
* the end-of-block token ends at a block boundary or after the final block,
  with fewer than 8 held bits (`inflate_fast` returns the unused whole bytes).

Input and output may be any caller byte views the dispatch packet admits,
also disjoint ranges of one block (`inflate_fast_entry`,
`tests/regression/inflate-shared-block`). The leaf
flags and the prefix reads the fast decoder needs are part of `TableMeaning`.

A rejected token gives `BAD`, and the input read is doomed (`LoopDoomed`):
the token is rejected on the bits it consumed followed by anything
(`actual_body_rejects_prefix`, which needs `PrefixQuery`, P15), and the
returned whole bytes come after those bits. A distance too far back for the
saved window is too far back for the whole history once the source has a
full window (`Token.Rejected.rebase`, `full_width`).
-/

namespace Zlib.Inflate.Proofs.MeaningFast
open C Zlib.Inflate Zlib.Inflate.Proofs Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs.MeaningMatch Zlib.Inflate.Proofs.MeaningLength
open Zlib.Inffast.Proofs.FastMeaning (hist cur src finalHeap fast_call_tokens)
set_option autoImplicit false

/-- The tables of a fast call from the format meaning of the state's tables. -/
theorem fast_tables (e : Zlib.Inffast.Proofs.Env) {h : Heap} {s : InflateState} {L D : List Nat}
    (codes : ∀ ref : CodeRef, (Space.get e.h0 ref : Option (Array Code)) = Space.get h ref)
    (lenEq : e.s0.lencode = s.lencode) (distEq : e.s0.distcode = s.distcode)
    (lbEq : e.s0.lenbits = s.lenbits) (dbEq : e.s0.distbits = s.distbits)
    (lenT : TableMeaning h s.lencode s.lenbits LENS L)
    (distT : TableMeaning h s.distcode s.distbits DISTS D) :
    Zlib.Inffast.Spec.BodyToken.Tables e L D := by
  obtain ⟨lr, lo, lc, lu, lp, lg, linv, lst, _, lfl⟩ := lenT
  obtain ⟨dr, dof, dc, du, dp, dg, dinv, dst, _, dfl⟩ := distT
  have lptr := e.hlc
  rw [lenEq, lp] at lptr
  cases lptr
  have dptr := e.hdc
  rw [distEq, dp] at dptr
  cases dptr
  have lget := e.hLCA
  rw [codes, lg] at lget
  cases lget
  have dget := e.hDCA
  rw [codes, dg] at dget
  cases dget
  refine ⟨⟨lu, ?_⟩, ⟨du, ?_⟩, ?_, ?_, ?_, ?_⟩
  · rw [lbEq]; exact linv
  · rw [dbEq]; exact dinv
  · rw [lbEq]; exact lst
  · rw [dbEq]; exact dst
  · rw [lbEq]; exact lfl
  · rw [dbEq]; exact dfl

/-- The prefix reads of the tables of a fast call. -/
theorem fast_prefix (e : Zlib.Inffast.Proofs.Env) {h : Heap} {s : InflateState} {L D : List Nat}
    (codes : ∀ ref : CodeRef, (Space.get e.h0 ref : Option (Array Code)) = Space.get h ref)
    (lenEq : e.s0.lencode = s.lencode) (distEq : e.s0.distcode = s.distcode)
    (lbEq : e.s0.lenbits = s.lenbits) (dbEq : e.s0.distbits = s.distbits)
    (lenT : TableMeaning h s.lencode s.lenbits LENS L)
    (distT : TableMeaning h s.distcode s.distbits DISTS D) :
    Zlib.Inftrees.Proofs.PrefixQuery LENS e.LCA e.ol e.s0.lenbits.toNat ∧
      Zlib.Inftrees.Proofs.PrefixQuery DISTS e.DCA e.od e.s0.distbits.toNat := by
  obtain ⟨lr, lo, lc, lu, lp, lg, _, _, lpf, _⟩ := lenT
  obtain ⟨dr, dof, dc, du, dp, dg, _, _, dpf, _⟩ := distT
  have lptr := e.hlc
  rw [lenEq, lp] at lptr
  cases lptr
  have dptr := e.hdc
  rw [distEq, dp] at dptr
  cases dptr
  have lget := e.hLCA
  rw [codes, lg] at lget
  cases lget
  have dget := e.hDCA
  rw [codes, dg] at dget
  cases dget
  exact ⟨by rw [lbEq]; exact lpf, by rw [dbEq]; exact dpf⟩

/-- A match distance is at most 32768. -/
theorem distance_le {distanceSymbol distanceExtra : Nat} {r rest : List Bool}
    (valid : distanceSymbol ≤ 29)
    (read : readBits (distExtras.getD distanceSymbol 0) r = some (distanceExtra, rest)) :
    distBases.getD distanceSymbol 0 + distanceExtra ≤ 32768 := by
  have lt := Zlib.Inffast.Proofs.readBits_value_lt read
  have table : ∀ n : Fin 30, distBases.getD n.val 0 + 2 ^ distExtras.getD n.val 0 ≤ 32769 := by
    decide
  have := table ⟨distanceSymbol, by omega⟩
  simp only at this
  omega

/-- A token rejected against a retained suffix of the history is rejected
against the whole history, when the suffix holds the whole history or a
full 32 KiB window. -/
theorem _root_.ZlibF.Spec.Token.Rejected.rebase {L D : List Nat}
    {saved dict past current : List UInt8} {inp : List Bool}
    (enough : 32768 ≤ saved.length ∨ (dict ++ past).length ≤ saved.length)
    (rejected : Token.Rejected L D saved current inp) :
    Token.Rejected L D dict (past ++ current) inp := by
  cases rejected with
  | length never => exact .length never
  | distance d lo hi x never => exact .distance d lo hi x never
  | tooFar d lo hi x e ds y far =>
    refine .tooFar d lo hi x e ds y ?_
    have bound := distance_le ds y
    simp only [List.length_append] at far enough ⊢
    omega

/-- A suffix of a list that is not longer than another suffix is a suffix of it. -/
theorem suffix_of_shorter {xs ys zs : List UInt8} (x : xs <:+ zs) (y : ys <:+ zs)
    (le : xs.length ≤ ys.length) : xs <:+ ys :=
  List.suffix_of_suffix_length_le x y le

/-- The bytes the fast decoder copies from are a suffix of the body
dictionary and the output before the call. -/
theorem hist_suffix (e : Zlib.Inffast.Proofs.Env) {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {dict logOut bodyDict : List UInt8}
    (good : Good h r zs z s) (bytes : ∀ b, e.h0.bytes b = h.bytes b)
    (window : e.s0.window = s.window) (ws : e.s0.wsize = s.wsize) (wn : e.s0.wnext = s.wnext)
    (wh : e.s0.whave = s.whave) (meaning : WindowMeaning h s dict logOut)
    (haveLe : s.whave.toNat ≤ bodyDict.length + logOut.length)
    (tail : bodyDict ++ logOut <:+ dict ++ logOut) :
    hist e <:+ bodyDict ++ logOut := by
  have len : (hist e).length = s.whave.toNat := by
    simp [hist, Zlib.Inffast.Spec.MatchHistory.saved, wh]
  apply suffix_of_shorter _ tail (by rw [len, List.length_append]; exact haveLe)
  by_cases zero : s.whave = 0
  · have : hist e = [] := List.eq_nil_of_length_eq_zero (by rw [len, zero]; rfl)
    rw [this]
    exact List.nil_suffix
  obtain ⟨wptr, _, wget, _⟩ := e.hwin (by rw [wh]; exact zero)
  rcases meaning with ⟨_, dictn⟩ | ⟨_, z2, _⟩
  · rcases Zlib.Inflate.Proofs.WindowHistory.dictionary_saved_or_lazy good dictn with
      ⟨null, _, _⟩ | ⟨w, a, sptr, sget, _, _, savedEq⟩
    · rw [window, null] at wptr
      cases wptr
    · rw [window, sptr] at wptr
      obtain ⟨blkEq, offEq⟩ := Ptr.ref.inj wptr
      have wbEq : e.wb = w := (BRef.blk.inj blkEq).symm
      rw [bytes, wbEq, sget] at wget
      have arrEq : e.W = a := (Option.some.inj wget).symm
      have : hist e = Zlib.Inffast.Spec.MatchHistory.saved a s.wsize.toNat s.wnext.toNat
          s.whave.toNat 0 := by
        simp only [hist, ws, wn, wh, arrEq, ← offEq]
      rw [this, savedEq]
      exact List.drop_suffix _ _
  · exact absurd z2 zero

/-- The bits consumed before a position, from the bits left after it. -/
theorem take_of_drop {xs tb : List Bool} {u u' : Nat}
    (split : xs.drop u = tb ++ xs.drop u') : xs.take u' = xs.take u ++ tb := by
  have whole := List.take_append_drop u' xs
  have other := List.take_append_drop u xs
  rw [split, ← List.append_assoc] at other
  exact List.append_cancel_right (whole.trans other.symm)

/-- The registers after the fast call and `LOAD`: `used` input bytes read
with the output cursor at `o`, and the bit buffer of the state. -/
def fastRegs (l : IL) (ib io ob oo used o : Nat) (hold : UInt64) (bits : UInt32) : IL :=
  { l with put := .ref (.blk ob) o, left := UInt32.ofNat (l.left.toNat - (o - oo)), next := .ref (.blk ib) (io + used), have_ := UInt32.ofNat (l.have_.toNat - used), hold := hold, bits := bits }

/-- The loop meaning after the fast call, from the facts its run gives. The
state differs from the one before only in its mode, bit buffer and back
counter; the remaining input stays apart from the output room and from the call's
output (`sepNext`, `sepStart`). -/
theorem fast_rebuild {c : Ctx} {f : LoopFrame} {H : Heap} {l : IL} {zs : Nat} {s : InflateState}
    {callOut : List UInt8} {header bodyDict : List UInt8}
    {bitsP : List Bool} {pos : DeflatePos} {m : UInt32} {hold : UInt64} {bits : UInt32} {bk : Int32}
    {ib io ob oo used o : Nat} {IN A : Array UInt8} {newOut : List UInt8}
    (st : c.st = some (.tab zs)) (retOk : l.ret = Z_OK)
    (config : ConfigMatches (loopState s l) f.wrap f.configured) (msync : m ≠ SYNC)
    (haveLe : l.have_.toNat ≤ l.in_.toNat) (inLen : l.in_.toNat = f.inp.length)
    (leftLe : l.left.toNat ≤ l.out_.toNat) (pendBase : loopPending l = callOut.length)
    (sepNext : Separate (.ref (.blk ob) o) (l.left.toNat - (o - oo)) (.ref (.blk ib) (io + used))
      (l.have_.toNat - used))
    (sepStart : Separate (.ref (.blk ob) (oo - callOut.length)) (callOut.length + (o - oo))
      (.ref (.blk ib) (io + used)) (l.have_.toNat - used))
    (startEq : f.start = .ref (.blk ob) (oo - callOut.length)) (startLe : callOut.length ≤ oo)
    (usedLe : used ≤ l.have_.toNat) (ooLe : oo ≤ o) (oLe : o - oo ≤ l.left.toNat)
    (haveLen : l.have_.toNat = (f.inp.drop (loopRead l)).length)
    (view : f.inp.drop (loopRead l) = (IN.toList.drop io).take (f.inp.drop (loopRead l)).length)
    (inFit : io + l.have_.toNat ≤ IN.size)
    (hs : H.istates zs = some { s with mode := m, hold := hold, bits := bits, back := bk })
    (inGet : (Space.get H (BRef.blk ib) : Option (Array UInt8)) = some IN)
    (outGet : (Space.get H (BRef.blk ob) : Option (Array UInt8)) = some A)
    (outRo : Space.ro H (BRef.blk ob) = false)
    (outFit : oo + l.left.toNat ≤ A.size)
    (newOutEq : newOut = (A.toList.drop (oo - callOut.length)).take (callOut.length + (o - oo)))
    (holdLt : hold.toNat < 2 ^ bits.toNat)
    (window : WindowMeaning H (loopState s l) f.dict f.logOut)
    (sepWin : Separate (.ref (.blk ob) o) (l.left.toNat - (o - oo)) s.window s.wsize.toNat)
    (check : CheckMeaning (loopState s l) f.wrap header f.logOut)
    (flagsM : FlagsMatch (loopState s l) f.wrap header)
    (widthM : HeaderWidth (loopState s l) f.configured header)
    (dictM : f.dict = [] ∨ f.wrap = .raw ∨ header.length = 6)
    (wrapHeader : WrapHeader f.wrap f.configured f.dict header bodyDict)
    (bitsEq : bytesToBits (f.logIn ++ f.inp.take (loopRead l + used)) =
      (bytesToBits header ++ bitsP) ++ natBits bits.toNat hold.toNat)
    (parsed : DeflateParsed bodyDict bitsP pos)
    (body : BodyMatches H { s with mode := m, hold := hold, bits := bits, back := bk } pos)
    (outEq : pos.out = f.logOut ++ newOut) :
    LoopMatches c f H (fastRegs l ib io ob oo used o hold bits) := by
  have haveSub : (UInt32.ofNat (l.have_.toNat - used)).toNat = l.have_.toNat - used := by
    rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by have := l.have_.toNat_lt; omega)]
  have leftSub : (UInt32.ofNat (l.left.toNat - (o - oo))).toNat = l.left.toNat - (o - oo) := by
    rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by have := l.left.toNat_lt; omega)]
  have readEq : loopRead (fastRegs l ib io ob oo used o hold bits) = loopRead l + used := by
    simp only [loopRead, fastRegs, haveSub]
    omega
  have pendEq : loopPending (fastRegs l ib io ob oo used o hold bits) = callOut.length + (o - oo) := by
    simp only [loopPending, fastRegs, leftSub]
    simp only [loopPending] at pendBase
    omega
  have newLen : newOut.length = callOut.length + (o - oo) := by
    rw [newOutEq]
    simp only [List.length_take, List.length_drop, Array.length_toList]
    omega
  refine ⟨zs, { s with mode := m, hold := hold, bits := bits, back := bk }, newOut,
    bytesToBits header ++ bitsP, natBits bits.toNat hold.toNat, .body header pos, st, hs, retOk,
    ⟨config.1, config.2.1, config.2.2.1, config.2.2.2.1, config.2.2.2.2.1, msync⟩, ?_, inLen,
    ⟨?_, ?_, holdLt⟩, ?_, ⟨?_, fun _ _ _ => ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, Zlib.Inflate.Proofs.MeaningBits.HeldBits.of_natBits (s := { s with mode := m, hold := hold, bits := bits, back := bk }) holdLt, ⟨bodyDict, bitsP, wrapHeader, rfl, parsed⟩,
    ⟨body, window, ?_⟩, ⟨flagsM, widthM, dictM⟩, outEq⟩
  · show (UInt32.ofNat (l.have_.toNat - used)).toNat ≤ l.in_.toNat
    rw [haveSub]
    omega
  · show (UInt32.ofNat (l.have_.toNat - used)).toNat =
      (f.inp.drop (loopRead (fastRegs l ib io ob oo used o hold bits))).length
    rw [haveSub, readEq, ← List.drop_drop, List.length_drop, ← haveLen]
  · right
    refine ⟨.blk ib, IN, io + used, rfl, inGet, ?_, ?_⟩
    · rw [readEq, ← List.drop_drop, List.length_drop, ← haveLen]
      omega
    · rw [readEq, ← List.drop_drop, List.length_drop]
      have v := congrArg (List.drop used) view
      rw [List.drop_take] at v
      rw [v, List.drop_drop]
  · show (UInt32.ofNat (l.left.toNat - (o - oo))).toNat ≤ l.out_.toNat
    rw [leftSub]
    omega
  · rw [pendEq, newLen]
    exact Nat.le_refl _
  · rw [pendEq, newLen]
  · show Ptr.ref (.blk ob) o = inputAdvance f.start newOut.length
    rw [startEq, newLen]
    simp only [inputAdvance]
    congr 1
    omega
  · rw [startEq, newLen]
    refine Or.inr ⟨.blk ob, oo - callOut.length, A, rfl, outGet, by omega, ?_⟩
    rw [newOutEq]
  · refine Or.inr ⟨.blk ob, o, A, rfl, outGet, outRo, ?_⟩
    show o + (UInt32.ofNat (l.left.toNat - (o - oo))).toNat ≤ A.size
    rw [leftSub]
    omega
  · show Separate (.ref (.blk ob) o) (UInt32.ofNat (l.left.toNat - (o - oo))).toNat
      (.ref (.blk ib) (io + used)) (UInt32.ofNat (l.have_.toNat - used)).toNat
    rw [leftSub, haveSub]
    exact sepNext
  · show Separate (.ref (.blk ob) o) (UInt32.ofNat (l.left.toNat - (o - oo))).toNat
      s.window s.wsize.toNat
    rw [leftSub]
    exact sepWin
  · rw [startEq]
    show Separate (.ref (.blk ob) (oo - callOut.length)) newOut.length
      (.ref (.blk ib) (io + used)) (UInt32.ofNat (l.have_.toNat - used)).toNat
    rw [newLen, haveSub]
    exact sepStart
  · rw [readEq]
    exact bitsEq
  · rw [pendEq, ← newLen, List.length_append, Nat.add_sub_cancel, List.take_left' rfl]
    exact check

#print axioms fast_rebuild

/-- The heap a fast call returns, seen from the decoder before the call. -/
theorem finalHeap_facts (e : Zlib.Inffast.Proofs.Env) {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL}
    (heap0 : e.h0 = setI (r.put h (leaveStream z l)) zs (leaveState s l))
    (ref0 : e.r = r) (id0 : e.stid = zs) (state0 : e.s0 = leaveState s l)
    (hs : h.istates zs = some s) (A : Array UInt8) (msg : BPtr) (md : UInt32) (hold : UInt64)
    (bits : UInt32) (used o : Nat) :
    let H := finalHeap e A msg md hold bits used o
    H.istates zs = some { s with mode := md, hold := hold, bits := bits } ∧
    (∀ b, b ≠ e.ob → (Space.get H (BRef.blk b) : Option (Array UInt8)) = Space.get h (BRef.blk b)) ∧
    (Space.get H (BRef.blk e.ob) : Option (Array UInt8)) = some A ∧
    (∀ b, Space.ro H (BRef.blk b) = Space.ro h (BRef.blk b)) ∧
    (∀ ref : CodeRef, (Space.get H ref : Option (Array Code)) = Space.get h ref) ∧
    r.get H = some { e.sm0 with next_in := .ref (.blk e.ib) (e.i0 + used), next_out := .ref (.blk e.ob) o, avail_in := UInt32.ofNat (e.sm0.avail_in.toNat - used), avail_out := UInt32.ofNat (e.sm0.avail_out.toNat - (o - e.o0)), msg := msg } := by
  intro H
  have istates : H.istates = upd h.istates zs (some { s with mode := md, hold := hold, bits := bits }) := by
    simp only [H, finalHeap, Zlib.Inffast.Proofs.put_istates, heap0, setI, id0, state0, leaveState,
      Zlib.Inffast.Proofs.put_istates, upd_upd]
  have bytes : H.bytes = upd h.bytes e.ob (some A) := by
    simp only [H, finalHeap, Zlib.Inffast.Proofs.put_bytes, heap0, setI,
      Zlib.Inffast.Proofs.put_bytes]
  refine ⟨by rw [istates]; exact upd_same _ _ _, ?_, ?_, ?_, ?_, ?_⟩
  · intro b ne
    show H.bytes b = h.bytes b
    rw [bytes, upd_ne _ _ _ _ ne]
  · show H.bytes e.ob = some A
    rw [bytes, upd_same]
  · intro b
    show H.ro b = h.ro b
    simp only [H, finalHeap, Zlib.Inffast.Proofs.put_ro, heap0, setI, Zlib.Inffast.Proofs.put_ro]
  · intro ref
    cases ref with
    | istate_codes i =>
      show (H.istates i).map (·.codes) = (h.istates i).map (·.codes)
      rw [istates]
      by_cases same : i = zs
      · subst same
        simp [hs]
      · simp [upd_ne _ _ _ _ same]
    | st_lenfix =>
      show some H.static.lenfix = some h.static.lenfix
      simp only [H, finalHeap, Zlib.Inffast.Proofs.put_static, heap0, setI]
    | st_distfix =>
      show some H.static.distfix = some h.static.distfix
      simp only [H, finalHeap, Zlib.Inffast.Proofs.put_static, heap0, setI]
  · simp only [H, finalHeap]
    rw [← ref0]
    exact ZStreamRef.get_put_same (Zlib.Inffast.Proofs.Env.stream_get_frame e _ _) _

/-- The bits read after `used` more input bytes. -/
theorem fast_bits {logIn inp : List UInt8} {read used u : Nat}
    {consumed held initial heldNew : List Bool}
    (before : bytesToBits (logIn ++ inp.take read) = consumed ++ held)
    (initialEq : initial = held ++ bytesToBits (inp.drop read))
    (after : heldNew ++ bytesToBits (inp.drop (read + used)) = initial.drop u) :
    bytesToBits (logIn ++ inp.take (read + used)) = (consumed ++ initial.take u) ++ heldNew := by
  have whole : bytesToBits (logIn ++ inp) =
      bytesToBits (logIn ++ inp.take (read + used)) ++ bytesToBits (inp.drop (read + used)) := by
    rw [← MeaningCopy.bytesToBits_app, List.append_assoc, List.take_append_drop]
  have whole2 : bytesToBits (logIn ++ inp) = consumed ++ initial := by
    rw [← List.take_append_drop read inp, ← List.append_assoc, MeaningCopy.bytesToBits_app, before,
      initialEq, List.append_assoc]
  have split := List.take_append_drop u initial
  rw [← after] at split
  rw [whole2, ← split] at whole
  apply List.append_cancel_right (bs := bytesToBits (inp.drop (read + used)))
  rw [← whole]
  simp only [List.append_assoc]

#print axioms finalHeap_facts

/-- The situation of the fast call from `LEN`, for input and output in any
caller byte views the dispatch packet admits: distinct blocks or disjoint
ranges of one block (`Separate`). The window block is not the output block
(`callerRange_slow_output`: the caller's output range excludes the
decoder-owned window). -/
theorem inflate_fast_entry {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {bs : List UInt8} {ib io ob oo : Nat}
    (E : Env c h r zs z s) (good : Good h r zs z s)
    (fit : ZlibF.PlatformMemory.ByteObjectsFit h) (tables : DataTablesSafe h s)
    (buffers : DispatchBuffers h r l bs) (pending : DataPendingInvariant s)
    (input : l.next = .ref (.blk ib) io) (output : l.put = .ref (.blk ob) oo)
    (fast : (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    ∃ e : Zlib.Inffast.Proofs.Env,
      e.h0 = setI (r.put h (leaveStream z l)) zs (leaveState s l) ∧
      e.strm = c.strm ∧ e.start = l.out_ ∧ e.r = r ∧ e.stid = zs ∧
      e.sm0 = leaveStream z l ∧ e.s0 = leaveState s l ∧
      e.ib = ib ∧ e.i0 = io ∧ e.ob = ob ∧ e.o0 = oo := by
  have margins : (6 ≤ l.have_ ∧ 258 ≤ l.left) ∧ l.bits < 8 := by
    simpa only [Bool.and_eq_true, decide_eq_true_eq] using fast
  have inputRoom : 6 ≤ l.have_.toNat := by simpa [UInt32.le_iff_toNat_le] using margins.1.1
  have outputRoom : 258 ≤ l.left.toNat := by simpa [UInt32.le_iff_toNat_le] using margins.1.2
  have bits : l.bits.toNat < 8 := by simpa [UInt32.lt_iff_toNat_lt] using margins.2
  have nonempty : bs ≠ [] := by
    intro empty; have := buffers.bits.have_eq; rw [empty] at this; simp at this; omega
  obtain ⟨inref, ina, inoff, inptr, inget, insize, _⟩ := buffers.bits.next.resolve_left nonempty
  have sameInput : inref = .blk ib ∧ inoff = io := by rw [input] at inptr; cases inptr; exact ⟨rfl, rfl⟩
  rcases sameInput with ⟨refEq, offEq⟩
  subst inref
  subst inoff
  obtain ⟨outref, outa, outoff, outptr, outget, outwrite, outsize, _, made, privateWindow⟩ :=
    callerRange_slow_output good l buffers.output.range buffers.output.nonnull buffers.output.count
      buffers.output.produced
  have sameOutput : outref = .blk ob ∧ outoff = oo := by
    rw [output] at outptr; cases outptr; exact ⟨rfl, rfl⟩
  rcases sameOutput with ⟨refEq, offEq⟩
  subst outref
  subst outoff
  have separated : ib ≠ ob ∨ io + l.have_.toNat ≤ oo ∨ oo + l.left.toNat ≤ io := by
    have packet := buffers.separate
    rw [input, output] at packet
    dsimp [Separate] at packet
    rcases packet with zeroIn | zeroOut | disjoint
    · omega
    · omega
    · rcases disjoint with ne | d
      · exact Or.inl (fun same => ne (by rw [same]))
      · exact Or.inr d
  let stream0 := leaveStream z l
  let state0 := leaveState s l
  let heap0 := setI (r.put h stream0) zs state0
  obtain ⟨good0, _, _, sizes0⟩ := leave_restore_invariant E good pending buffers.bits (by omega)
  have fit0 : ZlibF.PlatformMemory.ByteObjectsFit heap0 := sizes0.platform fit
  obtain ⟨lr, lo, la, lp, lg, ls⟩ := tables.lengthTable
  obtain ⟨dr, doff, da, dp, dg, ds⟩ := tables.distanceTable
  have codeViews : ∀ ref : CodeRef,
      (Space.get heap0 ref : Option (Array Code)) = Space.get h ref := by
    intro ref
    unfold heap0 state0 leaveState
    rw [code_views_set_bits (by simpa using E.hs), code_views_put_stream]
  have window : ∃ (wb : Nat) (wa : Array UInt8),
      state0.whave ≠ 0 → state0.window = .ref (.blk wb) 0 ∧ wb ≠ ob ∧
        heap0.bytes wb = some wa ∧ state0.wsize.toNat ≤ wa.size := by
    rcases good.inv.win.block with null | ⟨wb, wa, ptr, get, ro, size⟩
    · refine ⟨0, #[], ?_⟩
      intro live
      have zero := good.inv.win.nullws null
      have whave := good.inv.win.hv
      have : s.whave = 0 := UInt32.toNat_inj.mp (by rw [zero] at whave; simpa using whave)
      exact False.elim (live this)
    · refine ⟨wb, wa, ?_⟩
      intro _
      refine ⟨ptr, fun eq => privateWindow wb ptr (by rw [eq]), by simpa [heap0] using get, ?_⟩
      have := good.inv.win.ws
      change s.wsize.toNat ≤ wa.size
      rw [size]
      omega
  obtain ⟨wb, wa, win⟩ := window
  have wsize : s.wsize.toNat ≤ 32768 := by
    have pow := Nat.pow_le_pow_right (by decide : 0 < 2) good.inv.win.wbits
    have := good.inv.win.ws
    omega
  have inHeap : heap0.bytes ib = some ina := by simpa [heap0] using inget
  have outHeap : heap0.bytes ob = some outa := by simpa [heap0] using outget
  let e : Zlib.Inffast.Proofs.Env := {
    h0 := heap0, strm := c.strm, start := l.out_, r, sm0 := stream0, stid := zs, s0 := state0
    hstrm := E.strm, hsm := good0.live.hz, hrw := by cases r <;> rfl, hstate := good0.live.zst,
    hs0 := good0.live.hs
    ib, i0 := io, IN := ina, hnin := input, hIN := inHeap
    hai := inputRoom, hINsz := by change io + l.have_.toNat ≤ ina.size; rw [buffers.bits.have_eq]; exact insize
    hINbig := fit0 (.blk ib) ina inHeap
    ob, o0 := oo, A0 := outa, hnout := output, hA0 := outHeap
    hro := by simpa [heap0] using outwrite, hao := outputRoom, hAsz := outsize
    hAbig := fit0 (.blk ob) outa outHeap
    hstart := buffers.output.count, hbeg := made
    hsep := by
      by_cases same : ib = ob
      · refine Or.inr ⟨same, ?_⟩
        change io + l.have_.toNat ≤ oo ∨ oo + l.left.toNat ≤ io
        rcases separated with ne | d
        · exact absurd same ne
        · exact d
      · exact Or.inl same
    hbits := bits, hhold := buffers.bits.hold_lt,
    hsane := by change s.sane ≠ 0; rw [pending.sane]; decide
    hws := wsize, hwh := good.inv.win.hv,
    hwn := by change s.wnext.toNat ≤ s.wsize.toNat; have := good.inv.win.wn; omega
    wb, woff := 0, W := wa, hwin := by simpa using win
    rl := lr, ol := lo, LCA := la, hlc := lp, hLCA := by rw [codeViews]; exact lg, hlt := ls
    rd := dr, od := doff, DCA := da, hdc := dp, hDCA := by rw [codeViews]; exact dg, hdt := ds }
  exact ⟨e, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The input and output ranges after a fast call that read `used` bytes
and wrote up to `o`: the remaining input stays apart from the remaining
output room and from the call's output so far. -/
theorem fast_separate {ib ob io oo c left have_ used o : Nat}
    (sepIn : Separate (.ref (.blk ob) oo) left (.ref (.blk ib) io) have_)
    (sepStart : Separate (.ref (.blk ob) (oo - c)) c (.ref (.blk ib) io) have_)
    (cLe : c ≤ oo) (usedLe : used ≤ have_) (ooLe : oo ≤ o) (oLe : o - oo ≤ left)
    (six : 6 ≤ have_) (room : 258 ≤ left) :
    Separate (.ref (.blk ob) o) (left - (o - oo)) (.ref (.blk ib) (io + used)) (have_ - used) ∧
      Separate (.ref (.blk ob) (oo - c)) (c + (o - oo)) (.ref (.blk ib) (io + used))
        (have_ - used) := by
  simp only [Separate] at sepIn sepStart ⊢
  by_cases same : (BRef.blk ob : BRef) = BRef.blk ib
  · simp only [same, ne_eq, not_true_eq_false, false_or] at sepIn sepStart ⊢
    constructor <;> omega
  · exact ⟨Or.inr (Or.inr (Or.inl same)), Or.inr (Or.inr (Or.inl same))⟩

/-- `doomed_of_aligned`, where the rejection may use the full window and the
header of the source at hand. -/
theorem doomed_of_aligned_full {f : LoopFrame} {l : IL} {header bodyDict : List UInt8}
    {dbits rest : List Bool} {pos : DeflatePos}
    (wrapHeader : WrapHeader f.wrap f.configured f.dict header bodyDict)
    (dparsed : DeflateParsed bodyDict dbits pos)
    (bits : bytesToBits (f.logIn ++ f.inp.take (loopRead l)) = bytesToBits header ++ dbits ++ rest)
    (never : ∀ source, Api.FullWindow f.wrap f.configured source → header <+: source →
      ∀ more tail outF, ¬ Resid bodyDict pos (rest ++ more) tail outF) :
    LoopDoomed f l := by
  intro source decoded valid full started
  have pre : header <+: source := by
    have bp : bytesToBits header <+: bytesToBits (f.logIn ++ f.inp.take (loopRead l)) := by
      rw [bits]
      exact ⟨dbits ++ rest, by simp⟩
    exact (bytesToBits_prefix_iff.mp bp).trans started
  exact MeaningBlock.doomed_of_aligned wrapHeader dparsed bits
    (fun more tail outF _ => never source full pre more tail outF) source decoded valid full started

set_option maxHeartbeats 8000000 in
/-- `case LEN` on the fast branch: `RESTORE; inflate_fast(strm, out); LOAD`.
The call decodes tokens until the room runs out (`LoopMatches` at a later
token boundary of the same block), the block ends (`LoopMatches` at a block
boundary or after the final block, fewer than 8 held bits), or a token is
rejected (`BAD`, and the input read has no valid completion: the rejected
token is rejected on its own bits, `actual_body_rejects_prefix`, and the
history the fast decoder checks a distance against is the whole history or a
full 32 KiB window when the source has a full window).

Hypotheses beyond `LoopMatches` and the stream record: the safety invariant of
the decoder state (`Good`, `DataTablesSafe`, `DataPendingInvariant`), the caller
packet (`DispatchBuffers`, whose `Separate` admits input and output as
disjoint ranges of one block), and the platform premise. The window block is
not the output block; this comes from the caller's output range
(`callerRange_slow_output`), not from a premise. -/
theorem fast_call_meaning {c : Ctx} {f : LoopFrame} {h : Heap} {l : IL} {r : ZStreamRef} {z : ZStream}
    {ib io ob oo : Nat}
    (loop : LoopMatches c f h l) (strm : c.strm = some r) (hz : r.get h = some z)
    (fast : (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true)
    (state : ∀ zs s, c.st = some (.tab zs) → h.istates zs = some s →
      s.mode = LEN ∧ Good h r zs z s ∧ DataTablesSafe h s ∧ DataPendingInvariant s)
    (fit : ZlibF.PlatformMemory.ByteObjectsFit h)
    (buffers : DispatchBuffers h r l (f.inp.drop (loopRead l)))
    (input : l.next = .ref (.blk ib) io) (output : l.put = .ref (.blk ob) oo)
    (rawWidth : f.wrap = .raw → f.configured ≠ 0) :
    ∃ l' h', runX (inflate_LEN c) l h = .ok ((.ok (), l'), h') ∧ loopRead l ≤ loopRead l' ∧
      (LoopMatches c f h' l' ∨
        ((∀ zs s, c.st = some (.tab zs) → h'.istates zs = some s → s.mode = BAD) ∧
          LoopDoomed f l')) := by
  obtain ⟨zs, s, callOut, consumed, held, stage, st, hs, retOk, config, haveLe, inLen, binv, leftLe,
    ⟨_, pendBody⟩, putEq, outBytes, _, sepIn0, _, sepOutIn0, bitsEq, heldBits, parsed,
    stageM, wrapM, outputEq⟩ := loop
  obtain ⟨mode, good, tables, pending⟩ := state zs s st hs
  have E : Env c h r zs z s := ⟨strm, st, hz, hs⟩
  obtain ⟨header, out, final, L, D, rfl⟩ := stage_of_len stageM (Or.inl mode)
  have pendBase := pendBody _ _ rfl
  obtain ⟨⟨last, lenTable, distTable, _⟩, window, check⟩ := stageM
  obtain ⟨bodyDict, bitsP, wrapHeader, consumedEq, deflate⟩ := parsed
  obtain ⟨extL, extD⟩ := deflateParsed_codes_ext deflate L D .none rfl
  have heldEq : held = natBits l.bits.toNat l.hold.toNat := MeaningBits.HeldBits.eq_natBits heldBits
  have outEq0 : out = f.logOut ++ callOut := outputEq
  obtain ⟨e, heapEq, strmEq, startEq, refEq, idEq, streamEq, stateEq, ibEq, i0Eq, obEq, o0Eq⟩ :=
    inflate_fast_entry E good fit tables buffers pending input output fast
  have margins : (6 ≤ l.have_ ∧ 258 ≤ l.left) ∧ l.bits < 8 := by
    simpa only [Bool.and_eq_true, decide_eq_true_eq] using fast
  have haveSix : 6 ≤ l.have_.toNat := by simpa [UInt32.le_iff_toNat_le] using margins.1.1
  obtain ⟨dest, outArr, outOff, putPtr, outGet0, outRo0, outFit0, _, _, privateWindow⟩ :=
    callerRange_slow_output good l buffers.output.range buffers.output.nonnull buffers.output.count
      buffers.output.produced
  rw [output] at putPtr
  obtain ⟨destEq, offEq⟩ := Ptr.ref.inj putPtr
  subst destEq offEq
  have pendNat : l.out_.toNat - l.left.toNat = callOut.length := pendBase
  -- the output start
  obtain ⟨startF, startLe⟩ : f.start = .ref (.blk ob) (oo - callOut.length) ∧ callOut.length ≤ oo := by
    rw [output] at putEq
    cases hst : f.start with
    | null => rw [hst] at putEq; simp [inputAdvance] at putEq
    | ref d o' =>
      rw [hst] at putEq
      obtain ⟨d1, o1⟩ := Ptr.ref.inj putEq
      subst d1
      exact ⟨by rw [o1, Nat.add_sub_cancel], by omega⟩
  -- the fast call's situation
  have heap0 : e.h0 = setI (r.put h (leaveStream z l)) zs (leaveState s l) := heapEq
  have ref0 : e.r = r := refEq
  have id0 : e.stid = zs := idEq
  have state0 : e.s0 = leaveState s l := stateEq
  have stream0 : e.sm0 = leaveStream z l := streamEq
  have ib0 : e.ib = ib := ibEq
  have i00 : e.i0 = io := i0Eq
  have ob0 : e.ob = ob := obEq
  have o00 : e.o0 = oo := o0Eq
  have strm0 : e.strm = c.strm := strmEq
  have start0 : e.start = l.out_ := startEq
  have bytesEq : ∀ b, e.h0.bytes b = h.bytes b := by
    intro b
    rw [heap0]
    simp only [setI, Zlib.Inffast.Proofs.put_bytes]
  have codesEq : ∀ ref : CodeRef, (Space.get e.h0 ref : Option (Array Code)) = Space.get h ref := by
    intro ref
    rw [heap0]
    unfold leaveState
    rw [code_views_set_bits (by rw [Zlib.Inffast.Proofs.put_istates]; exact hs),
      code_views_put_stream]
  have tbls : Zlib.Inffast.Spec.BodyToken.Tables e L D :=
    fast_tables e codesEq (by rw [state0]; rfl) (by rw [state0]; rfl) (by rw [state0]; rfl)
      (by rw [state0]; rfl) lenTable distTable
  -- the history of the matches
  have bounds : s.wnext ≤ s.whave ∧ s.whave ≤ s.wsize := by
    have hv := good.inv.win.hv
    have wn := good.inv.win.wn
    have weq := good.inv.win.eq
    refine ⟨UInt32.le_iff_toNat_le.mpr ?_, UInt32.le_iff_toNat_le.mpr hv⟩
    by_cases lt : s.whave.toNat < s.wsize.toNat
    · have := weq lt
      omega
    · omega
  have wsizeBits : s.wsize ≠ 0 → s.wsize.toNat = 2 ^ s.wbits.toNat := by
    intro nz
    rcases good.inv.win.ws with z0 | full
    · exact absurd (UInt32.toNat_inj.mp (by simpa using z0)) nz
    · exact full
  have haveBound : s.whave.toNat ≤ bodyDict.length + f.logOut.length :=
    window_have_le (s := loopState s l) bounds wsizeBits config wrapM.2.1 wrapM.2.2 rawWidth
      wrapHeader window
  have tail : bodyDict ++ f.logOut <:+ f.dict ++ f.logOut := by
    obtain ⟨p, pe⟩ := wrapHeader_suffix wrapHeader
    exact ⟨p, by rw [pe, List.append_assoc]⟩
  have suffix : hist e <:+ bodyDict ++ f.logOut :=
    hist_suffix e good bytesEq (by rw [state0]; rfl) (by rw [state0]; rfl) (by rw [state0]; rfl)
      (by rw [state0]; rfl) window haveBound tail
  -- the output before the fast call
  have bg0 : e.bg = oo - callOut.length := by
    show e.o0 - (e.start.toNat - e.sm0.avail_out.toNat) = _
    rw [o00, start0, stream0]
    show oo - (l.out_.toNat - l.left.toNat) = _
    rw [pendNat]
  have a00 : h.bytes ob = some e.A0 := by rw [← bytesEq, ← ob0]; exact e.hA0
  have curEq0 : cur e e.A0 e.o0 = callOut := by
    rcases outBytes with ⟨null, _, _⟩ | ⟨rr, ii, aa, ptr, get, _, eq⟩
    · rw [startF] at null; cases null
    · rw [startF] at ptr
      obtain ⟨r1, i1⟩ := Ptr.ref.inj ptr
      subst r1 i1
      have : aa = e.A0 := Option.some.inj (get.symm.trans a00)
      subst this
      rw [eq]
      simp only [cur, ZlibF.Math.LZ77Copy.writtenBytes, o00, bg0]
      congr 2 <;> omega
  -- the fact kept between tokens
  let Q : Nat → List UInt8 → Prop := fun u current =>
    DeflateParsed bodyDict (bitsP ++ (Zlib.Inffast.Spec.Origin.initial e).take u)
      ⟨f.logOut ++ current, final, .codes L D .none⟩
  have step : ∀ u u' current next, u ≤ u' → Q u current →
      Token.Step L D (hist e) current (src e u) (src e u') next false → Q u' next := by
    intro u u' current next _ q tok
    obtain ⟨tb, split, tok'⟩ := tok.strip extL extD
    have bitsSplit := take_of_drop split
    show DeflateParsed _ _ _
    rw [bitsSplit, ← List.append_assoc]
    exact .token q (tok'.rebase suffix)
  have q0 : Q 0 (cur e e.A0 e.o0) := by
    show DeflateParsed _ _ _
    rw [List.take_zero, List.append_nil, curEq0, ← outEq0]
    exact deflate
  obtain ⟨lenPrefix, distPrefix⟩ := fast_prefix e codesEq (by rw [state0]; rfl) (by rw [state0]; rfl)
    (by rw [state0]; rfl) (by rw [state0]; rfl) lenTable distTable
  obtain ⟨A, msg, md, hold, bits, used, o, u, run, usedLe, oLo, oHi, Asz, bitsLt, origin, frameEnd,
    outcome⟩ :=
    fast_call_tokens e L D tbls lenPrefix distPrefix Q step q0
  -- the actual branch up to LOAD
  have execution : Zlib.Inffast.inflate_fast c.strm l.out_
      (setI (r.put h (leaveStream z l)) zs (leaveState s l)) =
        .ok ((), finalHeap e A msg md hold bits used o) := by
    have := run
    simp only [C.run] at this
    rw [strm0, start0, heap0] at this
    exact this
  have cut : runX (inflate_LEN c) l h =
      runX (inflateAfterFast c) l (finalHeap e A msg md hold bits used o) := by
    unfold inflate_LEN
    rw [runX_bind, runX_get]
    simp only [fast, ↓reduceIte]
    rw [runX_bind, RESTORE_pending_run E]
    simp only []
    rw [runX_bind, runX_lift_ok execution]
    rfl
  obtain ⟨hsH, bytesOther, bytesOut, roH, codesH, streamH⟩ :=
    finalHeap_facts e heap0 ref0 id0 state0 hs A msg md hold bits used o
  have E1 : Env c (finalHeap e A msg md hold bits used o) r zs _
      { s with mode := md, hold := hold, bits := bits } := ⟨strm, st, streamH, hsH⟩
  rw [cut, inflateAfterFast_run E1]
  dsimp only
  have regsEq : ({ l with put := .ref (.blk e.ob) o, left := UInt32.ofNat (e.sm0.avail_out.toNat - (o - e.o0)), next := .ref (.blk e.ib) (e.i0 + used), have_ := UInt32.ofNat (e.sm0.avail_in.toNat - used), hold := hold, bits := bits } : IL) = fastRegs l ib io ob oo used o hold bits := by
    rw [ob0, ib0, i00, o00, stream0]
    rfl
  -- facts shared by the outcomes
  have mode0 : e.s0.mode = LEN := by rw [state0]; exact mode
  have usedLe' : used ≤ l.have_.toNat := by rw [stream0] at usedLe; exact usedLe
  have ooLe : oo ≤ o := by rw [o00] at oLo; exact oLo
  have oLe : o - oo ≤ l.left.toNat := by
    rw [o00, stream0] at oHi
    change o ≤ oo + l.left.toNat at oHi
    omega
  have haveLen : l.have_.toNat = (f.inp.drop (loopRead l)).length := binv.have_eq
  have inArr : h.bytes ib = some e.IN := by rw [← bytesEq, ← ib0]; exact e.hIN
  obtain ⟨view, inFit⟩ : f.inp.drop (loopRead l) =
      (e.IN.toList.drop io).take (f.inp.drop (loopRead l)).length ∧
      io + l.have_.toNat ≤ e.IN.size := by
    rcases binv.next with empty | ⟨rr, aa, off, ptr, get, fits, eq⟩
    · rw [empty] at haveLen
      simp at haveLen
      omega
    · rw [input] at ptr
      obtain ⟨r1, o1⟩ := Ptr.ref.inj ptr
      subst r1 o1
      have : aa = e.IN := Option.some.inj (get.symm.trans inArr)
      subst this
      exact ⟨eq, by rw [haveLen]; exact fits⟩
  have inGet : (Space.get (finalHeap e A msg md hold bits used o) (BRef.blk ib) :
      Option (Array UInt8)) = some (e.inArr A) := by
    unfold Zlib.Inffast.Proofs.Env.inArr
    by_cases same : e.ib = e.ob
    · rw [if_pos same, ← ib0, same]
      exact bytesOut
    · rw [if_neg same]
      exact (bytesOther ib (fun eq => same (ib0.trans eq))).trans inArr
  have viewA : f.inp.drop (loopRead l) =
      ((e.inArr A).toList.drop io).take (f.inp.drop (loopRead l)).length := by
    have hl := haveLen
    generalize hn : (f.inp.drop (loopRead l)).length = n at view hl ⊢
    rw [view]
    apply List.ext_getElem?
    intro k
    simp only [List.getElem?_take, List.getElem?_drop, Array.getElem?_toList]
    by_cases hk : k < n
    · simp only [hk, ite_true]
      exact (frameEnd.get (k := io + k) (by rw [i00]; omega)
        (by rw [i00, stream0]; change io + k < io + l.have_.toNat; omega)).symm
    · simp only [hk, ite_false]
  have inFitA : io + l.have_.toNat ≤ (e.inArr A).size := by
    rw [e.inArr_size frameEnd]; exact inFit
  obtain ⟨sepNext, sepStart⟩ := fast_separate (ib := ib) (ob := ob) (io := io) (oo := oo)
    (left := l.left.toNat) (have_ := l.have_.toNat) (c := callOut.length) (used := used) (o := o)
    (by rw [← output, ← input]; exact sepIn0) (by rw [← startF, ← input]; exact sepOutIn0)
    startLe usedLe' ooLe oLe haveSix (by simpa [UInt32.le_iff_toNat_le] using margins.1.2)
  have outGet : (Space.get (finalHeap e A msg md hold bits used o) (BRef.blk ob) :
      Option (Array UInt8)) = some A := by rw [← ob0]; exact bytesOut
  have outRo : Space.ro (finalHeap e A msg md hold bits used o) (BRef.blk ob) = false :=
    (roH ob).trans outRo0
  have outFit : oo + l.left.toNat ≤ A.size := by
    have := e.hAsz
    rw [o00, stream0] at this
    rw [Asz]
    exact this
  have newOutEq : cur e A o = (A.toList.drop (oo - callOut.length)).take (callOut.length + (o - oo)) := by
    simp only [cur, ZlibF.Math.LZ77Copy.writtenBytes, bg0]
    congr 2 <;> omega
  have holdLt : hold.toNat < 2 ^ bits.toNat := origin.normalized
  have windowFrame : ∀ (H : Heap), (∀ b, b ≠ e.ob → (Space.get H (BRef.blk b) : Option (Array UInt8)) =
      Space.get h (BRef.blk b)) → WindowMeaning H (loopState s l) f.dict f.logOut := by
    intro H other
    apply Zlib.Inflate.Proofs.WindowMeaning.frame _ window
    intro rr off ptr
    rcases good.inv.win.block with null | ⟨w, _, wptr, _, _, _⟩
    · have : s.window = .ref rr off := ptr
      rw [null] at this
      cases this
    · have : s.window = .ref rr off := ptr
      rw [wptr] at this
      obtain ⟨r1, _⟩ := Ptr.ref.inj this
      subst r1
      exact other w (fun same => privateWindow w wptr (by rw [same, ob0]))
  have sepWin : Separate (.ref (.blk ob) o) (l.left.toNat - (o - oo)) s.window s.wsize.toNat := by
    rcases good.inv.win.block with null | ⟨w, _, wptr, _, _, _⟩
    · right; right
      rw [null]
      trivial
    · right; right
      rw [wptr]
      exact Or.inl (privateWindow w wptr)
  have check' : CheckMeaning (loopState s l) f.wrap header f.logOut := by
    rw [pendBase, List.length_append, Nat.add_sub_cancel, List.take_left' rfl] at check
    exact check
  have initialEq : Zlib.Inffast.Spec.Origin.initial e = held ++ bytesToBits (f.inp.drop (loopRead l)) := by
    rw [heldEq, view]
    show Zlib.Inffast.Proofs.bitsOfNat e.s0.hold.toNat e.s0.bits.toNat ++
      bytesToBits ((e.IN.toList.drop e.i0).take (e.i0 + e.sm0.avail_in.toNat - e.i0)) = _
    rw [state0, i00, stream0, natBits_testBit]
    have amount : io + (leaveStream z l).avail_in.toNat - io = (f.inp.drop (loopRead l)).length := by
      show io + l.have_.toNat - io = _
      omega
    rw [amount]
    rfl
  have dropEq : f.inp.drop (loopRead l + used) =
      (e.IN.toList.drop (io + used)).take ((f.inp.drop (loopRead l)).length - used) := by
    have v := congrArg (List.drop used) view
    rw [List.drop_take, List.drop_drop] at v
    rw [v, List.drop_drop]
  have afterEq : natBits bits.toNat hold.toNat ++ bytesToBits (f.inp.drop (loopRead l + used)) =
      (Zlib.Inffast.Spec.Origin.initial e).drop u := by
    rw [← origin.stream]
    show _ = Zlib.Inffast.Proofs.bitsOfNat hold.toNat bits.toNat ++
      bytesToBits ((e.IN.toList.drop (e.i0 + used)).take (e.i0 + e.sm0.avail_in.toNat - (e.i0 + used)))
    rw [dropEq, natBits_testBit, i00, stream0]
    have amount : io + (leaveStream z l).avail_in.toNat - (io + used) =
        (f.inp.drop (loopRead l)).length - used := by
      show io + l.have_.toNat - (io + used) = _
      omega
    rw [amount]
    rfl
  have bitsEq' : bytesToBits (f.logIn ++ f.inp.take (loopRead l + used)) =
      (bytesToBits header ++ (bitsP ++ (Zlib.Inffast.Spec.Origin.initial e).take u)) ++
        natBits bits.toNat hold.toNat := by
    rw [fast_bits bitsEq initialEq afterEq, consumedEq]
    simp only [List.append_assoc]
  have readLe : loopRead l ≤ loopRead (fastRegs l ib io ob oo used o hold bits) := by
    simp only [loopRead, fastRegs]
    rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by have := l.have_.toNat_lt; omega)]
    omega
  rcases outcome with ⟨mdEq, q⟩ | ⟨mdType, u0, _, q, tok⟩ | ⟨mdBad, u0, u0le, q, rejected⟩
  · -- more tokens of the same block
    have md' : md = LEN := mdEq.trans mode0
    rw [if_neg (show ¬ md = TYPE by rw [md']; decide)]
    refine ⟨fastRegs l ib io ob oo used o hold bits, _, by rw [← regsEq], readLe, Or.inl ?_⟩
    exact fast_rebuild (bk := s.back) st retOk config (show md ≠ SYNC by rw [md']; decide) haveLe inLen leftLe
      pendBase sepNext sepStart startF startLe usedLe' ooLe oLe haveLen viewA inFitA hsH inGet outGet outRo
      outFit newOutEq holdLt (windowFrame _ bytesOther) sepWin check' wrapM.1 wrapM.2.1 wrapM.2.2
      wrapHeader bitsEq' q
      ⟨last, Zlib.Inflate.Proofs.TableMeaning.frame codesH lenTable, Zlib.Inflate.Proofs.TableMeaning.frame codesH distTable,
        Or.inr md', Or.inl bitsLt⟩ rfl
  · -- the end of the block
    rw [if_pos mdType]
    have flat : ({ { s with mode := md, hold := hold, bits := bits } with back := -1 } : InflateState) =
        { s with mode := md, hold := hold, bits := bits, back := -1 } := rfl
    rw [flat]
    obtain ⟨tb, split, tok'⟩ := tok.strip extL extD
    have bitsSplit := take_of_drop split
    have tok'' := tok'.rebase suffix
    refine ⟨fastRegs l ib io ob oo used o hold bits, _, by rw [← regsEq], readLe, Or.inl ?_⟩
    have hsT := setI_istates_same (finalHeap e A msg md hold bits used o) zs
      { s with mode := md, hold := hold, bits := bits, back := -1 }
    have codesT : ∀ ref : CodeRef, (Space.get (setI (finalHeap e A msg md hold bits used o) zs
        { s with mode := md, hold := hold, bits := bits, back := -1 }) ref :
          Option (Array Code)) = Space.get h ref := by
      intro ref
      exact (MeaningDistance.code_get_setI (s' := { s with mode := md, hold := hold, bits := bits, back := -1 }) hsH rfl ref).trans (codesH ref)
    have otherT : ∀ b, b ≠ e.ob → (Space.get (setI (finalHeap e A msg md hold bits used o) zs
        { s with mode := md, hold := hold, bits := bits, back := -1 }) (BRef.blk b) :
          Option (Array UInt8)) = Space.get h (BRef.blk b) := by
      intro b ne
      rw [byte_view_get_setI]
      exact bytesOther b ne
    have common := fun (pos : DeflatePos) (parsed : DeflateParsed bodyDict
        (bitsP ++ (Zlib.Inffast.Spec.Origin.initial e).take u) pos)
        (body : BodyMatches (setI (finalHeap e A msg md hold bits used o) zs
          { s with mode := md, hold := hold, bits := bits, back := -1 })
          { s with mode := md, hold := hold, bits := bits, back := -1 } pos)
        (outEq : pos.out = f.logOut ++ cur e A o) =>
      fast_rebuild (bk := -1) st retOk config (show md ≠ SYNC by rw [mdType]; decide) haveLe inLen leftLe
        pendBase sepNext sepStart startF startLe usedLe' ooLe oLe haveLen viewA inFitA hsT
        (by rw [byte_view_get_setI]; exact inGet) (by rw [byte_view_get_setI]; exact outGet)
        (by rw [byte_view_ro_setI]; exact outRo)
        outFit newOutEq holdLt (windowFrame _ otherT) sepWin check' wrapM.1 wrapM.2.1 wrapM.2.2
        wrapHeader bitsEq' parsed body outEq
    cases final with
    | false =>
      apply common ⟨f.logOut ++ cur e A o, false, .boundary⟩ ?_ ?_ rfl
      · rw [bitsSplit, ← List.append_assoc]
        exact .endOfBlock q tok''
      · have l0 : s.last = (if false then (1 : Int32) else 0) := last
        exact ⟨Or.inl mdType, rfl, by simpa using l0, bitsLt⟩
    | true =>
      apply common ⟨f.logOut ++ cur e A o, true, .finished⟩ ?_ ?_ rfl
      · rw [bitsSplit, ← List.append_assoc]
        exact .endOfFinal q tok''
      · have l1 : s.last = (if true then (1 : Int32) else 0) := last
        exact ⟨Or.inl mdType, rfl, by simpa using l1, bitsLt⟩
  · -- a rejected token
    rw [if_neg (show ¬ md = TYPE by rw [mdBad]; decide)]
    refine ⟨fastRegs l ib io ob oo used o hold bits, _, by rw [← regsEq], readLe, Or.inr ⟨?_, ?_⟩⟩
    · intro zs' s' st' hs'
      rw [st] at st'
      cases st'
      rw [hsH] at hs'
      cases hs'
      exact mdBad
    · have readEq : loopRead (fastRegs l ib io ob oo used o hold bits) = loopRead l + used := by
        simp only [loopRead, fastRegs]
        rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by have := l.have_.toNat_lt; omega)]
        omega
      have takeSplit : (Zlib.Inffast.Spec.Origin.initial e).take u =
          (Zlib.Inffast.Spec.Origin.initial e).take u0 ++ (src e u0).take (u - u0) := by
        rw [show u = u0 + (u - u0) by omega, List.take_add, Nat.add_sub_cancel_left]
        rfl
      apply doomed_of_aligned_full (rest := (src e u0).take (u - u0) ++ natBits bits.toNat hold.toNat)
        wrapHeader q
      · rw [readEq, bitsEq', takeSplit]
        simp only [List.append_assoc]
      · intro source full pre more tail outF resid
        obtain ⟨_, _, r', h'', symbols, _⟩ := resid
        have w15 : s.wbits.toNat = 15 :=
          full_width (s := loopState s l) config wrapM.2.1 wrapHeader full pre
        have histLen : (hist e).length = s.whave.toNat := by
          have wh : e.s0.whave = s.whave := by rw [state0]; rfl
          simp [hist, Zlib.Inffast.Spec.MatchHistory.saved, wh]
        obtain ⟨p, pe⟩ := wrapHeader_suffix wrapHeader
        have dictLen : f.dict.length = p.length + bodyDict.length := by rw [pe, List.length_append]
        have enough : 32768 ≤ (hist e).length ∨ (bodyDict ++ f.logOut).length ≤ (hist e).length := by
          rw [histLen, List.length_append]
          rcases window with ⟨nz, dictn⟩ | ⟨_, h0, hEmpty⟩
          · have wl : s.whave.toNat =
                ((f.dict ++ f.logOut).drop ((f.dict ++ f.logOut).length - s.wsize.toNat)).length :=
              dictionary_length (s := loopState s l) bounds dictn
            have ws : s.wsize.toNat = 32768 := by rw [wsizeBits nz, w15]
            simp only [List.length_drop, List.length_append] at wl
            omega
          · have e0 : (f.dict ++ f.logOut).length = 0 := by rw [hEmpty]; rfl
            simp only [List.length_append] at e0
            right
            omega
        have rj := (rejected (natBits bits.toNat hold.toNat ++ more)).rebase enough
        exact ZlibF.Spec.Token.rejected_has_no_symbols _ _ _ _ _
          (by simpa only [List.append_assoc] using rj) r' h''
          (by simpa only [List.append_assoc] using symbols)

#print axioms fast_call_meaning

#print axioms fast_tables
#print axioms hist_suffix

end Zlib.Inflate.Proofs.MeaningFast
