import ZlibF.Proof.«inflate.c.meaning-match»
import ZlibF.Proof.«inflate.c.distance-extra»
import ZlibF.Proof.«inflate.c.distance-finish»
import ZlibF.Proof.«inflate.c.meaning-lookup»
import ZlibF.Proof.«inftrees.c.decode.forward»

/-!
# inflate.c: `LENEXT`, `DIST` and `DISTEXT` keep the format meaning

`case LENEXT` waits for the extra bits of the length, adds them to `length`,
copies it to `was` and falls through to `case DIST`: the parse moves from the
length symbol (`Pending.lengthExtra`) to the complete length
(`Pending.distance`).

`case DIST` looks up the distance symbol in the root table and, through a
link, in a second-level table. A byte is pulled only while the selected entry
does not fit the held bits (`lookupLoop_fail`), so when the call leaves for
input the held bits without their last byte hold no valid distance symbol
(the bound of `BodyMatches` at `.distance`, P13): a valid symbol in them
would have a fitting entry (`lookup_of_decode`). A fitted rejected entry
(`op & 64`) has no valid symbol on any continuation (`fitted_leaf_meaning`),
so the token is rejected (`Token.Rejected.distance`). A fitted accepted entry
is the canonical symbol; its code is dropped and the parse reaches the
started distance (`Pending.distanceExtra`) with fewer than 8 bits left.

`case DISTEXT` waits for the extra bits of the distance, adds them to the
base in `offset`, drops them and falls through to `case MATCH`. The parse
reaches the complete match with nothing written (`PendingParsed` at `.copy`,
P12), whose distance is not yet checked against the history; `match_step`
then copies or rejects it. Waiting for input keeps each position with more
held bits, within its bound.
-/

namespace Zlib.Inflate.Proofs.MeaningDistance
open C Zlib.Inflate Zlib.Inflate.Proofs Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs.MeaningLit Zlib.Inflate.Proofs.MeaningCopy Zlib.Inflate.Proofs.MeaningBits
open Zlib.Inflate.Proofs.MeaningBlock Zlib.Inflate.Proofs.MeaningMatch ZlibF.Spec.Proofs Zlib.Inffast.Spec
set_option autoImplicit false

/-! ## Heap and table facts of a state update -/

theorem code_get_setI {h : Heap} {zs : Nat} {s s' : InflateState} (hs : h.istates zs = some s)
    (codes : s'.codes = s.codes) (cref : CodeRef) :
    (Space.get (setI h zs s') cref : Option (Array Code)) = Space.get h cref := by
  cases cref with
  | istate_codes id =>
      by_cases same : id = zs
      · subst same
        simp [Space.get, setI, hs, codes]
      · simp [Space.get, setI, upd, Tbl.get_set, same]
  | st_lenfix => rfl
  | st_distfix => rfl

theorem table_setI {h : Heap} {zs : Nat} {s s' : InflateState} (hs : h.istates zs = some s)
    (codes : s'.codes = s.codes) {pointer : CodePtr} {root type : UInt32} {lens : List Nat}
    (table : TableMeaning h pointer root type lens) : TableMeaning (setI h zs s') pointer root type lens :=
  by
    obtain ⟨ref, offset, arr, used, ptr, get, inv, stable⟩ := table
    exact ⟨ref, offset, arr, used, ptr, by rw [code_get_setI hs codes]; exact get, inv, stable⟩

theorem distExtras_le : ∀ i < 30, distExtras.getD i 0 ≤ 13 := by decide

/-! ## Stage and parse -/

/-- The only stage a `DISTEXT` state can stand for. -/
theorem stage_of_distext {h : Heap} {s : InflateState} {f : LoopFrame} {checked : List UInt8}
    {stage : WrapStage} (stageFacts : LoopStageMatches h s f checked stage) (mode : s.mode = DISTEXT) :
    ∃ header out final L D length dsym,
      stage = .body header ⟨out, final, .codes L D (.distanceExtra length dsym)⟩ := by
  rcases stage with bytes | header | ⟨header, ⟨out, final, pos⟩⟩ | ⟨header, out, bytes⟩ | out
  · obtain ⟨lo, hi⟩ := stageFacts
    rw [mode] at lo hi
    exact absurd hi (by decide)
  · have := stageFacts
    simp only [LoopStageMatches] at this
    rw [mode] at this
    exact absurd this (by decide)
  · obtain ⟨body, _, _⟩ := stageFacts
    rcases pos with _ | _ | remaining | header' | ⟨L, D, pending⟩ | _
    · obtain ⟨m, _⟩ := body
      rw [mode] at m
      rcases m with m | m <;> exact absurd m (by decide)
    · obtain ⟨m, _⟩ := body
      rw [mode] at m
      exact absurd m (by decide)
    · obtain ⟨m, _⟩ := body
      rw [mode] at m
      rcases m with m | m <;> exact absurd m (by decide)
    · obtain ⟨dyn, _⟩ := body
      rcases dynamic_mode dyn with m | m | m <;> (rw [mode] at m; exact absurd m (by decide))
    · obtain ⟨_, _, _, rest⟩ := body
      rcases pending with _ | symbol | length | ⟨length, ds⟩ | ⟨remaining, dist⟩ | byte
      · rw [mode] at rest; rcases rest.1 with m | m <;> exact absurd m (by decide)
      · rw [mode] at rest; exact absurd rest.1 (by decide)
      · rw [mode] at rest; exact absurd rest.1 (by decide)
      · exact ⟨header, out, final, L, D, length, ds, rfl⟩
      · rw [mode] at rest; exact absurd rest.1 (by decide)
      · rw [mode] at rest; exact absurd rest.1 (by decide)
    · obtain ⟨m, _⟩ := body
      rw [mode] at m
      rcases m with m | m <;> exact absurd m (by decide)
  · obtain ⟨m, _⟩ := stageFacts
    rw [mode] at m
    rcases m with m | m <;> exact absurd m (by decide)
  · have m : s.mode = DONE := stageFacts
    rw [mode] at m
    exact absurd m (by decide)

/-- A started distance was reached by a started token. -/
theorem parsed_distext_inv {dict : List UInt8} {bits : List Bool} {out : List UInt8} {final : Bool}
    {L D : List Nat} {length dsym : Nat}
    (parsed : DeflateParsed dict bits ⟨out, final, .codes L D (.distanceExtra length dsym)⟩) :
    ∃ c0 tb, bits = c0 ++ tb ∧ DeflateParsed dict c0 ⟨out, final, .codes L D .none⟩ ∧
      PendingParsed L D tb (.distanceExtra length dsym) := by
  cases parsed with
  | partialToken _ prev pp => exact ⟨_, _, rfl, prev, pp⟩

/-- Reading the extra bits `X` of a started distance completes the match. -/
theorem pending_copy {L D : List Nat} {tb : List Bool} {length dsym dx : Nat}
    (extL : Ext L) (extD : Ext D) (pend : PendingParsed L D tb (.distanceExtra length dsym))
    {X : List Bool} (read : readBits (distExtras.getD dsym 0) X = some (dx, [])) :
    PendingParsed L D (tb ++ X) (.copy length (distBases.getD dsym 0 + dx)) := by
  obtain ⟨symbol, lx, r1, r2, d1, lo, hi, x1, lenEq, e1, dsle⟩ := pend
  exact ⟨symbol, lx, dsym, dx, r1 ++ X, r2 ++ X, [] ++ X, extL _ _ _ X d1, lo, hi,
    readBits_append _ _ _ _ X x1, extD _ _ _ X e1, dsle, by rw [List.nil_append]; exact read, lenEq, rfl⟩

/-! ## The runs of `DISTEXT` -/

/-- The state after the extra bits: the distance in `offset`, mode `MATCH`. -/
def distextState (s : InflateState) (l1 : IL) : InflateState :=
  let b : UInt32 := l1.hold.toUInt32 &&& ((1 : UInt32) <<< s.extra - 1)
  { s with offset := s.offset + b, back := u2i (i2u s.back + s.extra), mode := MATCH }

/-- The registers after the extra bits are dropped. -/
def distextRegs (s : InflateState) (l1 : IL) : IL :=
  { l1 with hold := l1.hold >>> s.extra.toUInt64, bits := l1.bits - s.extra }

theorem distext_run_zero {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {s : InflateState} (E : Env c h r zs z s) (l : IL) (zero : s.extra = 0) :
    runX (inflate_DISTEXT c) l h = runX (inflate_MATCH c) l (setI h zs { s with mode := MATCH }) := by
  have load : ldInflateState c.st h = .ok (s, h) := by rw [E.st, ldI_eq, E.hs]
  unfold inflate_DISTEXT
  simp only [runX_bind, runX_lift_ok load, zero, bne_self_eq_false, Bool.false_eq_true, ite_false,
    runX_setMode E]

theorem distext_run_wait {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {s : InflateState} (E : Env c h r zs z s) {l l1 : IL} (nonzero : s.extra ≠ 0)
    (run : runX (NEEDBITS s.extra) l h = .ok ((.error Ex.leave, l1), h)) :
    runX (inflate_DISTEXT c) l h = .ok ((.error Ex.leave, l1), h) := by
  rw [inflate_DISTEXT_need_cut E.st E.hs nonzero]
  unfold distExtraNeed
  rw [runX_bind, run]

theorem distext_run_ok {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {s : InflateState} (E : Env c h r zs z s) {l l1 : IL} (nonzero : s.extra ≠ 0)
    (small : s.extra.toNat < 32)
    (run : runX (NEEDBITS s.extra) l h = .ok ((.ok (), l1), h)) :
    runX (inflate_DISTEXT c) l h =
      runX (inflate_MATCH c) (distextRegs s l1) (setI h zs (distextState s l1)) := by
  have small64 : s.extra.toNat < 64 := by omega
  rw [inflate_DISTEXT_need_cut E.st E.hs nonzero]
  unfold distExtraNeed
  rw [runX_bind, run]
  simp only [runX_bind, BITS_run l1 h s.extra small, runX_lift, E.st, wrI_eq, E.hs, setI_istates_same,
    DROPBITS_run, small64, setI_setI, setMode]
  rfl

/-! ## The step -/

set_option maxHeartbeats 4000000 in
/-- `case DISTEXT` keeps the format meaning. Without the extra bits it leaves
with all input read (`have = 0`) and the started distance held. Otherwise the
match is complete and `case MATCH` follows (`match_step`): it leaves with no
output room (`left = 0`), copies, or rejects a distance beyond the history
with no valid continuation of the input.

The hypotheses after `loop` are those of `match_step`: the safety invariant of
the decoder state supplies the stream record, the window bounds, `sane ≠ 0`,
the window size, the ring shape and the private window; `rawWidth` comes from
the call's configuration (`Api.inflWbits`). -/
theorem distext_step {c : Ctx} {f : LoopFrame} {h : Heap} {l : IL} {r : ZStreamRef} {z : ZStream}
    (loop : LoopMatches c f h l) (strm : c.strm = some r) (hz : r.get h = some z)
    (distext : ∀ zs s, c.st = some (.tab zs) → h.istates zs = some s → s.mode = DISTEXT)
    (bounds : ∀ zs s, c.st = some (.tab zs) → h.istates zs = some s →
      s.wnext ≤ s.whave ∧ s.whave ≤ s.wsize)
    (sane : ∀ zs s, c.st = some (.tab zs) → h.istates zs = some s → s.sane ≠ 0)
    (wsizeBits : ∀ zs s, c.st = some (.tab zs) → h.istates zs = some s →
      s.wsize ≠ 0 → s.wsize.toNat = 2 ^ s.wbits.toNat)
    (ring : ∀ zs s, c.st = some (.tab zs) → h.istates zs = some s →
      s.whave < s.wsize → s.wnext = s.whave)
    (privateWindow : ∀ zs s, c.st = some (.tab zs) → h.istates zs = some s →
      ∀ w o d i, s.window = .ref w o → l.put = .ref d i → w ≠ d)
    (rawWidth : f.wrap = .raw → f.configured ≠ 0) :
    ∃ result l' h', runX (inflate_DISTEXT c) l h = .ok ((result, l'), h') ∧
      ((result = .error Ex.leave ∧ (l'.have_ = 0 ∨ l.left = 0) ∧ LoopMatches c f h' l') ∨
       (result = .ok () ∧ loopRead l ≤ loopRead l' ∧
         (LoopMatches c f h' l' ∨
          ((∀ zs s, c.st = some (.tab zs) → h'.istates zs = some s → s.mode = BAD) ∧
            LoopDoomed f l')))) := by
  obtain ⟨zs, s, callOut, consumed, held, stage, st, hs, retOk, config, haveLe, inLen, binv, leftLe,
    pendLe, putEq, outBytes, writable, sepIn, sepWin, sepOutIn, bitsEq, heldBits, parsed, stageM,
    wrapM, outputEq⟩ := loop
  have E : Env c h r zs z s := ⟨strm, st, hz, hs⟩
  have mode : s.mode = DISTEXT := distext zs s st hs
  obtain ⟨header, out, final, L, D, length, dsym, rfl⟩ := stage_of_distext stageM mode
  have pendBase := pendLe.2 _ _ rfl
  obtain ⟨⟨last, lenTable, distTable, _, lengthEq, extraEq, offsetEq, bitsLt⟩, window, check⟩ := stageM
  have extraEq' : s.extra.toNat = distExtras.getD dsym 0 := extraEq
  have offsetEq' : s.offset.toNat = distBases.getD dsym 0 := offsetEq
  have bitsLt' : l.bits.toNat < 8 + s.extra.toNat := bitsLt
  obtain ⟨bodyDict, bitsP, wrapHeader, consumedEq, deflate⟩ := parsed
  obtain ⟨c0, tb, rfl, prev, pend⟩ := parsed_distext_inv deflate
  have dsle : dsym ≤ 29 := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, le⟩ := pend
    exact le
  obtain ⟨extL, extD⟩ := deflateParsed_codes_ext prev L D .none rfl
  have extraLe : s.extra.toNat ≤ 13 := by rw [extraEq']; exact distExtras_le dsym (by omega)
  have baseBound := distBases_extra dsym (by omega)
  have heldEq : held = natBits l.bits.toNat l.hold.toNat := HeldBits.eq_natBits heldBits
  subst heldEq
  have window' := fun (s' : InflateState) (l' : IL) (wnd : s'.window = s.window)
      (ws : s'.wsize = s.wsize) (wn : s'.wnext = s.wnext) (wh : s'.whave = s.whave) =>
    window_transfer (s := loopState s l) (s' := loopState s' l') wnd ws wn wh
      (fun q => byte_view_get_setI h zs s' q) window
  -- `MATCH` on a complete match
  have viaMatch : ∀ (s2 : InflateState) (l2 : IL), s2.mode = MATCH → s2.window = s.window →
      s2.wsize = s.wsize → s2.wnext = s.wnext → s2.whave = s.whave → s2.wbits = s.wbits →
      s2.sane = s.sane → RegsKeep l l2 → loopRead l ≤ loopRead l2 →
      LoopMatches c f (setI h zs s2) l2 →
      ∃ result l' h', runX (inflate_MATCH c) l2 (setI h zs s2) = .ok ((result, l'), h') ∧
        ((result = .error Ex.leave ∧ (l'.have_ = 0 ∨ l.left = 0) ∧ LoopMatches c f h' l') ∨
         (result = .ok () ∧ loopRead l ≤ loopRead l' ∧
           (LoopMatches c f h' l' ∨
            ((∀ zs s, c.st = some (.tab zs) → h'.istates zs = some s → s.mode = BAD) ∧
              LoopDoomed f l')))) := by
    intro s2 l2 m2 wnd ws wn wh wb sn keep more loop2
    have same : ∀ zs' s', c.st = some (.tab zs') → (setI h zs s2).istates zs' = some s' → s' = s2 := by
      intro zs' s' st' hs'
      rw [st] at st'
      cases st'
      rw [setI_istates_same] at hs'
      cases hs'
      rfl
    obtain ⟨result, l', h', run, rest⟩ := match_step loop2 strm (by rw [ZStreamRef.get_setI]; exact hz)
      (fun zs' s' st' hs' => by rw [same zs' s' st' hs']; exact m2)
      (fun zs' s' st' hs' => by rw [same zs' s' st' hs', wn, wh, ws]; exact bounds zs s st hs)
      (fun zs' s' st' hs' => by rw [same zs' s' st' hs', sn]; exact sane zs s st hs)
      (fun zs' s' st' hs' => by rw [same zs' s' st' hs', ws, wb]; exact wsizeBits zs s st hs)
      (fun zs' s' st' hs' => by rw [same zs' s' st' hs', wh, ws, wn]; exact ring zs s st hs)
      (fun zs' s' st' hs' w o d i hw hp => by
        rw [same zs' s' st' hs', wnd] at hw
        rw [keep.2.2.2.1] at hp
        exact privateWindow zs s st hs w o d i hw hp)
      rawWidth
    refine ⟨result, l', h', run, ?_⟩
    rcases rest with ⟨leave, left0, rfl, rfl⟩ | ⟨ok, read, rest⟩
    · exact Or.inl ⟨leave, Or.inr (keep.2.2.1.symm.trans left0), loop2⟩
    · exact Or.inr ⟨ok, by omega, rest⟩
  by_cases zero : s.extra = 0
  · -- no extra bits
    have zeroNat : s.extra.toNat = 0 := by rw [zero]; rfl
    have pp := pending_copy (X := []) extL extD pend (dx := 0)
      (by rw [← extraEq', zeroNat]; rfl)
    have loop2 := loop_move (s' := { s with mode := MATCH }) (l' := l) (j := 0)
      (pos := ⟨out, final, .codes L D (.copy length (distBases.getD dsym 0 + 0))⟩) st retOk
      ⟨config.1, config.2.1, config.2.2.1, config.2.2.2.1, config.2.2.2.2.1, show MATCH ≠ SYNC by decide⟩
      haveLe inLen leftLe pendBase putEq outBytes writable sepIn sepWin sepOutIn
      ⟨rfl, rfl, rfl, rfl, rfl⟩ (by omega) (inputAdvance_zero l.next).symm binv
      (by rw [bitsEq, consumedEq]; simp only [List.append_assoc, List.append_nil]; rfl)
      (HeldBits.of_natBits (s := loopState { s with mode := MATCH } l) binv.hold_lt) wrapHeader
      rfl (DeflateParsed.partialToken (tb ++ []) prev pp)
      ⟨last, table_setI (s' := { s with mode := MATCH }) hs rfl lenTable,
        table_setI (s' := { s with mode := MATCH }) hs rfl distTable, rfl, lengthEq,
        by show s.offset.toNat = _; rw [offsetEq']; rfl,
        by show l.bits.toNat < 8; omega⟩
      (window' _ _ rfl rfl rfl rfl) check wrapM outputEq
    obtain ⟨result, l', h', run, rest⟩ := viaMatch { s with mode := MATCH } l rfl rfl rfl rfl rfl rfl rfl
      ⟨rfl, rfl, rfl, rfl, rfl⟩ (Nat.le_refl _) loop2
    exact ⟨result, l', h', (distext_run_zero E l zero).trans run, rest⟩
  · -- the extra bits
    obtain ⟨result, l1, j, run, jle, binv1, streamEq, _, shape, bitsBound, _, enough, empty,
      kinds, nextEq⟩ := NEEDBITS_run_cursor binv s.extra (by omega)
    have haveOld := binv.have_eq
    have haveNew := binv1.have_eq
    simp only [List.length_drop, loopRead] at haveOld haveNew jle
    have keep1 : RegsKeep l l1 := RegsKeep.of_shape shape
    have readEq : loopRead l1 = loopRead l + j := by
      simp only [loopRead, keep1.1]
      omega
    have used : l1.have_.toNat + j = l.have_.toNat := by omega
    have bits1 := bits_pull bitsEq readEq streamEq
    have binvL : BitInv h l1 (f.inp.drop (loopRead l1)) := by
      rw [readEq, ← List.drop_drop]
      exact binv1
    rcases kinds with rfl | rfl
    · -- the extra bits are held
      have available : s.extra.toNat ≤ l1.bits.toNat := enough rfl
      have bound1 : l1.bits.toNat < 8 + s.extra.toNat := by
        have : l1.bits.toNat ≤ max l.bits.toNat (s.extra.toNat + 7) := bitsBound
        omega
      obtain ⟨binv2, stream2, count2⟩ := DROPBITS_inv binvL s.extra available (by omega)
      have held2 := held_drop stream2 available
      have split1 : natBits l1.bits.toNat l1.hold.toNat =
          natBits s.extra.toNat l1.hold.toNat ++
            natBits (l1.bits - s.extra).toNat (l1.hold >>> s.extra.toUInt64).toNat := by
        rw [held2, ← natBits_take l1.bits.toNat l1.hold.toNat s.extra.toNat available,
          List.take_append_drop]
      have bNat : (l1.hold.toUInt32 &&& ((1 : UInt32) <<< s.extra - 1)).toNat =
          l1.hold.toNat % 2 ^ s.extra.toNat := BITS_toNat l1 s.extra (by omega)
      have bLt : l1.hold.toNat % 2 ^ s.extra.toNat < 2 ^ s.extra.toNat :=
        Nat.mod_lt _ (Nat.two_pow_pos _)
      have offNat : (s.offset + (l1.hold.toUInt32 &&& ((1 : UInt32) <<< s.extra - 1))).toNat =
          distBases.getD dsym 0 + l1.hold.toNat % 2 ^ s.extra.toNat := by
        rw [UInt32.toNat_add, bNat, offsetEq']
        rw [extraEq'] at bLt ⊢
        exact Nat.mod_eq_of_lt (by omega)
      have read : readBits (distExtras.getD dsym 0) (natBits s.extra.toNat l1.hold.toNat) =
          some (l1.hold.toNat % 2 ^ s.extra.toNat, []) := by
        rw [← extraEq']
        simpa only [List.append_nil] using readBits_natBits s.extra.toNat l1.hold.toNat []
      have pp := pending_copy extL extD pend read
      have keep : RegsKeep l (distextRegs s l1) := keep1.trans ⟨rfl, rfl, rfl, rfl, rfl⟩
      have read2 : loopRead (distextRegs s l1) = loopRead l + j := readEq
      have loop2 := loop_move (s' := distextState s l1) (l' := distextRegs s l1) (j := j)
        (pos := ⟨out, final, .codes L D
          (.copy length (distBases.getD dsym 0 + l1.hold.toNat % 2 ^ s.extra.toNat))⟩) st retOk
        ⟨config.1, config.2.1, config.2.2.1, config.2.2.2.1, config.2.2.2.2.1,
          show MATCH ≠ SYNC by decide⟩
        haveLe inLen leftLe pendBase putEq outBytes writable sepIn sepWin sepOutIn keep used
        (by show l1.next = _; exact nextEq) binv2
        (by
          show bytesToBits (f.logIn ++ f.inp.take (loopRead l1)) = _
          rw [bits1, split1, consumedEq]
          simp only [List.append_assoc]
          rfl)
        (HeldBits.of_natBits (s := loopState (distextState s l1) (distextRegs s l1)) binv2.hold_lt) wrapHeader
        rfl (DeflateParsed.partialToken (tb ++ natBits s.extra.toNat l1.hold.toNat) prev pp)
        ⟨last, table_setI (s' := distextState s l1) hs rfl lenTable,
          table_setI (s' := distextState s l1) hs rfl distTable, rfl, lengthEq, offNat,
          by show (l1.bits - s.extra).toNat < 8; rw [count2]; omega⟩
        (window' _ _ rfl rfl rfl rfl) check wrapM outputEq
      obtain ⟨result, l', h', run2, rest⟩ := viaMatch (distextState s l1) (distextRegs s l1) rfl rfl rfl rfl rfl rfl rfl keep
        (by rw [read2]; omega) loop2
      exact ⟨result, l', h', (distext_run_ok E zero (by omega) run).trans run2, rest⟩
    · -- waiting for input
      have wait := empty rfl
      have moved := loop_move (s' := s) (l' := l1) (j := j)
        (pos := ⟨out, final, .codes L D (.distanceExtra length dsym)⟩) st retOk config haveLe inLen
        leftLe pendBase putEq outBytes writable sepIn sepWin sepOutIn keep1 used nextEq binvL
        (by rw [bits1, consumedEq]; simp only [List.append_assoc]; rfl)
        (HeldBits.of_natBits (s := loopState s l1) binv1.hold_lt) wrapHeader rfl
        (DeflateParsed.partialToken tb prev pend)
        ⟨last, table_setI (s' := s) hs rfl lenTable, table_setI (s' := s) hs rfl distTable, mode, lengthEq, extraEq,
          offsetEq, by show l1.bits.toNat < 8 + s.extra.toNat; have := wait.2.2; omega⟩
        (window' _ _ rfl rfl rfl rfl) check wrapM outputEq
      rw [setI_self hs] at moved
      exact ⟨_, _, _, distext_run_wait E zero run, Or.inl ⟨rfl, Or.inl wait.2.1, moved⟩⟩

#print axioms distext_step

/-! ## Lookups that pull a byte only when the selected entry does not fit -/

/-- `lookupLoop_run_cursor` with the reason for every pulled byte: the state
before each pull has a selected entry that does not fit (`Fail` of its bit
count), and an exit for want of input leaves with an entry that does not fit. -/
theorem lookupLoop_fail {body : X Bool} {h : Heap} {l : IL} {bs : List UInt8}
    (query : IL → Code) (need : Code → UInt32)
    (stable : ∀ current, query { current with here := query current } = query current)
    (bound : ∀ current, (need (query current)).toNat ≤ 15)
    (bodyRun : ∀ current, LookupRegShape l current →
      runX body current h =
        if need (query current) ≤ current.bits then
          .ok ((.ok true, { current with here := query current }), h)
        else runX (do PULLBYTE; pure false : X Bool) { current with here := query current } h)
    (B : BitInv h l bs) (Fail : Nat → Prop)
    (fail : ∀ current used, LookupRegShape l current → BitInv h current (bs.drop used) →
      stream current (bs.drop used) = stream l bs →
      current.bits.toNat = l.bits.toNat + 8 * used →
      ¬ need (query current) ≤ current.bits → Fail current.bits.toNat) :
    ∃ result regs used,
      runX (xloopBrk body) l h = .ok ((result, regs), h) ∧
      used ≤ bs.length ∧ BitInv h regs (bs.drop used) ∧
      stream regs (bs.drop used) = stream l bs ∧ LookupRegShape l regs ∧
      regs.bits.toNat = l.bits.toNat + 8 * used ∧
      regs.bits.toNat ≤ max l.bits.toNat 22 ∧
      regs.here = query regs ∧
      (result = .ok () ∨ result = .error Ex.leave) ∧
      (result = .ok () → (need regs.here).toNat ≤ regs.bits.toNat) ∧
      (result = .error Ex.leave → regs.have_ = 0 ∧ ¬ need regs.here ≤ regs.bits) ∧
      regs.next = inputAdvance l.next used ∧
      ∀ k, k < used → Fail (l.bits.toNat + 8 * k) := by
  let P : IL → Heap → Prop := fun regs heap =>
    heap = h ∧ ∃ used, used ≤ bs.length ∧ BitInv h regs (bs.drop used) ∧
      stream regs (bs.drop used) = stream l bs ∧ LookupRegShape l regs ∧
      regs.bits.toNat = l.bits.toNat + 8 * used ∧ regs.bits.toNat ≤ max l.bits.toNat 22 ∧
      regs.next = inputAdvance l.next used ∧ ∀ k, k < used → Fail (l.bits.toNat + 8 * k)
  let Q : Except Ex Unit → IL → Heap → Prop := fun result regs heap =>
    P regs heap ∧ regs.here = query regs ∧ (result = .ok () ∨ result = .error Ex.leave) ∧
      (result = .ok () → (need regs.here).toNat ≤ regs.bits.toNat) ∧
      (result = .error Ex.leave → regs.have_ = 0 ∧ ¬ need regs.here ≤ regs.bits)
  have step : ∀ current heap, P current heap → ∃ test regs heap1,
      runX (pure true : X Bool) current heap = .ok ((test, regs), heap1) ∧
      (match test with
       | .error fault => Q (.error fault) regs heap1
       | .ok false => Q (.ok ()) regs heap1
       | .ok true => ∃ result final heap2,
           runX body regs heap1 = .ok ((result, final), heap2) ∧
           (match result with
            | .error fault => Q (.error fault) final heap2
            | .ok true => Q (.ok ()) final heap2
            | .ok false => P final heap2 ∧ 15 - final.bits.toNat < 15 - current.bits.toNat)) := by
    rintro current heap ⟨heapEq, used, usedBound, inv, sameStream, shape, count, bitBound, cursor, fails⟩
    subst heap
    refine ⟨.ok true, current, h, rfl, ?_⟩
    let entry := query current
    let read := { current with here := entry }
    have entryBound : (need entry).toNat ≤ 15 := bound current
    have readInv : BitInv h read (bs.drop used) := ⟨inv.have_eq, inv.next, inv.hold_lt⟩
    have readShape : LookupRegShape l read := shape.trans (by rfl)
    have actual := bodyRun current shape
    change runX body current h =
      if need entry ≤ current.bits then .ok ((.ok true, read), h)
      else runX (do PULLBYTE; pure false : X Bool) read h at actual
    by_cases fits : need entry ≤ current.bits
    · rw [ite_eq_left fits] at actual
      refine ⟨.ok true, read, h, actual,
        ⟨⟨rfl, used, usedBound, readInv, sameStream, readShape, count, bitBound, cursor, fails⟩,
        (stable current).symm, Or.inl rfl, ?_, ?_⟩⟩
      · intro _
        exact UInt32.le_iff_toNat_le.mp fits
      · intro impossible
        cases impossible
    · rw [ite_eq_right fits] at actual
      have short : current.bits.toNat < (need entry).toNat := by
        have := (not_congr UInt32.le_iff_toNat_le).mp fits
        omega
      have failNow : Fail current.bits.toNat := fail current used shape inv sameStream count fits
      cases remaining : bs.drop used with
      | nil =>
        have empty : read.have_ = 0 := by
          apply UInt32.toNat_inj.mp
          have len := inv.have_eq
          rw [remaining] at len
          exact len
        rw [runX_bind, PULLBYTE_zero empty] at actual
        refine ⟨.error Ex.leave, read, h, actual,
          ⟨⟨rfl, used, usedBound, readInv, sameStream, readShape, count, bitBound, cursor, fails⟩,
          (stable current).symm, Or.inr rfl, ?_, fun _ => ⟨empty, fits⟩⟩⟩
        intro impossible
        cases impossible
      | cons byte rest =>
        have readCons : BitInv h read (byte :: rest) := by rwa [remaining] at readInv
        obtain ⟨next, pull, nextInv, nextStream, nextBits, nextCursor⟩ := PULLBYTE_succ_cursor readCons
          (by change current.bits.toNat ≤ 56; omega)
        let final := pulled read byte next
        have restEq : bs.drop (used + 1) = rest := by
          have eq : (bs.drop used).drop 1 = rest := by rw [remaining]; rfl
          simpa only [List.drop_drop, Nat.add_comm] using eq
        have usedNext : used + 1 ≤ bs.length := by
          have len := congrArg List.length remaining
          simp only [List.length_drop, List.length_cons] at len
          omega
        have finalInv : BitInv h final (bs.drop (used + 1)) := by rwa [restEq]
        have finalStream : stream final (bs.drop (used + 1)) = stream l bs := by
          rw [restEq, nextStream, ← remaining]
          exact sameStream
        have finalCount : final.bits.toNat = l.bits.toNat + 8 * (used + 1) := by
          rw [nextBits]
          change current.bits.toNat + 8 = _
          rw [count, Nat.mul_add]
          omega
        have finalBound : final.bits.toNat ≤ max l.bits.toNat 22 := by
          rw [nextBits]
          change current.bits.toNat + 8 ≤ _
          omega
        rw [runX_bind, pull] at actual
        simp only [runX_pure] at actual
        refine ⟨.ok false, final, h, actual,
          ⟨rfl, used + 1, usedNext, finalInv, finalStream, readShape.trans (by rfl), finalCount,
            finalBound, ?_, ?_⟩, ?_⟩
        · change next = inputAdvance l.next (used + 1)
          rw [nextCursor]
          change inputAdvance current.next 1 = _
          rw [cursor, inputAdvance_add]
        · intro k lt
          by_cases last : k = used
          · subst last
            rw [← count]
            exact failNow
          · exact fails k (by omega)
        · rw [nextBits]
          change 15 - (current.bits.toNat + 8) < 15 - current.bits.toNat
          omega
  have initial : P l h := ⟨rfl, 0, by omega, by simpa using B, rfl, LookupRegShape.refl l, by simp,
    by omega, (inputAdvance_zero l.next).symm, fun k lt => absurd lt (by omega)⟩
  obtain ⟨result, regs, after, run, post, selected, kinds, enough, empty⟩ :=
    xwhileBrk_rank P (fun regs _ => 15 - regs.bits.toNat) Q step initial
      (by change 15 - l.bits.toNat + 2 < fuel; have : 17 < fuel := by decide
          omega)
  obtain ⟨heapEq, used, usedBound, inv, sameStream, shape, count, bitBound, cursor, fails⟩ := post
  subst after
  exact ⟨result, regs, used, run, usedBound, inv, sameStream, shape, count, bitBound,
    selected, kinds, enough, empty, cursor, fails⟩

/-- The root distance lookup with the reason for every pulled byte. -/
theorem lookup1_dist_fail {c : Ctx} {h : Heap} {zs : Nat} {s : InflateState}
    {ref : CodeRef} {offset : Nat} {ca : Array Code} {l : IL} {bs : List UInt8}
    (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s)
    (pointer : s.distcode = .ref ref offset) (get : Space.get h ref = some ca)
    (safe : DistTableSafe ca offset s.distbits.toNat) (B : BitInv h l bs) (Fail : Nat → Prop)
    (fail : ∀ current used, LookupRegShape l current → BitInv h current (bs.drop used) →
      stream current (bs.drop used) = stream l bs →
      current.bits.toNat = l.bits.toNat + 8 * used →
      current.bits.toNat < (codeLookupValue ca offset s.distbits.toNat current).bits.toNat →
      Fail current.bits.toNat) :
    ∃ result regs used,
      runX (lookup1 c true) l h = .ok ((result, regs), h) ∧
      used ≤ bs.length ∧ BitInv h regs (bs.drop used) ∧
      stream regs (bs.drop used) = stream l bs ∧ LookupRegShape l regs ∧
      regs.bits.toNat = l.bits.toNat + 8 * used ∧
      regs.here = codeLookupValue ca offset s.distbits.toNat regs ∧
      (result = .ok () ∨ result = .error Ex.leave) ∧
      (result = .ok () → regs.here.bits.toNat ≤ regs.bits.toNat) ∧
      (result = .error Ex.leave → regs.have_ = 0 ∧ regs.bits.toNat < regs.here.bits.toNat) ∧
      regs.next = inputAdvance l.next used ∧
      ∀ k, k < used → Fail (l.bits.toNat + 8 * k) := by
  have readable := distTableSafe_readable safe
  rw [lookup1_data_eq]
  obtain ⟨result, regs, used, run, usedBound, inv, sameStream, shape, count, _, selected, kinds,
    enough, empty, cursor, fails⟩ :=
    lookupLoop_fail (query := codeLookupValue ca offset s.distbits.toNat)
      (need := fun entry => entry.bits.toUInt32) (fun _ => rfl)
      (by intro current; rw [UInt8.toNat_toUInt32]; exact readable.2.2 _ (Nat.mod_lt _ (Nat.two_pow_pos _)))
      (by intro current _; exact dataLookupBody_run true current hc hs pointer get readable) B Fail
      (by
        intro current used shape inv same cnt nofit
        apply fail current used shape inv same cnt
        have := (not_congr UInt32.le_iff_toNat_le).mp nofit
        rw [UInt8.toNat_toUInt32] at this
        omega)
  refine ⟨result, regs, used, run, usedBound, inv, sameStream, shape, count, selected, kinds,
    fun ok => by have := enough ok; rwa [UInt8.toNat_toUInt32] at this, fun leave => ?_, cursor, fails⟩
  obtain ⟨e, nofit⟩ := empty leave
  refine ⟨e, ?_⟩
  have := (not_congr UInt32.le_iff_toNat_le).mp nofit
  rw [UInt8.toNat_toUInt32] at this
  omega

/-- The second-level distance lookup with the reason for every pulled byte. -/
theorem lookup2_dist_fail {c : Ctx} {h : Heap} {zs : Nat} {s : InflateState}
    {ref : CodeRef} {offset : Nat} {ca : Array Code} {l : IL} {bs : List UInt8} (last : Code)
    (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s)
    (pointer : s.distcode = .ref ref offset) (get : Space.get h ref = some ca)
    (remembered : l.last = last) (link : LinkOK DistLeaf ca offset last)
    (B : BitInv h l bs) (Fail : Nat → Prop)
    (fail : ∀ current used, LookupRegShape l current → BitInv h current (bs.drop used) →
      stream current (bs.drop used) = stream l bs →
      current.bits.toNat = l.bits.toNat + 8 * used →
      current.bits.toNat < last.bits.toNat + (subLookupValue ca offset last current).bits.toNat →
      Fail current.bits.toNat) :
    ∃ result regs used,
      runX (lookup2 c true) l h = .ok ((result, regs), h) ∧
      used ≤ bs.length ∧ BitInv h regs (bs.drop used) ∧
      stream regs (bs.drop used) = stream l bs ∧ LookupRegShape l regs ∧
      regs.bits.toNat = l.bits.toNat + 8 * used ∧
      regs.here = subLookupValue ca offset last regs ∧ DistLeaf last.bits.toNat regs.here ∧
      (result = .ok () ∨ result = .error Ex.leave) ∧
      (result = .ok () → last.bits.toNat + regs.here.bits.toNat ≤ regs.bits.toNat) ∧
      (result = .error Ex.leave → regs.have_ = 0 ∧
        regs.bits.toNat < last.bits.toNat + regs.here.bits.toNat) ∧
      regs.next = inputAdvance l.next used ∧
      ∀ k, k < used → Fail (l.bits.toNat + 8 * k) := by
  have leaf : ∀ current, DistLeaf last.bits.toNat (subLookupValue ca offset last current) := by
    intro current
    exact link.2.2.2.2 _ (subLookupIndex_lt _ _)
  have needNat : ∀ current, (last.bits.toUInt32 + (subLookupValue ca offset last current).bits.toUInt32).toNat =
      last.bits.toNat + (subLookupValue ca offset last current).bits.toNat := by
    intro current
    have bound := (leaf current).1
    rw [UInt32.toNat_add, UInt8.toNat_toUInt32, UInt8.toNat_toUInt32, Nat.mod_eq_of_lt (by omega)]
  have pointer' : (if true then s.distcode else s.lencode) = .ref ref offset := pointer
  rw [lookup2_data_eq]
  obtain ⟨result, regs, used, run, usedBound, inv, sameStream, shape, count, _, selected, kinds,
    enough, empty, cursor, fails⟩ :=
    lookupLoop_fail (query := subLookupValue ca offset last)
      (need := fun entry => last.bits.toUInt32 + entry.bits.toUInt32) (fun _ => rfl)
      (by intro current; rw [needNat]; have := (leaf current).1; omega)
      (by
        intro current frame
        have lastEq : current.last = last := by rw [frame, remembered]
        exact dataSubLookupBody_run true current last hc hs pointer' get lastEq link) B Fail
      (by
        intro current used shape inv same cnt nofit
        apply fail current used shape inv same cnt
        have := (not_congr UInt32.le_iff_toNat_le).mp nofit
        rw [needNat] at this
        omega)
  refine ⟨result, regs, used, run, usedBound, inv, sameStream, shape, count, selected,
    by rw [selected]; exact leaf regs, kinds,
    fun ok => by have := enough ok; rwa [selected, needNat, ← selected] at this, fun leave => ?_,
    cursor, fails⟩
  obtain ⟨e, nofit⟩ := empty leave
  refine ⟨e, ?_⟩
  have := (not_congr UInt32.le_iff_toNat_le).mp nofit
  rw [selected, needNat, ← selected] at this
  omega

#print axioms lookup1_dist_fail
#print axioms lookup2_dist_fail


/-! ## The meaning of a distance lookup -/

section DistMeaning
open Zlib.Inftrees Zlib.Inftrees.Spec Zlib.Inftrees.Proofs
open Zlib.Inftrees.Spec.DecodeSemantics Zlib.Inftrees.Spec.DecodeSoundness
open Zlib.Inftrees.Spec.DecodeTableInvariant Zlib.Inftrees.Spec.DecodeTableStability
open Zlib.Inflate.Proofs.MeaningLookup

/-- The held bits of a state on the same stream are a prefix of the stream. -/
theorem held_take {h : Heap} {l cur : IL} {bs bs' : List UInt8} (inv : BitInv h cur bs')
    (same : stream cur bs' = stream l bs) :
    natBits cur.bits.toNat cur.hold.toNat = (stream l bs).take cur.bits.toNat := by
  rw [← same, stream, List.take_left' (natBits_length _ _)]

theorem heldShort_eq (s : InflateState) :
    heldShort s = natBits (s.bits.toNat - 8) s.hold.toNat := by
  unfold heldShort
  rw [natBits_testBit]

/-- A symbol decoded from bits is decoded from every prefix that holds its code. -/
theorem decode_take {lens : List Nat} (ext : Ext lens) {inp rest : List Bool} {symbol : Nat}
    (decoded : decodeSym lens inp = some (symbol, rest)) {k : Nat} (le : lens.getD symbol 0 ≤ k) :
    decodeSym lens (inp.take k) = some (symbol, (inp.take k).drop (lens.getD symbol 0)) := by
  obtain ⟨lt, nz, pre, _⟩ := decoded_symbol_prefix decoded
  have codeLen : (codeOf lens symbol).length = lens.getD symbol 0 := by
    simp only [codeOf, ZlibF.Spec.Proofs.natToBitsMSB_length]
  have preTake : codeOf lens symbol <+: inp.take k := List.prefix_take_iff.mpr ⟨pre, by omega⟩
  cases found : decodeSym lens (inp.take k) with
  | none =>
    exfalso
    unfold decodeSym at found
    split at found
    · cases found
    · rename_i none
      have := List.find?_eq_none.mp none symbol (List.mem_range.mpr lt)
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, not_and] at this
      exact this nz (List.isPrefixOf_iff_prefix.mpr preTake)
  | some pair =>
    obtain ⟨s0, r0⟩ := pair
    have long := ext _ _ _ (inp.drop k) found
    rw [List.take_append_drop, decoded] at long
    simp only [Option.some.injEq, Prod.mk.injEq] at long
    obtain ⟨rfl, _⟩ := long
    obtain ⟨_, _, _, r0eq⟩ := decoded_symbol_prefix found
    rw [r0eq]

theorem distsValid {symbol : Nat} : ValidSymbol DISTS symbol ↔ symbol ≤ 29 := by
  unfold ValidSymbol
  rw [if_neg (by decide)]

theorem distsAccepted {entry : Code} : LeafAccepted DISTS entry ↔ entry.op &&& 64 = 0 := by
  unfold LeafAccepted
  rw [if_neg (by decide)]

theorem distsEntry {symbol : Nat} {entry : Code} (le : symbol ≤ 29) (meaning : SymbolEntry DISTS symbol entry) :
    entry.op.toNat = 16 + distExtras.getD symbol 0 ∧ entry.val.toNat = distBases.getD symbol 0 := by
  unfold SymbolEntry at meaning
  rw [if_neg (by decide), if_pos le] at meaning
  exact meaning

/-- A query that does not fit the held bits: they hold no valid symbol. -/
theorem nofit_invalid {ca : Array Code} {offset root used : Nat} {D : List Nat}
    (inv : Inv DISTS ca offset root used D) {inp : List Bool} {entry : Code} {consumed : Nat}
    (query : tableRead DISTS ca offset root (DecodeShort.padded inp) = some (entry, consumed))
    (nofit : inp.length < consumed) :
    ∀ symbol rest, decodeSym D inp = some (symbol, rest) → 29 < symbol := by
  intro symbol rest decoded
  apply Classical.byContradiction
  intro le
  obtain ⟨e', c', q', _, _, _, fits, _⟩ :=
    Zlib.Inftrees.Proofs.DecodeForward.lookup_of_decode inv decoded (distsValid.mpr (by omega))
  rw [query] at q'
  simp only [Option.some.injEq, Prod.mk.injEq] at q'
  omega

theorem slow_isLink {entry : Code} : Subtable.IsLink DISTS entry = true ↔ SlowDistLink entry := by
  unfold Subtable.IsLink SlowDistLink
  rw [if_neg (by decide)]
  simp

theorem op_and_mask (o : UInt8) : (o.toUInt32 &&& 15).toNat = o.toNat % 16 := by
  rw [UInt32.toNat_and, UInt8.toNat_toUInt32]
  exact Nat.and_two_pow_sub_one_eq_mod _ 4

/-- The query of the held bits at a state, as zlib's root and link reads see it. -/
theorem dist_query {ca : Array Code} {offset root used : Nat} {D : List Nat}
    (inv : Inv DISTS ca offset root used D) (safe : DistTableSafe ca offset root)
    {bits hold : Nat} (lt : hold < 2 ^ bits) :
    (¬ SlowDistLink (ca.getD (offset + hold % 2 ^ root) default) →
      DistLeaf 0 (ca.getD (offset + hold % 2 ^ root) default) ∧
      tableRead DISTS ca offset root (DecodeShort.padded (natBits bits hold)) =
        some (ca.getD (offset + hold % 2 ^ root) default,
          (ca.getD (offset + hold % 2 ^ root) default).bits.toNat)) ∧
    (SlowDistLink (ca.getD (offset + hold % 2 ^ root) default) →
      (ca.getD (offset + hold % 2 ^ root) default).bits.toNat = root ∧
      LinkOK DistLeaf ca offset (ca.getD (offset + hold % 2 ^ root) default) ∧
      tableRead DISTS ca offset root (DecodeShort.padded (natBits bits hold)) =
        some (ca.getD (offset + (ca.getD (offset + hold % 2 ^ root) default).val.toNat +
            subLookupIndexNat (ca.getD (offset + hold % 2 ^ root) default) hold) default,
          (ca.getD (offset + hold % 2 ^ root) default).bits.toNat +
            (ca.getD (offset + (ca.getD (offset + hold % 2 ^ root) default).val.toNat +
              subLookupIndexNat (ca.getD (offset + hold % 2 ^ root) default) hold)
              default).bits.toNat)) := by
  have root15 : root ≤ 15 := safe.1
  have idx : hold % 2 ^ root < 2 ^ root := Nat.mod_lt _ (Nat.two_pow_pos _)
  have inside : offset + hold % 2 ^ root < ca.size := by have := safe.2.1; omega
  have cell := safe.2.2 _ idx
  generalize e0def : ca.getD (offset + hold % 2 ^ root) default = e0 at cell ⊢
  have get0 : ca[offset + hold % 2 ^ root]? = some e0 := by
    rw [← e0def]; simp [Array.getD, inside]
  constructor
  · intro nl
    have leaf : DistLeaf 0 e0 := by
      split at cell
      · exact absurd (distLink_slow cell) nl
      · exact cell
    refine ⟨leaf, ?_⟩
    have notLink : Subtable.IsLink DISTS e0 = false := by
      cases hl : Subtable.IsLink DISTS e0
      · rfl
      · exact absurd (slow_isLink.mp hl) nl
    have := tableRead_root (type := DISTS) (ca := ca) (offset := offset) (root := root) lt root15 inside
      (by rw [e0def]; exact notLink)
    rw [e0def] at this
    exact this
  · intro sl
    have isLink : Subtable.IsLink DISTS e0 = true := slow_isLink.mpr sl
    obtain ⟨bitsEq, sub⟩ := inv.subtables _ e0 idx get0 isLink
    have link : LinkOK DistLeaf ca offset e0 := by
      split at cell
      · exact cell
      · rename_i nlink
        exact absurd (slowDistLink_fast sl) nlink
    refine ⟨bitsEq, link, ?_⟩
    have subLt : subLookupIndexNat e0 hold < 2 ^ e0.op.toNat :=
      ZlibF.Math.InflateLookup.slice_lt _ _ _
    have := tableRead_link (type := DISTS) (ca := ca) (offset := offset) (root := root) lt root15 inside
      (by rw [e0def]; exact isLink) (by rw [e0def]; exact sub.2.2.1)
      (by rw [e0def]; have := sub.2.2.2.1; omega)
    rw [e0def] at this
    exact this

/-- After a valid symbol of `consumed` bits fits `bits` held bits, fewer than
8 are left when the held bits without their last byte hold no valid symbol. -/
theorem left_short {D : List Nat} (ext : Ext D) {inp rest : List Bool} {symbol : Nat}
    (decoded : decodeSym D inp = some (symbol, rest)) (valid : symbol ≤ 29)
    (short : inp.length < 8 ∨ ∀ s r, decodeSym D (inp.take (inp.length - 8)) = some (s, r) → 29 < s) :
    inp.length - D.getD symbol 0 < 8 := by
  rcases short with lt | none
  · omega
  · apply Classical.byContradiction
    intro ge
    have := decode_take ext decoded (k := inp.length - 8) (by omega)
    have := none _ _ this
    omega

end DistMeaning


/-! ## The runs of `DIST` -/

theorem dist_run_leave {c : Ctx} {h : Heap} {l r1 : IL}
    (run1 : runX (lookup1 c true) l h = .ok ((.error Ex.leave, r1), h)) :
    runX (inflate_DIST c) l h = .ok ((.error Ex.leave, r1), h) := by
  rw [inflate_DIST_lookup_cut]
  unfold distLookup
  simp only [runX_bind, run1]

theorem dist_run_leaf {c : Ctx} {h : Heap} {l r1 : IL}
    (run1 : runX (lookup1 c true) l h = .ok ((.ok (), r1), h)) (leaf : ¬ SlowDistLink r1.here) :
    runX (inflate_DIST c) l h = runX (distFinish c) r1 h := by
  rw [inflate_DIST_lookup_cut]
  unfold distLookup
  simp only [runX_bind, run1, runX_get, distRootTail_leaf c _ leaf, runX_pure]

theorem dist_run_sub_leave {c : Ctx} {h : Heap} {l r1 r2 : IL}
    (run1 : runX (lookup1 c true) l h = .ok ((.ok (), r1), h)) (link : SlowDistLink r1.here)
    (run2 : runX (lookup2 c true) { r1 with last := r1.here } h = .ok ((.error Ex.leave, r2), h)) :
    runX (inflate_DIST c) l h = .ok ((.error Ex.leave, r2), h) := by
  rw [inflate_DIST_lookup_cut]
  unfold distLookup
  simp only [runX_bind, run1, runX_get, distRootTail_link c _ link]
  unfold distSubLookup
  simp only [runX_bind, runX_modify, run2]

theorem chk_back (n m : Nat) (lt : n + m < 2147483648) (h : Heap) :
    chkI32 ((Int32.ofNat n).toInt + m) h = .ok (Int32.ofNat (n + m), h) := by
  have e : (Int32.ofNat n).toInt = n := by
    have := int32_ofInt_toInt n (by omega) (by omega)
    exact this
  rw [e]
  unfold chkI32
  rw [if_pos (by omega)]
  rfl

theorem dist_run_sub_ok {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {s : InflateState} (E : Env c h r zs z s) {l r1 r2 : IL} (n : Nat)
    (run1 : runX (lookup1 c true) l h = .ok ((.ok (), r1), h)) (link : SlowDistLink r1.here)
    (run2 : runX (lookup2 c true) { r1 with last := r1.here } h = .ok ((.ok (), r2), h))
    (lastEq : r2.last = r1.here) (backEq : s.back = Int32.ofNat n) (small : r1.here.bits.toNat ≤ 15)
    (nb : n + 15 < 2147483648) :
    runX (inflate_DIST c) l h =
      runX (distFinish c)
        { r2 with hold := r2.hold >>> r1.here.bits.toUInt32.toUInt64, bits := r2.bits - r1.here.bits.toUInt32 }
        (setI h zs { s with back := Int32.ofNat (n + r1.here.bits.toNat) }) := by
  have small64 : r1.here.bits.toUInt32.toNat < 64 := by rw [UInt8.toNat_toUInt32]; omega
  have load : ldInflateState c.st h = .ok (s, h) := by rw [E.st, ldI_eq, E.hs]
  have checked := chk_back n r1.here.bits.toNat (by omega) h
  rw [← backEq] at checked
  have write : wrS c.st (fun s => { s with back := Int32.ofNat (n + r1.here.bits.toNat) }) h =
      .ok ((), setI h zs { s with back := Int32.ofNat (n + r1.here.bits.toNat) }) := by
    rw [E.st, wrI_eq, E.hs]
  rw [inflate_DIST_lookup_cut]
  unfold distLookup
  simp only [runX_bind, run1, runX_get, distRootTail_link c _ link]
  unfold distSubLookup
  simp only [runX_bind, runX_modify, run2, runX_get, lastEq, DROPBITS_run _ h _ small64,
    runX_lift_ok load, runX_lift_ok checked, runX_lift_ok write]

theorem dist_run_finish {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {s : InflateState} (E : Env c h r zs z s) (l : IL) (n : Nat) (backEq : s.back = Int32.ofNat n)
    (small : l.here.bits.toNat ≤ 15) (nb : n + 15 < 2147483648) :
    runX (distFinish c) l h =
      runX (distLeafTail c l.here)
        { l with hold := l.hold >>> l.here.bits.toUInt32.toUInt64, bits := l.bits - l.here.bits.toUInt32 }
        (setI h zs { s with back := Int32.ofNat (n + l.here.bits.toNat) }) := by
  have small64 : l.here.bits.toUInt32.toNat < 64 := by rw [UInt8.toNat_toUInt32]; omega
  have load : ldInflateState c.st h = .ok (s, h) := by rw [E.st, ldI_eq, E.hs]
  have checked := chk_back n l.here.bits.toNat (by omega) h
  rw [← backEq] at checked
  have write : wrS c.st (fun s => { s with back := Int32.ofNat (n + l.here.bits.toNat) }) h =
      .ok ((), setI h zs { s with back := Int32.ofNat (n + l.here.bits.toNat) }) := by
    rw [E.st, wrI_eq, E.hs]
  unfold distFinish distLeafTail
  simp only [runX_bind, runX_get, DROPBITS_run l h _ small64,
    runX_lift_ok load, runX_lift_ok checked, runX_lift_ok write]

theorem leafTail_bad {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {s : InflateState} (E : Env c h r zs z s) (here : Code) (l : IL) (bad : here.op &&& 64 ≠ 0) :
    ∃ i, runX (distLeafTail c here) l h = .ok ((.ok (), l), badHeap h r zs z s i) := by
  obtain ⟨i, _, run⟩ := runX_badMode E (msg := "invalid distance code") (by decide +kernel) l
  refine ⟨i, ?_⟩
  unfold distLeafTail
  have b : (here.op &&& 64 != 0) = true := by simpa using bad
  simp only [b, ite_true, runX_bind, run, runX_pure]

/-- The state `DIST` leaves for `DISTEXT`. -/
def distState (s : InflateState) (here : Code) : InflateState :=
  { s with offset := here.val.toUInt32, extra := here.op.toUInt32 &&& 15, mode := DISTEXT }

theorem leafTail_ok {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {s : InflateState} (E : Env c h r zs z s) (here : Code) (l : IL) (good : here.op &&& 64 = 0) :
    runX (distLeafTail c here) l h = runX (inflate_DISTEXT c) l (setI h zs (distState s here)) := by
  unfold distLeafTail
  have g : (here.op &&& 64 != 0) = false := by simp [good]
  simp only [g, Bool.false_eq_true, ite_false, runX_bind, runX_lift, E.st, wrI_eq, E.hs,
    setI_istates_same, setI_setI, setMode]
  rfl


/-! ## `DIST` -/

/-- The only stage a `DIST` state can stand for. -/
theorem stage_of_dist {h : Heap} {s : InflateState} {f : LoopFrame} {checked : List UInt8}
    {stage : WrapStage} (stageFacts : LoopStageMatches h s f checked stage) (mode : s.mode = DIST) :
    ∃ header out final L D length,
      stage = .body header ⟨out, final, .codes L D (.distance length)⟩ := by
  rcases stage with bytes | header | ⟨header, ⟨out, final, pos⟩⟩ | ⟨header, out, bytes⟩ | out
  · obtain ⟨lo, hi⟩ := stageFacts
    rw [mode] at lo hi
    exact absurd hi (by decide)
  · have := stageFacts
    simp only [LoopStageMatches] at this
    rw [mode] at this
    exact absurd this (by decide)
  · obtain ⟨body, _, _⟩ := stageFacts
    rcases pos with _ | _ | remaining | header' | ⟨L, D, pending⟩ | _
    · obtain ⟨m, _⟩ := body
      rw [mode] at m
      rcases m with m | m <;> exact absurd m (by decide)
    · obtain ⟨m, _⟩ := body
      rw [mode] at m
      exact absurd m (by decide)
    · obtain ⟨m, _⟩ := body
      rw [mode] at m
      rcases m with m | m <;> exact absurd m (by decide)
    · obtain ⟨dyn, _⟩ := body
      rcases dynamic_mode dyn with m | m | m <;> (rw [mode] at m; exact absurd m (by decide))
    · obtain ⟨_, _, _, rest⟩ := body
      rcases pending with _ | symbol | length | ⟨length, ds⟩ | ⟨remaining, dist⟩ | byte
      · rw [mode] at rest; rcases rest.1 with m | m <;> exact absurd m (by decide)
      · rw [mode] at rest; exact absurd rest.1 (by decide)
      · exact ⟨header, out, final, L, D, length, rfl⟩
      · rw [mode] at rest; exact absurd rest.1 (by decide)
      · rw [mode] at rest; exact absurd rest.1 (by decide)
      · rw [mode] at rest; exact absurd rest.1 (by decide)
    · obtain ⟨m, _⟩ := body
      rw [mode] at m
      rcases m with m | m <;> exact absurd m (by decide)
  · obtain ⟨m, _⟩ := stageFacts
    rw [mode] at m
    rcases m with m | m <;> exact absurd m (by decide)
  · have m : s.mode = DONE := stageFacts
    rw [mode] at m
    exact absurd m (by decide)

/-- A started distance was reached by a started token. -/
theorem parsed_dist_inv {dict : List UInt8} {bits : List Bool} {out : List UInt8} {final : Bool}
    {L D : List Nat} {length : Nat}
    (parsed : DeflateParsed dict bits ⟨out, final, .codes L D (.distance length)⟩) :
    ∃ c0 tb, bits = c0 ++ tb ∧ DeflateParsed dict c0 ⟨out, final, .codes L D .none⟩ ∧
      PendingParsed L D tb (.distance length) := by
  cases parsed with
  | partialToken _ prev pp => exact ⟨_, _, rfl, prev, pp⟩

theorem short_take {h : Heap} {l cur : IL} {bs bs' : List UInt8} (inv : BitInv h cur bs')
    (same : stream cur bs' = stream l bs) (k : Nat) (le : k ≤ cur.bits.toNat) :
    natBits k cur.hold.toNat = (stream l bs).take k := by
  rw [← natBits_take _ _ k le, held_take inv same, List.take_take, Nat.min_eq_left le]

theorem keep_of_lookup {l r : IL} (shape : LookupRegShape l r) : RegsKeep l r := by
  rw [shape]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

section DistStep
open Zlib.Inftrees Zlib.Inftrees.Spec Zlib.Inftrees.Proofs
open Zlib.Inftrees.Spec.DecodeSemantics Zlib.Inftrees.Spec.DecodeSoundness
open Zlib.Inftrees.Spec.DecodeTableInvariant Zlib.Inftrees.Spec.DecodeTableStability
open Zlib.Inflate.Proofs.MeaningLookup

set_option maxHeartbeats 16000000 in
/-- `case DIST` keeps the format meaning. The distance symbol is looked up in
the root table and, through a link, in a second-level table, pulling a byte
only while the selected entry does not fit the held bits. Without input it
leaves (`have = 0`) with the started distance held, and the held bits without
their last byte hold no valid distance symbol. An invalid code (`op & 64`)
goes to `BAD` with no valid continuation of the input. Otherwise the symbol's
code is dropped, the distance base and extra-bit count are stored, and
`case DISTEXT` follows (`distext_step`).

The safety invariant of the decoder state supplies `tables` (the data tables
are safe to read, `DataTablesSafe`) and `back` (the signed back counter of a
`DIST` state, `DataPendingInvariant`); the other hypotheses are those of
`match_step`. -/
theorem dist_step {c : Ctx} {f : LoopFrame} {h : Heap} {l : IL} {r : ZStreamRef} {z : ZStream}
    (loop : LoopMatches c f h l) (strm : c.strm = some r) (hz : r.get h = some z)
    (distMode : ∀ zs s, c.st = some (.tab zs) → h.istates zs = some s → s.mode = DIST)
    (tables : ∀ zs s, c.st = some (.tab zs) → h.istates zs = some s → DataTablesSafe h s)
    (back : ∀ zs s, c.st = some (.tab zs) → h.istates zs = some s → BackBound s 20)
    (bounds : ∀ zs s, c.st = some (.tab zs) → h.istates zs = some s →
      s.wnext ≤ s.whave ∧ s.whave ≤ s.wsize)
    (sane : ∀ zs s, c.st = some (.tab zs) → h.istates zs = some s → s.sane ≠ 0)
    (wsizeBits : ∀ zs s, c.st = some (.tab zs) → h.istates zs = some s →
      s.wsize ≠ 0 → s.wsize.toNat = 2 ^ s.wbits.toNat)
    (ring : ∀ zs s, c.st = some (.tab zs) → h.istates zs = some s →
      s.whave < s.wsize → s.wnext = s.whave)
    (privateWindow : ∀ zs s, c.st = some (.tab zs) → h.istates zs = some s →
      ∀ w o d i, s.window = .ref w o → l.put = .ref d i → w ≠ d)
    (rawWidth : f.wrap = .raw → f.configured ≠ 0) :
    ∃ result l' h', runX (inflate_DIST c) l h = .ok ((result, l'), h') ∧
      ((result = .error Ex.leave ∧ (l'.have_ = 0 ∨ l.left = 0) ∧ LoopMatches c f h' l') ∨
       (result = .ok () ∧ loopRead l ≤ loopRead l' ∧
         (LoopMatches c f h' l' ∨
          ((∀ zs s, c.st = some (.tab zs) → h'.istates zs = some s → s.mode = BAD) ∧
            LoopDoomed f l')))) := by
  obtain ⟨zs, s, callOut, consumed, held, stage, st, hs, retOk, config, haveLe, inLen, binv, leftLe,
    pendLe, putEq, outBytes, writable, sepIn, sepWin, sepOutIn, bitsEq, heldBits, parsed, stageM,
    wrapM, outputEq⟩ := loop
  have E : Env c h r zs z s := ⟨strm, st, hz, hs⟩
  have mode : s.mode = DIST := distMode zs s st hs
  obtain ⟨header, out, final, L, D, length, rfl⟩ := stage_of_dist stageM mode
  have pendBase := pendLe.2 _ _ rfl
  obtain ⟨⟨last, lenTable, distTable, _, lengthEq, p7⟩, window, check⟩ := stageM
  obtain ⟨bodyDict, bitsP, wrapHeader, consumedEq, deflate⟩ := parsed
  obtain ⟨c0, tb, rfl, prev, pend⟩ := parsed_dist_inv deflate
  obtain ⟨extL, extD⟩ := deflateParsed_codes_ext prev L D .none rfl
  have heldEq : held = natBits l.bits.toNat l.hold.toNat := HeldBits.eq_natBits heldBits
  subst heldEq
  have distTable0 := distTable
  obtain ⟨ref, offset, ca, used0, ptr, get, inv0, stable0⟩ := distTable
  have inv : Inv DISTS ca offset s.distbits.toNat used0 D := inv0
  have stable : StableQuery DISTS ca offset s.distbits.toNat := stable0.1
  have ptr0 : s.distcode = .ref ref offset := ptr
  obtain ⟨ref', offset', ca', ptr', get', safe⟩ := (tables zs s st hs).distanceTable
  rw [ptr0] at ptr'
  obtain ⟨rfl, rfl⟩ := Ptr.ref.inj ptr'
  rw [get] at get'
  cases get'
  obtain ⟨u0, u0le, backEq⟩ := back zs s st hs
  obtain ⟨symbol, lx, r1L, d1, lo, hi, x1, lenEq⟩ := pend
  have pend' : PendingParsed L D tb (.distance length) := ⟨symbol, lx, r1L, d1, lo, hi, x1, lenEq⟩
  have window' := fun (s' : InflateState) (l' : IL) (wnd : s'.window = s.window)
      (ws : s'.wsize = s.wsize) (wn : s'.wnext = s.wnext) (wh : s'.whave = s.whave) =>
    window_transfer (s := loopState s l) (s' := loopState s' l') wnd ws wn wh
      (fun q => byte_view_get_setI h zs s' q) window
  let Fail : Nat → Prop := fun k => ∀ sym rest,
    decodeSym D ((stream l (f.inp.drop (loopRead l))).take k) = some (sym, rest) → 29 < sym
  have entryShort : l.bits.toNat < 8 ∨ Fail (l.bits.toNat - 8) := by
    rcases p7 with lt | none
    · exact Or.inl lt
    · right
      intro sym rest dec
      apply none sym rest
      rw [heldShort_eq]
      show decodeSym D (natBits (l.bits.toNat - 8) l.hold.toNat) = _
      rw [short_take binv rfl _ (by omega)]
      exact dec
  have shortOf : ∀ (reg : IL) (u : Nat), reg.bits.toNat = l.bits.toNat + 8 * u →
      (∀ k, k < u → Fail (l.bits.toNat + 8 * k)) → reg.bits.toNat < 8 ∨ Fail (reg.bits.toNat - 8) := by
    intro reg u cnt fails
    cases u with
    | zero =>
      rw [cnt]
      simpa using entryShort
    | succ u =>
      right
      rw [show reg.bits.toNat - 8 = l.bits.toNat + 8 * u by omega]
      exact fails u (by omega)
  -- leaving for input
  have leaveLoop : ∀ (reg : IL) (u : Nat), u ≤ (f.inp.drop (loopRead l)).length →
      BitInv h reg ((f.inp.drop (loopRead l)).drop u) →
      stream reg ((f.inp.drop (loopRead l)).drop u) = stream l (f.inp.drop (loopRead l)) →
      RegsKeep l reg → reg.next = inputAdvance l.next u → reg.bits.toNat = l.bits.toNat + 8 * u →
      (∀ k, k < u → Fail (l.bits.toNat + 8 * k)) → LoopMatches c f h reg := by
    intro reg u ule inv' same' keep next' cnt fails
    have haveOld := binv.have_eq
    have haveNew := inv'.have_eq
    simp only [List.length_drop, loopRead] at haveOld haveNew ule
    have readEq : loopRead reg = loopRead l + u := by simp only [loopRead, keep.1]; omega
    have usedE : reg.have_.toNat + u = l.have_.toNat := by omega
    have bitsR := bits_pull bitsEq readEq same'
    have binvR : BitInv h reg (f.inp.drop (loopRead reg)) := by
      rw [readEq, ← List.drop_drop]; exact inv'
    have p7' : reg.bits.toNat < 8 ∨ ∀ sym rest,
        decodeSym D (heldShort (loopState s reg)) = some (sym, rest) → 29 < sym := by
      rcases shortOf reg u cnt fails with lt | fl
      · exact Or.inl lt
      · right
        intro sym rest dec
        apply fl sym rest
        rw [heldShort_eq] at dec
        rw [← short_take inv' same' _ (by omega)]
        exact dec
    have moved := loop_move (s' := s) (l' := reg) (j := u)
      (pos := ⟨out, final, .codes L D (.distance length)⟩) st retOk config haveLe inLen leftLe
      pendBase putEq outBytes writable sepIn sepWin sepOutIn keep usedE next' binvR
      (by rw [bitsR, consumedEq]; simp only [List.append_assoc]; rfl)
      (HeldBits.of_natBits (s := loopState s reg) binvR.hold_lt) wrapHeader rfl
      (DeflateParsed.partialToken tb prev pend')
      ⟨last, table_setI (s' := s) hs rfl lenTable, table_setI (s' := s) hs rfl distTable0, mode,
        lengthEq, p7'⟩
      (window' _ _ rfl rfl rfl rfl) check wrapM outputEq
    rw [setI_self hs] at moved
    exact moved
  -- the common end: a fitted leaf, its code dropped
  have tail : ∀ (rF rD : IL) (uF cons : Nat) (e : Code) (b : Int32),
      uF ≤ (f.inp.drop (loopRead l)).length →
      BitInv h rF ((f.inp.drop (loopRead l)).drop uF) →
      stream rF ((f.inp.drop (loopRead l)).drop uF) = stream l (f.inp.drop (loopRead l)) →
      RegsKeep l rF → RegsKeep rF rD → rD.have_ = rF.have_ → rD.next = inputAdvance l.next uF →
      rF.bits.toNat = l.bits.toNat + 8 * uF → (∀ k, k < uF → Fail (l.bits.toNat + 8 * k)) →
      tableRead DISTS ca offset s.distbits.toNat (DecodeShort.padded (natBits rF.bits.toNat rF.hold.toNat)) =
        some (e, cons) → cons ≤ rF.bits.toNat →
      BitInv h rD ((f.inp.drop (loopRead l)).drop uF) →
      natBits rF.bits.toNat rF.hold.toNat = natBits cons rF.hold.toNat ++ natBits rD.bits.toNat rD.hold.toNat →
      runX (inflate_DIST c) l h = runX (distLeafTail c e) rD (setI h zs { s with back := b }) →
      ∃ result l' h', runX (inflate_DIST c) l h = .ok ((result, l'), h') ∧
        ((result = .error Ex.leave ∧ (l'.have_ = 0 ∨ l.left = 0) ∧ LoopMatches c f h' l') ∨
         (result = .ok () ∧ loopRead l ≤ loopRead l' ∧
           (LoopMatches c f h' l' ∨
            ((∀ zs s, c.st = some (.tab zs) → h'.istates zs = some s → s.mode = BAD) ∧
              LoopDoomed f l')))) := by
    intro rF rD uF cons e b ule invF sameF keepF keepD haveD nextD cntF failsF query fit invD split run
    have haveOld := binv.have_eq
    have haveNew := invF.have_eq
    simp only [List.length_drop, loopRead] at haveOld haveNew ule
    have readF : loopRead rF = loopRead l + uF := by simp only [loopRead, keepF.1]; omega
    have readD : loopRead rD = loopRead l + uF := by
      simp only [loopRead, keepD.1, haveD]; exact readF
    have bitsF := bits_pull bitsEq readF sameF
    have bitsD : bytesToBits (f.logIn ++ f.inp.take (loopRead rD)) =
        (consumed ++ natBits cons rF.hold.toNat) ++ natBits rD.bits.toNat rD.hold.toNat := by
      rw [readD, ← readF, bitsF, split, List.append_assoc]
    have fitted := fitted_leaf_meaning inv stable query (by rw [natBits_length]; exact fit)
    have E' : Env c (setI h zs { s with back := b }) r zs z { s with back := b } :=
      ⟨strm, st, by simpa using hz, by simp⟩
    have binvD : BitInv h rD (f.inp.drop (loopRead rD)) := by
      rw [readD, ← List.drop_drop]; exact invD
    by_cases good : e.op &&& 64 = 0
    · -- a valid distance symbol: `DISTEXT`
      obtain ⟨sym, valid, meaning, cEq, decAll⟩ := fitted.1 (distsAccepted.mpr good)
      have valid' : sym ≤ 29 := distsValid.mp valid
      obtain ⟨opEq, valEq⟩ := distsEntry valid' meaning
      have dec0 : decodeSym D (natBits rF.bits.toNat rF.hold.toNat) =
          some (sym, (natBits rF.bits.toNat rF.hold.toNat).drop cons) := by
        simpa using decAll []
      have decX : decodeSym D (natBits cons rF.hold.toNat) = some (sym, []) := by
        have := decode_take extD dec0 (k := cons) (by omega)
        rw [natBits_take _ _ _ fit, ← cEq] at this
        rw [this, List.drop_eq_nil_of_le (by rw [natBits_length]; exact Nat.le_refl _)]
      have ppX : PendingParsed L D (tb ++ natBits cons rF.hold.toNat) (.distanceExtra length sym) :=
        ⟨symbol, lx, r1L ++ natBits cons rF.hold.toNat, [] ++ natBits cons rF.hold.toNat,
          extL _ _ _ _ d1, lo, hi, readBits_append _ _ _ _ _ x1, lenEq,
          by rw [List.nil_append]; exact decX, valid'⟩
      have lenD : rD.bits.toNat = rF.bits.toNat - cons := by
        have := congrArg List.length split
        simp only [List.length_append, natBits_length] at this
        omega
      have shortF : (natBits rF.bits.toNat rF.hold.toNat).length < 8 ∨ ∀ s' r',
          decodeSym D ((natBits rF.bits.toNat rF.hold.toNat).take
            ((natBits rF.bits.toNat rF.hold.toNat).length - 8)) = some (s', r') → 29 < s' := by
        rw [natBits_length]
        rcases shortOf rF uF cntF failsF with lt | fl
        · exact Or.inl lt
        · right
          intro s' r' dec
          rw [natBits_take _ _ _ (by omega), short_take invF sameF _ (by omega)] at dec
          exact fl s' r' dec
      have leftLt := left_short extD dec0 valid' shortF
      rw [natBits_length, ← cEq] at leftLt
      have extraNat : (e.op.toUInt32 &&& 15).toNat = distExtras.getD sym 0 := by
        rw [op_and_mask, opEq]
        have := distExtras_le sym (by omega)
        omega
      have loopD := loop_move (s' := distState { s with back := b } e) (l' := rD) (j := uF)
        (pos := ⟨out, final, .codes L D (.distanceExtra length sym)⟩) st retOk
        ⟨config.1, config.2.1, config.2.2.1, config.2.2.2.1, config.2.2.2.2.1,
          show DISTEXT ≠ SYNC by decide⟩
        haveLe inLen leftLe pendBase putEq outBytes writable sepIn sepWin sepOutIn (keepF.trans keepD)
        (by rw [haveD]; omega) nextD binvD
        (by rw [bitsD, consumedEq]; simp only [List.append_assoc]; rfl)
        (HeldBits.of_natBits (s := loopState (distState { s with back := b } e) rD) binvD.hold_lt)
        wrapHeader rfl (DeflateParsed.partialToken (tb ++ natBits cons rF.hold.toNat) prev ppX)
        ⟨last, table_setI (s' := distState { s with back := b } e) hs rfl lenTable,
          table_setI (s' := distState { s with back := b } e) hs rfl distTable0, rfl, lengthEq,
          extraNat, by show e.val.toUInt32.toNat = _; rw [UInt16.toNat_toUInt32, valEq],
          by show rD.bits.toNat < 8 + (e.op.toUInt32 &&& 15).toNat; omega⟩
        (window' _ _ rfl rfl rfl rfl) check wrapM outputEq
      have sameS : ∀ zs' s', c.st = some (.tab zs') →
          (setI h zs (distState { s with back := b } e)).istates zs' = some s' →
          s' = distState { s with back := b } e := by
        intro zs' s' st' hs'
        rw [st] at st'
        cases st'
        rw [setI_istates_same] at hs'
        cases hs'
        rfl
      have keepT := keepF.trans keepD
      obtain ⟨result, l', h', runT, rest⟩ := distext_step loopD strm
        (by rw [ZStreamRef.get_setI]; exact hz)
        (fun zs' s' st' hs' => by rw [sameS zs' s' st' hs']; rfl)
        (fun zs' s' st' hs' => by rw [sameS zs' s' st' hs']; exact bounds zs s st hs)
        (fun zs' s' st' hs' => by rw [sameS zs' s' st' hs']; exact sane zs s st hs)
        (fun zs' s' st' hs' => by rw [sameS zs' s' st' hs']; exact wsizeBits zs s st hs)
        (fun zs' s' st' hs' => by rw [sameS zs' s' st' hs']; exact ring zs s st hs)
        (fun zs' s' st' hs' w o d i hw hp => by
          rw [sameS zs' s' st' hs'] at hw
          rw [keepT.2.2.2.1] at hp
          exact privateWindow zs s st hs w o d i hw hp)
        rawWidth
      have runAll : runX (inflate_DIST c) l h = .ok ((result, l'), h') := by
        rw [run, leafTail_ok E' e rD good, setI_setI]
        exact runT
      refine ⟨result, l', h', runAll, ?_⟩
      rcases rest with ⟨leave, cause, m⟩ | ⟨ok, more, m⟩
      · exact Or.inl ⟨leave, cause.imp id (fun e => keepT.2.2.1.symm.trans e), m⟩
      · exact Or.inr ⟨ok, by rw [readD] at more; omega, m⟩
    · -- an invalid code: `BAD`
      obtain ⟨i, runB⟩ := leafTail_bad E' e rD good
      refine ⟨.ok (), rD, _, run.trans runB, Or.inr ⟨rfl, by rw [readD]; omega, Or.inr ⟨?_, ?_⟩⟩⟩
      · intro zs' s' st' hs'
        rw [st] at st'
        cases st'
        simp only [badHeap, setI_istates_same, Option.some.injEq] at hs'
        rw [← hs']
      · apply doomed_of_aligned (rest := tb ++ natBits rF.bits.toNat rF.hold.toNat) wrapHeader prev
        · rw [show loopRead rD = loopRead rF by rw [readD, readF], bitsF, consumedEq]
          simp only [List.append_assoc]
        · intro more tail outF _ resid
          obtain ⟨_, _, r', h'', symbols, _⟩ := resid
          have rej : Token.Rejected L D bodyDict out
              (tb ++ (natBits rF.bits.toNat rF.hold.toNat ++ more)) := by
            refine .distance (extL _ _ _ _ d1) lo hi (readBits_append _ _ _ _ _ x1) ?_
            intro more' found
            obtain ⟨ds, rest, dec, le⟩ := found
            exact fitted.2 (fun acc => good (distsAccepted.mp acc)) (more ++ more')
              ⟨ds, rest, by simpa only [List.nil_append, List.append_assoc] using dec,
                distsValid.mpr le⟩
          exact ZlibF.Spec.Token.rejected_has_no_symbols _ _ _ _ _ rej r' h''
            (by simpa only [List.append_assoc] using symbols)
  -- the root lookup
  have fail1 : ∀ current used, LookupRegShape l current →
      BitInv h current ((f.inp.drop (loopRead l)).drop used) →
      stream current ((f.inp.drop (loopRead l)).drop used) = stream l (f.inp.drop (loopRead l)) →
      current.bits.toNat = l.bits.toNat + 8 * used →
      current.bits.toNat < (codeLookupValue ca offset s.distbits.toNat current).bits.toNat →
      Fail current.bits.toNat := by
    intro cur u _ inv' same' _ nofit sym rest dec
    rw [← held_take inv' same'] at dec
    have q := dist_query inv safe (bits := cur.bits.toNat) (hold := cur.hold.toNat) inv'.hold_lt
    have nofit' : cur.bits.toNat < (ca.getD (offset + cur.hold.toNat % 2 ^ s.distbits.toNat) default).bits.toNat :=
      nofit
    by_cases sl : SlowDistLink (ca.getD (offset + cur.hold.toNat % 2 ^ s.distbits.toNat) default)
    · obtain ⟨_, _, query⟩ := q.2 sl
      exact nofit_invalid inv query
        (by rw [natBits_length]; exact Nat.lt_of_lt_of_le nofit' (Nat.le_add_right _ _)) sym rest dec
    · obtain ⟨_, query⟩ := q.1 sl
      exact nofit_invalid inv query (by rw [natBits_length]; exact nofit') sym rest dec
  obtain ⟨res1, r1, u1, run1, u1le, inv1, same1, shape1, count1, sel1, kinds1, ok1, leave1, cur1,
    fails1⟩ := lookup1_dist_fail st hs ptr0 get safe binv Fail fail1
  have keep1 := keep_of_lookup shape1
  by_cases isLeave : res1 = .error Ex.leave
  · subst isLeave
    exact ⟨_, _, _, dist_run_leave run1, Or.inl ⟨rfl, Or.inl (leave1 rfl).1,
      leaveLoop r1 u1 u1le inv1 same1 keep1 cur1 count1 fails1⟩⟩
  have isOk : res1 = .ok () := kinds1.resolve_right isLeave
  subst isOk
  have fit1 := ok1 rfl
  have hereEq : r1.here = ca.getD (offset + r1.hold.toNat % 2 ^ s.distbits.toNat) default := sel1
  have q1 := dist_query inv safe (bits := r1.bits.toNat) (hold := r1.hold.toNat) inv1.hold_lt
  rw [← hereEq] at q1
  have haveOld := binv.have_eq
  have have1 := inv1.have_eq
  simp only [List.length_drop, loopRead] at haveOld have1 u1le
  by_cases sl : SlowDistLink r1.here
  · -- a link: the second-level lookup
    obtain ⟨rootBits, link0, _⟩ := q1.2 sl
    have B1 : BitInv h { r1 with last := r1.here } ((f.inp.drop (loopRead l)).drop u1) :=
      ⟨inv1.have_eq, inv1.next, inv1.hold_lt⟩
    have idxAt : ∀ (cur : IL) (bs' : List UInt8), BitInv h cur bs' →
        stream cur bs' = stream l (f.inp.drop (loopRead l)) → r1.bits.toNat ≤ cur.bits.toNat →
        cur.hold.toNat % 2 ^ s.distbits.toNat = r1.hold.toNat % 2 ^ s.distbits.toNat := by
      intro cur bs' inv' same' le
      have a := short_take inv' same' s.distbits.toNat (by omega)
      have b := short_take inv1 same1 s.distbits.toNat (by omega)
      have := congrArg MeaningBits.heldValue (a.trans b.symm)
      rw [MeaningBits.heldValue_natBits, MeaningBits.heldValue_natBits] at this
      exact this
    have fail2 : ∀ current used, LookupRegShape { r1 with last := r1.here } current →
        BitInv h current (((f.inp.drop (loopRead l)).drop u1).drop used) →
        stream current (((f.inp.drop (loopRead l)).drop u1).drop used) =
          stream { r1 with last := r1.here } ((f.inp.drop (loopRead l)).drop u1) →
        current.bits.toNat = ({ r1 with last := r1.here } : IL).bits.toNat + 8 * used →
        current.bits.toNat < r1.here.bits.toNat + (subLookupValue ca offset r1.here current).bits.toNat →
        Fail current.bits.toNat := by
      intro cur u _ inv' same' cnt nofit sym rest dec
      have same'' : stream cur (((f.inp.drop (loopRead l)).drop u1).drop u) =
          stream l (f.inp.drop (loopRead l)) := same'.trans same1
      rw [← held_take inv' same''] at dec
      have q := dist_query inv safe (bits := cur.bits.toNat) (hold := cur.hold.toNat) inv'.hold_lt
      rw [idxAt cur _ inv' same'' (by change cur.bits.toNat = r1.bits.toNat + 8 * u at cnt; omega),
        ← hereEq] at q
      obtain ⟨_, _, query⟩ := q.2 sl
      exact nofit_invalid inv query (by rw [natBits_length]; exact nofit) sym rest dec
    obtain ⟨res2, r2, u2, run2, u2le, inv2, same2, shape2, count2, sel2, leaf2, kinds2, ok2, leave2,
      cur2, fails2⟩ := lookup2_dist_fail r1.here st hs ptr0 get rfl link0 B1 Fail fail2
    have keep2 : RegsKeep l r2 :=
      keep1.trans ((show RegsKeep r1 { r1 with last := r1.here } from ⟨rfl, rfl, rfl, rfl, rfl⟩).trans
        (keep_of_lookup shape2))
    have dropEq : ((f.inp.drop (loopRead l)).drop u1).drop u2 = (f.inp.drop (loopRead l)).drop (u1 + u2) :=
      List.drop_drop
    rw [dropEq] at inv2 same2
    have same2' : stream r2 ((f.inp.drop (loopRead l)).drop (u1 + u2)) = stream l (f.inp.drop (loopRead l)) :=
      same2.trans same1
    have u2le' : u2 ≤ ((f.inp.drop (loopRead l)).drop u1).length := u2le
    simp only [List.length_drop, loopRead] at u2le'
    have next2 : r2.next = inputAdvance l.next (u1 + u2) := by
      rw [cur2, show ({ r1 with last := r1.here } : IL).next = r1.next from rfl, cur1, inputAdvance_add]
    have count2' : r2.bits.toNat = l.bits.toNat + 8 * (u1 + u2) := by
      change r2.bits.toNat = r1.bits.toNat + 8 * u2 at count2
      omega
    have failsT : ∀ k, k < u1 + u2 → Fail (l.bits.toNat + 8 * k) := by
      intro k lt
      by_cases first : k < u1
      · exact fails1 k first
      · have := fails2 (k - u1) (by omega)
        change Fail (r1.bits.toNat + 8 * (k - u1)) at this
        rw [show r1.bits.toNat + 8 * (k - u1) = l.bits.toNat + 8 * k by omega] at this
        exact this
    by_cases isLeave2 : res2 = .error Ex.leave
    · subst isLeave2
      exact ⟨_, _, _, dist_run_sub_leave run1 sl run2, Or.inl ⟨rfl, Or.inl (leave2 rfl).1,
        leaveLoop r2 (u1 + u2) (by simp only [List.length_drop, loopRead]; omega) inv2 same2' keep2
          next2 count2' failsT⟩⟩
    have isOk2 : res2 = .ok () := kinds2.resolve_right isLeave2
    subst isOk2
    have fit2 := ok2 rfl
    have lastEq : r2.last = r1.here := by rw [shape2]
    have leafBits := leaf2.1
    have rootSmall : r1.here.bits.toNat ≤ 15 := link0.1
    have runS := dist_run_sub_ok E u0 run1 sl run2 lastEq backEq rootSmall (by omega)
    -- the two drops
    have small1 : r1.here.bits.toUInt32.toNat < 64 := by rw [UInt8.toNat_toUInt32]; omega
    obtain ⟨inv3, stream3, count3⟩ := DROPBITS_inv inv2 r1.here.bits.toUInt32
      (by rw [UInt8.toNat_toUInt32]; omega) small1
    let r3 : IL :=
      { r2 with hold := r2.hold >>> r1.here.bits.toUInt32.toUInt64, bits := r2.bits - r1.here.bits.toUInt32 }
    have count3' : r3.bits.toNat = r2.bits.toNat - r1.here.bits.toNat := by
      rw [UInt8.toNat_toUInt32] at count3; exact count3
    have small2 : r3.here.bits.toUInt32.toNat < 64 := by
      rw [UInt8.toNat_toUInt32]; show r2.here.bits.toNat < 64; omega
    obtain ⟨inv4, stream4, count4⟩ := DROPBITS_inv inv3 r3.here.bits.toUInt32
      (by rw [UInt8.toNat_toUInt32, count3']; show r2.here.bits.toNat ≤ _; omega) small2
    let r4 : IL :=
      { r3 with hold := r3.hold >>> r3.here.bits.toUInt32.toUInt64, bits := r3.bits - r3.here.bits.toUInt32 }
    have held3 := held_drop stream3 (by rw [UInt8.toNat_toUInt32]; omega)
    have held4 := held_drop stream4 (by rw [UInt8.toNat_toUInt32, count3']; show r2.here.bits.toNat ≤ _; omega)
    have split : natBits r2.bits.toNat r2.hold.toNat =
        natBits (r1.here.bits.toNat + r2.here.bits.toNat) r2.hold.toNat ++
          natBits r4.bits.toNat r4.hold.toNat := by
      have e4 : natBits r4.bits.toNat r4.hold.toNat =
          (natBits r2.bits.toNat r2.hold.toNat).drop (r1.here.bits.toNat + r2.here.bits.toNat) := by
        change natBits r4.bits.toNat r4.hold.toNat = _ at held4
        rw [held4]
        change (natBits r3.bits.toNat r3.hold.toNat).drop r3.here.bits.toUInt32.toNat = _
        change natBits r3.bits.toNat r3.hold.toNat = _ at held3
        rw [held3, List.drop_drop, UInt8.toNat_toUInt32, UInt8.toNat_toUInt32]
      rw [e4, ← natBits_take r2.bits.toNat r2.hold.toNat _ fit2, List.take_append_drop]
    have q2 := dist_query inv safe (bits := r2.bits.toNat) (hold := r2.hold.toNat) inv2.hold_lt
    rw [idxAt r2 _ inv2 same2' (by omega), ← hereEq] at q2
    obtain ⟨_, _, query2⟩ := q2.2 sl
    have hereEq2 : r2.here = ca.getD (offset + r1.here.val.toNat +
        subLookupIndexNat r1.here r2.hold.toNat) default := sel2
    rw [← hereEq2] at query2
    have E1 : Env c (setI h zs { s with back := Int32.ofNat (u0 + r1.here.bits.toNat) }) r zs z
        { s with back := Int32.ofNat (u0 + r1.here.bits.toNat) } :=
      ⟨strm, st, by simpa using hz, by simp⟩
    have runF := dist_run_finish E1 r3 (u0 + r1.here.bits.toNat) rfl
      (by show r2.here.bits.toNat ≤ 15; omega) (by omega)
    rw [setI_setI] at runF
    exact tail r2 r4 (u1 + u2) (r1.here.bits.toNat + r2.here.bits.toNat) r2.here
      (Int32.ofNat (u0 + r1.here.bits.toNat + r3.here.bits.toNat))
      (by simp only [List.length_drop, loopRead]; omega) inv2 same2' keep2 ⟨rfl, rfl, rfl, rfl, rfl⟩ rfl
      next2 count2' failsT query2 fit2
      inv4 split (runS.trans runF)
  · -- a root leaf
    obtain ⟨leaf0, query1⟩ := q1.1 sl
    have small : r1.here.bits.toUInt32.toNat < 64 := by rw [UInt8.toNat_toUInt32]; have := leaf0.1; omega
    obtain ⟨invD, streamD, countD⟩ := DROPBITS_inv inv1 r1.here.bits.toUInt32
      (by rw [UInt8.toNat_toUInt32]; exact fit1) small
    have heldD := held_drop streamD (by rw [UInt8.toNat_toUInt32]; exact fit1)
    have split : natBits r1.bits.toNat r1.hold.toNat =
        natBits r1.here.bits.toNat r1.hold.toNat ++
          natBits (r1.bits - r1.here.bits.toUInt32).toNat
            (r1.hold >>> r1.here.bits.toUInt32.toUInt64).toNat := by
      rw [heldD, UInt8.toNat_toUInt32, ← natBits_take r1.bits.toNat r1.hold.toNat _ fit1,
        List.take_append_drop]
    have runF := (dist_run_leaf run1 sl).trans
      (dist_run_finish E r1 u0 backEq (by have := leaf0.1; omega) (by omega))
    exact tail r1
      { r1 with hold := r1.hold >>> r1.here.bits.toUInt32.toUInt64, bits := r1.bits - r1.here.bits.toUInt32 }
      u1 r1.here.bits.toNat r1.here (Int32.ofNat (u0 + r1.here.bits.toNat))
      (by simp only [List.length_drop, loopRead]; omega) inv1 same1 keep1 ⟨rfl, rfl, rfl, rfl, rfl⟩ rfl cur1
      count1 fails1 query1 fit1 invD split runF

#print axioms dist_step

end DistStep


/-! ## `LENEXT` -/

theorem lengthExtras_le : ∀ i < 29, lengthExtras.getD i 0 ≤ 5 := by decide
theorem lengthBases_le : ∀ i < 29, lengthBases.getD i 0 + 2 ^ lengthExtras.getD i 0 ≤ 259 := by decide

/-- The only stage a `LENEXT` state can stand for. -/
theorem stage_of_lenext {h : Heap} {s : InflateState} {f : LoopFrame} {checked : List UInt8}
    {stage : WrapStage} (stageFacts : LoopStageMatches h s f checked stage) (mode : s.mode = LENEXT) :
    ∃ header out final L D symbol,
      stage = .body header ⟨out, final, .codes L D (.lengthExtra symbol)⟩ := by
  rcases stage with bytes | header | ⟨header, ⟨out, final, pos⟩⟩ | ⟨header, out, bytes⟩ | out
  · obtain ⟨lo, hi⟩ := stageFacts
    rw [mode] at lo hi
    exact absurd hi (by decide)
  · have := stageFacts
    simp only [LoopStageMatches] at this
    rw [mode] at this
    exact absurd this (by decide)
  · obtain ⟨body, _, _⟩ := stageFacts
    rcases pos with _ | _ | remaining | header' | ⟨L, D, pending⟩ | _
    · obtain ⟨m, _⟩ := body
      rw [mode] at m
      rcases m with m | m <;> exact absurd m (by decide)
    · obtain ⟨m, _⟩ := body
      rw [mode] at m
      exact absurd m (by decide)
    · obtain ⟨m, _⟩ := body
      rw [mode] at m
      rcases m with m | m <;> exact absurd m (by decide)
    · obtain ⟨dyn, _⟩ := body
      rcases dynamic_mode dyn with m | m | m <;> (rw [mode] at m; exact absurd m (by decide))
    · obtain ⟨_, _, _, rest⟩ := body
      rcases pending with _ | symbol | length | ⟨length, ds⟩ | ⟨remaining, dist⟩ | byte
      · rw [mode] at rest; rcases rest.1 with m | m <;> exact absurd m (by decide)
      · exact ⟨header, out, final, L, D, symbol, rfl⟩
      · rw [mode] at rest; exact absurd rest.1 (by decide)
      · rw [mode] at rest; exact absurd rest.1 (by decide)
      · rw [mode] at rest; exact absurd rest.1 (by decide)
      · rw [mode] at rest; exact absurd rest.1 (by decide)
    · obtain ⟨m, _⟩ := body
      rw [mode] at m
      rcases m with m | m <;> exact absurd m (by decide)
  · obtain ⟨m, _⟩ := stageFacts
    rw [mode] at m
    rcases m with m | m <;> exact absurd m (by decide)
  · have m : s.mode = DONE := stageFacts
    rw [mode] at m
    exact absurd m (by decide)

theorem parsed_lenext_inv {dict : List UInt8} {bits : List Bool} {out : List UInt8} {final : Bool}
    {L D : List Nat} {symbol : Nat}
    (parsed : DeflateParsed dict bits ⟨out, final, .codes L D (.lengthExtra symbol)⟩) :
    ∃ c0 tb, bits = c0 ++ tb ∧ DeflateParsed dict c0 ⟨out, final, .codes L D .none⟩ ∧
      PendingParsed L D tb (.lengthExtra symbol) := by
  cases parsed with
  | partialToken _ prev pp => exact ⟨_, _, rfl, prev, pp⟩

/-- The state after the extra length bits: the length in `length` and `was`, mode `DIST`. -/
def lenextState (s : InflateState) (l1 : IL) : InflateState :=
  let b : UInt32 := l1.hold.toUInt32 &&& ((1 : UInt32) <<< s.extra - 1)
  { s with length := s.length + b, back := u2i (i2u s.back + s.extra), was := s.length + b, mode := DIST }

theorem lenext_run_zero {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {s : InflateState} (E : Env c h r zs z s) (l : IL) (zero : s.extra = 0) :
    runX (inflate_LENEXT c) l h =
      runX (inflate_DIST c) l (setI h zs { s with was := s.length, mode := DIST }) := by
  have load : ldInflateState c.st h = .ok (s, h) := by rw [E.st, ldI_eq, E.hs]
  unfold inflate_LENEXT
  simp only [runX_bind, runX_lift_ok load, zero, bne_self_eq_false, Bool.false_eq_true, ite_false,
    runX_wrS E]

theorem lenext_run_wait {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {s : InflateState} (E : Env c h r zs z s) {l l1 : IL} (nonzero : s.extra ≠ 0)
    (run : runX (NEEDBITS s.extra) l h = .ok ((.error Ex.leave, l1), h)) :
    runX (inflate_LENEXT c) l h = .ok ((.error Ex.leave, l1), h) := by
  rw [inflate_LENEXT_need_cut E.st E.hs nonzero]
  unfold lenExtraNeed
  rw [runX_bind, run]

theorem lenext_run_ok {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {s : InflateState} (E : Env c h r zs z s) {l l1 : IL} (nonzero : s.extra ≠ 0)
    (small : s.extra.toNat < 32)
    (run : runX (NEEDBITS s.extra) l h = .ok ((.ok (), l1), h)) :
    runX (inflate_LENEXT c) l h =
      runX (inflate_DIST c) (distextRegs s l1) (setI h zs (lenextState s l1)) := by
  have small64 : s.extra.toNat < 64 := by omega
  rw [inflate_LENEXT_need_cut E.st E.hs nonzero]
  unfold lenExtraNeed
  rw [runX_bind, run]
  simp only [runX_bind, BITS_run l1 h s.extra small, runX_lift, E.st, wrI_eq, E.hs, setI_istates_same,
    DROPBITS_run, small64, setI_setI]
  rfl

set_option maxHeartbeats 4000000 in
/-- `case LENEXT` keeps the format meaning. Without the extra bits it leaves
with all input read (`have = 0`) and the started length held. Otherwise the
length is complete (`was = length`), and `case DIST` follows (`dist_step`).

The safety invariant of the decoder state supplies `tables` (`DataTablesSafe`)
and `back` (the signed back counter of a `LENEXT` state,
`DataPendingInvariant`); the other hypotheses are those of `match_step`. -/
theorem lenext_step {c : Ctx} {f : LoopFrame} {h : Heap} {l : IL} {r : ZStreamRef} {z : ZStream}
    (loop : LoopMatches c f h l) (strm : c.strm = some r) (hz : r.get h = some z)
    (lenext : ∀ zs s, c.st = some (.tab zs) → h.istates zs = some s → s.mode = LENEXT)
    (tables : ∀ zs s, c.st = some (.tab zs) → h.istates zs = some s → DataTablesSafe h s)
    (back : ∀ zs s, c.st = some (.tab zs) → h.istates zs = some s → BackBound s 15)
    (bounds : ∀ zs s, c.st = some (.tab zs) → h.istates zs = some s →
      s.wnext ≤ s.whave ∧ s.whave ≤ s.wsize)
    (sane : ∀ zs s, c.st = some (.tab zs) → h.istates zs = some s → s.sane ≠ 0)
    (wsizeBits : ∀ zs s, c.st = some (.tab zs) → h.istates zs = some s →
      s.wsize ≠ 0 → s.wsize.toNat = 2 ^ s.wbits.toNat)
    (ring : ∀ zs s, c.st = some (.tab zs) → h.istates zs = some s →
      s.whave < s.wsize → s.wnext = s.whave)
    (privateWindow : ∀ zs s, c.st = some (.tab zs) → h.istates zs = some s →
      ∀ w o d i, s.window = .ref w o → l.put = .ref d i → w ≠ d)
    (rawWidth : f.wrap = .raw → f.configured ≠ 0) :
    ∃ result l' h', runX (inflate_LENEXT c) l h = .ok ((result, l'), h') ∧
      ((result = .error Ex.leave ∧ (l'.have_ = 0 ∨ l.left = 0) ∧ LoopMatches c f h' l') ∨
       (result = .ok () ∧ loopRead l ≤ loopRead l' ∧
         (LoopMatches c f h' l' ∨
          ((∀ zs s, c.st = some (.tab zs) → h'.istates zs = some s → s.mode = BAD) ∧
            LoopDoomed f l')))) := by
  obtain ⟨zs, s, callOut, consumed, held, stage, st, hs, retOk, config, haveLe, inLen, binv, leftLe,
    pendLe, putEq, outBytes, writable, sepIn, sepWin, sepOutIn, bitsEq, heldBits, parsed, stageM,
    wrapM, outputEq⟩ := loop
  have E : Env c h r zs z s := ⟨strm, st, hz, hs⟩
  have mode : s.mode = LENEXT := lenext zs s st hs
  obtain ⟨header, out, final, L, D, symbol, rfl⟩ := stage_of_lenext stageM mode
  have pendBase := pendLe.2 _ _ rfl
  obtain ⟨⟨last, lenTable, distTable, _, extraEq, lengthEq, bitsLt⟩, window, check⟩ := stageM
  have extraEq' : s.extra.toNat = lengthExtras.getD (symbol - 257) 0 := extraEq
  have lengthEq' : s.length.toNat = lengthBases.getD (symbol - 257) 0 := lengthEq
  have bitsLt' : l.bits.toNat < 8 + s.extra.toNat := bitsLt
  obtain ⟨bodyDict, bitsP, wrapHeader, consumedEq, deflate⟩ := parsed
  obtain ⟨c0, tb, rfl, prev, pend⟩ := parsed_lenext_inv deflate
  obtain ⟨lo, hi, d1⟩ := pend
  obtain ⟨extL, extD⟩ := deflateParsed_codes_ext prev L D .none rfl
  have extraLe : s.extra.toNat ≤ 5 := by rw [extraEq']; exact lengthExtras_le _ (by omega)
  have baseBound := lengthBases_le (symbol - 257) (by omega)
  obtain ⟨u0, u0le, backEq⟩ := back zs s st hs
  have heldEq : held = natBits l.bits.toNat l.hold.toNat := HeldBits.eq_natBits heldBits
  subst heldEq
  have window' := fun (s' : InflateState) (l' : IL) (wnd : s'.window = s.window)
      (ws : s'.wsize = s.wsize) (wn : s'.wnext = s.wnext) (wh : s'.whave = s.whave) =>
    window_transfer (s := loopState s l) (s' := loopState s' l') wnd ws wn wh
      (fun q => byte_view_get_setI h zs s' q) window
  -- the extra bits `X` of the length complete it
  have ppOf : ∀ (X : List Bool) (x : Nat), readBits (lengthExtras.getD (symbol - 257) 0) X = some (x, []) →
      PendingParsed L D (tb ++ X) (.distance (lengthBases.getD (symbol - 257) 0 + x)) := by
    intro X x read
    exact ⟨symbol, x, [] ++ X, extL _ _ _ X d1, lo, hi, by rw [List.nil_append]; exact read, rfl⟩
  -- `DIST` on a complete length
  have viaDist : ∀ (s2 : InflateState) (l2 : IL), s2.mode = DIST → DecodeStateFrame s s2 →
      BackBound s2 20 → RegsKeep l l2 → loopRead l ≤ loopRead l2 →
      LoopMatches c f (setI h zs s2) l2 →
      ∃ result l' h', runX (inflate_DIST c) l2 (setI h zs s2) = .ok ((result, l'), h') ∧
        ((result = .error Ex.leave ∧ (l'.have_ = 0 ∨ l.left = 0) ∧ LoopMatches c f h' l') ∨
         (result = .ok () ∧ loopRead l ≤ loopRead l' ∧
           (LoopMatches c f h' l' ∨
            ((∀ zs s, c.st = some (.tab zs) → h'.istates zs = some s → s.mode = BAD) ∧
              LoopDoomed f l')))) := by
    intro s2 l2 m2 frame b2 keep more loop2
    have same : ∀ zs' s', c.st = some (.tab zs') → (setI h zs s2).istates zs' = some s' → s' = s2 := by
      intro zs' s' st' hs'
      rw [st] at st'
      cases st'
      rw [setI_istates_same] at hs'
      cases hs'
      rfl
    have fr : s2.window = s.window ∧ s2.wsize = s.wsize ∧ s2.wnext = s.wnext ∧ s2.whave = s.whave ∧
        s2.wbits = s.wbits ∧ s2.sane = s.sane := by
      rw [frame]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    obtain ⟨wnd, ws, wn, wh, wb, sn⟩ := fr
    obtain ⟨result, l', h', run, rest⟩ := dist_step loop2 strm (by rw [ZStreamRef.get_setI]; exact hz)
      (fun zs' s' st' hs' => by rw [same zs' s' st' hs']; exact m2)
      (fun zs' s' st' hs' => by
        rw [same zs' s' st' hs']; exact (tables zs s st hs).decode_update hs frame)
      (fun zs' s' st' hs' => by rw [same zs' s' st' hs']; exact b2)
      (fun zs' s' st' hs' => by rw [same zs' s' st' hs', wn, wh, ws]; exact bounds zs s st hs)
      (fun zs' s' st' hs' => by rw [same zs' s' st' hs', sn]; exact sane zs s st hs)
      (fun zs' s' st' hs' => by rw [same zs' s' st' hs', ws, wb]; exact wsizeBits zs s st hs)
      (fun zs' s' st' hs' => by rw [same zs' s' st' hs', wh, ws, wn]; exact ring zs s st hs)
      (fun zs' s' st' hs' w o d i hw hp => by
        rw [same zs' s' st' hs', wnd] at hw
        rw [keep.2.2.2.1] at hp
        exact privateWindow zs s st hs w o d i hw hp)
      rawWidth
    refine ⟨result, l', h', run, ?_⟩
    rcases rest with ⟨leave, cause, m⟩ | ⟨ok, read, rest⟩
    · exact Or.inl ⟨leave, cause.imp id (fun e => keep.2.2.1.symm.trans e), m⟩
    · exact Or.inr ⟨ok, by omega, rest⟩
  by_cases zero : s.extra = 0
  · -- no extra bits
    have zeroNat : s.extra.toNat = 0 := by rw [zero]; rfl
    have pp := ppOf [] 0 (by rw [← extraEq', zeroNat]; rfl)
    have loop2 := loop_move (s' := { s with was := s.length, mode := DIST }) (l' := l) (j := 0)
      (pos := ⟨out, final, .codes L D (.distance (lengthBases.getD (symbol - 257) 0 + 0))⟩) st retOk
      ⟨config.1, config.2.1, config.2.2.1, config.2.2.2.1, config.2.2.2.2.1, show DIST ≠ SYNC by decide⟩
      haveLe inLen leftLe pendBase putEq outBytes writable sepIn sepWin sepOutIn
      ⟨rfl, rfl, rfl, rfl, rfl⟩ (by omega) (inputAdvance_zero l.next).symm binv
      (by rw [bitsEq, consumedEq]; simp only [List.append_assoc, List.append_nil]; rfl)
      (HeldBits.of_natBits (s := loopState { s with was := s.length, mode := DIST } l) binv.hold_lt)
      wrapHeader rfl (DeflateParsed.partialToken (tb ++ []) prev pp)
      ⟨last, table_setI (s' := { s with was := s.length, mode := DIST }) hs rfl lenTable,
        table_setI (s' := { s with was := s.length, mode := DIST }) hs rfl distTable, rfl,
        by show s.length.toNat = _; rw [lengthEq', Nat.add_zero],
        Or.inl (by show l.bits.toNat < 8; omega)⟩
      (window' _ _ rfl rfl rfl rfl) check wrapM outputEq
    obtain ⟨result, l', h', run, rest⟩ := viaDist { s with was := s.length, mode := DIST } l rfl rfl
      ⟨u0, by omega, backEq⟩ ⟨rfl, rfl, rfl, rfl, rfl⟩ (Nat.le_refl _) loop2
    exact ⟨result, l', h', (lenext_run_zero E l zero).trans run, rest⟩
  · -- the extra bits
    obtain ⟨result, l1, j, run, jle, binv1, streamEq, _, shape, bitsBound, _, enough, empty,
      kinds, nextEq⟩ := NEEDBITS_run_cursor binv s.extra (by omega)
    have haveOld := binv.have_eq
    have haveNew := binv1.have_eq
    simp only [List.length_drop, loopRead] at haveOld haveNew jle
    have keep1 : RegsKeep l l1 := RegsKeep.of_shape shape
    have readEq : loopRead l1 = loopRead l + j := by
      simp only [loopRead, keep1.1]
      omega
    have used : l1.have_.toNat + j = l.have_.toNat := by omega
    have bits1 := bits_pull bitsEq readEq streamEq
    have binvL : BitInv h l1 (f.inp.drop (loopRead l1)) := by
      rw [readEq, ← List.drop_drop]
      exact binv1
    rcases kinds with rfl | rfl
    · -- the extra bits are held
      have available : s.extra.toNat ≤ l1.bits.toNat := enough rfl
      have bound1 : l1.bits.toNat < 8 + s.extra.toNat := by
        have : l1.bits.toNat ≤ max l.bits.toNat (s.extra.toNat + 7) := bitsBound
        omega
      obtain ⟨binv2, stream2, count2⟩ := DROPBITS_inv binvL s.extra available (by omega)
      have held2 := held_drop stream2 available
      have split1 : natBits l1.bits.toNat l1.hold.toNat =
          natBits s.extra.toNat l1.hold.toNat ++
            natBits (l1.bits - s.extra).toNat (l1.hold >>> s.extra.toUInt64).toNat := by
        rw [held2, ← natBits_take l1.bits.toNat l1.hold.toNat s.extra.toNat available,
          List.take_append_drop]
      have bNat : (l1.hold.toUInt32 &&& ((1 : UInt32) <<< s.extra - 1)).toNat =
          l1.hold.toNat % 2 ^ s.extra.toNat := BITS_toNat l1 s.extra (by omega)
      have bLt : l1.hold.toNat % 2 ^ s.extra.toNat < 2 ^ s.extra.toNat :=
        Nat.mod_lt _ (Nat.two_pow_pos _)
      have lenNat : (s.length + (l1.hold.toUInt32 &&& ((1 : UInt32) <<< s.extra - 1))).toNat =
          lengthBases.getD (symbol - 257) 0 + l1.hold.toNat % 2 ^ s.extra.toNat := by
        rw [UInt32.toNat_add, bNat, lengthEq']
        rw [extraEq'] at bLt ⊢
        exact Nat.mod_eq_of_lt (by omega)
      have read : readBits (lengthExtras.getD (symbol - 257) 0) (natBits s.extra.toNat l1.hold.toNat) =
          some (l1.hold.toNat % 2 ^ s.extra.toNat, []) := by
        rw [← extraEq']
        simpa only [List.append_nil] using readBits_natBits s.extra.toNat l1.hold.toNat []
      have pp := ppOf _ _ read
      have unsignedBack : (i2u s.back).toNat = u0 := by
        rw [backEq]
        simp [i2u, Nat.mod_eq_of_lt (by omega : u0 < 2 ^ 32)]
      have backNat : (i2u s.back + s.extra).toNat = u0 + s.extra.toNat := by
        rw [UInt32.toNat_add, unsignedBack, Nat.mod_eq_of_lt (by omega)]
      have backEq2 : u2i (i2u s.back + s.extra) = Int32.ofNat (u0 + s.extra.toNat) := by
        unfold u2i
        rw [backNat]
        rfl
      have keep : RegsKeep l (distextRegs s l1) := keep1.trans ⟨rfl, rfl, rfl, rfl, rfl⟩
      have read2 : loopRead (distextRegs s l1) = loopRead l + j := readEq
      have loop2 := loop_move (s' := lenextState s l1) (l' := distextRegs s l1) (j := j)
        (pos := ⟨out, final, .codes L D
          (.distance (lengthBases.getD (symbol - 257) 0 + l1.hold.toNat % 2 ^ s.extra.toNat))⟩) st retOk
        ⟨config.1, config.2.1, config.2.2.1, config.2.2.2.1, config.2.2.2.2.1,
          show DIST ≠ SYNC by decide⟩
        haveLe inLen leftLe pendBase putEq outBytes writable sepIn sepWin sepOutIn keep used
        (by show l1.next = _; exact nextEq) binv2
        (by
          show bytesToBits (f.logIn ++ f.inp.take (loopRead l1)) = _
          rw [bits1, split1, consumedEq]
          simp only [List.append_assoc]
          rfl)
        (HeldBits.of_natBits (s := loopState (lenextState s l1) (distextRegs s l1)) binv2.hold_lt)
        wrapHeader rfl (DeflateParsed.partialToken (tb ++ natBits s.extra.toNat l1.hold.toNat) prev pp)
        ⟨last, table_setI (s' := lenextState s l1) hs rfl lenTable,
          table_setI (s' := lenextState s l1) hs rfl distTable, rfl, lenNat,
          Or.inl (by show (l1.bits - s.extra).toNat < 8; rw [count2]; omega)⟩
        (window' _ _ rfl rfl rfl rfl) check wrapM outputEq
      obtain ⟨result, l', h', run2, rest⟩ := viaDist (lenextState s l1) (distextRegs s l1) rfl rfl
        ⟨u0 + s.extra.toNat, by omega, backEq2⟩ keep (by rw [read2]; omega) loop2
      exact ⟨result, l', h', (lenext_run_ok E zero (by omega) run).trans run2, rest⟩
    · -- waiting for input
      have wait := empty rfl
      have moved := loop_move (s' := s) (l' := l1) (j := j)
        (pos := ⟨out, final, .codes L D (.lengthExtra symbol)⟩) st retOk config haveLe inLen
        leftLe pendBase putEq outBytes writable sepIn sepWin sepOutIn keep1 used nextEq binvL
        (by rw [bits1, consumedEq]; simp only [List.append_assoc]; rfl)
        (HeldBits.of_natBits (s := loopState s l1) binv1.hold_lt) wrapHeader rfl
        (DeflateParsed.partialToken tb prev ⟨lo, hi, d1⟩)
        ⟨last, table_setI (s' := s) hs rfl lenTable, table_setI (s' := s) hs rfl distTable, mode,
          extraEq, lengthEq, by show l1.bits.toNat < 8 + s.extra.toNat; have := wait.2.2; omega⟩
        (window' _ _ rfl rfl rfl rfl) check wrapM outputEq
      rw [setI_self hs] at moved
      exact ⟨_, _, _, lenext_run_wait E zero run, Or.inl ⟨rfl, Or.inl wait.2.1, moved⟩⟩

#print axioms lenext_step

end Zlib.Inflate.Proofs.MeaningDistance
