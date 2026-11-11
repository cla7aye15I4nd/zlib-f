import ZlibF.Proof.«inflate.c.meaning-match»
import ZlibF.Proof.«inflate.c.distance-extra»

/-!
# inflate.c: `DISTEXT` keeps the format meaning

`case DISTEXT` waits for the extra bits of the distance (`NEEDBITS`), adds
them to the distance base in `offset`, drops them and falls through to
`case MATCH`. The parse moves from the started distance
(`Pending.distanceExtra`) to the complete match with nothing written
(`PendingParsed` at `.copy`, P12), whose distance is not yet checked against
the history; `match_step` then copies or rejects it. Waiting for input keeps
the started distance with more held bits, still fewer than `8 + extra`.
-/

namespace Zlib.Inflate.Proofs.MeaningDistance
open C Zlib.Inflate Zlib.Inflate.Proofs Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs.MeaningLit Zlib.Inflate.Proofs.MeaningCopy Zlib.Inflate.Proofs.MeaningBits
open Zlib.Inflate.Proofs.MeaningBlock Zlib.Inflate.Proofs.MeaningMatch ZlibF.Spec.Proofs
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

end Zlib.Inflate.Proofs.MeaningDistance
