import ZlibF.Proof.«gzlib.c.open-append-io»
import ZlibF.Math.«gz-mode-parser»

/-!
# gzlib.c: complete actual mode-loop step

Every source action is retained. The normal and '+' branches are separate
cases of the complete loop, with arbitrary old handle fields and mode storage.
-/

namespace Zlib.Gzlib.Proofs
open C Zlib.GzFs Zlib.Gzguts Zlib.Gzlib.Spec ZlibF.Spec.Public.OffsetProof
open ZlibF.Math.GzModeParser

/-- Exact source mode-loop condition. -/
def modeCondition (l : ModeLoop) : G (Bool × ModeLoop) := do
  let c ← load8 l.mode
  return (c != 0 && !l.done, l)

/-- Exact source mode-loop body. -/
def modeBody (state : GzStatePtr) (l : ModeLoop) : G ModeLoop := do
  let c : Int32 := (← load8 l.mode).toInt8.toInt32
  let mut l := l
  if c ≥ 48 && c ≤ 57 then
    -- state->level = *mode - '0';
    updS state fun s => { s with level := c - 48 }
  else if c == 114 then       -- 'r'
    updS state fun s => { s with mode := GZ_READ }
  else if c == 119 then       -- 'w'
    updS state fun s => { s with mode := GZ_WRITE }
  else if c == 97 then        -- 'a'
    updS state fun s => { s with mode := GZ_APPEND }
  else if c == 43 then        -- '+': can't read and write at the same time
    freeGzState state
    l := { l with done := true }
  else if c == 98 then        -- 'b'
    pure ()
  else if c == 101 then       -- 'e'
    l := { l with oflag := l.oflag ||| O_CLOEXEC }
  else if c == 120 then       -- 'x'
    l := { l with exclusive := 1 }
  else if c == 102 then       -- 'f'
    updS state fun s => { s with strategy := Z_FILTERED }
  else if c == 104 then       -- 'h'
    updS state fun s => { s with strategy := Z_HUFFMAN_ONLY }
  else if c == 82 then        -- 'R'
    updS state fun s => { s with strategy := Z_RLE }
  else if c == 70 then        -- 'F'
    updS state fun s => { s with strategy := Z_FIXED }
  else if c == 71 then        -- 'G'
    updS state fun s => { s with direct := -1 }
  else if c == 78 then        -- 'N'
    l := { l with oflag := l.oflag ||| O_NONBLOCK }
  else if c == 84 then        -- 'T'
    updS state fun s => { s with direct := 1 }
  else pure ()                -- default: ignore
  if !l.done then l := { l with mode := ← l.mode.add 1 }
  return l

/-- The named condition and body are exactly the original source mode loop. -/
theorem openModeLoop_step_cut (state : GzStatePtr) (mode : BPtr) :
    openModeLoop state mode = gwhile modeCondition (modeBody state)
      { mode, oflag := 0, exclusive := 0, done := false } := by rfl

/-- Pure effect of one nonfreeing source action on the four actual fields. -/
def modeActionState (s : GzState) : Action → GzState
  | .level v => { s with level := v }
  | .mode .read => { s with mode := GZ_READ }
  | .mode .write => { s with mode := GZ_WRITE }
  | .mode .append => { s with mode := GZ_APPEND }
  | .strategy n => { s with strategy := Int32.ofNat n }
  | .gzipOnly => { s with direct := -1 }
  | .transparent => { s with direct := 1 }
  | _ => s

def modeActionFlags (flags : Int32) : Action → Int32
  | .cloexec => flags ||| O_CLOEXEC
  | .nonblock => flags ||| O_NONBLOCK
  | _ => flags

def modeActionExclusive (old : Int32) : Action → Int32
  | .exclusive => 1
  | _ => old

/-- The actual condition reads the original byte once without changing either
world. This includes its post-'+' test with done=true. -/
theorem modeCondition_byte (h : Heap) (fs : Fs) (l : ModeLoop) (b : UInt8)
    (hb : load8 l.mode h = .ok (b, h)) :
    modeCondition l fs h = .ok (((b != 0 && !l.done, l), fs), h) := by
  unfold modeCondition
  offsetsimp [hb]

/-- Every nonfreeing action has the actual state/flags/exclusive effect and
advances the original mode pointer once. No field is assumed initially zero. -/
theorem modeBody_normal (h : Heap) (fs : Fs) (i : Nat) (s : GzState)
    (r : BRef) (off : Nat) (a : Array UInt8) (b : UInt8) (flags exclusive : Int32)
    (hs : h.gzstates i = some s) (ha : Space.get h r = some a)
    (hoff : off < a.size) (hnext : off + 1 ≤ a.size) (hb : a[off] = b)
    (hn : sourceAction b ≠ .bad) :
    modeBody (some (.tab i)) { mode := .ref r off, oflag := flags, exclusive, done := false } fs h =
      .ok (({ mode := .ref r (off + 1)
              oflag := modeActionFlags flags (sourceAction b)
              exclusive := modeActionExclusive exclusive (sourceAction b)
              done := false }, fs),
        setS h i (modeActionState s (sourceAction b))) := by
  have hadd : 0 ≤ (off : Int) + 1 ∧ (off : Int) + 1 ≤ (a.size : Int) := by omega
  have hself : setS h i s = h := by simp [setS, upd_self _ _ _ hs]
  by_cases h0 : 48 ≤ b.toInt8.toInt32 ∧ b.toInt8.toInt32 ≤ 57
  · offsetsimp [modeBody, sourceAction, modeActionState, modeActionFlags, modeActionExclusive, hs, load8, Ptr.load, ha, hoff, hb, Ptr.add, hadd, modeBytes_setS, hself, Z_FILTERED, Z_HUFFMAN_ONLY, Z_RLE, Z_FIXED, h0]
  ·
    by_cases h1 : b.toInt8.toInt32 = 114
    · offsetsimp [modeBody, sourceAction, modeActionState, modeActionFlags, modeActionExclusive, hs, load8, Ptr.load, ha, hoff, hb, Ptr.add, hadd, modeBytes_setS, hself, Z_FILTERED, Z_HUFFMAN_ONLY, Z_RLE, Z_FIXED, h0, h1]
    ·
      by_cases h2 : b.toInt8.toInt32 = 119
      · offsetsimp [modeBody, sourceAction, modeActionState, modeActionFlags, modeActionExclusive, hs, load8, Ptr.load, ha, hoff, hb, Ptr.add, hadd, modeBytes_setS, hself, Z_FILTERED, Z_HUFFMAN_ONLY, Z_RLE, Z_FIXED, h0, h1, h2]
      ·
        by_cases h3 : b.toInt8.toInt32 = 97
        · offsetsimp [modeBody, sourceAction, modeActionState, modeActionFlags, modeActionExclusive, hs, load8, Ptr.load, ha, hoff, hb, Ptr.add, hadd, modeBytes_setS, hself, Z_FILTERED, Z_HUFFMAN_ONLY, Z_RLE, Z_FIXED, h0, h1, h2, h3]
        ·
          by_cases h4 : b.toInt8.toInt32 = 43
          · exact False.elim (hn (by simp [sourceAction, h4]))
          ·
            by_cases h5 : b.toInt8.toInt32 = 98
            · offsetsimp [modeBody, sourceAction, modeActionState, modeActionFlags, modeActionExclusive, hs, load8, Ptr.load, ha, hoff, hb, Ptr.add, hadd, modeBytes_setS, hself, Z_FILTERED, Z_HUFFMAN_ONLY, Z_RLE, Z_FIXED, h0, h1, h2, h3, h4, h5]
            ·
              by_cases h6 : b.toInt8.toInt32 = 101
              · offsetsimp [modeBody, sourceAction, modeActionState, modeActionFlags, modeActionExclusive, hs, load8, Ptr.load, ha, hoff, hb, Ptr.add, hadd, modeBytes_setS, hself, Z_FILTERED, Z_HUFFMAN_ONLY, Z_RLE, Z_FIXED, h0, h1, h2, h3, h4, h5, h6]
              ·
                by_cases h7 : b.toInt8.toInt32 = 120
                · offsetsimp [modeBody, sourceAction, modeActionState, modeActionFlags, modeActionExclusive, hs, load8, Ptr.load, ha, hoff, hb, Ptr.add, hadd, modeBytes_setS, hself, Z_FILTERED, Z_HUFFMAN_ONLY, Z_RLE, Z_FIXED, h0, h1, h2, h3, h4, h5, h6, h7]
                ·
                  by_cases h8 : b.toInt8.toInt32 = 102
                  · offsetsimp [modeBody, sourceAction, modeActionState, modeActionFlags, modeActionExclusive, hs, load8, Ptr.load, ha, hoff, hb, Ptr.add, hadd, modeBytes_setS, hself, Z_FILTERED, Z_HUFFMAN_ONLY, Z_RLE, Z_FIXED, h0, h1, h2, h3, h4, h5, h6, h7, h8]
                  ·
                    by_cases h9 : b.toInt8.toInt32 = 104
                    · offsetsimp [modeBody, sourceAction, modeActionState, modeActionFlags, modeActionExclusive, hs, load8, Ptr.load, ha, hoff, hb, Ptr.add, hadd, modeBytes_setS, hself, Z_FILTERED, Z_HUFFMAN_ONLY, Z_RLE, Z_FIXED, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]
                    ·
                      by_cases h10 : b.toInt8.toInt32 = 82
                      · offsetsimp [modeBody, sourceAction, modeActionState, modeActionFlags, modeActionExclusive, hs, load8, Ptr.load, ha, hoff, hb, Ptr.add, hadd, modeBytes_setS, hself, Z_FILTERED, Z_HUFFMAN_ONLY, Z_RLE, Z_FIXED, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
                      ·
                        by_cases h11 : b.toInt8.toInt32 = 70
                        · offsetsimp [modeBody, sourceAction, modeActionState, modeActionFlags, modeActionExclusive, hs, load8, Ptr.load, ha, hoff, hb, Ptr.add, hadd, modeBytes_setS, hself, Z_FILTERED, Z_HUFFMAN_ONLY, Z_RLE, Z_FIXED, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
                        ·
                          by_cases h12 : b.toInt8.toInt32 = 71
                          · offsetsimp [modeBody, sourceAction, modeActionState, modeActionFlags, modeActionExclusive, hs, load8, Ptr.load, ha, hoff, hb, Ptr.add, hadd, modeBytes_setS, hself, Z_FILTERED, Z_HUFFMAN_ONLY, Z_RLE, Z_FIXED, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
                          ·
                            by_cases h13 : b.toInt8.toInt32 = 78
                            · offsetsimp [modeBody, sourceAction, modeActionState, modeActionFlags, modeActionExclusive, hs, load8, Ptr.load, ha, hoff, hb, Ptr.add, hadd, modeBytes_setS, hself, Z_FILTERED, Z_HUFFMAN_ONLY, Z_RLE, Z_FIXED, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
                            ·
                              by_cases h14 : b.toInt8.toInt32 = 84
                              · offsetsimp [modeBody, sourceAction, modeActionState, modeActionFlags, modeActionExclusive, hs, load8, Ptr.load, ha, hoff, hb, Ptr.add, hadd, modeBytes_setS, hself, Z_FILTERED, Z_HUFFMAN_ONLY, Z_RLE, Z_FIXED, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]
                              ·
                                offsetsimp [modeBody, sourceAction, modeActionState, modeActionFlags, modeActionExclusive, hs, load8, Ptr.load, ha, hoff, hb, Ptr.add, hadd, modeBytes_setS, hself, Z_FILTERED, Z_HUFFMAN_ONLY, Z_RLE, Z_FIXED, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]

/-- '+' really frees the actual handle, sets done, and leaves the mode pointer
on the offending byte. It performs no pointer increment or file operation. -/
theorem modeBody_bad (h : Heap) (fs : Fs) (i : Nat) (s : GzState)
    (r : BRef) (off : Nat) (a : Array UInt8) (b : UInt8) (flags exclusive : Int32)
    (hs : h.gzstates i = some s) (ha : Space.get h r = some a)
    (hoff : off < a.size) (hb : a[off] = b) (hbad : sourceAction b = .bad) :
    modeBody (some (.tab i)) { mode := .ref r off, oflag := flags, exclusive, done := false } fs h =
      .ok (({ mode := .ref r off, oflag := flags, exclusive, done := true }, fs),
        { h with gzstates := upd h.gzstates i none }) := by
  have he : b = 43 := (sourceAction_bad b).mp hbad
  have hbyte : a[off] = 43 := hb.trans he
  unfold modeBody
  offsetsimp [load8, Ptr.load, ha, hoff, hbyte, hs, freeGzState]

/-- Releasing the new handle cannot change any caller byte-reference kind. -/
theorem modeBytes_remove_state (h : Heap) (i : Nat) (r : BRef) :
    Space.get ({ h with gzstates := upd h.gzstates i none } : Heap) r = Space.get h r := by
  cases r <;> rfl

/-- After '+', the actual loop still safely reads that caller byte before
observing done=true, then terminates with the freed handle already absent. -/
theorem modeWhile_bad (h : Heap) (fs : Fs) (i : Nat) (s : GzState)
    (r : BRef) (off : Nat) (a : Array UInt8) (flags exclusive : Int32) (remaining : Nat)
    (hs : h.gzstates i = some s) (ha : Space.get h r = some a)
    (hoff : off < a.size) (hb : a[off] = 43) :
    gwhile.go (modeCondition) (modeBody (some (.tab i))) (remaining + 2)
      { mode := .ref r off, oflag := flags, exclusive, done := false } fs h =
      .ok (({ mode := .ref r off, oflag := flags, exclusive, done := true }, fs),
        { h with gzstates := upd h.gzstates i none }) := by
  have hload : load8 (.ref r off) h = .ok (43, h) := by
    simp [load8, Ptr.load, ha, hoff, hb]
  have hbody := modeBody_bad h fs i s r off a 43 flags exclusive hs ha hoff hb (by decide +kernel)
  have hload' : load8 (.ref r off) { h with gzstates := upd h.gzstates i none } =
      .ok (43, { h with gzstates := upd h.gzstates i none }) := by
    simp [load8, Ptr.load, modeBytes_remove_state, ha, hoff, hb]
  rw [show remaining + 2 = (remaining + 1) + 1 by omega, gwhile.go]
  simp only [G_bind_app, modeCondition_byte h fs { mode := .ref r off, oflag := flags, exclusive, done := false } 43 hload]
  simp only [show ((43 : UInt8) != 0 && !false) = true by decide, ite_true]
  simp only [G_bind_app, hbody]
  rw [gwhile.go]
  simp only [G_bind_app, modeCondition_byte _ fs { mode := .ref r off, oflag := flags, exclusive, done := true } 43 hload']
  simp [G_pure_app]

/-- C encoding of the public optional mode, before final append normalization. -/
def modeCode : Option ZlibF.Spec.Api.GzMode → Int32
  | none => GZ_NONE
  | some .read => GZ_READ
  | some .write => GZ_WRITE
  | some .append => GZ_APPEND

/-- The ghost parser's five fields are actual initialized record fields.
Untouched pointer and integer fields are deliberately absent. -/
def ModeRep (s : GzState) (acc : Acc) : Prop :=
  s.mode = modeCode acc.1 ∧ s.level.toInt = acc.2.1 ∧
  s.strategy.toInt = (acc.2.2.1 : Int) ∧ s.direct.toInt = acc.2.2.2.1 ∧ acc.2.2.2.2 = false

/-- Real allocation and the source's first field writes establish the relation. -/
theorem modeRep_initial (h : Heap) : ModeRep (openFrontRecord h) initial := by
  simp [ModeRep, openFrontRecord, initial, modeCode, Z_DEFAULT_COMPRESSION, Z_DEFAULT_STRATEGY]

/-- The source's strategy actions always fit the physical signed field. -/
theorem sourceAction_strategy_fit (b : UInt8) :
    match sourceAction b with | .strategy n => n < 2 ^ 31 | _ => True := by
  have complete : ∀ j : Fin 256,
      (match sourceAction (UInt8.ofNat j.val) with | .strategy n => decide (n < 2 ^ 31) | _ => true) = true := by
    decide +kernel
  have hb := complete ⟨b.toNat, b.toNat_lt⟩
  simp only [UInt8.ofNat_toNat] at hb
  cases he : sourceAction b <;> simp_all

/-- A nonfreeing actual source action preserves the representation relation
with the same semantic step used by the unchanged public API parser. -/
theorem modeRep_action (s : GzState) (acc : Acc) (b : UInt8)
    (hr : ModeRep s acc) (hn : sourceAction b ≠ .bad) :
    ModeRep (modeActionState s (sourceAction b))
      (semanticStep acc (semanticAction (sourceAction b))) := by
  have hfit := sourceAction_strategy_fit b
  generalize he : sourceAction b = action at *
  rcases acc with ⟨mo, lv, st, di, bad⟩
  rcases hr with ⟨hm, hl, hs, hd, hb⟩
  dsimp only at hm hl hs hd hb
  cases action with
  | level v => simp [ModeRep, semanticAction, semanticStep, modeActionState, hm, hs, hd, hb]
  | mode m =>
    cases m <;> simp [ModeRep, semanticAction, semanticStep, modeActionState, modeCode, hl, hs, hd, hb]
  | bad => contradiction
  | strategy n =>
    have hv : (Int32.ofNat n).toInt = n := Int32.toInt_ofNat_of_lt hfit
    simp [ModeRep, semanticAction, semanticStep, modeActionState, hm, hl, hd, hb, hv]
  | gzipOnly => simp [ModeRep, semanticAction, semanticStep, modeActionState, hm, hl, hs, hb]
  | transparent => simp [ModeRep, semanticAction, semanticStep, modeActionState, hm, hl, hs, hb]
  | binary | cloexec | exclusive | nonblock | ignore =>
    exact ⟨hm, hl, hs, hd, hb⟩

#print axioms modeRep_initial
#print axioms modeRep_action
#print axioms modeBody_bad
#print axioms modeWhile_bad
#print axioms openModeLoop_step_cut
#print axioms modeCondition_byte
#print axioms modeBody_normal
end Zlib.Gzlib.Proofs
