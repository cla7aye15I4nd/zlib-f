import ZlibF.Proof.«deflate.c.engine.fill-source»
import ZlibF.Proof.«deflate.c.engine.insert-chains»

/-! # The first fill_window call

The execution boundary allows every good status. Header output may have
changed INIT_STATE to BUSY_STATE before the strategy reaches this call.
-/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
set_option autoImplicit false

theorem EngineStart.window_size {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (start : EngineStart h r ds z d) : d.window_size = 65536 := by
  apply UInt64.toNat_inj.mp
  rw [start.good.inv.wsz, start.good.inv.wsize, start.windowBits]
  rfl

theorem EngineStart.w_size {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (start : EngineStart h r ds z d) : d.w_size = 32768 := by
  apply UInt32.toNat_inj.mp
  rw [start.good.inv.wsize, start.windowBits]
  rfl

theorem do_once {α : Type} {body : α → M α} {cond : α → M (Bool × α)}
    {h g j : Heap} {a b c : α} (hb : body a h = .ok (b, g))
    (hc : cond b g = .ok ((false, c), j)) : cdoWhile body cond a h = .ok (c, j) := by
  unfold cdoWhile
  change cdoWhile.go body cond (18446744073709551615 + 1) a h = _
  rw [cdoWhile.go, bind_app, hb]
  simp only []
  rw [bind_app, hc]
  rfl

/-- The no-input branch of the first fill executes one outer iteration.
The status is unrestricted within DGood. -/
theorem fill_body_empty {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (good : DGood h r ds z d) (ss : d.strstart = 0) (la : d.lookahead = 0)
    (ws : d.w_size = 32768) (wsz : d.window_size = 65536) (input : z.avail_in = 0) :
    fillBody (some (.tab ds)) 32768 false h = .ok (true, h) := by
  simp [fillBody, bind_app, ldDeflateState_tab good.live.hs, rdD_eq, good.live.hs,
    good.live.back, zrd_eq, good.live.hz, ss, la, ws, wsz, input, MIN_LOOKAHEAD_u]

theorem fill_cond_break (s : DeflateStatePtr) (h : Heap) :
    fillCond s true h = .ok ((false, true), h) := rfl

/-- High-water padding after an empty first fill. The write initializes
exactly the first 258 window bytes and leaves their allocation size intact. -/
theorem fill_high_water_empty {h : Heap} {ds w : Nat} {d : DeflateState} {wa : Array UInt8}
    (state : h.dstates ds = some d) (win : d.window = .ref (.blk w) 0)
    (get : h.bytes w = some wa) (writable : h.ro w = false) (size : wa.size = 65536)
    (ss : d.strstart = 0) (la : d.lookahead = 0) (hw : d.high_water = 0)
    (wsz : d.window_size = 65536) :
    fillHighWater (some (.tab ds)) h = .ok ((),
      setD { h with bytes := upd h.bytes w (some (fillRange wa 0 258 0)) }
        ds { d with high_water := 258 }) := by
  have add : padd (.ref (.blk w) 0 : BPtr) 0 h = .ok (.ref (.blk w) 0, h) := by
    simpa only [OkOn, padd, Nat.zero_add] using Ptr.add_nat_ok
      (show Space.get h (BRef.blk w) = some wa from get) (by omega : 0 + 0 ≤ wa.size)
  have fill : memsetB (.ref (.blk w) 0) 0 258 h =
      .ok ((), { h with bytes := upd h.bytes w (some (fillRange wa 0 258 0)) }) := by
    exact Ptr.fill_ok get writable (by omega)
  simp [fillHighWater, bind_app, ldDeflateState_tab state, ss, la, hw, wsz, win,
    WIN_INIT_u, add, fill, wrD_eq, state, setD]

/-- `local void fill_window(deflate_state *s)`.
The complete first call with no input terminates after one iteration,
initializes the lookahead padding and preserves representation and H.
It covers the no-input branch; the positive-input branch is separate. -/
theorem fill_window_empty_initial {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState}
    (good : DGood h r ds z d) (chains : HeapChains h d 0)
    (ss : d.strstart = 0) (la : d.lookahead = 0) (hw : d.high_water = 0)
    (ws : d.w_size = 32768) (wsz : d.window_size = 65536) (input : z.avail_in = 0) :
    ∃ after, fill_window (some (.tab ds)) h = .ok ((), after) ∧
      DGood after r ds z { d with high_water := 258 } ∧
      HeapChains after { d with high_water := 258 } 0 := by
  obtain ⟨w, p, q, b, blocks⟩ := good.inv.blocks
  obtain ⟨wa, get, size⟩ := blocks.wa
  have size' : wa.size = 65536 := by simpa [ws] using size
  let a := fillRange wa 0 258 0
  let hb := { h with bytes := upd h.bytes w (some a) }
  let after := setD hb ds { d with high_water := 258 }
  have bytesGood : DGood hb r ds z d := good.bytes_set w a wa get (size_fillRange _ _ _ _)
  have inv : DStInv hb ds { d with high_water := 258 } :=
    { bytesGood.inv with
      hw := by change (258 : UInt64).toNat ≤ d.window_size.toNat; rw [wsz]; decide
      blocks := bytesGood.inv.blocks_keys rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl }
  have kept := bytesGood.setD' (d' := { d with high_water := 258 }) rfl good.live.status inv (by trkeep)
  refine ⟨after, ?_, kept, ?_⟩
  · have loop := do_once (fill_body_empty good ss la ws wsz input)
      (fill_cond_break (some (.tab ds)) h)
    rw [fill_window_source]
    simp only [bind_app, rdD_eq, good.live.hs]
    rw [ws]
    simp only [bind_app, loop]
    exact fill_high_water_empty good.live.hs blocks.win get blocks.wro size' ss la hw wsz
  · have H := heap_chains_window_write chains blocks.win get (wa' := a) (by
      intro i hi
      simp [ss, la] at hi)
    simpa only [HeapChains, after, hb, setD] using H

end Zlib.Deflate.Engine.Proofs
