import ZlibF.Proof.«deflate.c.engine.public-dispatch»

/-! # The completed default header retains the initialized content boundary -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

def headerCompleteState (d : DeflateState) : DeflateState :=
  { d with status := BUSY_STATE, last_flush := Z_NO_FLUSH }

def headerCompleteStream (z : ZStream) (ob oo : Nat) : ZStream :=
  pendingStream z (.ref (.blk ob) (oo + 2)) 2

def headerCompleteBytes (h : Heap) (pb ob oo : Nat) (buf output : Array UInt8) : Heap :=
  let contents := upd (upd h.bytes pb (some (zlibHeaderBytes buf))) ob
    (some (copyRange output (zlibHeaderBytes buf) oo 0 2))
  { h with bytes := contents }

def headerCompleteHeap (h : Heap) (r : ZStreamRef) (ds pb ob oo : Nat)
    (z : ZStream) (d : DeflateState) (buf output : Array UInt8) : Heap :=
  setD (r.put (headerCompleteBytes h pb ob oo buf output) (headerCompleteStream z ob oo)) ds
    (headerCompleteState d)

theorem header_complete_good {h : Heap} {r : ZStreamRef} {ds pb ob oo : Nat}
    {z : ZStream} {d : DeflateState} {buf output : Array UInt8}
    (good : DGood h r ds z d) (get : h.bytes pb = some buf) (outGet : h.bytes ob = some output)
    (separate : ob ≠ pb) :
    DGood (headerCompleteHeap h r ds pb ob oo z d buf output) r ds
      (headerCompleteStream z ob oo) (headerCompleteState d) := by
  have first := good.bytes_set pb (zlibHeaderBytes buf) buf get (by simp [zlibHeaderBytes])
  have second := first.bytes_set ob (copyRange output (zlibHeaderBytes buf) oo 0 2) output
    (by simpa only [upd_ne _ _ _ _ separate] using outGet) (size_copyRange _ _ _ _ _)
  have inv : DStInv (headerCompleteBytes h pb ob oo buf output) ds (headerCompleteState d) :=
    { second.inv with blocks := second.inv.blocks_keys rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl }
  exact second.setZD (z' := headerCompleteStream z ob oo) (d' := headerCompleteState d) rfl good.live.zalloc good.live.zfree rfl
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))) inv (by trkeep)

theorem header_complete_window {h : Heap} {r : ZStreamRef} {ds pb ob oo w : Nat}
    {z : ZStream} {d : DeflateState} {buf output wa : Array UInt8}
    (good : DGood h r ds z d) (pending : d.pending_buf = .ref (.blk pb) 0)
    (window : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa)
    (outside : ¬ DeflateOwned ds d ob) :
    (headerCompleteHeap h r ds pb ob oo z d buf output).bytes w = some wa := by
  obtain ⟨w0, p, q, b0, blocks⟩ := good.inv.blocks
  have wid : w0 = w := by simpa only [window, Ptr.ref.injEq, BRef.blk.injEq, and_true] using blocks.win.symm
  have bid : b0 = pb := by simpa only [pending, Ptr.ref.injEq, BRef.blk.injEq, and_true] using blocks.pbuf.symm
  subst w0 b0
  have outWindow : w ≠ ob := by
    intro same
    subst w
    exact outside (Or.inr (Or.inl window))
  simpa only [headerCompleteHeap, setD_bytes, ZStreamRef.put_bytes, headerCompleteBytes,
    upd_ne _ _ _ _ outWindow, upd_ne _ _ _ _ blocks.wb] using get

theorem header_complete_chains {h : Heap} {r : ZStreamRef} {ds pb ob oo top : Nat}
    {z : ZStream} {d : DeflateState} {buf output : Array UInt8}
    (good : DGood h r ds z d) (pending : d.pending_buf = .ref (.blk pb) 0)
    (chains : HeapChains h d top) (outside : ¬ DeflateOwned ds d ob) :
    HeapChains (headerCompleteHeap h r ds pb ob oo z d buf output) (headerCompleteState d) top := by
  obtain ⟨w, p, q, wa, pa, qa, win, prev, head, hw, hp, hq, H⟩ := chains
  refine ⟨w, p, q, wa, pa, qa, win, prev, head,
    header_complete_window good pending win hw outside, ?_, ?_, H⟩
  · simpa only [headerCompleteHeap, setD_words, ZStreamRef.put_words, headerCompleteBytes] using hp
  · simpa only [headerCompleteHeap, setD_words, ZStreamRef.put_words, headerCompleteBytes] using hq

/-- Empty packed content survives the real header's two pending writes
and the caller copy. The hash frontiers and logical window are unchanged.
The output object is outside the initialized private ownership graph. -/
theorem header_complete_content {h : Heap} {r : ZStreamRef} {ds pb ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {buf output : Array UInt8} {input : Nat → UInt8}
    (boundary : ContentBoundary h r ds z d input origin base [])
    (pending : d.pending_buf = .ref (.blk pb) 0) (get : h.bytes pb = some buf)
    (outGet : h.bytes ob = some output) (outside : ¬ DeflateOwned ds d ob) :
    ContentBoundary (headerCompleteHeap h r ds pb ob oo z d buf output) r ds
      (headerCompleteStream z ob oo) (headerCompleteState d) input origin base [] := by
  have separate : ob ≠ pb := by
    intro same
    subst ob
    exact outside (Or.inr (Or.inr (Or.inr (Or.inr pending))))
  have good := header_complete_good (oo := oo) boundary.good get outGet separate
  obtain ⟨b, old, trees, ledger, balance⟩ := boundary.symbols
  have bid : b = pb := by simpa only [pending, Ptr.ref.injEq, BRef.blk.injEq, and_true] using trees.base.pbuf.symm
  subst b
  have getA : (headerCompleteHeap h r ds pb ob oo z d buf output).bytes pb = some (zlibHeaderBytes buf) := by
    simp [headerCompleteHeap, headerCompleteBytes, upd_ne _ _ _ _ (Ne.symm separate)]
  have ledgerA : SymbolLedger (zlibHeaderBytes buf) (headerCompleteState d) [] := by
    refine ⟨ledger.count, ledger.valid, ?_, ledger.literal, ledger.distance⟩
    intro i s selected
    simp at selected
  have symbols : SymbolBoundary (headerCompleteHeap h r ds pb ob oo z d buf output) ds (headerCompleteState d) [] :=
    symbol_boundary_of_ledger good pending getA ledgerA balance
  obtain ⟨w, wa, win, hw, view, form⟩ := boundary.data
  refine { boundary with
    good := good
    chains := header_complete_chains boundary.good pending boundary.chains outside
    symbols := symbols
    frontier := header_complete_chains boundary.good pending boundary.frontier outside
    data := ⟨w, wa, win, header_complete_window boundary.good pending win hw outside, view, form⟩ }

end Zlib.Deflate.Engine.Proofs
