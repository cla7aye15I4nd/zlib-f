import ZlibF.Spec.Public.Back

namespace ZlibF.Spec.Public
open C Zlib.GzFs

/-- Caller storage before init. No library invariant or callee contract is supplied. -/
def InitDomain (h : Heap) (r : ZStreamRef) (version : BPtr) : Prop :=
  Fresh h ∧ Zlib.Inflate.Spec.Uniq h ∧ LibraryGlobals h ∧
  VersionValue h version (some 49) ∧
  ∃ z, r.get h = some z ∧ DefaultOrNull z ∧ z.state = none

/-- Fixed caller storage for top-level non-emptiness obligations. The window remains caller-owned. -/
def witnessHeap : Heap :=
  { Heap.empty with
    streams := upd Heap.empty.streams 0 (some default)
    bytes := upd (upd Heap.empty.bytes 1 (some #[49, 0])) 2
      (some (Array.replicate 32768 0))
    nextBlk := 3
    static := Zlib.Crc32.initStatics
      (Zlib.Inftrees.initStatics (Zlib.Trees.trees_statics Heap.empty.static)) }

/-- Every accepted signed window parameter has a non-failing init on every permitted heap.
The fixed witness additionally rules out an empty caller domain. -/
def Goal.inflate_initialisation_domain : Prop :=
  (∀ h r version wb wrap bits,
    InitDomain h r version → Api.inflWbits wb.toInt = some (wrap, bits) →
    h.allocOk h.nalloc = true →
    ∃ after, C.run (Zlib.Inflate.inflateInit2_ (some r) wb version 112) h = .ok (Z_OK, after) ∧
      InflateInitial h after r wrap bits ∧ StreamReachable .inflate after r) ∧
  InitDomain witnessHeap (.tab 0) (.ref (.blk 1) 0) ∧
  (∀ wb wrap bits, Api.inflWbits wb.toInt = some (wrap, bits) →
    ∃ after, C.run (Zlib.Inflate.inflateInit2_ (some (.tab 0)) wb (.ref (.blk 1) 0) 112)
      witnessHeap = .ok (Z_OK, after) ∧ InflateInitial witnessHeap after (.tab 0) wrap bits)

/-- Full level, method, window, memory-level and strategy coverage, including normalisation.
No assumption that the post-init invariant already holds is permitted. -/
def Goal.deflate_initialisation_domain : Prop :=
  (∀ h r version level method wb mem strategy p,
    InitDomain h r version →
    Api.deflInit? level.toInt method.toInt wb.toInt mem.toInt strategy.toInt = some p →
    (∀ j, j < 5 → h.allocOk (h.nalloc + j) = true) →
    ∃ after, C.run (Zlib.Deflate.deflateInit2_ (some r) level method wb mem strategy version 112) h =
      .ok (Z_OK, after) ∧ DeflateInitial h after r p ∧ StreamReachable .deflate after r) ∧
  InitDomain witnessHeap (.tab 0) (.ref (.blk 1) 0) ∧
  (∀ level method wb mem strategy p,
    Api.deflInit? level.toInt method.toInt wb.toInt mem.toInt strategy.toInt = some p →
    ∃ after, C.run (Zlib.Deflate.deflateInit2_ (some (.tab 0)) level method wb mem strategy
      (.ref (.blk 1) 0) 112) witnessHeap = .ok (Z_OK, after) ∧
      DeflateInitial witnessHeap after (.tab 0) p)

/-- All eight documented callback-window sizes, with an arbitrary valid caller window.
Init establishes the back-decoder invariant and retains ownership of the window. -/
def Goal.inflate_back_initialisation_domain : Prop :=
  (∀ h r version wb window,
    InitDomain h r version → 8 ≤ wb.toInt → wb.toInt ≤ 15 →
    window ≠ .null → Writable h window (2 ^ wb.toInt.toNat) → h.allocOk h.nalloc = true →
    ∃ after z s, C.run (Zlib.Infback.inflateBackInit_ (some r) wb window version 112) h =
      .ok (Z_OK, after) ∧ BackValid after r h.nextBlk z s ∧ s.window = window ∧
      s.wbits = wb.toUInt32 ∧ Frame h after (StreamRoot r) ∧
      LiveChange h after (fun b => b = h.nextBlk) (fun _ => False)) ∧
  InitDomain witnessHeap (.tab 0) (.ref (.blk 1) 0) ∧
  (∀ wb : Int32, 8 ≤ wb.toInt → wb.toInt ≤ 15 →
    ∃ after z s, C.run (Zlib.Infback.inflateBackInit_ (some (.tab 0)) wb (.ref (.blk 2) 0)
      (.ref (.blk 1) 0) 112) witnessHeap = .ok (Z_OK, after) ∧
      BackValid after (.tab 0) witnessHeap.nextBlk z s ∧ s.window = .ref (.blk 2) 0)

def gzWitnessHeap (mode : List UInt8) : Heap :=
  { witnessHeap with
    bytes := upd (upd witnessHeap.bytes 3 (some #[120, 0])) 4 (some (mode ++ [0]).toArray)
    nextBlk := 5 }

def gzWitnessFs (mode : Api.GzMode) : Fs :=
  if mode = .read then Fs.put default #[120] #[] else default

/-- External open success is specified by the fixed file-system semantics. No gz contract
is an assumption. Every accepted mode has a successful concrete open witness. -/
def Goal.gz_initialisation_domain : Prop :=
  (∀ h fs path mode name flags kind level strategy direct fd world start,
    Fresh h → Zlib.Gzlib.Spec.Uniq h → LibraryGlobals h → FileSystem fs →
    NoAllocationFailure h → CString h path name → CString h mode flags →
    parsedMode flags = some (kind, level, strategy, direct) →
    OpenWorld h fs world name flags kind none fd start → fd ≠ -1 →
    ∃ after fs' i s, Zlib.Gzlib.gzopen path mode fs h = .ok ((some (.in_gzstate_x i), fs'), after) ∧
      OpenState after i s kind level strategy direct fd name ∧ GzReachable after fs' i ∧
      Frame h after (fun _ => False) ∧ LiveChange h after (GzOwned after i s) (fun _ => False)) ∧
  (∀ flags kind level strategy direct, 0 ∉ flags →
    parsedMode flags = some (kind, level, strategy, direct) →
    ∃ after fs' i s,
      Zlib.Gzlib.gzopen (.ref (.blk 3) 0) (.ref (.blk 4) 0) (gzWitnessFs kind) (gzWitnessHeap flags) =
        .ok ((some (.in_gzstate_x i), fs'), after) ∧
      OpenState after i s kind level strategy direct s.fd [120] ∧ GzReachable after fs' i)

end ZlibF.Spec.Public
