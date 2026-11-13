import ZlibF.Spec.Public.GzRead

namespace ZlibF.Spec.Public
open C Zlib.GzFs

def WriteRoom (fs : Fs) (s : GzState) (n : Nat) : Prop :=
  ∃ file node, 0 ≤ s.fd.toInt ∧ fs.fds[s.fd.toInt.toNat]? = some (some file) ∧
    file.wr = true ∧ fs.nodes[file.node]? = some node ∧ node.isDir = false ∧
    max node.data.size file.pos + 2 * (n + s.strm.avail_in.toNat +
      s.skip.toInt.toNat + 2 * s.size.toNat) + 1024 ≤ fs.fsizeLimit ∧
    s.x.pos.toInt + s.skip.toInt + (n : Int) < 2 ^ 63

def WriterReady (s : GzState) : Prop :=
  s.mode = GZ_WRITE ∧ (s.err = Z_OK ∨ s.again ≠ 0) ∧
  -1 ≤ s.level.toInt ∧ s.level.toInt ≤ 9 ∧ 0 ≤ s.strategy.toInt ∧ s.strategy.toInt ≤ 4

/-- Account for accepted input separately from the reported count. A hard write error can
return zero after accepting a prefix. A pending forward seek contributes zero-filled input. -/
def WriteEffect (h after : Heap) (fs fs' : Fs) (i : Nat) (s s' : GzState)
    (input : List UInt8) (accepted : Nat) : Prop :=
  GzStateFrame h after fs fs' i s s' [] ∧ accepted ≤ input.length ∧
  ∃ zeros, zeros ≤ s.skip.toInt.toNat ∧
    s'.x.pos.toInt = s.x.pos.toInt + (zeros : Int) + (accepted : Int)

/-- `int gzwrite(gzFile file, voidpc buf, unsigned len)`.
Requests above INT_MAX return zero. A positive result counts accepted bytes. Allocation,
descriptor and size-limit failures retain the prefix already accepted by the encoder. -/
def Goal.gzwrite : Prop :=
  (∀ h fs p n, Zlib.Gzwrite.gzwrite none p n fs h = .ok ((0, fs), h)) ∧
  (∀ h fs i s p n input, GzReachable h fs i → GzValid h i s → RegularOs fs →
    (n.toNat < 2 ^ 31 → Bytes h p n.toNat input ∧ GzRange h i s p n.toNat false) →
    ∃ rc fs' after s' accepted,
      Zlib.Gzwrite.gzwrite (some (.in_gzstate_x i)) p n fs h = .ok ((rc, fs'), after) ∧
      WriteEffect h after fs fs' i s s' (if n.toNat < 2 ^ 31 then input else []) accepted ∧
      0 ≤ rc.toInt ∧ rc.toInt ≤ (accepted : Int) ∧
      (rc ≠ 0 → rc.toInt = accepted) ∧
      (2 ^ 31 ≤ n.toNat ∨ s.mode ≠ GZ_WRITE → rc = 0) ∧
      (NoAllocationFailure h → WriterReady s → WriteRoom fs s n.toNat → n.toNat < 2 ^ 31 →
        rc.toInt = n.toNat))

/-- `z_size_t gzfwrite(voidpc buf, z_size_t size, z_size_t nitems, gzFile file)`.
Return whole items. Zero-sized and overflowing products report zero without reading input. -/
def Goal.gzfwrite : Prop :=
  (∀ h fs p size n, Zlib.Gzwrite.gzfwrite p size n none fs h = .ok ((0, fs), h)) ∧
  (∀ h fs i s p size n input, GzReachable h fs i → GzValid h i s → RegularOs fs →
    (size.toNat * n.toNat < 2 ^ 64 →
      Bytes h p (size.toNat * n.toNat) input ∧ GzRange h i s p (size.toNat * n.toNat) false) →
    ∃ items fs' after s' accepted,
      Zlib.Gzwrite.gzfwrite p size n (some (.in_gzstate_x i)) fs h = .ok ((items, fs'), after) ∧
      WriteEffect h after fs fs' i s s'
        (if size.toNat * n.toNat < 2 ^ 64 then input else []) accepted ∧
      items ≤ n ∧ (items = 0 ∨ items.toNat = accepted / size.toNat) ∧
      (size = 0 ∨ 2 ^ 64 ≤ size.toNat * n.toNat ∨ s.mode ≠ GZ_WRITE → items = 0) ∧
      (NoAllocationFailure h → WriterReady s → WriteRoom fs s (size.toNat * n.toNat) →
        0 < size.toNat → size.toNat * n.toNat < 2 ^ 64 → items = n))

/-- `int gzputc(gzFile file, int c)`.
Convert to an unsigned byte. Success returns that byte even when the original integer was negative. -/
def Goal.gzputc : Prop :=
  (∀ h fs c, Zlib.Gzwrite.gzputc none c fs h = .ok ((-1, fs), h)) ∧
  (∀ h fs i s c, GzReachable h fs i → GzValid h i s → RegularOs fs →
    ∃ rc fs' after s' accepted,
      Zlib.Gzwrite.gzputc (some (.in_gzstate_x i)) c fs h = .ok ((rc, fs'), after) ∧
      WriteEffect h after fs fs' i s s' [c.toUInt32.toUInt8] accepted ∧
      (rc = -1 ∨ rc = (c &&& 255) ∧ accepted = 1) ∧
      (NoAllocationFailure h → WriterReady s → WriteRoom fs s 1 → rc = (c &&& 255)))

/-- `int gzputs(gzFile file, const char *str)`.
Write the characters before NUL. An empty string returns zero; a nonempty string that accepts
nothing returns -1, unlike `gzwrite`'s zero. -/
def Goal.gzputs : Prop :=
  (∀ h fs p, Zlib.Gzwrite.gzputs none p fs h = .ok ((-1, fs), h)) ∧
  (∀ h fs i s p input, GzReachable h fs i → GzValid h i s → RegularOs fs →
    CString h p input → GzRange h i s p (input.length + 1) false →
    ∃ rc fs' after s' accepted,
      Zlib.Gzwrite.gzputs (some (.in_gzstate_x i)) p fs h = .ok ((rc, fs'), after) ∧
      WriteEffect h after fs fs' i s s' input accepted ∧
      (rc = -1 ∨ 0 ≤ rc.toInt ∧ rc.toInt = accepted) ∧
      (2 ^ 31 ≤ input.length ∨ s.mode ≠ GZ_WRITE → rc = -1) ∧
      (NoAllocationFailure h → WriterReady s → WriteRoom fs s input.length → input.length < 2 ^ 31 →
        rc.toInt = input.length))

def FormatCaller (h : Heap) (i : Nat) (s : GzState) (format : BPtr) (args : List VaArg) : Prop :=
  (∃ bytes, CString h format bytes ∧ GzRange h i s format (bytes.length + 1) false) ∧
  ∀ p, VaArg.str p ∈ args → p = .null ∨ ∃ bytes, CString h p bytes ∧ GzRange h i s p (bytes.length + 1) false

def PrintContract (program : GzFilePtr → BPtr → List VaArg → G Int32) : Prop :=
  (∀ h fs format args, program none format args fs h = .ok ((Z_STREAM_ERROR, fs), h)) ∧
  (∀ h fs i s format args text, GzReachable h fs i → GzValid h i s → RegularOs fs →
    Formatted h format args text → FormatCaller h i s format args →
    ∃ rc fs' after s' accepted,
      program (some (.in_gzstate_x i)) format args fs h = .ok ((rc, fs'), after) ∧
      WriteEffect h after fs fs' i s s' text accepted ∧
      (0 < rc.toInt → rc.toInt = text.length ∧ accepted = text.length) ∧
      (s.mode ≠ GZ_WRITE → rc = Z_STREAM_ERROR) ∧
      (NoAllocationFailure h → WriterReady s → WriteRoom fs s text.length →
        fs.printfOk fs.nprintf = true → text.length ≤ 2147483647 →
        rc.toInt = if text.length < (if s.size = 0 then s.want.toNat else s.size.toNat) then text.length else 0) ∧
      (NoAllocationFailure h → WriterReady s → WriteRoom fs s text.length →
        (fs.printfOk fs.nprintf = false ∨ 2147483647 < text.length) → rc = 0 ∧ accepted = 0))

/-- `int gzvprintf(gzFile file, const char *format, va_list va)`.
The fixed external formatter supplies the formatted bytes. Wrong mode and serious errors
return a negative zlib code; an empty or oversized formatted result returns zero. The C
library may fail on any call (the world oracle `printfOk`; a length past `INT_MAX`): then
`len = -1`, `(unsigned)len >= state->size`, and the call returns zero having accepted
nothing. Safety (the run returns, the state stays valid, the frame) holds on both branches. -/
def Goal.gzvprintf : Prop := PrintContract Zlib.Gzwrite.gzvprintf

/-- `int gzprintf(gzFile file, const char *format, ...)`.
The variadic wrapper uses the same typed argument sequence and error/result contract. -/
def Goal.gzprintf : Prop := PrintContract Zlib.Gzwrite.gzprintf

/-- `int gzflush(gzFile file, int flush)`.
Finish pending zeros and flush the encoder. Invalid modes and flush values return a stream
error. Z_FINISH completes a gzip member; later writes can start another member. -/
def Goal.gzflush : Prop :=
  (∀ h fs flush, Zlib.Gzwrite.gzflush none flush fs h = .ok ((Z_STREAM_ERROR, fs), h)) ∧
  (∀ h fs i s flush, GzReachable h fs i → GzValid h i s → RegularOs fs →
    ∃ rc fs' after s',
      Zlib.Gzwrite.gzflush (some (.in_gzstate_x i)) flush fs h = .ok ((rc, fs'), after) ∧
      GzStateFrame h after fs fs' i s s' [] ∧
      (s.mode ≠ GZ_WRITE ∨ flush.toInt < 0 ∨ 4 < flush.toInt → rc = Z_STREAM_ERROR) ∧
      (s.mode = GZ_WRITE → s.err = Z_OK ∨ s.again ≠ 0 →
        0 ≤ flush.toInt → flush.toInt ≤ 4 → rc = s'.err) ∧
      (NoAllocationFailure h → WriterReady s → WriteRoom fs s 0 →
        0 ≤ flush.toInt → flush.toInt ≤ 4 → rc = Z_OK ∧ s'.skip = 0))

/-- `int gzsetparams(gzFile file, int level, int strategy)`.
Only a compressed writer can change parameters. Preserve previously buffered input while
flushing the old settings. The header does not promise rejection of invalid level/strategy
values. The current entry stores those values even if the inner parameter change refuses them;
do not invent a Z_STREAM_ERROR guarantee for that case. -/
def Goal.gzsetparams : Prop :=
  (∀ h fs level strategy, Zlib.Gzwrite.gzsetparams none level strategy fs h = .ok ((Z_STREAM_ERROR, fs), h)) ∧
  (∀ h fs i s level strategy, GzReachable h fs i → GzValid h i s → RegularOs fs →
    ∃ rc fs' after s',
      Zlib.Gzwrite.gzsetparams (some (.in_gzstate_x i)) level strategy fs h = .ok ((rc, fs'), after) ∧
      GzStateFrame h after fs fs' i s s' [] ∧
      (rc = Z_OK ∨ rc = Z_STREAM_ERROR ∨ rc = Z_ERRNO ∨ rc = Z_MEM_ERROR ∨ rc = Z_BUF_ERROR) ∧
      (s.mode ≠ GZ_WRITE ∨ s.direct ≠ 0 ∨ (s.err ≠ Z_OK ∧ s.again = 0) →
        rc = Z_STREAM_ERROR ∧ after = h ∧ fs' = fs) ∧
      (rc = Z_OK → s'.level = level ∧ s'.strategy = strategy) ∧
      (rc = Z_OK → s.size ≠ 0 → -1 ≤ level.toInt → level.toInt ≤ 9 →
        0 ≤ strategy.toInt → strategy.toInt ≤ 4 →
        ∃ state inner, s'.strm.state = some (.deflate state) ∧ after.dstates state = some inner ∧
          inner.level = (if level = -1 then 6 else level) ∧ inner.strategy = strategy) ∧
      (NoAllocationFailure h → WriterReady s → s.direct = 0 → WriteRoom fs s 0 →
        -1 ≤ level.toInt → level.toInt ≤ 9 → 0 ≤ strategy.toInt → strategy.toInt ≤ 4 → rc = Z_OK))

end ZlibF.Spec.Public
