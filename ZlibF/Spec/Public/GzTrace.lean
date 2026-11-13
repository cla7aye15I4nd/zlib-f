import ZlibF.Spec.Public.Domains

namespace ZlibF.Spec.Public
open C Zlib.GzFs

/-- Input bytes supplied by the caller, independently of what the implementation accepts.
Oversized requests are rejected before their pointer is read. -/
def GzInputBytes (h : Heap) : Call → List UInt8 → Prop
  | .gzwrite _ p n, bytes => if n.toNat < 2 ^ 31 then Bytes h p n.toNat bytes else bytes = []
  | .gzfwrite p size n _, bytes =>
      if size.toNat * n.toNat < 2 ^ 64 then Bytes h p (size.toNat * n.toNat) bytes else bytes = []
  | .gzputc _ c, bytes => bytes = [c.toUInt32.toUInt8]
  | .gzputs _ p, bytes => CString h p bytes
  | .gzprintf _ p args, bytes | .gzvprintf _ p args, bytes => Formatted h p args bytes
  | _, bytes => bytes = []

def MayFillZeros : Call → Bool
  | .gzwrite _ _ _ | .gzfwrite _ _ _ _ | .gzputc _ _ | .gzputs _ _
  | .gzprintf _ _ _ | .gzvprintf _ _ _ | .gzflush _ _ | .gzsetparams _ _ _ => true
  | _ => false

/-- Record accepted bytes from observable position and pending-seek changes. This is not an
assumed write contract. The sequence goal must show that those bytes are actually encoded. -/
def writtenBy (call : Call) (before after : GzState) (input : List UInt8) : List UInt8 :=
  let zeros := if MayFillZeros call then before.skip.toInt.toNat - after.skip.toInt.toNat else 0
  List.replicate zeros 0 ++ input.take ((after.x.pos.toInt - before.x.pos.toInt).toNat - zeros)

/-- A complete writer history begins at a new handle. It includes every public gz operation,
so flushes, parameter changes, queries and forward seeks can be interleaved with writes.
The file-system state and the actual calls are fixed by the translation. -/
inductive GzWriterTrace (start : Heap) (world : Fs) (i : Nat) : Heap → Fs → List UInt8 → Prop
  | initial {s} : GzReachable start world i → start.gzstates i = some s →
      s.mode = GZ_WRITE → s.size = 0 → s.x.pos = 0 → s.skip = 0 →
      GzWriterTrace start world i start world []
  | caller {h after fs input s} : GzWriterTrace start world i h fs input →
      h.gzstates i = some s → GzCallerFrame h after i s →
      GzWriterTrace start world i after fs input
  | step {h after fs fs' input s s' call value bytes} : GzWriterTrace start world i h fs input →
      h.gzstates i = some s → GzOperation i call → GzArguments h i s call → GzInputBytes h call bytes →
      call.execute fs h = .ok ((value, fs'), after) → after.gzstates i = some s' →
      GzWriterTrace start world i after fs' (input ++ writtenBy call s s' bytes)

/-- Closing a successful writer produces exactly the accepted data and any final seek zeros.
Compression may create concatenated members; transparent writing copies bytes. Existing file
prefixes and any tail beyond an overwritten segment are retained exactly. -/
def GzWriterFormat : Prop :=
  ∀ start world i h fs input initial file node s after fs',
    GzWriterTrace start world i h fs input → RegularOs world → start.gzstates i = some initial →
    0 ≤ initial.fd.toInt → world.fds[initial.fd.toInt.toNat]? = some (some file) →
    world.nodes[file.node]? = some node → h.gzstates i = some s →
    Zlib.Gzclose.gzclose (some (.in_gzstate_x i)) fs h = .ok ((Z_OK, fs'), after) →
    ∃ encoded final,
      fs'.nodes[file.node]? = some final ∧ final.isDir = false ∧
      let offset := if file.append then node.data.size else file.pos
      let plain := input ++ List.replicate s.skip.toInt.toNat 0
      (if initial.direct ≠ 0 then encoded = plain else GzipMembers encoded plain) ∧
      final.data.toList = node.data.toList.take offset ++
        List.replicate (offset - node.data.size) 0 ++ encoded ++
        node.data.toList.drop (offset + encoded.length)

end ZlibF.Spec.Public
