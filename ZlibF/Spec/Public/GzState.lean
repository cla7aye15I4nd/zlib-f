import ZlibF.Spec.Public.Copy
import ZlibF.Proof.«gzlib.c.base»
import ZlibF.Spec.Api.Gz

namespace ZlibF.Spec.Public
open C Zlib.GzFs ZlibF.Spec

def FileSystem (fs : Fs) : Prop :=
  fs.fds.size < 2 ^ 31 - 1 ∧ fs.fsizeLimit ≤ 2 ^ 63 - 1 ∧
  (∀ path node, (path, node) ∈ fs.names.toList → node < fs.nodes.size) ∧
  (∀ (i : Nat) (file : OFile), fs.fds[i]? = some (some file) → file.node < fs.nodes.size ∧
    file.pos ≤ 2 ^ 63 - 1 ∧ (∀ node : Node, fs.nodes[file.node]? = some node → node.isDir = true → file.wr = false)) ∧
  (∀ (i : Nat) (node : Node), fs.nodes[i]? = some node → node.data.size ≤ 2 ^ 63 - 1)

def GzOwned (h : Heap) (i : Nat) (s : GzState) (b : Nat) : Prop :=
  b = i ∨ s.path = .ref (.blk b) 0 ∨ s.msg = .ref (.blk b) 0 ∨
  (s.size ≠ 0 ∧ (s.in = .ref (.blk b) 0 ∨
    ((s.mode = GZ_READ ∨ s.direct = 0) ∧
      (s.out = .ref (.blk b) 0 ∨ StreamOwned h (.in_gzstate_strm i) b))))

def MallocBuffer (h : Heap) (p : BPtr) (n : Nat) : Prop :=
  ∃ b a, p = .ref (.blk b) 0 ∧ h.bytes b = some a ∧ h.ro b = false ∧ n ≤ a.size

/-- Buffer fields may dangle after a failed lazy allocation. They are inactive when size is
zero and must be overwritten before reuse. Nonempty cached output must remain privately owned. -/
def GzValid (h : Heap) (i : Nat) (s : GzState) : Prop :=
  h.gzstates i = some s ∧ (s.mode = GZ_READ ∨ s.mode = GZ_WRITE) ∧
  Fresh h ∧ Zlib.Gzlib.Spec.Uniq h ∧ LibraryGlobals h ∧
  (∃ path, CString h s.path path ∧ MallocBuffer h s.path (path.length + 1)) ∧
  (s.msg = .null ∨ ∃ message, CString h s.msg message ∧ MallocBuffer h s.msg (message.length + 1)) ∧
  (s.err = Z_MEM_ERROR → s.msg = .null) ∧ 8 ≤ s.want.toNat ∧ s.want.toNat < 2 ^ 31 ∧
  (s.size ≠ 0 → s.size = s.want ∧
    MallocBuffer h s.in (if s.mode = GZ_READ then s.size.toNat else 2 * s.size.toNat) ∧
    (s.mode = GZ_READ ∨ s.direct = 0 →
      MallocBuffer h s.out (if s.mode = GZ_READ then 2 * s.size.toNat else s.size.toNat))) ∧
  (s.x.have ≠ 0 → (∃ xs, Bytes h s.x.next s.x.have.toNat xs) ∧
    ∀ b, ByteRoot s.x.next b → GzOwned h i s b)

def GzRange (h : Heap) (i : Nat) (s : GzState) (p : BPtr) (n : Nat) (write : Bool) : Prop :=
  n = 0 ∨ ((∃ xs, Bytes h p n xs) ∧ (write = true → Writable h p n) ∧
    ∀ b, ByteRoot p b → ¬ GzOwned h i s b)

def Formatted (h : Heap) (format : BPtr) (args : List VaArg) (xs : List UInt8) : Prop :=
  ∃ fmt, CString h format fmt ∧
    Zlib.GzFs.formatGo fmt.toArray (Zlib.GzFs.heapStr h) (fmt.length + 1) 0 args #[] = .ok xs.toArray

def GzOperation (i : Nat) : Call → Prop
  | .gzbuffer p _ | .gzclearerr p | .gzdirect p | .gzeof p | .gzerror p _
  | .gzflush p _ | .gzgetc p | .gzgetc_ p | .gzgets p _ _ | .gzoffset p | .gzoffset64 p
  | .gzprintf p _ _ | .gzputc p _ | .gzputs p _ | .gzread p _ _ | .gzrewind p
  | .gzseek p _ _ | .gzseek64 p _ _ | .gzsetparams p _ _ | .gztell p | .gztell64 p
  | .gzvprintf p _ _ | .gzwrite p _ _ | .gzungetc _ p | .gzfread _ _ _ p | .gzfwrite _ _ _ p =>
      p = some (.in_gzstate_x i)
  | _ => False

def GzArguments (h : Heap) (i : Nat) (s : GzState) : Call → Prop
  | .gzread _ p n =>
      if n.toNat ≥ 2 ^ 31 then True else GzRange h i s p n.toNat true
  | .gzwrite _ p n =>
      if n.toNat ≥ 2 ^ 31 then True else GzRange h i s p n.toNat false
  | .gzfread p size n _ =>
      if size.toNat * n.toNat ≥ 2 ^ 64 then True else GzRange h i s p (size.toNat * n.toNat) true
  | .gzfwrite p size n _ =>
      if size.toNat * n.toNat ≥ 2 ^ 64 then True else GzRange h i s p (size.toNat * n.toNat) false
  | .gzgets _ p n => if n.toInt < 1 ∨ p = .null then True else GzRange h i s p n.toInt.toNat true
  | .gzputs _ p => ∃ xs, CString h p xs ∧ GzRange h i s p (xs.length + 1) false
  | .gzprintf _ p args | .gzvprintf _ p args => ∃ xs, Formatted h p args xs
  | .gzerror _ p => p = .null ∨ GzRange h i s p 4 true
  | _ => True

def GzCallerFrame (h after : Heap) (i : Nat) (s : GzState) : Prop :=
  Fresh after ∧ Zlib.Gzlib.Spec.Uniq after ∧ LibraryGlobals after ∧
  Frame h after (fun b => ¬ GzOwned h i s b)

/-- Actual public histories. No earlier library contract is an assumption.
Appending input after EOF is admitted explicitly, as required by `gzclearerr`. -/
inductive GzReachable : Heap → Fs → Nat → Prop
  | open {h after fs fs' path mode i name flags} :
      Fresh h → Zlib.Gzlib.Spec.Uniq h → LibraryGlobals h → FileSystem fs →
      CString h path name → CString h mode flags →
      Zlib.Gzlib.gzopen path mode fs h = .ok ((some (.in_gzstate_x i), fs'), after) →
      GzReachable after fs' i
  | dopen {h after fs fs' fd mode i flags} :
      Fresh h → Zlib.Gzlib.Spec.Uniq h → LibraryGlobals h → FileSystem fs →
      CString h mode flags →
      Zlib.Gzlib.gzdopen fd mode fs h = .ok ((some (.in_gzstate_x i), fs'), after) →
      GzReachable after fs' i
  | step {h after fs fs' i s call value} : GzReachable h fs i → h.gzstates i = some s →
      GzOperation i call → GzArguments h i s call →
      call.execute fs h = .ok ((value, fs'), after) → GzReachable after fs' i
  | caller {h after fs i s} : GzReachable h fs i → h.gzstates i = some s →
      GzCallerFrame h after i s → GzReachable after fs i
  | append {h fs fs' i s file old new extra} : GzReachable h fs i →
      h.gzstates i = some s → s.mode = GZ_READ →
      fs.fds[s.fd.toInt.toNat]? = some (some file) →
      fs.nodes[file.node]? = some old → new = { old with data := old.data ++ extra } →
      fs' = { fs with nodes := fs.nodes.set! file.node new } → FileSystem fs' →
      GzReachable h fs' i

def GzStateFrame (before after : Heap) (fs fs' : Fs) (i : Nat) (s s' : GzState)
    (regions : List Region) : Prop :=
  GzValid after i s' ∧ s'.mode = s.mode ∧ s'.fd = s.fd ∧ s'.path = s.path ∧
  FileSystem fs' ∧ fs'.names = fs.names ∧ fs'.fsizeLimit = fs.fsizeLimit ∧
  fs'.fds.size = fs.fds.size ∧ fs'.nodes.size = fs.nodes.size ∧
  (∀ j, j ≠ s.fd.toInt.toNat → fs'.fds[j]? = fs.fds[j]?) ∧
  (∀ file j, fs.fds[s.fd.toInt.toNat]? = some (some file) → j ≠ file.node →
    fs'.nodes[j]? = fs.nodes[j]?) ∧
  BufferFrame before after (GzOwned before i s) regions ∧
  LiveChange before after
    (fun b => GzOwned after i s' b ∧ ¬ before.live b)
    (fun b => GzOwned before i s b ∧ ¬ GzOwned after i s' b)

def gzipMagic (xs : List UInt8) : Prop := xs.take 2 = [31, 139]

inductive GzipMembers : List UInt8 → List UInt8 → Prop
  | empty : GzipMembers [] []
  | member {compressed decoded rest output} : Gzip.Decodes compressed decoded →
      GzipMembers rest output → GzipMembers (compressed ++ rest) (decoded ++ output)

/-- Normal transparent input, or gzip members with an optional non-gzip tail.
Two magic bytes select gzip; a bad method or flags are not transparent input. -/
def GzData (s : GzState) (raw decoded : List UInt8) : Prop :=
  (s.direct = 1 ∧ ¬ gzipMagic raw ∧ decoded = raw) ∨
  ∃ members tail, members ≠ [] ∧ raw = members ++ tail ∧ ¬ gzipMagic tail ∧ GzipMembers members decoded

def FileData (fs : Fs) (s : GzState) (decoded : List UInt8) : Prop :=
  ∃ file node, 0 ≤ s.fd.toInt ∧ fs.fds[s.fd.toInt.toNat]? = some (some file) ∧
    file.rd = true ∧ fs.nodes[file.node]? = some node ∧ node.isDir = false ∧
    GzData s (node.data.toList.drop s.start.toInt.toNat) decoded

def Buffered (h : Heap) (s : GzState) (bytes : List UInt8) : Prop :=
  if s.x.have = 0 then bytes = [] else Bytes h s.x.next s.x.have.toNat bytes

def availableRead (s : GzState) (buffered decoded : List UInt8) : List UInt8 :=
  (buffered ++ (if s.eof ≠ 0 ∧ s.strm.avail_in = 0 then [] else
    decoded.drop (s.x.pos.toInt + (buffered.length : Int)).toNat)).drop s.skip.toInt.toNat

def NoAllocationFailure (h : Heap) : Prop := ∀ n, h.allocOk n = true

end ZlibF.Spec.Public
