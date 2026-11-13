import ZlibF.Spec.Public.GzWrite

namespace ZlibF.Spec.Public
open C Zlib.GzFs

def DescriptorPresent (fs : Fs) (fd : Int32) : Prop :=
  0 ≤ fd.toInt ∧ ∃ file, fs.fds[fd.toInt.toNat]? = some (some file)

def CloseEffects (h after : Heap) (fs fs' : Fs) (i : Nat) (s : GzState) : Prop :=
  after.gzstates i = none ∧ Frame h after (GzOwned h i s) ∧
  LiveChange h after (fun _ => False) (GzOwned h i s) ∧
  FileSystem fs' ∧ fs'.names = fs.names ∧ fs'.fsizeLimit = fs.fsizeLimit ∧
  fs'.fds.size = fs.fds.size ∧ fs'.nodes.size = fs.nodes.size ∧
  (∀ j, j ≠ s.fd.toInt.toNat → fs'.fds[j]? = fs.fds[j]?) ∧
  (DescriptorPresent fs s.fd → fs'.fds[s.fd.toInt.toNat]? = some none) ∧
  (¬ DescriptorPresent fs s.fd → fs'.fds = fs.fds) ∧
  (∀ file j, fs.fds[s.fd.toInt.toNat]? = some (some file) → j ≠ file.node →
    fs'.nodes[j]? = fs.nodes[j]?) ∧
  (s.mode = GZ_READ → fs'.nodes = fs.nodes)

def CloseContract (program : GzFilePtr → G Int32) (mode : Option Int32) : Prop :=
  (∀ h fs, program none fs h = .ok ((Z_STREAM_ERROR, fs), h)) ∧
  (∀ h fs i s, GzReachable h fs i → GzValid h i s → RegularOs fs →
    ∃ rc fs' after, program (some (.in_gzstate_x i)) fs h = .ok ((rc, fs'), after) ∧
      (if ∃ expected, mode = some expected ∧ expected ≠ s.mode then
        rc = Z_STREAM_ERROR ∧ after = h ∧ fs' = fs
       else CloseEffects h after fs fs' i s ∧
        (¬ DescriptorPresent fs s.fd → rc = Z_ERRNO) ∧
        (DescriptorPresent fs s.fd → s.mode = GZ_READ → rc = if s.err = Z_BUF_ERROR then Z_BUF_ERROR else Z_OK) ∧
        (NoAllocationFailure h → WriterReady s → WriteRoom fs s 0 → rc = Z_OK)))

/-- `int gzclose_r(gzFile file)`.
Reject a writer without closing it. A reader releases every owned allocation and closes its
descriptor, reporting a truncated-member buffer error unless close itself fails. -/
def Goal.gzclose_r : Prop := CloseContract Zlib.Gzread.gzclose_r (some GZ_READ)

/-- `int gzclose_w(gzFile file)`.
Reject a reader without closing it. Complete pending zeros and the final member, then release
all storage and close the descriptor, including every error path. -/
def Goal.gzclose_w : Prop := CloseContract Zlib.Gzwrite.gzclose_w (some GZ_WRITE)

/-- `int gzclose(gzFile file)`.
Dispatch by the actual mode and apply the corresponding complete close contract. -/
def Goal.gzclose : Prop := CloseContract Zlib.Gzclose.gzclose none

end ZlibF.Spec.Public
