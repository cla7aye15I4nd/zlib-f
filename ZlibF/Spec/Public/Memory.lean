import ZlibF.Spec.Public.Checksums

namespace ZlibF.Spec.Public
open C

/-- A readable range. A null pointer denotes only an empty range here; checksum queries
have their separate null-buffer convention in `BufferBytes`. -/
def Bytes (h : Heap) (p : BPtr) (n : Nat) (xs : List UInt8) : Prop :=
  (p = .null ∧ n = 0 ∧ xs = []) ∨
  ∃ r i a, p = .ref r i ∧ Space.get h r = some a ∧ i + n ≤ a.size ∧
    xs = (a.toList.drop i).take n

/-- A writable range, including a null empty range. -/
def Writable (h : Heap) (p : BPtr) (n : Nat) : Prop :=
  (p = .null ∧ n = 0) ∨ ∃ r i a,
    p = .ref r i ∧ Space.get h r = some a ∧ Space.ro h r = false ∧ i + n ≤ a.size

/-- Two ranges may share an allocation, but their occupied intervals must be disjoint. -/
def Separate (p : BPtr) (n : Nat) (q : BPtr) (m : Nat) : Prop :=
  n = 0 ∨ m = 0 ∨
  match p, q with
  | .ref r i, .ref s j => r ≠ s ∨ i + n ≤ j ∨ j + m ≤ i
  | _, _ => True

/-- The exact byte-array update, preserving both sides of the written interval. -/
def Store (h : Heap) (p : BPtr) (xs : List UInt8) (after : Heap) : Prop :=
  (xs = [] ∧ after = h) ∨ ∃ r i a,
    p = .ref r i ∧ Space.get h r = some a ∧ Space.ro h r = false ∧
    i + xs.length ≤ a.size ∧
    after = Space.put h r (a.extract 0 i ++ xs.toArray ++ a.extract (i + xs.length) a.size)

/-- Successful temporary allocations may advance the allocation metadata. They must leave
every object and read-only flag as specified, and leave no new live object behind. -/
def SameObjects (expected after : Heap) : Prop :=
  after.bytes = expected.bytes ∧ after.words = expected.words ∧
  (∀ b, expected.live b → after.ro b = expected.ro b) ∧
  after.streams = expected.streams ∧ after.gzheaders = expected.gzheaders ∧
  after.dstates = expected.dstates ∧ after.istates = expected.istates ∧
  after.gzstates = expected.gzstates ∧ after.static = expected.static ∧
  after.allocOk = expected.allocOk ∧ after.garbage = expected.garbage ∧
  expected.nextBlk ≤ after.nextBlk ∧ expected.nalloc ≤ after.nalloc

/-- `SameObjects` up to the physical length of the object tables. Every table is compared
entry by entry, so a table that grew to hold a temporary allocation and now holds an empty
entry there is accepted. No C operation observes the table length. As in `SameObjects`, no
new live object remains: an empty entry is not live. -/
def SameObjectsUpToTableShape (expected after : Heap) : Prop :=
  (∀ b, after.bytes b = expected.bytes b) ∧ (∀ b, after.words b = expected.words b) ∧
  (∀ b, expected.live b → after.ro b = expected.ro b) ∧
  (∀ b, after.streams b = expected.streams b) ∧ (∀ b, after.gzheaders b = expected.gzheaders b) ∧
  (∀ b, after.dstates b = expected.dstates b) ∧ (∀ b, after.istates b = expected.istates b) ∧
  (∀ b, after.gzstates b = expected.gzstates b) ∧ after.static = expected.static ∧
  after.allocOk = expected.allocOk ∧ after.garbage = expected.garbage ∧
  expected.nextBlk ≤ after.nextBlk ∧ expected.nalloc ≤ after.nalloc

/-- A little-endian length cell in the current scalar-pointer representation. -/
def LengthCell (h : Heap) (p : BPtr) (value : UInt64) : Prop :=
  Bytes h p 8 ((List.range 8).map fun i => UInt8.ofNat (value.toNat / 256 ^ i % 256)) ∧
  Writable h p 8

/-- Only genuine allocator failures can justify an allocation-error result. -/
def AllocationFailed (before after : Heap) : Prop :=
  ∃ i, before.nalloc ≤ i ∧ i < after.nalloc ∧ before.allocOk i = false

/-- The constant tables of the selected build. -/
def LibraryGlobals (h : Heap) : Prop :=
  h.static = Zlib.Crc32.initStatics
    (Zlib.Inftrees.initStatics (Zlib.Trees.trees_statics Heap.empty.static))

def lengthBytes (n : UInt64) : List UInt8 :=
  (List.range 8).map fun i => UInt8.ofNat (n.toNat / 256 ^ i % 256)

end ZlibF.Spec.Public
