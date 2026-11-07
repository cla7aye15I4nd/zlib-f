import ZlibF.Runtime.Address
import ZlibF.Runtime.Ptr
import ZlibF.Zlib.«crc32.c»

/-!
# Obligations for the CRC low-address-bit model

These goals check the metadata interpretation independently of checksum
arithmetic. Non-block origins range over all residues. Raw blocks retain
the existing aligned-origin convention; general ABI layout is not claimed.
-/

namespace C.ByteAddress.Spec

/-- The exact integer observation made by the CRC alignment condition. -/
def low (value : UInt64) : Nat := (value &&& 7).toNat

/-- A concrete base-address assignment agrees with the model where the
program observes it. This is a representation relation, not a caller
contract required by the general checksum theorem. -/
def ModelsLowBits (h : Heap) (physicalBase : BRef → Nat) : Prop :=
  ∀ ref, physicalBase ref % 8 = base h ref

/-- Assign concrete low address bits without rebuilding the existing heap. -/
def withLayout (h : Heap) (physicalBase : BRef → Nat) : Heap :=
  { h with byteBase := fun ref =>
      ⟨physicalBase ref.toBRef % 8, Nat.mod_lt _ (by decide)⟩ }

/-- All heap components that predate the address metadata are unchanged. -/
def SameStorage (before after : Heap) : Prop :=
  after.bytes = before.bytes ∧ after.words = before.words ∧
  after.ro = before.ro ∧ after.streams = before.streams ∧
  after.gzheaders = before.gzheaders ∧ after.dstates = before.dstates ∧
  after.istates = before.istates ∧ after.gzstates = before.gzstates ∧
  after.static = before.static ∧ after.nextBlk = before.nextBlk ∧
  after.nalloc = before.nalloc ∧ after.allocOk = before.allocOk ∧
  after.garbage = before.garbage

def Goal.address_read_is_pure : Prop :=
  ∀ (h : Heap) (p : BPtr),
    C.run (Zlib.Crc32.addrOf p) h = .ok (value h p, h)

def Goal.raw_block_unchanged : Prop :=
  ∀ (h : Heap) (block offset : Nat),
    C.run (Zlib.Crc32.addrOf (.ref (.blk block) offset)) h =
      .ok (UInt64.ofNat offset, h)

/-- Every concrete non-block origin residue is representable. No static
or embedded field is forced to be aligned. -/
def Goal.every_layout_is_representable : Prop :=
  ∀ physicalBase : BRef → Nat,
    (∀ block, physicalBase (.blk block) % 8 = 0) →
    ∃ h : Heap, ModelsLowBits h physicalBase

/-- Every existing heap admits any concrete non-block layout, while all
pre-existing storage and allocation choices stay exactly the same. -/
def Goal.every_existing_heap_accepts_layout : Prop :=
  ∀ (h : Heap) (physicalBase : BRef → Nat),
    (∀ block, physicalBase (.blk block) % 8 = 0) →
    ModelsLowBits (withLayout h physicalBase) physicalBase ∧
      SameStorage h (withLayout h physicalBase)

/-- The source cast followed by its mask agrees with the actual base plus
offset, including unsigned wrap before masking. -/
def Goal.mask_refines_base_plus_offset : Prop :=
  ∀ (h : Heap) (physicalBase : BRef → Nat), ModelsLowBits h physicalBase →
    ∀ (ref : BRef) (offset : Nat),
      low (value h (.ref ref offset)) = (physicalBase ref + offset) % 8

def Goal.pointer_advance_preserves_low_bits : Prop :=
  ∀ (h : Heap) (ref : BRef) (offset count : Nat),
    low (value h (.ref ref (offset + count))) =
      (low (value h (.ref ref offset)) + count) % 8

/-- The first aligned position lies at most seven bytes ahead. A source
loop may exhaust its input earlier; this is a position-arithmetic claim. -/
def Goal.first_aligned_offset : Prop :=
  ∀ (h : Heap) (ref : BRef) (offset : Nat),
    let count := (8 - low (value h (.ref ref offset))) % 8
    count ≤ 7 ∧ low (value h (.ref ref (offset + count))) = 0 ∧
      ∀ before, before < count → low (value h (.ref ref (offset + before))) ≠ 0

def Goal.byte_stores_preserve_bases : Prop :=
  ∀ (h : Heap) (ref : BRef) (bytes : Array UInt8),
    (Space.put h ref bytes).byteBase = h.byteBase

def Goal.byte_modifies_preserve_bases : Prop :=
  ∀ (h : Heap) (ref : BRef) (modify : Array UInt8 → Array UInt8),
    (Space.modify h ref modify).byteBase = h.byteBase

end C.ByteAddress.Spec
