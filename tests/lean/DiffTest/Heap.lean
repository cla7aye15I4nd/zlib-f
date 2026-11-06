import ZlibF.Zlib.«crc32.c»
import ZlibF.Zlib.«inftrees.c»
import ZlibF.Zlib.«trees.c»
import DiffTest.Common

/-!
# The initial heap of whole-library tests

The translations read the static tables (`crc_table`, `lenfix`, `distfix`, the tree tables) from the heap. A driver
that calls `inflate`, `deflate`, the gz functions or `uncompress` starts from this heap, not from `Heap.empty`.
A driver that forgets this sees faults that are not translation errors.
-/

namespace DiffTest

/-- `Heap.empty` with every static table of the library installed. -/
def fullHeap : C.Heap :=
  { C.Heap.empty with static :=
      Zlib.Crc32.initStatics (Zlib.Inftrees.initStatics (Zlib.Trees.trees_statics C.Heap.empty.static)) }

end DiffTest
