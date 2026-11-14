import ZlibF.Spec.Public.History
import ZlibF.Zlib.«inflate.c»
import ZlibF.Spec.Functional.Api.Basic

namespace Zlib.Inflate.Spec
open C ZlibF.Spec.Public

/-- The output clause at an actual dispatch boundary. The outer entry has
already rejected NULL output. A caller range carries the current capacity
and exclusion of stream-owned storage. Counter and cursor facts relate the
current segment to this call's original output count. -/
structure OutputCursorInvariant (h : Heap) (r : ZStreamRef) (l : Zlib.Inflate.IL) : Prop where
  range : CallerRange h r l.put l.left.toNat true
  nonnull : l.put ≠ .null
  count : l.left.toNat ≤ l.out_.toNat
  produced : ∀ ref off, l.put = .ref ref off → l.out_.toNat - l.left.toNat ≤ off

/-- Literal and match emission preserve all input, bit, symbol and return
registers. Their only local writes are output and copy cursors. -/
def EmitRegFrame (before after : Zlib.Inflate.IL) : Prop :=
  after = { before with put := after.put, left := after.left, copy := after.copy, from_ := after.from_ }

end Zlib.Inflate.Spec
