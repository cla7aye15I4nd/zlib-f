import ZlibF.Proof.«inflate.c.default-readonly-controls»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The selected default calls. Reset2 selects fifteen bits. Synchronization
recovery and copy require additional history facts and are not included. -/
inductive DefaultHistoryCall (r : ZStreamRef) : Call → Prop where
  | inflate (flush : Int32) : DefaultHistoryCall r (.inflate (some r) flush)
  | resetKeep : DefaultHistoryCall r (.inflateResetKeep (some r))
  | reset : DefaultHistoryCall r (.inflateReset (some r))
  | reset2 : DefaultHistoryCall r (.inflateReset2 (some r) 15)
  | prime (bits value : Int32) : DefaultHistoryCall r (.inflatePrime (some r) bits value)
  | validate (check : Int32) : DefaultHistoryCall r (.inflateValidate (some r) check)
  | getHeader (head : GzHeaderPtr) : DefaultHistoryCall r (.inflateGetHeader (some r) head)
  | undermine (subvert : Int32) : DefaultHistoryCall r (.inflateUndermine (some r) subvert)
  | setDictionary (source : BPtr) (len : UInt32) :
      DefaultHistoryCall r (.inflateSetDictionary (some r) source len)
  | getDictionary (dest : BPtr) (dl : Option UInt32) :
      DefaultHistoryCall r (.inflateGetDictionary (some r) dest dl)
  | syncPoint : DefaultHistoryCall r (.inflateSyncPoint (some r))
  | mark : DefaultHistoryCall r (.inflateMark (some r))
  | codesUsed : DefaultHistoryCall r (.inflateCodesUsed (some r))

/-- Every selected call is one of the original public stream operations. -/
theorem DefaultHistoryCall.public_operation {r : ZStreamRef} {call : Call}
    (selected : DefaultHistoryCall r call) : StreamOperation .inflate r call := by
  cases selected <;> exact ⟨rfl, rfl⟩

end Zlib.Inflate.Proofs
