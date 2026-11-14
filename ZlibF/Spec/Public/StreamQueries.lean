import ZlibF.Spec.Public.Memory

namespace ZlibF.Spec.Public
open C

/-- The stream and inflate record accepted by the public state check. This is a
representation condition, to be established by init and preserved by stream operations. -/
def InflateView (h : Heap) (r : ZStreamRef) (i : Nat) (z : ZStream) (s : InflateState) : Prop :=
  r.get h = some z ∧ z.state = StateRef.ofInflateState (some (.tab i)) ∧
  h.istates i = some s ∧ s.strm = some r ∧ z.zalloc ≠ .null ∧ z.zfree ≠ .null ∧
  HEAD ≤ s.mode ∧ s.mode ≤ SYNC

/-- The stream and deflate record accepted by the public state check. -/
def DeflateView (h : Heap) (r : ZStreamRef) (i : Nat) (z : ZStream) (s : DeflateState) : Prop :=
  r.get h = some z ∧ z.state = StateRef.ofDeflateState (some (.tab i)) ∧
  h.dstates i = some s ∧ s.strm = some r ∧ z.zalloc ≠ .null ∧ z.zfree ≠ .null ∧
  (s.status = INIT_STATE ∨ s.status = GZIP_STATE ∨ s.status = EXTRA_STATE ∨
   s.status = NAME_STATE ∨ s.status = COMMENT_STATE ∨ s.status = HCRC_STATE ∨
   s.status = BUSY_STATE ∨ s.status = FINISH_STATE)

def putInflate (h : Heap) (i : Nat) (s : InflateState) : Heap :=
  { h with istates := upd h.istates i (some s) }

def putDeflate (h : Heap) (i : Nat) (s : DeflateState) : Heap :=
  { h with dstates := upd h.dstates i (some s) }

/-- Cleanly rejected pointers contain enough live storage for the source state check.
A dangling or wrongly typed state is not a permitted caller argument. -/
def RefusedInflate (h : Heap) (p : ZStreamPtr) : Prop :=
  p = none ∨ ∃ r z, p = some r ∧ r.get h = some z ∧
    (z.zalloc = .null ∨ z.zfree = .null ∨ z.state = none ∨
      ∃ i s, z.state = some (.inflate i) ∧ h.istates i = some s ∧
        (s.strm ≠ some r ∨ s.mode < HEAD ∨ SYNC < s.mode))

def RefusedDeflate (h : Heap) (p : ZStreamPtr) : Prop :=
  p = none ∨ ∃ r z, p = some r ∧ r.get h = some z ∧
    (z.zalloc = .null ∨ z.zfree = .null ∨ z.state = none ∨
      ∃ i s, z.state = some (.deflate i) ∧ h.dstates i = some s ∧
        (s.strm ≠ some r ∨ ¬ (s.status = INIT_STATE ∨ s.status = GZIP_STATE ∨
          s.status = EXTRA_STATE ∨ s.status = NAME_STATE ∨ s.status = COMMENT_STATE ∨
          s.status = HCRC_STATE ∨ s.status = BUSY_STATE ∨ s.status = FINISH_STATE)))

def CheckedInflate {α : Type} (program : ZStreamPtr → M α) (error : α)
    (accepted : Prop) : Prop :=
  (∀ h p, RefusedInflate h p → C.run (program p) h = .ok (error, h)) ∧ accepted

def CheckedDeflate {α : Type} (program : ZStreamPtr → M α) (error : α)
    (accepted : Prop) : Prop :=
  (∀ h p, RefusedDeflate h p → C.run (program p) h = .ok (error, h)) ∧ accepted

end ZlibF.Spec.Public
