import ZlibF.Proof.«inflate.c.meaning»

/-!
# inflate.c: frame lemmas of the format meaning

`BodyMatches` reads the heap only through code arrays (the installed tables and
the code-length table), and `WindowMeaning` only through the window block. A
heap change that keeps those keeps the facts. Interface lemmas for the call
assembly, rebuffering and `inf_leave`.
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
set_option autoImplicit false

theorem TableMeaning.frame {h h' : Heap}
    (codes : ∀ r : CodeRef, (Space.get h' r : Option (Array Code)) = Space.get h r)
    {pointer : CodePtr} {root type : UInt32} {lens : List Nat}
    (table : TableMeaning h pointer root type lens) : TableMeaning h' pointer root type lens := by
  obtain ⟨ref, offset, arr, used, ptr, get, inv, stable⟩ := table
  exact ⟨ref, offset, arr, used, ptr, (codes ref).trans get, inv, stable⟩

theorem DynamicMatches.frame {h h' : Heap}
    (codes : ∀ r : CodeRef, (Space.get h' r : Option (Array Code)) = Space.get h r)
    {s : InflateState} {header : List Bool} (dyn : DynamicMatches h s header) :
    DynamicMatches h' s header := by
  rcases dyn with table | ⟨hlit, hdist, hclen, r1, r2, r3, a1, a2, a3, a4, a5, a6, a7, lenlens | codelens⟩
  · exact Or.inl table
  · exact Or.inr ⟨hlit, hdist, hclen, r1, r2, r3, a1, a2, a3, a4, a5, a6, a7, Or.inl lenlens⟩
  · obtain ⟨m, cl, r4, ref, offset, arr, b1, b2, get, b4⟩ := codelens
    exact Or.inr ⟨hlit, hdist, hclen, r1, r2, r3, a1, a2, a3, a4, a5, a6, a7,
      Or.inr ⟨m, cl, r4, ref, offset, arr, b1, b2, (codes ref).trans get, b4⟩⟩

/-- `BodyMatches` is kept by a heap change that keeps every code array. -/
theorem BodyMatches.frame {h h' : Heap}
    (codes : ∀ r : CodeRef, (Space.get h' r : Option (Array Code)) = Space.get h r)
    {s : InflateState} {pos : DeflatePos} (body : BodyMatches h s pos) : BodyMatches h' s pos := by
  rcases pos with ⟨out, final, stage⟩
  cases stage with
  | dynamicHeader header =>
      exact ⟨DynamicMatches.frame codes body.1, body.2⟩
  | codes L D pending =>
      obtain ⟨last, lt, dt, rest⟩ := body
      exact ⟨last, TableMeaning.frame codes lt, TableMeaning.frame codes dt, rest⟩
  | boundary => exact body
  | storedHeader => exact body
  | stored remaining => exact body
  | finished => exact body

/-- `WindowMeaning` is kept by a heap change that keeps the window block. -/
theorem WindowMeaning.frame {h h' : Heap} {s : InflateState} {dict out : List UInt8}
    (window : ∀ r off, s.window = .ref r off →
      (Space.get h' r : Option (Array UInt8)) = Space.get h r)
    (meaning : WindowMeaning h s dict out) : WindowMeaning h' s dict out := by
  rcases meaning with ⟨nonzero, dictionary⟩ | empty
  · refine Or.inl ⟨nonzero, ?_⟩
    rcases dictionary with none | ⟨r, off, a, ptr, get, fits, content⟩
    · exact Or.inl none
    · exact Or.inr ⟨r, off, a, ptr, (window r off ptr).trans get, fits, content⟩
  · exact Or.inr empty

end Zlib.Inflate.Proofs
