import ZlibF.Proof.«gzlib.c.open-mode»
import ZlibF.Proof.gzfs

/-!
# gzlib.c: path reading and copying

The supporting lemmas below evaluate the actual path-reading and formatting
operations used by the source tail. Heap facts describe readable ranges;
callee contracts are proved here rather than supplied as assumptions.
-/

namespace Zlib.Gzlib.Proofs
open C Zlib.GzFs Zlib.Gzguts Zlib.Gzlib.Spec ZlibF.Spec.Public.OffsetProof

/-- The actual character-reading loop preserves the heap and appends exactly
the indexed bytes. Every index is justified in its physical byte object. -/
theorem openPath_read_loop (h : Heap) (r : BRef) (off : Nat) (a : Array UInt8)
    (hg : Space.get h r = some a) (js : List Nat) (out : Array UInt8)
    (hb : ∀ j, j ∈ js → off + j < a.size) :
    (forIn' js out (fun (j : Nat) _ acc => do
      let b ← index8 (.ref r off) (j : Int)
      pure (.yield (acc.push b))) : M (Array UInt8)) h =
      .ok (out ++ (js.map fun j => a[off + j]!).toArray, h) := by
  induction js generalizing out with
  | nil => simp [List.forIn'_nil, pure_app]
  | cons j js ih =>
    have hj : off + j < a.size := hb j (by simp)
    have hx : index8 (.ref r off) (j : Int) h = .ok (a[off + j]!, h) := by
      have he := Ptr.index_ok hg hj
      simpa [OkOn, getElem!_pos a (off + j) hj] using he
    simp only [List.forIn'_cons, bind_app, hx, pure_app]
    rw [ih (out.push a[off + j]!) (fun k hk => hb k (by simp [hk]))]
    simp

/-- `cstring` used by the actual formatter/open calls reads the terminated
range, changes no heap field, and returns its bytes before NUL. The natural
length only needs to fit `size_t`; the platform object-size bound implies this. -/
theorem openPath_cstring (h : Heap) (r : BRef) (off last : Nat) (a : Array UInt8)
    (hg : Space.get h r = some a) (hoff : off ≤ last) (hz : a[last]? = some 0)
    (hn : ∀ j, off ≤ j → j < last → a[j]? ≠ some 0)
    (hlen : last - off < 2 ^ 64) :
    cstring (.ref r off) h =
      .ok (((List.range' 0 (last - off)).map fun j => a[off + j]!).toArray, h) := by
  have hlast : last < a.size := by
    by_cases hlt : last < a.size
    · exact hlt
    · have he := Array.getElem?_eq_none (xs := a) (i := last) (by omega)
      rw [he] at hz
      contradiction
  have hstr := strlenB_ok hg hoff hz hn
  change strlenB (.ref r off) h = .ok (UInt64.ofNat (last - off), h) at hstr
  have hsize : (UInt64.ofNat (last - off)).toNat = last - off := by
    rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt hlen]
  unfold cstring
  simp only [bind_app, hstr, hsize]
  simp only [forIn, Std.Legacy.Range.forIn'_eq_forIn'_range', Std.Legacy.Range.size]
  simp only [Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  rw [openPath_read_loop h r off a hg (List.range' 0 (last - off)) #[]]
  · simp [pure_app]
  · intro j hj
    have hjb : j < last - off := by simpa [List.mem_range'] using hj
    omega

/-- The public caller string predicate implies the actual `cstring` execution.
This discharges the formatter/open callee obligation from heap contents, for
every byte-reference kind and every admitted string length. -/
theorem openPath_cstring_public (h : Heap) (p : BPtr) (xs : List UInt8)
    (hstr : ZlibF.Spec.Public.CString h p xs) :
    cstring p h = .ok (xs.toArray, h) := by
  rcases hstr with ⟨hb, hn, hlen⟩
  rcases hb with ⟨_, hz, _⟩ | ⟨r, off, a, rfl, hg, hbound, hbytes⟩
  · simp at hz
  · have hchar (k : Nat) (hk : k < xs.length + 1) :
        a[off + k]? = (xs ++ [0])[k]? := by
      have he := congrArg (fun ys : List UInt8 => ys[k]?) hbytes
      simpa [List.getElem?_take, hk, List.getElem?_drop] using he.symm
    have hzero : a[off + xs.length]? = some 0 := by
      simpa using hchar xs.length (by omega)
    have hnonzero (j : Nat) (hj0 : off ≤ j) (hj1 : j < off + xs.length) :
        a[j]? ≠ some 0 := by
      intro he
      have hk : j - off < xs.length := by omega
      have hc := hchar (j - off) (by omega)
      have heq : off + (j - off) = j := by omega
      rw [heq, he] at hc
      have hx : xs[j - off]? = some 0 := by
        simpa [List.getElem?_append_left hk] using hc.symm
      exact hn (List.mem_of_getElem? hx)
    have hr := openPath_cstring h r off (off + xs.length) a hg (by omega)
      hzero hnonzero (by simpa using hlen)
    have hout : ((List.range' 0 xs.length).map fun j => a[off + j]!).toArray = xs.toArray := by
      apply Array.ext
      · simp
      · intro k hkl hkr
        have hk : k < xs.length := by simpa using hkr
        have hc := hchar k (by omega)
        have ha : off + k < a.size := by omega
        have hv : a[off + k]! = xs[k] := by
          have he : a[off + k]? = some xs[k] := by
            simpa [List.getElem?_append_left hk, List.getElem?_eq_getElem hk] using hc
          simpa [Array.getElem?_eq_getElem ha, getElem!_pos a (off + k) ha] using he
        simp [hv]
    simpa [hout] using hr

/-- A `%s` result longer than `INT_MAX` makes `snprintf` return −1, as glibc does (`EOVERFLOW`), for a valid
public caller string: with no room (`size = 0`) nothing is written and the heap is unchanged. -/
theorem openPath_snprintf_overflow (h : Heap) (dest fmt path : BPtr)
    (xs : List UInt8) (hp : ZlibF.Spec.Public.CString h path xs)
    (hf : ZlibF.Spec.Public.CString h fmt [37, 115]) (hlen : 2147483647 < xs.length) :
    snprintf dest 0 fmt [.str path] h = .ok (-1, h) := by
  have hr := openPath_cstring_public h path xs hp
  have hfmt : cstring fmt h = .ok (#[37, 115], h) :=
    openPath_cstring_public h fmt [37, 115] hf
  have hnonnull : path ≠ .null := by
    intro he
    rw [he] at hr
    simp [cstring, strlenB, bind_app] at hr
  have hout := Zlib.GzFs.Proofs.formatBytes_s hnonnull hr
  unfold snprintf
  simp [bind_app, hfmt, hout, hlen, ub]

#print axioms openPath_read_loop
#print axioms openPath_cstring
#print axioms openPath_cstring_public
#print axioms openPath_snprintf_overflow
end Zlib.Gzlib.Proofs
