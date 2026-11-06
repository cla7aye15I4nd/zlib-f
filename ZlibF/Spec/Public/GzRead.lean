import ZlibF.Spec.Public.GzOpen

namespace ZlibF.Spec.Public
open C Zlib.GzFs

def ReadEffect (h after : Heap) (fs fs' : Fs) (i : Nat) (s s' : GzState)
    (requested : Nat) (out : List UInt8) (regions : List Region) : Prop :=
  GzStateFrame h after fs fs' i s s' regions ∧ out.length ≤ requested ∧
  (s.mode ≠ GZ_READ → out = []) ∧
  (s.skip = 0 → s'.x.pos.toInt = s.x.pos.toInt + (out.length : Int)) ∧
  (∀ decoded buffered, FileData fs s decoded → Buffered h s buffered →
    out <+: availableRead s buffered decoded ∧
    (NoAllocationFailure h → s.mode = GZ_READ → s.err = Z_OK ∨ s.err = Z_BUF_ERROR →
      out = (availableRead s buffered decoded).take requested))

def ReturnedBytes (h : Heap) (p : BPtr) (bytes : List UInt8) : Prop :=
  bytes = [] ∨ Bytes h p bytes.length bytes

/-- `int gzread(gzFile file, voidp buf, unsigned len)`.
Return bytes, EOF zero, or -1. Requests above INT_MAX fail before touching the output.
Buffered bytes precede a later error; partial output remains part of the result. -/
def Goal.gzread : Prop :=
  (∀ h fs p n, Zlib.Gzread.gzread none p n fs h = .ok ((-1, fs), h)) ∧
  (∀ h fs i s p n, GzReachable h fs i → GzValid h i s →
    (n.toNat < 2 ^ 31 → GzRange h i s p n.toNat true) →
    ∃ rc fs' after s' out,
      Zlib.Gzread.gzread (some (.in_gzstate_x i)) p n fs h = .ok ((rc, fs'), after) ∧
      ReturnedBytes after p out ∧
      ReadEffect h after fs fs' i s s' (if n.toNat < 2 ^ 31 then n.toNat else 0) out [⟨p, out.length⟩] ∧
      (rc = -1 ∧ out = [] ∨ 0 ≤ rc.toInt ∧ rc.toInt = (out.length : Int)) ∧
      (2 ^ 31 ≤ n.toNat → rc = -1) ∧
      (s.mode ≠ GZ_READ → rc = -1 ∧ after = h ∧ fs' = fs))

/-- `z_size_t gzfread(voidp buf, z_size_t size, z_size_t nitems, gzFile file)`.
Report complete items. A final partial item is still written and consumed. Multiplication
overflow and zero-sized requests do not touch the destination. -/
def Goal.gzfread : Prop :=
  (∀ h fs p size n, Zlib.Gzread.gzfread p size n none fs h = .ok ((0, fs), h)) ∧
  (∀ h fs i s p size n, GzReachable h fs i → GzValid h i s →
    (size.toNat * n.toNat < 2 ^ 64 → GzRange h i s p (size.toNat * n.toNat) true) →
    ∃ items fs' after s' out,
      Zlib.Gzread.gzfread p size n (some (.in_gzstate_x i)) fs h = .ok ((items, fs'), after) ∧
      ReturnedBytes after p out ∧
      ReadEffect h after fs fs' i s s'
        (if size.toNat * n.toNat < 2 ^ 64 then size.toNat * n.toNat else 0)
        out [⟨p, out.length⟩] ∧
      items.toNat = (if size = 0 then 0 else out.length / size.toNat) ∧ items ≤ n ∧
      (2 ^ 64 ≤ size.toNat * n.toNat → items = 0 ∧ out = []))

def GetcContract (program : GzFilePtr → G Int32) : Prop :=
  (∀ h fs, program none fs h = .ok ((-1, fs), h)) ∧
  (∀ h fs i s, GzReachable h fs i → GzValid h i s →
    ∃ rc fs' after s' out, program (some (.in_gzstate_x i)) fs h = .ok ((rc, fs'), after) ∧
      ReadEffect h after fs fs' i s s' 1 out [] ∧
      ((rc = -1 ∧ out = []) ∨ ∃ b, out = [b] ∧ rc.toInt = b.toNat))

/-- `int gzgetc(gzFile file)`; byte values are unsigned 0..255, distinct from EOF -1. -/
def Goal.gzgetc : Prop := GetcContract Zlib.Gzread.gzgetc

/-- `int gzgetc_(gzFile file)`; the exported wrapper retains the byte/EOF distinction. -/
def Goal.gzgetc_ : Prop := GetcContract Zlib.Gzread.gzgetc_

/-- `int gzungetc(int c, gzFile file)`.
On success store the low byte but return the original nonnegative integer. Clear past-EOF.
The initial look and pending skip can precede rejection of a negative character. -/
def Goal.gzungetc : Prop :=
  (∀ h fs c, Zlib.Gzread.gzungetc c none fs h = .ok ((-1, fs), h)) ∧
  (∀ h fs i s c, GzReachable h fs i → GzValid h i s →
    ∃ rc fs' after s',
      Zlib.Gzread.gzungetc c (some (.in_gzstate_x i)) fs h = .ok ((rc, fs'), after) ∧
      GzStateFrame h after fs fs' i s s' [] ∧
      (rc = -1 ∨ (rc = c ∧ 0 ≤ c.toInt ∧ s'.past = 0 ∧
        ∃ rest, Buffered after s' (c.toUInt32.toUInt8 :: rest))) ∧
      (c.toInt < 0 ∨ s.mode ≠ GZ_READ → rc = -1) ∧
      (rc ≠ -1 → s.skip = 0 → s'.x.pos.toInt = s.x.pos.toInt - 1))

/-- `char *gzgets(gzFile file, char *buf, int len)`.
Copy at most len-1 bytes, stopping after the first newline, and append a NUL on success.
Length one succeeds with an empty string; an EOF with no bytes returns null for larger lengths. -/
def Goal.gzgets : Prop :=
  (∀ h fs p n, Zlib.Gzread.gzgets none p n fs h = .ok ((.null, fs), h)) ∧
  (∀ h fs i s p n, GzReachable h fs i → GzValid h i s →
    (0 < n.toInt → p ≠ .null → GzRange h i s p n.toInt.toNat true) →
    ∃ result fs' after s' out,
      Zlib.Gzread.gzgets (some (.in_gzstate_x i)) p n fs h = .ok ((result, fs'), after) ∧
      GzStateFrame h after fs fs' i s s' [⟨p, if result = .null then out.length else out.length + 1⟩] ∧
      out.length ≤ n.toInt.toNat - 1 ∧
      (result = .null → out = []) ∧
      (result = .null ∨ result = p ∧ Bytes after p (out.length + 1) (out ++ [0])) ∧
      (∀ left right, out = left ++ 10 :: right → right = []) ∧
      (p = .null ∨ n.toInt < 1 ∨ s.mode ≠ GZ_READ → result = .null ∧ after = h ∧ fs' = fs) ∧
      (∀ decoded buffered, FileData fs s decoded → Buffered h s buffered →
        out <+: availableRead s buffered decoded ∧
        (NoAllocationFailure h → s.mode = GZ_READ → p ≠ .null → 0 < n.toInt →
          s.err = Z_OK ∨ s.err = Z_BUF_ERROR →
          let line := ((availableRead s buffered decoded).takeWhile (fun b => b != 10))
          let full := if line.length < (availableRead s buffered decoded).length then line ++ [10] else line
          out = full.take (n.toInt.toNat - 1) ∧
            (n = 1 ∨ full ≠ [] → result = p))))

/-- `int gzdirect(gzFile file)`.
The query may initialize and inspect a reader. Its result is exactly the resulting direct-mode flag. -/
def Goal.gzdirect : Prop :=
  (∀ h fs, Zlib.Gzread.gzdirect none fs h = .ok ((0, fs), h)) ∧
  (∀ h fs i s, GzReachable h fs i → GzValid h i s →
    ∃ rc fs' after s', Zlib.Gzread.gzdirect (some (.in_gzstate_x i)) fs h = .ok ((rc, fs'), after) ∧
      GzStateFrame h after fs fs' i s s' [] ∧
      rc = (if s'.direct = 1 then 1 else 0) ∧
      (s.mode ≠ GZ_READ ∨ s.how ≠ LOOK ∨ s.x.have ≠ 0 → after = h ∧ fs' = fs))

end ZlibF.Spec.Public
