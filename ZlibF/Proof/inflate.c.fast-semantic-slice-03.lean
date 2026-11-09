import ZlibF.Proof.«inflate.c.fast-semantic-slice-02»
set_option autoImplicit false

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The valid-window cases of translated `copyMatch` share one packet,
output-cursor, writable-view and buffer-size postcondition. -/
theorem FastInputPacket.copyMatch_window_array_view
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    (packet : FastInputPacket h slow bs l)
    (separate : Separate slow.next slow.have_.toNat
      slow.put slow.left.toNat)
    (left : slow.left ≠ 0)
    (windowBranch : l.dist > l.op)
    (validBack : ¬ l.dist - l.op > c.whave)
    (whaveBound : c.whave.toNat ≤ c.wsize.toNat)
    (wnextBound : c.wnext.toNat ≤ c.wsize.toNat)
    (wsizeBound : c.wsize.toNat ≤ 32768)
    {window dest : BRef} (different : window ≠ dest)
    {saved output : Array UInt8} {woff oo j : Nat}
    (windowPtr : c.window = .ref window woff)
    (windowGet : Space.get h window = some saved)
    (windowSize : woff + c.wsize.toNat ≤ saved.size)
    (outPtr : l.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (outputGet : Space.get h dest = some output)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (outputRoom : oo ≤ j ∧
      j + l.len.toNat ≤ oo + slow.left.toNat)
    (produced : l.op.toNat ≤ j) :
    ∃ result after array,
      C.run (Zlib.Inffast.copyMatch c l) h =
        .ok (result, after) ∧
      FastInputPacket after slow bs result ∧
      result.out = .ref dest (j + l.len.toNat) ∧
      result.broke = l.broke ∧
      result.againD = l.againD ∧
      result.againL = l.againL ∧
      Space.get after dest = some array ∧
      array.size = output.size ∧
      Space.ro after dest = false ∧
      array = Zlib.Inffast.Proofs.matchArr c.wsize.toNat c.wnext.toNat woff saved (j - l.op.toNat) j l.dist.toNat l.len.toNat output := by
  have countEq : j - (j - l.op.toNat) = l.op.toNat := by omega
  have route : l.op.toNat < l.dist.toNat := UInt32.lt_iff_toNat_lt.mp windowBranch
  have backNat : (l.dist - l.op).toNat = l.dist.toNat - l.op.toNat :=
    Zlib.Inffast.Proofs.u32_toNat_sub (by omega)
  have wnZero : (c.wnext.toNat = 0) ↔ c.wnext = 0 := by simpa only [UInt32.toNat_zero] using (UInt32.toNat_inj (a := c.wnext) (b := 0))
  have backSize : (l.dist - l.op).toNat ≤ c.wsize.toNat := by
    have backLeWhave : (l.dist - l.op).toNat ≤ c.whave.toNat := by
      by_cases hle : (l.dist - l.op).toNat ≤ c.whave.toNat
      · exact hle
      · have hgt : c.whave.toNat < (l.dist - l.op).toNat := by
          omega
        exact False.elim (validBack (UInt32.lt_iff_toNat_lt.mpr hgt))
    omega
  have sumFits : c.wsize.toNat + c.wnext.toNat < 2 ^ 32 := by
    omega
  have finish {result : Zlib.Inffast.L} {after : Heap}
      {array : Array UInt8}
      (run : C.run (Zlib.Inffast.copyMatch c l) h =
        .ok (result, after))
      (resultPacket : FastInputPacket after slow bs result)
      (out : result.out = .ref dest (j + l.len.toNat))
      (broke : result.broke = l.broke)
      (againD : result.againD = l.againD)
      (againL : result.againL = l.againL)
      (bytes : Space.get after dest = some array)
      (size : array.size = output.size)
      (write : Space.ro after dest = false)
      (arrayEq : array = Zlib.Inffast.Proofs.matchArr c.wsize.toNat c.wnext.toNat woff saved (j - l.op.toNat) j l.dist.toNat l.len.toNat output) :
      ∃ result after array,
        C.run (Zlib.Inffast.copyMatch c l) h =
          .ok (result, after) ∧
        FastInputPacket after slow bs result ∧
        result.out = .ref dest (j + l.len.toNat) ∧
        result.broke = l.broke ∧
        result.againD = l.againD ∧
        result.againL = l.againL ∧
        Space.get after dest = some array ∧
        array.size = output.size ∧
        Space.ro after dest = false ∧
        array = Zlib.Inffast.Proofs.matchArr c.wsize.toNat c.wnext.toNat woff saved (j - l.op.toNat) j l.dist.toNat l.len.toNat output :=
    ⟨result, after, array, run, resultPacket, out,
      broke, againD, againL,
      bytes, size, write, arrayEq⟩
  by_cases noWrap : c.wnext = 0
  · by_cases mixed : l.dist - l.op < l.len
    · obtain ⟨result, after, run, resultPacket,
          resultEq, bytes, write⟩ :=
        packet.copyMatch_window_nowrap_mixed_view
          separate left windowBranch validBack noWrap backSize
          mixed different windowPtr windowGet windowSize outPtr
          outputPtr outputGet outputWrite outputSize outputRoom
          produced
      exact finish run resultPacket (by rw [resultEq])
        (by rw [resultEq]) (by rw [resultEq])
        (by rw [resultEq]) bytes
        (by simp [Zlib.Inffast.Proofs.cpyN_size,
          Zlib.Inffast.Proofs.blitN_size]) write (by
          have mixedNat := UInt32.lt_iff_toNat_lt.mp mixed
          have off : woff + c.wsize.toNat - (l.dist - l.op).toNat = woff + (c.wsize.toNat - (l.dist - l.op).toNat) := by omega
          simp only [Zlib.Inffast.Proofs.matchArr, countEq, route, ↓reduceIte, ← backNat, noWrap, UInt32.toNat_zero, mixedNat, off])
    · have wholeWindow : l.len.toNat ≤
          (l.dist - l.op).toNat := by
        have hnot : ¬ (l.dist - l.op).toNat < l.len.toNat := by
          intro hlt
          exact mixed (UInt32.lt_iff_toNat_lt.mpr hlt)
        omega
      obtain ⟨result, after, run, resultPacket,
          resultEq, bytes, write⟩ :=
        packet.copyMatch_window_nowrap_short_view
          separate left windowBranch validBack noWrap backSize
          wholeWindow different windowPtr windowGet windowSize
          outPtr outputPtr outputGet outputWrite outputSize
          outputRoom
      exact finish run resultPacket (by rw [resultEq])
        (by rw [resultEq]) (by rw [resultEq])
        (by rw [resultEq]) bytes
        (by simp [Zlib.Inffast.Proofs.blitN_size]) write (by
          have mixedNat : ¬ (l.dist - l.op).toNat < l.len.toNat := by
            intro e; exact mixed (UInt32.lt_iff_toNat_lt.mpr e)
          have off : woff + c.wsize.toNat - (l.dist - l.op).toNat = woff + (c.wsize.toNat - (l.dist - l.op).toNat) := by omega
          simp only [Zlib.Inffast.Proofs.matchArr, countEq, route, ↓reduceIte, ← backNat, noWrap, UInt32.toNat_zero, mixedNat, off])
  · by_cases wrap : c.wnext < l.dist - l.op
    · by_cases mixed : l.dist - l.op - c.wnext < l.len
      · by_cases third : c.wnext <
            l.len - (l.dist - l.op - c.wnext)
        · obtain ⟨result, after, run, resultPacket,
              resultEq, bytes, write⟩ :=
            packet.copyMatch_window_wrapped_three_view
              separate left windowBranch validBack noWrap wrap
              backSize sumFits mixed third different
              windowPtr windowGet windowSize outPtr outputPtr
              outputGet outputWrite outputSize outputRoom produced
          exact finish run resultPacket (by rw [resultEq])
            (by rw [resultEq]) (by rw [resultEq])
            (by rw [resultEq]) bytes
            (by simp [Zlib.Inffast.Proofs.cpyN_size,
              Zlib.Inffast.Proofs.blitN_size]) write (by
          have nz : c.wnext.toNat ≠ 0 := by
            intro e; exact noWrap (UInt32.toNat_inj.mp (by simpa only [UInt32.toNat_zero] using e))
          have wrapNat := UInt32.lt_iff_toNat_lt.mp wrap
          have lastNat : (l.dist - l.op - c.wnext).toNat = (l.dist - l.op).toNat - c.wnext.toNat :=
            Zlib.Inffast.Proofs.u32_toNat_sub (by omega)
          have mixedNat : (l.dist - l.op).toNat - c.wnext.toNat < l.len.toNat := by
            have e := UInt32.lt_iff_toNat_lt.mp mixed; rwa [lastNat] at e
          have lenNat : (l.len - (l.dist - l.op - c.wnext)).toNat = l.len.toNat - ((l.dist - l.op).toNat - c.wnext.toNat) := by
            rw [Zlib.Inffast.Proofs.u32_toNat_sub (by have e := UInt32.lt_iff_toNat_lt.mp mixed; omega), lastNat]
          have thirdNat : c.wnext.toNat < l.len.toNat - ((l.dist - l.op).toNat - c.wnext.toNat) := by
            have e := UInt32.lt_iff_toNat_lt.mp third; rwa [lenNat] at e
          have remain : l.len.toNat - ((l.dist - l.op).toNat - c.wnext.toNat) - c.wnext.toNat = l.len.toNat - (l.dist - l.op).toNat := by omega
          have advance : j + ((l.dist - l.op).toNat - c.wnext.toNat) + c.wnext.toNat = j + (l.dist - l.op).toNat := by omega
          have off : woff + c.wsize.toNat + c.wnext.toNat - (l.dist - l.op).toNat = woff + (c.wsize.toNat + c.wnext.toNat - (l.dist - l.op).toNat) := by omega
          simp only [Zlib.Inffast.Proofs.matchArr, countEq, route, ↓reduceIte, ← backNat, nz, wrapNat, lastNat, mixedNat, thirdNat, remain, advance, off])
        · obtain ⟨result, after, run, resultPacket,
              resultEq, bytes, write⟩ :=
            packet.copyMatch_window_wrapped_two_view
              separate left windowBranch validBack noWrap wrap
              backSize sumFits mixed third different
              windowPtr windowGet windowSize outPtr outputPtr
              outputGet outputWrite outputSize outputRoom
          exact finish run resultPacket (by rw [resultEq])
            (by rw [resultEq]) (by rw [resultEq])
            (by rw [resultEq]) bytes
            (by simp [Zlib.Inffast.Proofs.blitN_size]) write (by
          have nz : c.wnext.toNat ≠ 0 := by
            intro e; exact noWrap (UInt32.toNat_inj.mp (by simpa only [UInt32.toNat_zero] using e))
          have wrapNat := UInt32.lt_iff_toNat_lt.mp wrap
          have lastNat : (l.dist - l.op - c.wnext).toNat = (l.dist - l.op).toNat - c.wnext.toNat :=
            Zlib.Inffast.Proofs.u32_toNat_sub (by omega)
          have mixedNat : (l.dist - l.op).toNat - c.wnext.toNat < l.len.toNat := by
            have e := UInt32.lt_iff_toNat_lt.mp mixed; rwa [lastNat] at e
          have lenNat : (l.len - (l.dist - l.op - c.wnext)).toNat = l.len.toNat - ((l.dist - l.op).toNat - c.wnext.toNat) := by
            rw [Zlib.Inffast.Proofs.u32_toNat_sub (by have e := UInt32.lt_iff_toNat_lt.mp mixed; omega), lastNat]
          have thirdNat : ¬ c.wnext.toNat < l.len.toNat - ((l.dist - l.op).toNat - c.wnext.toNat) := by
            intro e; apply third; apply UInt32.lt_iff_toNat_lt.mpr; rwa [lenNat]
          have off : woff + c.wsize.toNat + c.wnext.toNat - (l.dist - l.op).toNat = woff + (c.wsize.toNat + c.wnext.toNat - (l.dist - l.op).toNat) := by omega
          simp only [Zlib.Inffast.Proofs.matchArr, countEq, route, ↓reduceIte, ← backNat, nz, wrapNat, lastNat, mixedNat, thirdNat, off])
      · have wholeWindow : l.len.toNat ≤
            (l.dist - l.op - c.wnext).toNat := by
          have hnot : ¬ (l.dist - l.op - c.wnext).toNat <
              l.len.toNat := by
            intro hlt
            exact mixed (UInt32.lt_iff_toNat_lt.mpr hlt)
          omega
        obtain ⟨result, after, run, resultPacket,
            resultEq, bytes, write⟩ :=
          packet.copyMatch_window_wrapped_short_view
            separate left windowBranch validBack noWrap wrap
            backSize sumFits wholeWindow different windowPtr
            windowGet windowSize outPtr outputPtr outputGet
            outputWrite outputSize outputRoom
        exact finish run resultPacket (by rw [resultEq])
          (by rw [resultEq]) (by rw [resultEq])
          (by rw [resultEq]) bytes
          (by simp [Zlib.Inffast.Proofs.blitN_size]) write (by
          have nz : c.wnext.toNat ≠ 0 := by
            intro e; exact noWrap (UInt32.toNat_inj.mp (by simpa only [UInt32.toNat_zero] using e))
          have wrapNat := UInt32.lt_iff_toNat_lt.mp wrap
          have lastNat : (l.dist - l.op - c.wnext).toNat = (l.dist - l.op).toNat - c.wnext.toNat :=
            Zlib.Inffast.Proofs.u32_toNat_sub (by omega)
          have mixedNat : ¬ (l.dist - l.op).toNat - c.wnext.toNat < l.len.toNat := by
            intro e; apply mixed; apply UInt32.lt_iff_toNat_lt.mpr; rwa [lastNat]
          have off : woff + c.wsize.toNat + c.wnext.toNat - (l.dist - l.op).toNat = woff + (c.wsize.toNat + c.wnext.toNat - (l.dist - l.op).toNat) := by omega
          simp only [Zlib.Inffast.Proofs.matchArr, countEq, route, ↓reduceIte, ← backNat, nz, wrapNat, mixedNat, off])
    · by_cases mixed : l.dist - l.op < l.len
      · obtain ⟨result, after, run, resultPacket,
            resultEq, bytes, write⟩ :=
          packet.copyMatch_window_contiguous_mixed_view
            separate left windowBranch validBack noWrap wrap
            wnextBound mixed different windowPtr windowGet
            windowSize outPtr outputPtr outputGet outputWrite
            outputSize outputRoom produced
        exact finish run resultPacket (by rw [resultEq])
          (by rw [resultEq]) (by rw [resultEq])
          (by rw [resultEq]) bytes
          (by simp [Zlib.Inffast.Proofs.cpyN_size,
            Zlib.Inffast.Proofs.blitN_size]) write (by
          have nz : c.wnext.toNat ≠ 0 := by
            intro e; exact noWrap (UInt32.toNat_inj.mp (by simpa only [UInt32.toNat_zero] using e))
          have wrapNat : ¬ c.wnext.toNat < (l.dist - l.op).toNat := by
            intro e; exact wrap (UInt32.lt_iff_toNat_lt.mpr e)
          have off : woff + c.wnext.toNat - (l.dist - l.op).toNat = woff + (c.wnext.toNat - (l.dist - l.op).toNat) := by omega
          have mixedNat := UInt32.lt_iff_toNat_lt.mp mixed
          simp only [Zlib.Inffast.Proofs.matchArr, countEq, route, ↓reduceIte, ← backNat, nz, wrapNat, mixedNat, off])
      · have wholeWindow : l.len.toNat ≤
            (l.dist - l.op).toNat := by
          have hnot : ¬ (l.dist - l.op).toNat < l.len.toNat := by
            intro hlt
            exact mixed (UInt32.lt_iff_toNat_lt.mpr hlt)
          omega
        obtain ⟨result, after, run, resultPacket,
            resultEq, bytes, write⟩ :=
          packet.copyMatch_window_contiguous_short_view
            separate left windowBranch validBack noWrap wrap
            wnextBound wholeWindow different windowPtr
            windowGet windowSize outPtr outputPtr outputGet
            outputWrite outputSize outputRoom
        exact finish run resultPacket (by rw [resultEq])
          (by rw [resultEq]) (by rw [resultEq])
          (by rw [resultEq]) bytes
          (by simp [Zlib.Inffast.Proofs.blitN_size]) write (by
          have nz : c.wnext.toNat ≠ 0 := by
            intro e; exact noWrap (UInt32.toNat_inj.mp (by simpa only [UInt32.toNat_zero] using e))
          have wrapNat : ¬ c.wnext.toNat < (l.dist - l.op).toNat := by
            intro e; exact wrap (UInt32.lt_iff_toNat_lt.mpr e)
          have off : woff + c.wnext.toNat - (l.dist - l.op).toNat = woff + (c.wnext.toNat - (l.dist - l.op).toNat) := by omega
          have mixedNat : ¬ (l.dist - l.op).toNat < l.len.toNat := by
            intro e; exact mixed (UInt32.lt_iff_toNat_lt.mpr e)
          simp only [Zlib.Inffast.Proofs.matchArr, countEq, route, ↓reduceIte, ← backNat, nz, wrapNat, mixedNat, off])

#print axioms FastInputPacket.copyMatch_window_array_view

/-- The actual generic-view window copier implements the independent chronological match. -/
theorem FastInputPacket.copyMatch_window_lz77_view
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    (packet : FastInputPacket h slow bs l)
    (separate : Separate slow.next slow.have_.toNat
      slow.put slow.left.toNat)
    (left : slow.left ≠ 0)
    (windowBranch : l.dist > l.op)
    (validBack : ¬ l.dist - l.op > c.whave)
    (whaveBound : c.whave.toNat ≤ c.wsize.toNat)
    (wnextBound : c.wnext.toNat ≤ c.wsize.toNat)
    (wsizeBound : c.wsize.toNat ≤ 32768)
    {window dest : BRef} (different : window ≠ dest)
    {saved output : Array UInt8} {woff oo j : Nat}
    (windowPtr : c.window = .ref window woff)
    (windowGet : Space.get h window = some saved)
    (windowSize : woff + c.wsize.toNat ≤ saved.size)
    (outPtr : l.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (outputGet : Space.get h dest = some output)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (outputRoom : oo ≤ j ∧
      j + l.len.toNat ≤ oo + slow.left.toNat)
    (produced : l.op.toNat ≤ j) :
    ∃ result after array,
      C.run (Zlib.Inffast.copyMatch c l) h =
        .ok (result, after) ∧
      FastInputPacket after slow bs result ∧
      result.out = .ref dest (j + l.len.toNat) ∧
      result.broke = l.broke ∧
      result.againD = l.againD ∧
      result.againL = l.againL ∧
      Space.get after dest = some array ∧
      array.size = output.size ∧
      Space.ro after dest = false ∧
      array = Zlib.Inffast.Proofs.matchArr c.wsize.toNat c.wnext.toNat woff saved (j - l.op.toNat) j l.dist.toNat l.len.toNat output ∧
      ZlibF.Math.LZ77Copy.writtenBytes array (j + l.len.toNat) (l.op.toNat + l.len.toNat) =
        ZlibF.Spec.copyBack (Zlib.Inffast.Spec.MatchHistory.saved saved c.wsize.toNat c.wnext.toNat c.whave.toNat woff)
          l.dist.toNat l.len.toNat (ZlibF.Math.LZ77Copy.writtenBytes output j l.op.toNat) := by
  obtain ⟨result, after, array, run, next, cursor, broke, againD, againL,
    get, size, ro, exactArray⟩ :=
    packet.copyMatch_window_array_view separate left windowBranch validBack whaveBound
      wnextBound wsizeBound different windowPtr windowGet windowSize outPtr outputPtr
      outputGet outputWrite outputSize outputRoom produced
  have distGt := UInt32.lt_iff_toNat_lt.mp windowBranch
  have backNat : (l.dist - l.op).toNat = l.dist.toNat - l.op.toNat :=
    Zlib.Inffast.Proofs.u32_toNat_sub (by omega)
  have backLe : (l.dist - l.op).toNat ≤ c.whave.toNat := by
    by_cases yes : (l.dist - l.op).toNat ≤ c.whave.toNat
    · exact yes
    · have tooFar : c.whave.toNat < (l.dist - l.op).toNat := by omega
      exact False.elim (validBack (UInt32.lt_iff_toNat_lt.mpr tooFar))
  have countEq : j - (j - l.op.toNat) = l.op.toNat := by omega
  have semantic := Zlib.Inffast.Proofs.fast_match_array_refines_lz77 saved output
    c.wsize.toNat c.wnext.toNat c.whave.toNat woff (j - l.op.toNat) j
    l.dist.toNat l.len.toNat whaveBound wnextBound (by intro _; exact windowSize)
    (by omega) (by omega) (by omega) (by rw [countEq]; omega)
  refine ⟨result, after, array, run, next, cursor, broke, againD, againL,
    get, size, ro, exactArray, ?_⟩
  rw [exactArray]
  simpa only [countEq] using semantic

#print axioms FastInputPacket.copyMatch_window_lz77_view

/-- Direct and chronological-window copies share the same actual output
semantics. The window only needs a physical view when this copy uses it. -/
theorem FastInputPacket.copyMatch_valid_lz77_view
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    (packet : FastInputPacket h slow bs l)
    (separate : Separate slow.next slow.have_.toNat slow.put slow.left.toNat)
    (left : slow.left ≠ 0) (length : 3 ≤ l.len.toNat)
    (distance : 0 < l.dist.toNat)
    (available : l.dist.toNat ≤ c.whave.toNat + l.op.toNat)
    (whaveBound : c.whave.toNat ≤ c.wsize.toNat)
    (wnextBound : c.wnext.toNat ≤ c.wsize.toNat)
    (wsizeBound : c.wsize.toNat ≤ 32768)
    {dest : BRef} {saved output : Array UInt8} {woff oo j : Nat}
    (outPtr : l.out = .ref dest j) (outputPtr : slow.put = .ref dest oo)
    (outputGet : Space.get h dest = some output) (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (outputRoom : oo ≤ j ∧ j + l.len.toNat ≤ oo + slow.left.toNat)
    (produced : l.op.toNat ≤ j)
    (windowData : l.dist > l.op → ∃ window,
      window ≠ dest ∧ c.window = .ref window woff ∧
      Space.get h window = some saved ∧ woff + c.wsize.toNat ≤ saved.size) :
    ∃ result after array,
      C.run (Zlib.Inffast.copyMatch c l) h = .ok (result, after) ∧
      FastInputPacket after slow bs result ∧
      result.out = .ref dest (j + l.len.toNat) ∧
      result.broke = l.broke ∧ result.againD = l.againD ∧ result.againL = l.againL ∧
      Space.get after dest = some array ∧ array.size = output.size ∧ Space.ro after dest = false ∧
      array = Zlib.Inffast.Proofs.matchArr c.wsize.toNat c.wnext.toNat woff saved
        (j - l.op.toNat) j l.dist.toNat l.len.toNat output ∧
      ZlibF.Math.LZ77Copy.writtenBytes array (j + l.len.toNat) (l.op.toNat + l.len.toNat) =
        ZlibF.Spec.copyBack (Zlib.Inffast.Spec.MatchHistory.saved saved
          c.wsize.toNat c.wnext.toNat c.whave.toNat woff)
          l.dist.toNat l.len.toNat (ZlibF.Math.LZ77Copy.writtenBytes output j l.op.toNat) := by
  by_cases branch : l.dist > l.op
  · obtain ⟨window, different, windowPtr, windowGet, windowSize⟩ := windowData branch
    have backNat : (l.dist - l.op).toNat = l.dist.toNat - l.op.toNat :=
      Zlib.Inffast.Proofs.u32_toNat_sub (by have := UInt32.lt_iff_toNat_lt.mp branch; omega)
    have validBack : ¬ l.dist - l.op > c.whave := by
      intro invalid
      have ht := UInt32.lt_iff_toNat_lt.mp invalid
      omega
    exact packet.copyMatch_window_lz77_view separate left branch validBack whaveBound
      wnextBound wsizeBound different windowPtr windowGet windowSize outPtr outputPtr
      outputGet outputWrite outputSize outputRoom produced
  · have directCount : l.dist.toNat ≤ l.op.toNat := by
      by_cases yes : l.dist.toNat ≤ l.op.toNat
      · exact yes
      · have tooFar : l.op.toNat < l.dist.toNat := by omega
        exact False.elim (branch (UInt32.lt_iff_toNat_lt.mpr tooFar))
    obtain ⟨result, after, run, next, resultEq, get, ro⟩ :=
      packet.copyMatch_direct_view separate left branch (by omega) length outPtr outputPtr
        outputGet outputWrite outputSize outputRoom
    let array := Zlib.Inffast.Proofs.cpyN l.len.toNat (j - l.dist.toNat) j output
    have countEq : j - (j - l.op.toNat) = l.op.toNat := by omega
    have exactArray : array = Zlib.Inffast.Proofs.matchArr c.wsize.toNat c.wnext.toNat woff
        saved (j - l.op.toNat) j l.dist.toNat l.len.toNat output := by
      simp only [Zlib.Inffast.Proofs.matchArr, countEq,
        show ¬ l.op.toNat < l.dist.toNat by omega, ↓reduceIte]
      rfl
    have semantic := ZlibF.Math.LZ77Copy.output_copy_refines_lz77
      (Zlib.Inffast.Spec.MatchHistory.saved saved c.wsize.toNat c.wnext.toNat c.whave.toNat woff)
      output j l.op.toNat l.dist.toNat l.len.toNat produced distance directCount (by omega)
    exact ⟨result, after, array, run, next, by rw [resultEq], by rw [resultEq],
      by rw [resultEq], by rw [resultEq], get, Zlib.Inffast.Proofs.cpyN_size .., ro,
      exactArray, semantic⟩

#print axioms FastInputPacket.copyMatch_valid_lz77_view

end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec

/-- The actual valid `copyMatch` operation refines one independent length/
distance token once the source decoders and the saved-history representation
identify its numerical fields. Input and output may occupy disjoint slices
of the same byte object. -/
theorem FastInputPacket.copyMatch_valid_token_view
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    (packet : FastInputPacket h slow bs l)
    (separate : Separate slow.next slow.have_.toNat
      slow.put slow.left.toNat)
    (left : slow.left ≠ 0) (length : 3 ≤ l.len.toNat)
    (distance : 0 < l.dist.toNat)
    (available : l.dist.toNat ≤ c.whave.toNat + l.op.toNat)
    (whaveBound : c.whave.toNat ≤ c.wsize.toNat)
    (wnextBound : c.wnext.toNat ≤ c.wsize.toNat)
    (wsizeBound : c.wsize.toNat ≤ 32768)
    {dest : BRef} {saved output : Array UInt8}
    {woff oo j : Nat}
    (outPtr : l.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (outputGet : Space.get h dest = some output)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (outputRoom : oo ≤ j ∧ j + l.len.toNat ≤ oo + slow.left.toNat)
    (produced : l.op.toNat ≤ j)
    (windowData : l.dist > l.op → ∃ window,
      window ≠ dest ∧ c.window = .ref window woff ∧
      Space.get h window = some saved ∧
      woff + c.wsize.toNat ≤ saved.size)
    {L D : List Nat} {dict history : List UInt8}
    {input r1 r2 r3 rest : List Bool}
    {symbol distanceSymbol lengthExtra distanceExtra : Nat}
    (source : stream slow bs = rest)
    (lengthCode : decodeSym L input = some (symbol, r1))
    (lengthSymbolMin : 257 ≤ symbol)
    (lengthSymbolMax : symbol ≤ 285)
    (lengthBits : readBits
      (lengthExtras.getD (symbol - 257) 0) r1 =
      some (lengthExtra, r2))
    (distanceCode : decodeSym D r2 = some (distanceSymbol, r3))
    (distanceSymbolBound : distanceSymbol ≤ 29)
    (distanceBits : readBits
      (distExtras.getD distanceSymbol 0) r3 =
      some (distanceExtra, rest))
    (lengthValue : l.len.toNat =
      lengthBases.getD (symbol - 257) 0 + lengthExtra)
    (distanceValue : l.dist.toNat =
      distBases.getD distanceSymbol 0 + distanceExtra)
    (dictionary : Zlib.Inffast.Spec.MatchHistory.saved saved
      c.wsize.toNat c.wnext.toNat c.whave.toNat woff = dict)
    (written : ZlibF.Math.LZ77Copy.writtenBytes output j
      l.op.toNat = history)
    (backBound : l.dist.toNat ≤ (dict ++ history).length) :
    ∃ result after array,
      C.run (Zlib.Inffast.copyMatch c l) h = .ok (result, after) ∧
      FastInputPacket after slow bs result ∧
      result.out = .ref dest (j + l.len.toNat) ∧
      Space.get after dest = some array ∧
      ZlibF.Math.LZ77Copy.writtenBytes array
        (j + l.len.toNat) (l.op.toNat + l.len.toNat) =
        ZlibF.Spec.copyBack dict l.dist.toNat l.len.toNat history ∧
      (bs ≠ [] → Bytes after slow.next slow.have_.toNat bs) ∧
      stream slow bs = rest ∧
      ZlibF.Spec.Token.Step L D dict history input rest
        (ZlibF.Math.LZ77Copy.writtenBytes array
          (j + l.len.toNat) (l.op.toNat + l.len.toNat)) false := by
  obtain ⟨result, after, array, run, next, cursor,
    _, _, _, get, _, _, _, exactCopy⟩ :=
    packet.copyMatch_valid_lz77_view separate left length
      distance available whaveBound wnextBound wsizeBound
      outPtr outputPtr outputGet outputWrite outputSize
      outputRoom produced windowData
  have physical : ZlibF.Math.LZ77Copy.writtenBytes array
      (j + l.len.toNat) (l.op.toNat + l.len.toNat) =
      ZlibF.Spec.copyBack dict l.dist.toNat l.len.toNat history := by
    simpa only [dictionary, written] using exactCopy
  have inputBytes : bs ≠ [] → Bytes after
      slow.next slow.have_.toNat bs := by
    intro nonempty
    have actual := next.source.input_slice_of_nonempty nonempty
    simpa only [next.cursor] using actual
  have token : ZlibF.Spec.Token.Step L D dict history input rest
      (ZlibF.Math.LZ77Copy.writtenBytes array
        (j + l.len.toNat) (l.op.toNat + l.len.toNat)) false := by
    rw [physical, lengthValue, distanceValue]
    exact ZlibF.Spec.Token.Step.copy lengthCode lengthSymbolMin
      lengthSymbolMax lengthBits distanceCode distanceSymbolBound
      distanceBits (by simpa only [distanceValue] using backBound)
  exact ⟨result, after, array, run, next, cursor,
    get, physical, inputBytes, source, token⟩

#print axioms FastInputPacket.copyMatch_valid_token_view
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec

/-- The actual distance extra-bit suffix consumes exactly the independent
low-bit read. This strengthens the source-backed `distCont_post` result with
the numerical extra value used to update the distance register. -/
theorem FastInputPacket.distCont_extra_semantics
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow bs l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow bs)
    (streamPtr : c.strm = some r)
    (statePtr : c.state = some (.tab zs))
    (whaveEq : c.whave = s.whave)
    (wsizeEq : c.wsize = s.wsize)
    (wnextEq : c.wnext = s.wnext)
    (windowEq : c.window = s.window)
    (extraBits : l.op.toNat ≤ slow.bits.toNat)
    (extraSmall : l.op.toNat < 32)
    (left : slow.left ≠ 0)
    (avail : 258 ≤ slow.left.toNat)
    (length : 3 ≤ l.len.toNat ∧ l.len.toNat ≤ 258)
    {dest : BRef} {output : Array UInt8} {oo bg j : Nat}
    (outPtr : l.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (begPtr : c.beg = .ref dest bg)
    (endPtr : c.end_ = .ref dest
      (oo + slow.left.toNat - 257))
    (outputGet : Space.get h dest = some output)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (current : oo ≤ j)
    (beginLe : bg ≤ j)
    (span : j - bg < 2 ^ 32)
    (guard : C.run (Ptr.lt l.out c.end_) h = .ok (true, h)) :
    let extra := l.hold.toNat % 2 ^ l.op.toNat
    let slowNext : IL := { slow with
      hold := slow.hold >>> l.op.toUInt64,
      bits := slow.bits - l.op }
    ∃ result after,
      C.run (Zlib.Inffast.Proofs.distCont c l) h =
        .ok (result, after) ∧
      FastDistancePost h after r zs z s slowNext bs result
        dest output j l.len.toNat ∧
      readBits l.op.toNat (stream slow bs) =
        some (extra, stream slowNext bs) ∧
      (l.dist + (l.hold.toUInt32 &&&
        (((1 : UInt32) <<< l.op) - 1))).toNat =
        (l.dist.toNat + extra) % 2 ^ 32 := by
  obtain ⟨result, after, run, post, sourceDrop⟩ :=
    packet.distCont_post invariant buffers streamPtr
      statePtr whaveEq wsizeEq wnextEq windowEq
      extraBits extraSmall left avail length outPtr
      outputPtr begPtr endPtr outputGet outputWrite
      outputSize current beginLe span guard
  have read := readBits_held_stream slow bs l.op.toNat extraBits
  have extraEq : (l.hold.toUInt32 &&&
      (((1 : UInt32) <<< l.op) - 1)).toNat =
      l.hold.toNat % 2 ^ l.op.toNat :=
    Zlib.Inffast.Proofs.hold_low32 extraSmall
  have distanceEq :
      (l.dist + (l.hold.toUInt32 &&&
        (((1 : UInt32) <<< l.op) - 1))).toNat =
      (l.dist.toNat + l.hold.toNat % 2 ^ l.op.toNat) % 2 ^ 32 := by
    rw [UInt32.toNat_add, extraEq]
  refine ⟨result, after, run, post, ?_, distanceEq⟩
  rw [← sourceDrop] at read
  simpa only [packet.hold] using read

#print axioms FastInputPacket.distCont_extra_semantics
end Zlib.Inflate.Proofs

