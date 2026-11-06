import ZlibF.Spec.InflateFastMatchHistory
import ZlibF.Math.LZ77Copy
import ZlibF.Math.LZ77History

/-!
# The fast copier's physical pieces form one independent match

Every window segment is related to its chronological ring position. The
pieces are then joined with the bytewise copyBack composition theorem.
-/

set_option autoImplicit false

namespace Zlib.Inffast.Proofs
open C Zlib.Inffast.Spec Zlib.Inffast.Spec.MatchHistory
open ZlibF.Spec ZlibF.Math.LZ77Copy ZlibF.Math.LZ77History
open Zlib.Inflate.Spec (ringSlot)

private theorem saved_length (W : Array UInt8) (ws wn wh woff : Nat) :
    (saved W ws wn wh woff).length = wh := by simp [saved]

private theorem saved_get (W : Array UInt8) (ws wn wh woff j : Nat) (hj : j < wh) :
    (saved W ws wn wh woff).getD j 0 = W.getD (woff + ringSlot ws wn wh j) 0 := by
  have hlen : j < (saved W ws wn wh woff).length := by simpa [saved] using hj
  rw [← List.getElem_eq_getD (h := hlen) 0]
  simp only [saved, List.getElem_map, List.getElem_range]

private theorem before_wrap (ws wn wh back i : Nat)
    (hwh : wh ≤ ws) (hb : back ≤ wh) (hw : wn < back) (hi : i < back - wn) :
    ringSlot ws wn wh (wh - back + i) = ws + wn - back + i := by
  have hfull : ¬ wh ≤ wn := by omega
  have hindex : wh - back + i < wh - wn := by omega
  simp only [ringSlot, hfull, hindex, ite_false, ite_true]
  omega

private theorem after_wrap (ws wn wh back i : Nat)
    (hb : back ≤ wh) (hw : wn < back) (hi : i < wn) :
    ringSlot ws wn wh (wh - wn + i) = i := by
  have hfull : ¬ wh ≤ wn := by omega
  have hindex : ¬ wh - wn + i < wh - wn := by omega
  simp only [ringSlot, hfull, hindex, ite_false]
  omega

private theorem no_wrap (ws wn wh back i : Nat)
    (hb : back ≤ wh) (hw : back ≤ wn) (hi : i < back) :
    ringSlot ws wn wh (wh - back + i) = wn - back + i := by
  by_cases hfull : wh ≤ wn
  · simp only [ringSlot, hfull, ite_true]
    omega
  · have hindex : ¬ wh - back + i < wh - wn := by omega
    simp only [ringSlot, hfull, hindex, ite_false]
    omega

/-- Both window segments, followed by overlapping output if necessary,
implement one independent copyBack on the actual chronological history. -/
theorem fast_match_array_refines_lz77 : MatchHistory.Goal.match_array_refines_lz77 := by
  intro W A ws wn wh woff bg o dist len hwh hwn hW hbg hroom hd havail
  let count := o - bg
  let history := saved W ws wn wh woff
  let current := writtenBytes A o count
  have hcount : count ≤ o := by dsimp [count]; omega
  have hhistory : history.length = wh := saved_length W ws wn wh woff
  by_cases route : o - bg < dist
  · let back := dist - count
    have hroute : count < dist := route
    have hback : 0 < back ∧ back ≤ wh := by dsimp [back]; dsimp [count] at *; omega
    have hstorage : woff + ws ≤ W.size := hW (by omega)
    have first : ∀ (n sourceOffset : Nat), n ≤ back → o + n ≤ A.size →
        sourceOffset + n ≤ W.size →
        (∀ i, i < n → W.getD (sourceOffset + i) 0 =
          history.getD (history.length + count - dist + i) 0) →
        writtenBytes (blitN W n sourceOffset o A) (o + n) (count + n) =
          copyBack history dist n current := by
      intro n sourceOffset hn hr hs hp
      exact window_copy_refines_lz77 history A W o count sourceOffset dist n
        hcount hroute (by rw [hhistory]; exact havail) (by dsimp [back] at hn; exact hn) hr hs hp
    have finish : ∀ (B : Array UInt8) (k : Nat),
        B.size = A.size → k ≤ len → dist ≤ count + k →
        writtenBytes B (o + k) (count + k) = copyBack history dist k current →
        writtenBytes (cpyN (len - k) (o + k - dist) (o + k) B)
          (o + len) (count + len) = copyBack history dist len current := by
      intro B k hsz hk hdist hp
      have H := output_copy_refines_lz77 history B (o + k) (count + k) dist (len - k)
        (by omega) hd hdist (by omega)
      have hoff : o + k + (len - k) = o + len := by omega
      have hc : count + k + (len - k) = count + len := by omega
      rw [hoff, hc, hp, ← copy_back_compose] at H
      simpa only [show k + (len - k) = len by omega] using H
    by_cases hzero : wn = 0
    · have segment : ∀ n, n ≤ back → n ≤ len →
          writtenBytes (blitN W n (woff + ws - back) o A) (o + n) (count + n) =
            copyBack history dist n current := by
        intro n hn hlen
        apply first n (woff + ws - back) hn (by omega) (by omega)
        intro i hi
        have hj : history.length + count - dist + i < wh := by rw [hhistory]; dsimp [back] at hn; omega
        have hidx : history.length + count - dist + i = wh - back + i := by rw [hhistory]; dsimp [back]; omega
        rw [hidx, saved_get W ws wn wh woff _ (by omega)]
        rw [before_wrap ws wn wh back i hwh hback.2 (by omega) (by omega)]
        congr 1
        omega
      by_cases hlen : back < len
      · have hprefix := segment back (by omega) (by omega)
        have H := finish (blitN W back (woff + ws - back) o A) back
          (blitN_size ..) (by omega) (by dsimp [back]; omega) hprefix
        simpa [matchArr, route, hzero, hlen, back, count, history, current] using H
      · have H := segment len (by omega) (by omega)
        simpa [matchArr, route, hzero, hlen, back, count, history, current] using H
    · by_cases hwrap : wn < back
      · let k := back - wn
        have hkpos : 0 < k := by dsimp [k]; omega
        have segment : ∀ n, n ≤ k → n ≤ len →
            writtenBytes (blitN W n (woff + ws + wn - back) o A) (o + n) (count + n) =
              copyBack history dist n current := by
          intro n hn hlen
          apply first n (woff + ws + wn - back) (by dsimp [k] at hn; omega) (by omega) (by dsimp [k] at hn; omega)
          intro i hi
          have hidx : history.length + count - dist + i = wh - back + i := by rw [hhistory]; dsimp [back]; omega
          rw [hidx, saved_get W ws wn wh woff _ (by dsimp [k] at hn; omega)]
          rw [before_wrap ws wn wh back i hwh hback.2 hwrap (by dsimp [k] at hn; omega)]
          congr 1
          omega
        by_cases hlen1 : k < len
        · let B := blitN W k (woff + ws + wn - back) o A
          have hB : B.size = A.size := blitN_size ..
          have hfirst := segment k (by omega) (by omega)
          have second : ∀ n, n ≤ wn → n ≤ len - k →
              writtenBytes (blitN W n woff (o + k) B) (o + k + n) (count + k + n) =
                copyBack history dist (k + n) current := by
            intro n hn hlen
            have H := window_copy_refines_lz77 history B W (o + k) (count + k) woff dist n
              (by omega) (by dsimp [k, back]; omega) (by rw [hhistory]; omega)
              (by dsimp [k, back]; omega) (by omega) (by omega) ?_
            · rw [show writtenBytes B (o + k) (count + k) = copyBack history dist k current from hfirst,
                ← copy_back_compose] at H
              exact H
            · intro i hi
              have hidx : history.length + (count + k) - dist + i = wh - wn + i := by
                rw [hhistory]; dsimp [k, back]; omega
              rw [hidx, saved_get W ws wn wh woff _ (by omega)]
              rw [after_wrap ws wn wh back i hback.2 hwrap (by omega)]
          by_cases hlen2 : wn < len - k
          · have hsecond := second wn (by omega) (by omega)
            have heq : k + wn = back := by dsimp [k]; omega
            have hprefix : writtenBytes (blitN W wn woff (o + k) B) (o + back) (count + back) =
                copyBack history dist back current := by simpa only [Nat.add_assoc, heq] using hsecond
            have H := finish (blitN W wn woff (o + k) B) back
              (by simp only [blitN_size]; exact hB) (by dsimp [k] at hlen2; omega)
              (by dsimp [back]; omega) hprefix
            have hlenrem : len - k - wn = len - back := by dsimp [k]; omega
            simpa [matchArr, route, hzero, hwrap, hlen1, hlen2, hlenrem, B, k, back, count,
              history, current, Nat.add_assoc, heq] using H
          · have H := second (len - k) (by omega) (by omega)
            have hlenfull : k + (len - k) = len := by omega
            simpa [matchArr, route, hzero, hwrap, hlen1, hlen2, B, k, back, count,
              history, current, Nat.add_assoc, hlenfull] using H
        · have H := segment len (by omega) (by omega)
          simpa [matchArr, route, hzero, hwrap, hlen1, k, back, count, history, current] using H
      · have segment : ∀ n, n ≤ back → n ≤ len →
            writtenBytes (blitN W n (woff + wn - back) o A) (o + n) (count + n) =
              copyBack history dist n current := by
          intro n hn hlen
          apply first n (woff + wn - back) hn (by omega) (by omega)
          intro i hi
          have hidx : history.length + count - dist + i = wh - back + i := by rw [hhistory]; dsimp [back]; omega
          rw [hidx, saved_get W ws wn wh woff _ (by omega)]
          rw [no_wrap ws wn wh back i hback.2 (by omega) (by omega)]
          congr 1
          omega
        by_cases hlen : back < len
        · have H := finish (blitN W back (woff + wn - back) o A) back
            (blitN_size ..) (by omega) (by dsimp [back]; omega) (segment back (by omega) (by omega))
          simpa [matchArr, route, hzero, hwrap, hlen, back, count, history, current] using H
        · have H := segment len (by omega) (by omega)
          simpa [matchArr, route, hzero, hwrap, hlen, back, count, history, current] using H
  · have H := output_copy_refines_lz77 (saved W ws wn wh woff) A o (o - bg) dist len
      (by omega) hd (by omega) hroom
    simpa only [matchArr, route, ite_false] using H

end Zlib.Inffast.Proofs
