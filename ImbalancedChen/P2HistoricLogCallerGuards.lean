import ImbalancedChen.P2HistoricLogCallerCore
import ImbalancedChen.P2HistoricLogPointInterpreter
import ImbalancedChen.P2HistoricQ80OrdinaryEstimatorSoundness
import ImbalancedChen.P2HistoricChordDivisorGuard
import ImbalancedChen.Certificates.PairedV2FullMask

/-!
SOURCE ONLY / UNCOMPILED.

Actual nonenhanced/nondiagonal pair_cell in certify_sharp_184_baseline.py
(a4ebffaf2b13123cf8d7510fed18482f85ec1a79f1bcddb220bd3d3ec8197639)
calls log(I(tR/tL)) and log(I(uR/uL)). Its affine moments reuse these two
cached logs; there is no additional logarithm of an affine expression in
this branch. All 512-by-512 parent rectangles, hence every adopted row,
have both ratios >=1 and strictly positive rounded I80 lower endpoints.

The interval wrapper below keeps the original positive rounded-lower guard
for arbitrary intervals. Actual grid specializations prove that guard from
the imported knots. The final ordinary-estimator adapter removes both
logarithm-query premises, retaining the separate sf/divisor obligations.
-/

namespace ImbalancedChen.Certificates.P2HistoricLogCallerGuards

open P2HistoricQ80DefectLookup P2HistoricLogPointInterpreter
open PairedV2
open ImbalancedChen.P2SavedFloorSemantics
open ImbalancedChen.P2HistoricQ80OrdinaryEstimatorSoundness

noncomputable section

/-- Ordinary-estimator soundness with the historical log backend completely
closed. The sf backend and eligible chord divisors retain their own licences. -/
theorem savedOrdinaryRectangle_actual_lower_logClosed (sf : ℚ → I80)
    (tl tr ul ur : ℚ) (htl : (0 : ℝ) < tl) (hul : (0 : ℝ) < ul)
    (ht : tl ≤ tr) (hu : ul ≤ ur) (hHigh : (25 / 128 : ℚ) ≤ tl)
    (hsf : ∀ q : ℚ, (sf q).Contains (actualExtendedThirdLowerFactor (q : ℝ)))
    (hden₀ : chordEligible ordinaryPlane₀ ordinaryPlane₁ tl tr ul ur →
      0 < (I80.point ((affineRange ordinaryPlane₀ tl tr ul ur).2 -
        (affineRange ordinaryPlane₀ tl tr ul ur).1)).lo)
    (hden₁ : chordEligible ordinaryPlane₁ ordinaryPlane₀ tl tr ul ur →
      0 < (I80.point ((affineRange ordinaryPlane₁ tl tr ul ur).2 -
        (affineRange ordinaryPlane₁ tl tr ul ur).1)).lo) :
    ((((savedOrdinaryRectangle sf logI tl tr ul ur : ℤ) : ℚ) / Q : ℚ) : ℝ) ≤
      ordinaryCellIntegral tl tr ul ur := by
  have htlQ : (0 : ℚ) < tl := by exact_mod_cast htl
  have hulQ : (0 : ℚ) < ul := by exact_mod_cast hul
  obtain ⟨hT, hU⟩ := rectangle_log_contract htlQ hulQ ht hu
  exact savedOrdinaryRectangle_actual_lower sf logI tl tr ul ur
    htl hul ht hu hHigh hsf hT hU hden₀ hden₁

/-- Concrete 512-parent consumer: the existing actual knot divisor theorem
and this module's literal log contracts remove every log/divisor query
guard. The separate sf semantic licence is the only backend premise. -/
theorem parent_savedOrdinaryRectangle_actual_lower_logClosed (sf : ℚ → I80)
    (i j : Fin 512)
    (hsf : ∀ q : ℚ, (sf q).Contains (actualExtendedThirdLowerFactor (q : ℝ))) :
    ((((savedOrdinaryRectangle sf logI (tLower i.val) (tUpper i.val)
      (uLower j.val) (uUpper j.val) : ℤ) : ℚ) / Q : ℚ) : ℝ) ≤
      ordinaryCellIntegral (tLower i.val) (tUpper i.val) (uLower j.val) (uUpper j.val) := by
  obtain ⟨hT, hU⟩ := grid_log_contract i.val j.val
  exact ImbalancedChen.P2HistoricChordDivisorGuard.parent_savedOrdinaryRectangle_actual_lower
    sf logI i.val j.val i.isLt j.isLt hsf hT hU

/-- Every one of the 17572 actual adopted rows receives the same fully
closed log/divisor backend, without an arbitrary global log guard. -/
theorem adopted_savedOrdinaryRectangle_actual_lower_logClosed (sf : ℚ → I80)
    (r : FullMask.Row)
    (hsf : ∀ q : ℚ, (sf q).Contains (actualExtendedThirdLowerFactor (q : ℝ))) :
    ((((savedOrdinaryRectangle sf logI
      (tLower (FullMask.indices r).1) (tUpper (FullMask.indices r).1)
      (uLower (FullMask.indices r).2) (uUpper (FullMask.indices r).2) : ℤ) : ℚ) / Q : ℚ) : ℝ) ≤
      ordinaryCellIntegral
        (tLower (FullMask.indices r).1) (tUpper (FullMask.indices r).1)
        (uLower (FullMask.indices r).2) (uUpper (FullMask.indices r).2) := by
  obtain ⟨hi, _, hj⟩ := FullMask.indices_bounds r
  exact parent_savedOrdinaryRectangle_actual_lower_logClosed sf
    ⟨(FullMask.indices r).1, hi⟩ ⟨(FullMask.indices r).2, hj⟩ hsf

end

end ImbalancedChen.Certificates.P2HistoricLogCallerGuards
