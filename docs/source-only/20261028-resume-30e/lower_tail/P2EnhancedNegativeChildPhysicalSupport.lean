import ImbalancedChen.P2EnhancedNegativeChildRosser
import ImbalancedChen.P2OriginalNegativeSingleSameQSupport

/-! SOURCE ONLY / UNCOMPILED / ZERO CREDIT.
Bind the independent count coefficient to the independently frozen
original-window square-support supplier. The only input gates are for
the actual old tagged prefix. No output square gate, adopted L5/L6 plan,
ordinary-rho enhancement or action soundness is assumed. -/

namespace ImbalancedChen.P2EnhancedNegativeChildPhysicalSupport

noncomputable section
open scoped Classical
open P2EnhancedNegativeChildRosser
open P2OriginalSelectedIntegerPrefixSquares P2OriginalSelectedNativeSmallExtension

/-- Independent definitions coincide literally at the old d*N mask,
original a cutoff and common-Q residual level Q/(d*p). -/
theorem childCoefficient_eq_original (N : ℕ) (Q : ℝ) (d p k : ℕ) :
    childCoefficient N Q d p k =
      P2OriginalNegativeSingleSameQSupport.ordinaryChildLower N Q d p k := rfl

/-- The actual coefficient in the three negative count estimators carries
the full and selected-complement squares through its actual prime word. -/
theorem count_coefficient_complete_gates (N : ℕ) (cap : ℝ) {d p k : ℕ}
    (hd : 0 < d) (hR : 1 < (N : ℝ)^cap / (d : ℝ)) (j : Fin 3)
    (hp : p ∈ P2OriginalNegativeSingleSameQSupport.negativeWindow N ((N : ℝ)^cap) d j)
    (hk : childCoefficient N ((N : ℝ)^cap) d p k ≠ 0)
    (old : List (ℕ × Bool)) (holdprod : (old.map Prod.fst).prod = d)
    (hfull : IntegerSquareGates N cap 1 (old.map Prod.fst))
    (hselected : IntegerSquareGates N cap (selectedPrimes old).prod (remainingPrimes old)) :
    let afterP := appendUnselected old [p]
    let whole := appendUnselected afterP k.primeFactorsList.reverse
    IntegerSquareGates N cap 1 (whole.map Prod.fst) ∧
      IntegerSquareGates N cap (selectedPrimes whole).prod (remainingPrimes whole) ∧
      selectedPrimes whole = selectedPrimes old ∧
      (whole.map Prod.fst).prod = (d * p) * k ∧
      (((d * p) * k : ℕ) : ℝ) < (N : ℝ)^cap := by
  exact P2OriginalNegativeSingleSameQSupport.negative_single_native_complete_gates
    N cap hd hR j hp (by simpa only [childCoefficient_eq_original] using hk)
    old holdprod hfull hselected

end
end ImbalancedChen.P2EnhancedNegativeChildPhysicalSupport
