import ImbalancedChen.Part3OriginalClassicalCommonPoissonSupport

open ImbalancedChen.Part3.OriginalCommonPoissonLanes20261102
open ImbalancedChen.Part3.OriginalClassicalSpectralSupports20261102

example : classicalMScale 0 = (1 : ℝ) / 2 := by
  norm_num [classicalMScale]

example (k1 : ℤ) :
    (1 : ℝ) ∈ Set.Ioc (classicalMScale 0) (2 * classicalMScale 0) ∧
    (commonPoissonCompleted 1 0 k1).weight 1 =
      Complex.exp (2*(Real.pi : ℂ)*Complex.I*
        ((k1 : ℝ)/(64*(2^0 : ℕ)) : ℝ)*(1 : ℂ)) := by
  have hm : 1 ∈ commonMBlock 1 0 := by decide
  simpa only [Nat.cast_one] using (commonPoissonCompleted_classical_support 1 0 k1 hm).2

example : commonMBlock 0 0 = ∅ := by decide
