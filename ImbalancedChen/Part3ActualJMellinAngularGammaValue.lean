import ImbalancedChen.Part3ActualJMellinBoundaryPhasePair

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-26.

The actual boundary angular integral is evaluated, with no angular-value
assumption, by pairing its two half intervals and consuming the genuine
complex-power Poisson moment. The resulting Gamma product is still shown
explicitly before its final duplication/reflection simplification.
-/

namespace ImbalancedChen.Part3.ActualJMellinAngularGammaValue20261026b

noncomputable section
open Complex Set MeasureTheory
open ActualJMellinBoundaryPhasePair20261026b ActualJMellinAngularAbelLimit20261026b
open ActualJMellinPoissonGammaReduction20261026b ActualJFixedOrderMellinL120261026b
open PoissonComplexPowerMoment20261026b

def angularBoundaryGammaValue (s : ℂ) (t : ℝ) : ℂ :=
  Complex.cos ((Real.pi : ℂ) * (s + 2 * I * (t : ℂ)) / 2) *
    Gamma (s + 2 * I * (t : ℂ)) * Gamma ((1 - (s + 2 * I * (t : ℂ))) / 2) *
      Gamma (2 * I * (t : ℂ) + 1 / 2) /
        Gamma ((1 - (s + 2 * I * (t : ℂ))) / 2 + 2 * I * (t : ℂ) + 1 / 2)

private theorem boundary_integral_half_pair {s : ℂ}
    (hs0 : 0 < s.re) (hs1 : s.re < 1) (t : ℝ) :
    angularBoundaryIntegral s t = ∫ u in Ioo (0 : ℝ) 1,
      (angularBoundaryIntegrand s t u + angularBoundaryIntegrand s t (-u)) := by
  have hi := angularBoundaryIntegrand_integrable hs0 hs1 t
  have hp : IntervalIntegrable (angularBoundaryIntegrand s t) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)).2
      (hi.mono_set (fun u hu => ⟨by linarith [hu.1], hu.2⟩))
  have hn : IntervalIntegrable (angularBoundaryIntegrand s t) volume (-1) 0 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (-1 : ℝ) ≤ 0)).2
      (hi.mono_set (fun u hu => ⟨hu.1, by linarith [hu.2]⟩))
  have hc : IntervalIntegrable (fun u => angularBoundaryIntegrand s t (-u)) volume 0 1 := by
    have h := (IntervalIntegrable.iff_comp_neg).mp hn
    simpa only [neg_neg, neg_zero] using h.symm
  have hneg : (∫ u in (-1 : ℝ)..0, angularBoundaryIntegrand s t u) =
      ∫ u in (0 : ℝ)..1, angularBoundaryIntegrand s t (-u) := by
    simpa only [neg_zero, neg_one] using
      (intervalIntegral.integral_comp_neg (angularBoundaryIntegrand s t)
        (a := (0 : ℝ)) (b := 1)).symm
  unfold angularBoundaryIntegral
  rw [← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
    ← intervalIntegral.integral_add_adjacent_intervals hn hp, hneg, add_comm,
    ← intervalIntegral.integral_add hp hc,
    intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), integral_Ioc_eq_integral_Ioo]

/-- Actual angular Gamma evaluation derived from the positive-square
Beta Jacobian and the native principal imaginary-axis phases. -/
theorem angularBoundaryIntegral_eq_gamma {s : ℂ}
    (hs0 : 0 < s.re) (hs1 : s.re < 1) (t : ℝ) :
    angularBoundaryIntegral s t = angularBoundaryGammaValue s t := by
  let a : ℂ := s + 2 * I * (t : ℂ)
  let nu : ℂ := 2 * I * (t : ℂ)
  have hre : a.re = s.re := by dsimp [a]; simp
  have ha : 0 < (1 - a).re := by
    rw [Complex.sub_re, Complex.one_re, hre]
    linarith
  have hn : -(1 / 2 : ℝ) < nu.re := by dsimp [nu]; simp
  have hm := poissonPowerMoment_half_integral ha hn
  calc
    angularBoundaryIntegral s t = ∫ u in Ioo (0 : ℝ) 1,
        (2 * Complex.cos ((Real.pi : ℂ) * a / 2) * Gamma a) *
          poissonPowerMoment (1 - a) nu u := by
      rw [boundary_integral_half_pair hs0 hs1 t]
      apply setIntegral_congr_fun measurableSet_Ioo
      intro u hu
      exact angularBoundaryIntegrand_pair s t hu
    _ = (2 * Complex.cos ((Real.pi : ℂ) * a / 2) * Gamma a) *
        ∫ u in Ioo (0 : ℝ) 1, poissonPowerMoment (1 - a) nu u := integral_const_mul _ _
    _ = (Complex.cos ((Real.pi : ℂ) * a / 2) * Gamma a) *
        (2 * ∫ u in Ioo (0 : ℝ) 1, poissonPowerMoment (1 - a) nu u) := by ring
    _ = (Complex.cos ((Real.pi : ℂ) * a / 2) * Gamma a) *
        (Gamma ((1 - a) / 2) * Gamma (nu + 1 / 2) /
          Gamma ((1 - a) / 2 + nu + 1 / 2)) := by rw [hm]
    _ = angularBoundaryGammaValue s t := by unfold angularBoundaryGammaValue; dsimp [a, nu]; ring

/-- First honest evaluated form of the actual full J Mellin integral.
Its canonical single-Gamma-ratio simplification is a separate next step. -/
theorem actualJMellinIntegral_eq_gamma_product {s : ℂ}
    (hs0 : 0 < s.re) (hsHalf : s.re < 1 / 2) (t : ℝ) :
    actualJMellinIntegral s t = poissonMellinConstant t * angularBoundaryGammaValue s t := by
  rw [actualJMellinIntegral_eq_angularBoundary hs0 hsHalf t,
    angularBoundaryIntegral_eq_gamma hs0 (by linarith : s.re < 1) t]

end
end ImbalancedChen.Part3.ActualJMellinAngularGammaValue20261026b
