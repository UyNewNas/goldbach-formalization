import ImbalancedChen.Part3ActualRealOrderJAbelPoisson
import ImbalancedChen.Part3ActualJAngularAbelRateBound
import ImbalancedChen.Part3ActualJMellinBoundaryPhasePair
import ImbalancedChen.Part3PoissonComplexPowerMoment

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-26.

Real-order angular Abel removal and actual Beta/Gamma value. The weight
is the actual order-nu Poisson weight, including negative real nu>-1/2.
The arbitrary complex moment supplies its genuine endpoint majorant;
native imaginary-axis powers supply both phases. No imaginary-order
specialization, angular-value hypothesis, or spectral claim is used.
-/

namespace ImbalancedChen.Part3.ActualRealOrderJAngularGamma20261026b

noncomputable section
open Complex Set Filter MeasureTheory
open scoped Topology
open JBesselPoissonEvenMoments20261025a PoissonComplexPowerMoment20261026b
open ActualRealOrderJMellinL120261026b ActualRealOrderJAbelPoisson20261026b
open ActualJAngularAbelRateBound20261026b ActualJMellinBoundaryPhasePair20261026b

def realAngularEnvelope (sigma nu u : ℝ) : ℝ := |u| ^ (-sigma) * ‖poissonWeight (nu : ℂ) u‖
def realAngularBoundaryIntegrand (s : ℂ) (nu u : ℝ) : ℂ :=
  poissonWeight (nu : ℂ) u * ((-(I * (u : ℂ))) ^ (-(s + (nu : ℂ))) * Gamma (s + (nu : ℂ)))
def realAngularBoundaryIntegral (s : ℂ) (nu : ℝ) : ℂ :=
  ∫ u in Ioo (-1 : ℝ) 1, realAngularBoundaryIntegrand s nu u
def realAngularGammaValue (s : ℂ) (nu : ℝ) : ℂ :=
  Complex.cos ((Real.pi : ℂ) * (s + (nu : ℂ)) / 2) * Gamma (s + (nu : ℂ)) *
    Gamma ((1 - (s + (nu : ℂ))) / 2) * Gamma ((nu : ℂ) + 1 / 2) /
      Gamma ((1 - (s + (nu : ℂ))) / 2 + (nu : ℂ) + 1 / 2)

private theorem realAngularEnvelope_integrable {sigma nu : ℝ}
    (hs : sigma < 1) (hn : -(1 / 2 : ℝ) < nu) :
    IntegrableOn (realAngularEnvelope sigma nu) (Ioo (-1 : ℝ) 1) := by
  have hm := (poissonPowerMoment_half_integrable
    (alpha := ((1 - sigma : ℝ) : ℂ)) (nu := (nu : ℂ))
    (by simpa using (show 0 < 1 - sigma by linarith)) (by simpa using hn)).norm
  have hh : IntegrableOn (realAngularEnvelope sigma nu) (Ioo 0 1) := by
    apply hm.congr_fun _ measurableSet_Ioo
    intro u hu
    rw [poissonPowerMoment, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu.1]
    have he : ((((1 - sigma : ℝ) : ℂ) - 1) : ℂ).re = -sigma := by simp
    rw [he]
    simp only [realAngularEnvelope, abs_of_pos hu.1]
  have heven (u : ℝ) : realAngularEnvelope sigma nu (-u) = realAngularEnvelope sigma nu u := by
    simp [realAngularEnvelope, poissonWeight]
  have hp : IntervalIntegrable (realAngularEnvelope sigma nu) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)).2 hh
  have hm : IntervalIntegrable (realAngularEnvelope sigma nu) volume (-1) 0 := by
    have h := (IntervalIntegrable.iff_comp_neg).mp hp
    simpa only [neg_zero, neg_one, heven] using h.symm
  exact (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (-1 : ℝ) ≤ 1)).1 (hm.trans hp)

private theorem realAngular_norm_le {s : ℂ} {nu : ℝ} (ha : 0 < s.re + nu)
    (epsilon : ℝ) {u : ℝ} (hu : u ≠ 0) :
    ‖poissonWeight (nu : ℂ) u * (((epsilon : ℂ) - I * (u : ℂ)) ^ (-(s + (nu : ℂ))) * Gamma (s + (nu : ℂ)))‖ ≤
      (Real.exp (Real.pi * |(s + (nu : ℂ)).im|) * ‖Gamma (s + (nu : ℂ))‖) *
        realAngularEnvelope (s.re + nu) nu u := by
  have hrate := angularAbelRate_power_norm_le (a := s + (nu : ℂ)) (by simpa using ha) epsilon hu
  rw [norm_mul, norm_mul]
  calc
    _ ≤ ‖poissonWeight (nu : ℂ) u‖ *
        ((Real.exp (Real.pi * |(s + (nu : ℂ)).im|) * |u| ^ (-(s + (nu : ℂ)).re)) * ‖Gamma (s + (nu : ℂ))‖) := by
      apply mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      exact mul_le_mul_of_nonneg_right hrate (norm_nonneg _)
    _ = _ := by simp only [realAngularEnvelope, Complex.add_re, Complex.ofReal_re]; ring

theorem realAngularAbelIntegral_tendsto_zero {s : ℂ} {nu : ℝ}
    (hn : -(1 / 2 : ℝ) < nu) (ha0 : 0 < s.re + nu) (ha1 : s.re + nu < 1) :
    Tendsto (realAngularAbelIntegral s nu) (𝓝 (0 : ℝ)) (𝓝 (realAngularBoundaryIntegral s nu)) := by
  unfold realAngularAbelIntegral realAngularBoundaryIntegral
  apply tendsto_integral_filter_of_dominated_convergence
    (fun u => (Real.exp (Real.pi * |(s + (nu : ℂ)).im|) * ‖Gamma (s + (nu : ℂ))‖) *
      realAngularEnvelope (s.re + nu) nu u)
  · exact Eventually.of_forall (fun epsilon => (by
      unfold poissonWeight
      fun_prop : Measurable (fun u : ℝ => poissonWeight (nu : ℂ) u *
        (((epsilon : ℂ) - I * (u : ℂ)) ^ (-(s + (nu : ℂ))) * Gamma (s + (nu : ℂ))))).aestronglyMeasurable)
  · exact Eventually.of_forall (fun epsilon => by
      filter_upwards [ae_neq (0 : ℝ)] with u hu
      exact realAngular_norm_le ha0 epsilon hu)
  · exact (realAngularEnvelope_integrable ha1 hn).const_mul _
  · filter_upwards [ae_neq (0 : ℝ)] with u hu
    exact ((angularAbelRate_power_tendsto (s + (nu : ℂ)) hu).mul_const (Gamma (s + (nu : ℂ))))
      .const_mul (poissonWeight (nu : ℂ) u)

private theorem realBoundary_integrable {s : ℂ} {nu : ℝ}
    (hn : -(1 / 2 : ℝ) < nu) (ha0 : 0 < s.re + nu) (ha1 : s.re + nu < 1) :
    IntegrableOn (realAngularBoundaryIntegrand s nu) (Ioo (-1 : ℝ) 1) := by
  apply ((realAngularEnvelope_integrable ha1 hn).const_mul
    (Real.exp (Real.pi * |(s + (nu : ℂ)).im|) * ‖Gamma (s + (nu : ℂ))‖)).mono'
      (by unfold realAngularBoundaryIntegrand poissonWeight; fun_prop : Measurable (realAngularBoundaryIntegrand s nu)).aestronglyMeasurable
  filter_upwards [ae_neq (0 : ℝ)] with u hu
  simpa only [realAngularBoundaryIntegrand, Complex.ofReal_zero, zero_sub] using realAngular_norm_le ha0 0 hu

theorem realOrderJMellinIntegral_eq_boundary {s : ℂ} {nu : ℝ} (hnu : |nu| < 1 / 2)
    (hsnu : 0 < s.re + nu) (hsHalf : s.re < 1 / 2) :
    realOrderJMellinIntegral s nu = realPoissonMellinConstant nu * realAngularBoundaryIntegral s nu := by
  have hn := abs_lt.mp hnu
  have ha1 : s.re + nu < 1 := by linarith [hn.2]
  have hl := (realJAbelIntegral_tendsto_zero hnu.le hsnu hsHalf).mono_left
    (nhdsWithin_mono (0 : ℝ) Ioi_subset_Ici_self)
  have hr := ((realAngularAbelIntegral_tendsto_zero hn.1 hsnu ha1).const_mul (realPoissonMellinConstant nu))
    .mono_left (nhdsWithin_le_nhds : (𝓝[>] (0 : ℝ)) ≤ 𝓝 0)
  have he : realJAbelIntegral s nu =ᶠ[𝓝[>] (0 : ℝ)]
      (fun epsilon => realPoissonMellinConstant nu * realAngularAbelIntegral s nu epsilon) := by
    filter_upwards [self_mem_nhdsWithin] with epsilon he
    exact realJAbelIntegral_eq_poissonGamma hn.1 hsnu he
  exact tendsto_nhds_unique_of_eventuallyEq hl hr he

private theorem realBoundary_pair (s : ℂ) (nu : ℝ) {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    realAngularBoundaryIntegrand s nu u + realAngularBoundaryIntegrand s nu (-u) =
      2 * Complex.cos ((Real.pi : ℂ) * (s + (nu : ℂ)) / 2) * Gamma (s + (nu : ℂ)) *
        poissonPowerMoment (1 - (s + (nu : ℂ))) (nu : ℂ) u := by
  let a : ℂ := s + (nu : ℂ)
  have hW : poissonWeight (nu : ℂ) (-u) = poissonWeight (nu : ℂ) u := by simp [poissonWeight]
  have hphase : Complex.exp ((Real.pi : ℂ) * I * a / 2) + Complex.exp (-((Real.pi : ℂ) * I * a / 2)) =
      2 * Complex.cos ((Real.pi : ℂ) * a / 2) := by
    calc
      _ = Complex.exp (((Real.pi : ℂ) * a / 2) * I) + Complex.exp (-((Real.pi : ℂ) * a / 2) * I) := by
        congr 1 <;> congr 1 <;> ring
      _ = _ := (Complex.two_cos _).symm
  simp only [realAngularBoundaryIntegrand, Complex.ofReal_neg, mul_neg, neg_neg, hW]
  rw [negative_imaginary_axis_cpow _ hu.1, positive_imaginary_axis_cpow _ hu.1]
  have he : (1 - a) - 1 = -a := by ring
  change poissonWeight (nu : ℂ) u * ((u : ℂ) ^ (-a) * Complex.exp ((Real.pi : ℂ) * I * a / 2) * Gamma a) +
    poissonWeight (nu : ℂ) u * ((u : ℂ) ^ (-a) * Complex.exp (-((Real.pi : ℂ) * I * a / 2)) * Gamma a) = _
  calc
    _ = (Complex.exp ((Real.pi : ℂ) * I * a / 2) + Complex.exp (-((Real.pi : ℂ) * I * a / 2))) * Gamma a *
        ((u : ℂ) ^ (-a) * poissonWeight (nu : ℂ) u) := by ring
    _ = _ := by rw [hphase]; unfold poissonPowerMoment; change _ = _ * ((u : ℂ) ^ ((1 - a) - 1) * _); rw [he]

theorem realAngularBoundaryIntegral_eq_gamma {s : ℂ} {nu : ℝ}
    (hn : -(1 / 2 : ℝ) < nu) (ha0 : 0 < s.re + nu) (ha1 : s.re + nu < 1) :
    realAngularBoundaryIntegral s nu = realAngularGammaValue s nu := by
  have hi := realBoundary_integrable hn ha0 ha1
  have hp : IntervalIntegrable (realAngularBoundaryIntegrand s nu) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)).2
      (hi.mono_set (fun u hu => ⟨by linarith [hu.1], hu.2⟩))
  have hm : IntervalIntegrable (realAngularBoundaryIntegrand s nu) volume (-1) 0 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (-1 : ℝ) ≤ 0)).2
      (hi.mono_set (fun u hu => ⟨hu.1, by linarith [hu.2]⟩))
  have hc : IntervalIntegrable (fun u => realAngularBoundaryIntegrand s nu (-u)) volume 0 1 := by
    have h := (IntervalIntegrable.iff_comp_neg).mp hm
    simpa only [neg_neg, neg_zero] using h.symm
  have href : (∫ u in (-1 : ℝ)..0, realAngularBoundaryIntegrand s nu u) =
      ∫ u in (0 : ℝ)..1, realAngularBoundaryIntegrand s nu (-u) := by
    simpa only [neg_zero, neg_one] using (intervalIntegral.integral_comp_neg (realAngularBoundaryIntegrand s nu)
      (a := (0 : ℝ)) (b := 1)).symm
  have hpair : realAngularBoundaryIntegral s nu = ∫ u in Ioo (0 : ℝ) 1,
      (realAngularBoundaryIntegrand s nu u + realAngularBoundaryIntegrand s nu (-u)) := by
    unfold realAngularBoundaryIntegral
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
      ← intervalIntegral.integral_add_adjacent_intervals hm hp, href, add_comm, ← intervalIntegral.integral_add hp hc,
      intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), integral_Ioc_eq_integral_Ioo]
  have halpha : 0 < (1 - (s + (nu : ℂ))).re := by
    simpa using (show 0 < 1 - (s.re + nu) by linarith)
  have hmoment := poissonPowerMoment_half_integral halpha (show -(1 / 2 : ℝ) < (nu : ℂ).re by simpa using hn)
  calc
    realAngularBoundaryIntegral s nu = ∫ u in Ioo (0 : ℝ) 1,
        (2 * Complex.cos ((Real.pi : ℂ) * (s + (nu : ℂ)) / 2) * Gamma (s + (nu : ℂ))) *
          poissonPowerMoment (1 - (s + (nu : ℂ))) (nu : ℂ) u := by
      rw [hpair]
      apply setIntegral_congr_fun measurableSet_Ioo
      intro u hu
      exact realBoundary_pair s nu hu
    _ = (Complex.cos ((Real.pi : ℂ) * (s + (nu : ℂ)) / 2) * Gamma (s + (nu : ℂ))) *
        (2 * ∫ u in Ioo (0 : ℝ) 1, poissonPowerMoment (1 - (s + (nu : ℂ))) (nu : ℂ) u) := by
      rw [integral_const_mul]
      ring
    _ = realAngularGammaValue s nu := by rw [hmoment]; unfold realAngularGammaValue; ring

theorem realOrderJMellinIntegral_eq_gamma_product {s : ℂ} {nu : ℝ} (hnu : |nu| < 1 / 2)
    (hsnu : 0 < s.re + nu) (hsHalf : s.re < 1 / 2) :
    realOrderJMellinIntegral s nu = realPoissonMellinConstant nu * realAngularGammaValue s nu := by
  have hn := abs_lt.mp hnu
  rw [realOrderJMellinIntegral_eq_boundary hnu hsnu hsHalf,
    realAngularBoundaryIntegral_eq_gamma hn.1 hsnu (by linarith [hn.2] : s.re + nu < 1)]

end
end ImbalancedChen.Part3.ActualRealOrderJAngularGamma20261026b
