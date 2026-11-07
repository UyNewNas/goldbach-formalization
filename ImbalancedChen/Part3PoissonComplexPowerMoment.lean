import ImbalancedChen.Part3JBesselPoissonEvenMoments

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-26.

Actual Poisson moments with an arbitrary complex power, extending the
previous integer even moments to the Mellin parameter required by J.
The square substitution proves convergence and the exact Beta/Gamma value.
Its real norm specialization supplies the angular Abel majorant through
both the angular origin and the Poisson endpoints.
-/

namespace ImbalancedChen.Part3.PoissonComplexPowerMoment20261026b

noncomputable section
open Complex Set MeasureTheory
open JBesselPoissonEvenMoments20261025a
open ImbalancedChen.Part3ComplexBetaHalfLineGamma

def poissonPowerMoment (alpha nu : ℂ) (u : ℝ) : ℂ :=
  (u : ℂ) ^ (alpha - 1) * poissonWeight nu u

def angularAbelEnvelope (sigma u : ℝ) : ℝ :=
  |u| ^ (-sigma) * ‖poissonWeight 0 u‖

private theorem square_image : (fun u : ℝ => u ^ 2) '' Ioo (0 : ℝ) 1 = Ioo (0 : ℝ) 1 := by
  ext v
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨sq_pos_of_pos hu.1, ?_⟩
    nlinarith [mul_pos (sub_pos.mpr hu.2) (show 0 < 1 + u by linarith [hu.1])]
  · intro hv
    refine ⟨Real.sqrt v, ⟨Real.sqrt_pos.2 hv.1, ?_⟩, Real.sq_sqrt hv.1.le⟩
    apply (sq_lt_sq₀ (Real.sqrt_nonneg v) zero_le_one).mp
    simpa only [Real.sq_sqrt hv.1.le, one_pow] using hv.2

private theorem square_injective : Set.InjOn (fun u : ℝ => u ^ 2) (Ioo (0 : ℝ) 1) := by
  intro u hu v hv huv
  exact (sq_eq_sq₀ hu.1.le hv.1.le).mp huv

private theorem square_hasDerivAt (u : ℝ) :
    HasDerivAt (fun x : ℝ => x ^ 2) (2 * u) u := by
  simpa using (hasDerivAt_id u).pow 2

theorem poissonPowerMoment_square_jacobian (alpha nu : ℂ) {u : ℝ} (hu : 0 < u) :
    |2 * u| • compactKernel (alpha / 2) (nu + 1 / 2) (u ^ 2) =
      (2 : ℂ) * poissonPowerMoment alpha nu u := by
  have huC : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu.ne'
  have hp : (((u ^ 2 : ℝ) : ℂ)) ^ (alpha / 2 - 1) = (u : ℂ) ^ (alpha - 2) := by
    rw [← Real.rpow_two u, ← Complex.cpow_mul_ofReal_nonneg hu.le (2 : ℝ)]
    congr 1
    ring
  have hc : (u : ℂ) * (((u ^ 2 : ℝ) : ℂ)) ^ (alpha / 2 - 1) =
      (u : ℂ) ^ (alpha - 1) := by
    rw [hp]
    nth_rw 1 [← Complex.cpow_one (u : ℂ)]
    rw [← Complex.cpow_add 1 (alpha - 2) huC]
    congr 1
    ring
  have he : (nu + 1 / 2) - 1 = nu - 1 / 2 := by ring
  rw [Complex.real_smul, abs_of_pos (mul_pos (by norm_num) hu)]
  dsimp only [compactKernel, poissonPowerMoment, poissonWeight]
  rw [he]
  push_cast
  have hc' := hc
  push_cast at hc'
  calc
    _ = (2 : ℂ) * ((u : ℂ) * ((u : ℂ) ^ 2) ^ (alpha / 2 - 1)) *
        (1 - (u : ℂ) ^ 2) ^ (nu - 1 / 2) := by ring
    _ = _ := by rw [hc']; ring

theorem poissonPowerMoment_half_integrable {alpha nu : ℂ}
    (ha : 0 < alpha.re) (hn : -(1 / 2 : ℝ) < nu.re) :
    IntegrableOn (poissonPowerMoment alpha nu) (Ioo 0 1) := by
  have ha' : 0 < (alpha / 2).re := by simpa using (show 0 < alpha.re / 2 by linarith)
  have hn' : 0 < (nu + 1 / 2).re := by simp only [Complex.add_re]; norm_num; linarith
  have hchange := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioo
    (fun u _ => (square_hasDerivAt u).hasDerivWithinAt) square_injective
    (compactKernel (alpha / 2) (nu + 1 / 2))
  rw [square_image] at hchange
  have h := hchange.mp (integrableOn_compactKernel ha' hn')
  apply (h.div_const (2 : ℂ)).congr_fun _ measurableSet_Ioo
  intro u hu
  rw [poissonPowerMoment_square_jacobian alpha nu hu.1]
  ring

/-- Actual continuous complex-power moment, not an assumed Mellin value. -/
theorem poissonPowerMoment_half_integral {alpha nu : ℂ}
    (ha : 0 < alpha.re) (hn : -(1 / 2 : ℝ) < nu.re) :
    (2 : ℂ) * (∫ u in Ioo (0 : ℝ) 1, poissonPowerMoment alpha nu u) =
      Gamma (alpha / 2) * Gamma (nu + 1 / 2) / Gamma (alpha / 2 + nu + 1 / 2) := by
  have ha' : 0 < (alpha / 2).re := by simpa using (show 0 < alpha.re / 2 by linarith)
  have hn' : 0 < (nu + 1 / 2).re := by simp only [Complex.add_re]; norm_num; linarith
  have hchange := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo
    (fun u _ => (square_hasDerivAt u).hasDerivWithinAt) square_injective
    (compactKernel (alpha / 2) (nu + 1 / 2))
  rw [square_image] at hchange
  calc
    (2 : ℂ) * (∫ u in Ioo (0 : ℝ) 1, poissonPowerMoment alpha nu u) =
        ∫ u in Ioo (0 : ℝ) 1, (2 : ℂ) * poissonPowerMoment alpha nu u :=
      (integral_const_mul _ _).symm
    _ = ∫ u in Ioo (0 : ℝ) 1,
        |2 * u| • compactKernel (alpha / 2) (nu + 1 / 2) (u ^ 2) := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro u hu
      exact (poissonPowerMoment_square_jacobian alpha nu hu.1).symm
    _ = ∫ v in Ioo (0 : ℝ) 1, compactKernel (alpha / 2) (nu + 1 / 2) v := hchange.symm
    _ = _ := by
      simpa only [add_assoc] using integral_compactKernel_eq_gamma ha' hn'

theorem angularAbelEnvelope_half_integrable {sigma : ℝ} (hs : sigma < 1) :
    IntegrableOn (angularAbelEnvelope sigma) (Ioo 0 1) := by
  have hm := (poissonPowerMoment_half_integrable
    (alpha := ((1 - sigma : ℝ) : ℂ)) (nu := (0 : ℂ))
    (by simpa using (show 0 < 1 - sigma by linarith)) (by norm_num)).norm
  apply hm.congr_fun _ measurableSet_Ioo
  intro u hu
  rw [poissonPowerMoment, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu.1]
  have he : ((((1 - sigma : ℝ) : ℂ) - 1) : ℂ).re = -sigma := by simp
  rw [he]
  simp only [angularAbelEnvelope, abs_of_pos hu.1]

theorem angularAbelEnvelope_even (sigma u : ℝ) :
    angularAbelEnvelope sigma (-u) = angularAbelEnvelope sigma u := by
  simp [angularAbelEnvelope, poissonWeight]

/-- Genuine L1 through u=0 and both Poisson endpoints. The endpoint
condition sigma<1 is supplied, not hidden in an assumed envelope. -/
theorem angularAbelEnvelope_integrable {sigma : ℝ} (hs : sigma < 1) :
    IntegrableOn (angularAbelEnvelope sigma) (Ioo (-1 : ℝ) 1) := by
  have hp : IntervalIntegrable (angularAbelEnvelope sigma) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)).2
      (angularAbelEnvelope_half_integrable hs)
  have hn : IntervalIntegrable (angularAbelEnvelope sigma) volume (-1) 0 := by
    have h := (IntervalIntegrable.iff_comp_neg).mp hp
    simpa only [neg_zero, neg_one, angularAbelEnvelope_even] using h.symm
  exact (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (-1 : ℝ) ≤ 1)).1
    (hn.trans hp)

end
end ImbalancedChen.Part3.PoissonComplexPowerMoment20261026b
