import ImbalancedChen.Part3Gamma0ActualResolventScalarMeasure
import ImbalancedChen.Part3GenericResolventWeightedScalarMeasure
import ImbalancedChen.Part3GenericResolventScalarZeroAtom

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

The ACTUAL Gamma0 unbounded Friedrichs domain has its true scalar
spectral moments in lambda=(1-r)/r. The canonical forcing f=u+A_Fu
satisfies Rf=u, hence its actual scalar measure obeys mu_u=r^2 mu_f.
Injectivity of the genuine actual physical R removes the zero fiber for
EVERY actual quotient vector, using the proved generic cyclic theorem.

Consequently the first and second lambda moments on mu_u are integrable
and equal respectively Re<u,A_Fu> and ||A_Fu||^2. Integrability is proved
by the exact weighted measure identity and bounded polynomial moments;
it is not accepted as a target premise. No generic lambda pushforward,
whole-plane identification, normalization, or all-H spectral transform
is defined in this module.
-/

namespace ImbalancedChen.Part3.Gamma0ActualFriedrichsSpectralMoments20261025a

noncomputable section
open Set MeasureTheory Filter
open Gamma0ActualSmoothQuotientCore20261025a
open Gamma0ActualWeakRieszResolvent20261025a
open Gamma0ActualFriedrichsOperator20261025a
open Gamma0ActualResolventScalarMeasure20261025a

def actualZeroFiber (N : ℕ) [NeZero N] : Set (ActualResolventSpectrum N) :=
  {r | (r : ℝ) = 0}

/-- This is the actual quotient R's injectivity theorem applied to the
genuine generic scalar measure, not a support or endpoint certificate. -/
theorem actualScalarMeasure_zeroFiber (N : ℕ) [NeZero N] (f : QuotientL2 N) :
    actualScalarMeasure N f (actualZeroFiber N) = 0 :=
  GenericResolventScalarZeroAtom20261025a.scalarMeasure_zeroFiber
    (actualGammaResolvent N) (actualGammaResolvent_selfAdjoint N)
    (actualGammaResolvent_injective N) f

theorem actualScalarMeasure_ae_coordinate_pos (N : ℕ) [NeZero N] (f : QuotientL2 N) :
    ∀ᵐ r ∂actualScalarMeasure N f, 0 < (r : ℝ) := by
  have hn := GenericResolventScalarZeroAtom20261025a.scalarMeasure_ae_coordinate_ne_zero
    (actualGammaResolvent N) (actualGammaResolvent_selfAdjoint N)
    (actualGammaResolvent_injective N) f
  filter_upwards [hn] with r hr
  exact lt_of_le_of_ne (actualSpectrum_coordinate_mem_unitInterval N r).1 (Ne.symm hr)

/-- Exact measure identity on the actual native unbounded domain. -/
theorem actualScalarMeasure_domain_weighted (N : ℕ) [NeZero N]
    (u : (actualGammaFriedrichs N).domain) :
    actualScalarMeasure N (u : QuotientL2 N) =
      (actualScalarMeasure N (domainForcing N u)).withDensity
        (fun r : ActualResolventSpectrum N => ENNReal.ofReal ((r : ℝ)^2)) := by
  have h := GenericResolventWeightedScalarMeasure20261025a.scalarMeasure_apply
    (actualGammaResolvent N) (actualGammaResolvent_selfAdjoint N) (domainForcing N u)
  change actualScalarMeasure N (actualGammaResolvent N (domainForcing N u)) = _ at h
  rw [actualResolvent_domainForcing] at h
  exact h

/-- The domain zero-fiber statement also follows already from weighting,
independently of the separate all-vector injective-R endpoint theorem. -/
theorem actualScalarMeasure_domain_zeroFiber (N : ℕ) [NeZero N]
    (u : (actualGammaFriedrichs N).domain) :
    actualScalarMeasure N (u : QuotientL2 N) (actualZeroFiber N) = 0 := by
  have h := GenericResolventWeightedScalarMeasure20261025a.scalarMeasure_apply_zeroFiber
    (actualGammaResolvent N) (actualGammaResolvent_selfAdjoint N) (domainForcing N u)
  change actualScalarMeasure N (actualGammaResolvent N (domainForcing N u))
    (actualZeroFiber N) = 0 at h
  rwa [actualResolvent_domainForcing] at h

private theorem density_measurable (N : ℕ) [NeZero N] :
    Measurable (fun r : ActualResolventSpectrum N => ENNReal.ofReal ((r : ℝ)^2)) := by
  fun_prop

/-- The exact real integral transformation, for any real test, on the
actual unbounded domain. The theorem also respects total Bochner integrals. -/
theorem domain_integral_eq_weighted (N : ℕ) [NeZero N]
    (u : (actualGammaFriedrichs N).domain) (g : ActualResolventSpectrum N → ℝ) :
    (∫ r, g r ∂actualScalarMeasure N (u : QuotientL2 N)) =
      ∫ r, (r : ℝ)^2 * g r ∂actualScalarMeasure N (domainForcing N u) := by
  rw [actualScalarMeasure_domain_weighted,
    integral_withDensity_eq_integral_toReal_smul (density_measurable N)
      (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (sq_nonneg _), smul_eq_mul]

private theorem domain_integrable_of_weighted (N : ℕ) [NeZero N]
    (u : (actualGammaFriedrichs N).domain) (g : ActualResolventSpectrum N → ℝ)
    (hg : Integrable (fun r => (r : ℝ)^2 * g r)
      (actualScalarMeasure N (domainForcing N u))) :
    Integrable g (actualScalarMeasure N (u : QuotientL2 N)) := by
  rw [actualScalarMeasure_domain_weighted]
  apply (integrable_withDensity_iff_integrable_smul' (density_measurable N)
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))).mpr
  simpa only [ENNReal.toReal_ofReal (sq_nonneg _), smul_eq_mul] using hg

private theorem domain_weight_lambda_sq_ae (N : ℕ) [NeZero N]
    (u : (actualGammaFriedrichs N).domain) :
    (fun r : ActualResolventSpectrum N => (r : ℝ)^2 * (actualSpectralLambda N r)^2)
      =ᵐ[actualScalarMeasure N (domainForcing N u)] (fun r => (1-(r : ℝ))^2) := by
  filter_upwards [actualScalarMeasure_ae_coordinate_pos N (domainForcing N u)] with r hr
  simpa only [mul_comm] using actualSpectralLambda_sq_mul_coordinate_sq N r hr

private theorem domain_weight_lambda_ae (N : ℕ) [NeZero N]
    (u : (actualGammaFriedrichs N).domain) :
    (fun r : ActualResolventSpectrum N => (r : ℝ)^2 * actualSpectralLambda N r)
      =ᵐ[actualScalarMeasure N (domainForcing N u)] (fun r => (r : ℝ)*(1-(r : ℝ))) := by
  filter_upwards [actualScalarMeasure_ae_coordinate_pos N (domainForcing N u)] with r hr
  calc
    (r : ℝ)^2 * actualSpectralLambda N r =
        (r : ℝ)*(actualSpectralLambda N r*(r : ℝ)) := by ring
    _ = (r : ℝ)*(1-(r : ℝ)) := by rw [actualSpectralLambda_mul_coordinate N r hr]

/-- The unbounded-coordinate second moment is genuinely integrable on
the measure of every ACTUAL operator-domain input. -/
theorem domain_lambda_sq_integrable (N : ℕ) [NeZero N]
    (u : (actualGammaFriedrichs N).domain) :
    Integrable (fun r => (actualSpectralLambda N r)^2)
      (actualScalarMeasure N (u : QuotientL2 N)) := by
  apply domain_integrable_of_weighted N u
  have hi : Integrable (fun r : ActualResolventSpectrum N => (1-(r : ℝ))^2)
      (actualScalarMeasure N (domainForcing N u)) :=
    (show Continuous (fun r : ActualResolventSpectrum N => (1-(r : ℝ))^2) by fun_prop)
      .integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  exact hi.congr (domain_weight_lambda_sq_ae N u).symm

/-- Exact geometric-output norm, not an assumed spectral graph identity. -/
theorem domain_lambda_sq_integral (N : ℕ) [NeZero N]
    (u : (actualGammaFriedrichs N).domain) :
    (∫ r, (actualSpectralLambda N r)^2 ∂actualScalarMeasure N (u : QuotientL2 N)) =
      ‖actualGammaFriedrichs N u‖^2 := by
  rw [domain_integral_eq_weighted]
  calc
    _ = ∫ r : ActualResolventSpectrum N, (1-(r : ℝ))^2
        ∂actualScalarMeasure N (domainForcing N u) :=
      integral_congr_ae (domain_weight_lambda_sq_ae N u)
    _ = _ := domainForcing_complement_second_moment N u

theorem domain_lambda_integrable (N : ℕ) [NeZero N]
    (u : (actualGammaFriedrichs N).domain) :
    Integrable (actualSpectralLambda N) (actualScalarMeasure N (u : QuotientL2 N)) := by
  apply domain_integrable_of_weighted N u
  have hi : Integrable (fun r : ActualResolventSpectrum N => (r : ℝ)*(1-(r : ℝ)))
      (actualScalarMeasure N (domainForcing N u)) :=
    (show Continuous (fun r : ActualResolventSpectrum N => (r : ℝ)*(1-(r : ℝ))) by fun_prop)
      .integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  exact hi.congr (domain_weight_lambda_ae N u).symm

/-- The mixed polynomial moment has the ACTUAL native-domain energy
pairing as coefficient. Both resolvent coordinate factors are retained. -/
theorem domainForcing_gap_moment (N : ℕ) [NeZero N]
    (u : (actualGammaFriedrichs N).domain) :
    (∫ r : ActualResolventSpectrum N, (r : ℝ)*(1-(r : ℝ))
      ∂actualScalarMeasure N (domainForcing N u)) =
      (inner ℂ (u : QuotientL2 N) (actualGammaFriedrichs N u)).re := by
  have h := GenericResolventScalarMeasure20261025a.scalarMeasure_integral
    (actualGammaResolvent N) (actualGammaResolvent_selfAdjoint N) (domainForcing N u)
    (GenericResolventScalarMeasure20261025a.spectrumCoordinate (actualGammaResolvent N) *
      (1-GenericResolventScalarMeasure20261025a.spectrumCoordinate (actualGammaResolvent N)))
  simp only [map_mul, map_sub, map_one,
    GenericResolventScalarMeasure20261025a.resolventCFC_coordinate] at h
  change (∫ r : ActualResolventSpectrum N, (r : ℝ)*(1-(r : ℝ))
      ∂actualScalarMeasure N (domainForcing N u)) =
    (inner ℂ (domainForcing N u)
      (actualGammaResolvent N ((1-actualGammaResolvent N) (domainForcing N u)))).re at h
  rw [← (actualGammaResolvent_selfAdjoint N).isSymmetric (domainForcing N u)
    ((1-actualGammaResolvent N) (domainForcing N u)),
    actualResolvent_domainForcing, actualComplement_domainForcing] at h
  exact h

/-- The first lambda moment is the actual nonnegative Friedrichs
quadratic form on its true operator domain. -/
theorem domain_lambda_integral_pair (N : ℕ) [NeZero N]
    (u : (actualGammaFriedrichs N).domain) :
    (∫ r, actualSpectralLambda N r ∂actualScalarMeasure N (u : QuotientL2 N)) =
      (inner ℂ (u : QuotientL2 N) (actualGammaFriedrichs N u)).re := by
  rw [domain_integral_eq_weighted]
  calc
    _ = ∫ r : ActualResolventSpectrum N, (r : ℝ)*(1-(r : ℝ))
        ∂actualScalarMeasure N (domainForcing N u) :=
      integral_congr_ae (domain_weight_lambda_ae N u)
    _ = _ := domainForcing_gap_moment N u

end
end ImbalancedChen.Part3.Gamma0ActualFriedrichsSpectralMoments20261025a
