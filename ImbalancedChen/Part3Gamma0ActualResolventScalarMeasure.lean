import ImbalancedChen.Part3GenericResolventScalarMeasure
import ImbalancedChen.Part3Gamma0ActualFriedrichsOperator

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

Scalar RMK measures of the ACTUAL Gamma0 physical resolvent J J* on the
actual quotient Hilbert space, with its independently constructed actual
shifted-energy completion. All self-adjointness, positivity and contraction
inputs are proved actual-source theorems, not hSA/hMeasure suppliers.

The measure is tied to the TRUE unbounded Friedrichs domain: for every
u in that domain, its canonical forcing f=u+A_F u satisfies Rf=u and
(I-R)f=A_F u. Exact r^2 and (1-r)^2 scalar moments are respectively the
physical squared norms of u and A_F u. Thus this is also a genuine actual
unbounded-domain spectral-coordinate binding, not only a measure alias.

The inverse coordinate lambda=(1-r)/r is treated algebraically on r>0.
Vanishing of the zero atom is NOT inferred from [0,1] spectrum containment.
Weighted-measure identities and endpoint removal remain separate joins.
-/

namespace ImbalancedChen.Part3.Gamma0ActualResolventScalarMeasure20261025a

noncomputable section
open MeasureTheory Set
open Gamma0ActualSmoothQuotientCore20261025a
open Gamma0ActualWeakRieszResolvent20261025a
open Gamma0ActualFriedrichsOperator20261025a

abbrev ActualResolventSpectrum (N : ℕ) [NeZero N] :=
  GenericResolventScalarMeasure20261025a.ResolventSpectrum (actualGammaResolvent N)

def actualResolventCFC (N : ℕ) [NeZero N] :
    C(ActualResolventSpectrum N, ℝ) →⋆ₐ[ℝ] (QuotientL2 N →L[ℂ] QuotientL2 N) :=
  GenericResolventScalarMeasure20261025a.resolventCFC
    (actualGammaResolvent N) (actualGammaResolvent_selfAdjoint N)

def actualScalarMeasure (N : ℕ) [NeZero N] (f : QuotientL2 N) :
    Measure (ActualResolventSpectrum N) :=
  GenericResolventScalarMeasure20261025a.scalarMeasure
    (actualGammaResolvent N) (actualGammaResolvent_selfAdjoint N) f

instance actualScalarMeasure_finite (N : ℕ) [NeZero N] (f : QuotientL2 N) :
    IsFiniteMeasure (actualScalarMeasure N f) := by
  unfold actualScalarMeasure
  infer_instance

instance actualScalarMeasure_regular (N : ℕ) [NeZero N] (f : QuotientL2 N) :
    (actualScalarMeasure N f).Regular := by
  unfold actualScalarMeasure
  infer_instance

theorem actualResolvent_spectrum_subset_unitInterval (N : ℕ) [NeZero N] :
    spectrum ℝ (actualGammaResolvent N) ⊆ Icc (0 : ℝ) 1 :=
  GenericResolventScalarMeasure20261025a.resolventSpectrum_subset_unitInterval
    (actualGammaResolvent N)
    ((ContinuousLinearMap.nonneg_iff_isPositive _).2 (actualGammaResolvent_isPositive N))
    (actualGammaResolvent_opNorm_le_one N)

theorem actualSpectrum_coordinate_mem_unitInterval (N : ℕ) [NeZero N]
    (r : ActualResolventSpectrum N) : (r : ℝ) ∈ Icc (0 : ℝ) 1 :=
  actualResolvent_spectrum_subset_unitInterval N r.property

theorem actualScalarMeasure_integral (N : ℕ) [NeZero N] (f : QuotientL2 N)
    (φ : C(ActualResolventSpectrum N, ℝ)) :
    (∫ r, φ r ∂actualScalarMeasure N f) =
      (inner ℂ f ((actualResolventCFC N φ) f)).re :=
  GenericResolventScalarMeasure20261025a.scalarMeasure_integral
    (actualGammaResolvent N) (actualGammaResolvent_selfAdjoint N) f φ

theorem actualScalarMeasure_complex_integral (N : ℕ) [NeZero N] (f : QuotientL2 N)
    (φ : C(ActualResolventSpectrum N, ℝ)) :
    (∫ r, (φ r : ℂ) ∂actualScalarMeasure N f) =
      inner ℂ f ((actualResolventCFC N φ) f) :=
  GenericResolventScalarMeasure20261025a.scalarMeasure_complex_integral
    (actualGammaResolvent N) (actualGammaResolvent_selfAdjoint N) f φ

theorem actualScalarMeasure_mass (N : ℕ) [NeZero N] (f : QuotientL2 N) :
    (actualScalarMeasure N f).real univ = ‖f‖^2 :=
  GenericResolventScalarMeasure20261025a.scalarMeasure_mass
    (actualGammaResolvent N) (actualGammaResolvent_selfAdjoint N) f

theorem actualScalarMeasure_univ (N : ℕ) [NeZero N] (f : QuotientL2 N) :
    actualScalarMeasure N f univ = ENNReal.ofReal (‖f‖^2) :=
  GenericResolventScalarMeasure20261025a.scalarMeasure_univ
    (actualGammaResolvent N) (actualGammaResolvent_selfAdjoint N) f

theorem actualScalarMeasure_moment (N : ℕ) [NeZero N] (f : QuotientL2 N) (n : ℕ) :
    (∫ r : ActualResolventSpectrum N, (r : ℝ)^n ∂actualScalarMeasure N f) =
      (inner ℂ f (((actualGammaResolvent N)^n) f)).re :=
  GenericResolventScalarMeasure20261025a.scalarMeasure_moment
    (actualGammaResolvent N) (actualGammaResolvent_selfAdjoint N) f n

theorem actualScalarMeasure_survival_moment (N : ℕ) [NeZero N]
    (f : QuotientL2 N) (n : ℕ) :
    (∫ r : ActualResolventSpectrum N, (1-(r : ℝ))^n ∂actualScalarMeasure N f) =
      (inner ℂ f (((1-actualGammaResolvent N)^n) f)).re :=
  GenericResolventScalarMeasure20261025a.scalarMeasure_survival_moment
    (actualGammaResolvent N) (actualGammaResolvent_selfAdjoint N) f n

/-- The forcing is constructed from the ACTUAL native unbounded domain. -/
def domainForcing (N : ℕ) [NeZero N] (u : (actualGammaFriedrichs N).domain) : QuotientL2 N :=
  (u : QuotientL2 N) + actualGammaFriedrichs N u

theorem actualResolvent_domainForcing (N : ℕ) [NeZero N]
    (u : (actualGammaFriedrichs N).domain) :
    actualGammaResolvent N (domainForcing N u) = (u : QuotientL2 N) :=
  actualGammaResolvent_shift_friedrichs N u

/-- The actual unbounded output is the complementary resolvent
coordinate applied to the SAME canonical forcing. -/
theorem actualComplement_domainForcing (N : ℕ) [NeZero N]
    (u : (actualGammaFriedrichs N).domain) :
    (1-actualGammaResolvent N) (domainForcing N u) = actualGammaFriedrichs N u := by
  change domainForcing N u - actualGammaResolvent N (domainForcing N u) = _
  rw [actualResolvent_domainForcing, domainForcing]
  abel

/-- Exact spectral norm identity for the domain input, using the actual
resolvent graph rather than a proposed unbounded spectral representation. -/
theorem domainForcing_second_moment (N : ℕ) [NeZero N]
    (u : (actualGammaFriedrichs N).domain) :
    (∫ r : ActualResolventSpectrum N, (r : ℝ)^2
      ∂actualScalarMeasure N (domainForcing N u)) = ‖(u : QuotientL2 N)‖^2 := by
  rw [actualScalarMeasure_moment, pow_two, ContinuousLinearMap.mul_apply]
  rw [← (actualGammaResolvent_selfAdjoint N).isSymmetric
    (domainForcing N u) (actualGammaResolvent N (domainForcing N u))]
  rw [actualResolvent_domainForcing, inner_self_eq_norm_sq_to_K,
    ← Complex.ofReal_pow, Complex.ofReal_re]

/-- The true unbounded output norm is the complementary spectral
second moment of the SAME actual forcing vector. -/
theorem domainForcing_complement_second_moment (N : ℕ) [NeZero N]
    (u : (actualGammaFriedrichs N).domain) :
    (∫ r : ActualResolventSpectrum N, (1-(r : ℝ))^2
      ∂actualScalarMeasure N (domainForcing N u)) = ‖actualGammaFriedrichs N u‖^2 := by
  have hB : IsSelfAdjoint ((1 : QuotientL2 N →L[ℂ] QuotientL2 N)-actualGammaResolvent N) :=
    (IsSelfAdjoint.one _).sub (actualGammaResolvent_selfAdjoint N)
  rw [actualScalarMeasure_survival_moment, pow_two, ContinuousLinearMap.mul_apply]
  rw [← hB.isSymmetric (domainForcing N u)
    ((1-actualGammaResolvent N) (domainForcing N u))]
  rw [actualComplement_domainForcing, inner_self_eq_norm_sq_to_K,
    ← Complex.ofReal_pow, Complex.ofReal_re]

def actualSpectralLambda (N : ℕ) [NeZero N] (r : ActualResolventSpectrum N) : ℝ :=
  (1-(r : ℝ))/(r : ℝ)

theorem actualSpectralLambda_nonneg (N : ℕ) [NeZero N]
    (r : ActualResolventSpectrum N) : 0 ≤ actualSpectralLambda N r :=
  div_nonneg (sub_nonneg.mpr (actualSpectrum_coordinate_mem_unitInterval N r).2)
    (actualSpectrum_coordinate_mem_unitInterval N r).1

/-- The genuine spectral coordinate of A_F follows from Rf=u and
(I-R)f=A_Fu. Division is used ONLY on the positive resolvent coordinate. -/
theorem actualSpectralLambda_mul_coordinate (N : ℕ) [NeZero N]
    (r : ActualResolventSpectrum N) (hr : 0 < (r : ℝ)) :
    actualSpectralLambda N r * (r : ℝ) = 1-(r : ℝ) := by
  exact div_mul_cancel₀ _ hr.ne'

theorem actualSpectralLambda_sq_mul_coordinate_sq (N : ℕ) [NeZero N]
    (r : ActualResolventSpectrum N) (hr : 0 < (r : ℝ)) :
    (actualSpectralLambda N r)^2 * (r : ℝ)^2 = (1-(r : ℝ))^2 := by
  rw [← mul_pow, actualSpectralLambda_mul_coordinate N r hr]

end
end ImbalancedChen.Part3.Gamma0ActualResolventScalarMeasure20261025a
