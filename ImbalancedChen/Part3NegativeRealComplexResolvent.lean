import ImbalancedChen.Part3ComplexContractionResolvent
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances

/-!
# The negative real axis joins the generic complex and positive resolvents

SOURCE_WRITTEN / UNCOMPILED / NOT_ROOT_ACCEPTED.

The existing real and complex CFC resolvents on arbitrary complex Hilbert
H coincide at z=-a. This follows from the exact scalar ratio and the native
real-to-complex CFC restriction theorem, without assuming an inverse.
For positive a, the already proved real normalizer inverse gives the
explicit bounded complex-linear inverse I+(1-a)R_a on BOTH sides. The
actual negative-real complex resolvent therefore inherits both graph
inverse directions and the norm bound 1/a. No new real resolvent, spectral
calculus or concrete radial/Gamma0 operator is defined here.
-/

namespace ImbalancedChen.Part3.NegativeRealComplexResolvent20261025a
noncomputable section
open ImbalancedChen.Part3.PositiveContractionResolventCalculus20261025a
open ImbalancedChen.Part3.ComplexContractionResolvent20261025a

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem complexResolventRatio_neg_real (a t : ℝ) :
    complexResolventRatio (-(a : ℂ)) (t : ℂ) = (resolventRatio a t : ℂ) := by
  unfold complexResolventRatio complexDenominator resolventRatio denominator
  push_cast
  congr 1
  ring

theorem complexInverseDenominator_neg_real (a t : ℝ) :
    complexInverseDenominator (-(a : ℂ)) (t : ℂ) = (inverseDenominator a t : ℂ) := by
  unfold complexInverseDenominator complexDenominator inverseDenominator denominator
  push_cast
  congr 1
  ring

/-- Equality of the ACTUAL existing generic CFC operators. This identity
of total CFC expressions holds for every real a, including parameter
values for which no inverse is asserted. Positive a is used below. -/
theorem complexResolvent_neg_real (R : H →L[ℂ] H) (hSA : IsSelfAdjoint R) (a : ℝ) :
    complexResolvent R (-(a : ℂ)) = shiftedResolvent R a := by
  unfold complexResolvent shiftedResolvent
  rw [cfc_real_eq_complex (resolventRatio a) hSA]
  apply cfc_congr
  intro w hw
  rw [hSA.mem_spectrum_eq_re hw]
  simpa only [Complex.ofReal_re] using complexResolventRatio_neg_real a w.re

theorem complexInverseNormalizer_neg_real (R : H →L[ℂ] H) (hSA : IsSelfAdjoint R) (a : ℝ) :
    complexInverseNormalizer R (-(a : ℂ)) = inverseNormalizer R a := by
  unfold complexInverseNormalizer inverseNormalizer
  rw [cfc_real_eq_complex (inverseDenominator a) hSA]
  apply cfc_congr
  intro w hw
  rw [hSA.mem_spectrum_eq_re hw]
  simpa only [Complex.ofReal_re] using complexInverseDenominator_neg_real a w.re

theorem complexNormalizer_neg_real (R : H →L[ℂ] H) (a : ℝ) :
    complexNormalizer R (-(a : ℂ)) = normalizer R a := by
  unfold complexNormalizer normalizer
  push_cast
  module

theorem normalizer_commutes_original (R : H →L[ℂ] H) (a : ℝ) :
    R * normalizer R a = normalizer R a * R := by
  unfold normalizer
  simp only [mul_add,add_mul,mul_one,one_mul,mul_smul_comm,smul_mul_assoc]

/-- The missing right product is derived from the genuine existing
normalizer inverse and its original-coordinate commutation. -/
theorem shiftedResolvent_mul_normalizer (R : H →L[ℂ] H) (hSA : IsSelfAdjoint R)
    (hpos : 0 ≤ R) (hnorm : ‖R‖ ≤ 1) {a : ℝ} (ha : 0 < a) :
    shiftedResolvent R a * normalizer R a = R := by
  rw [shiftedResolvent_eq_inverseNormalizer_mul R hSA hpos hnorm ha,
    mul_assoc,normalizer_commutes_original,← mul_assoc,
    inverseNormalizer_mul_normalizer R hSA hpos hnorm ha,one_mul]

/-- Explicit bounded inverse on the RIGHT, proved from B R_a=R. -/
theorem normalizer_mul_explicitInverse (R : H →L[ℂ] H) (hSA : IsSelfAdjoint R)
    (hpos : 0 ≤ R) (hnorm : ‖R‖ ≤ 1) {a : ℝ} (ha : 0 < a) :
    normalizer R a * (1 + (((1 - a : ℝ) : ℂ) • shiftedResolvent R a)) = 1 := by
  rw [mul_add,mul_one,mul_smul_comm,normalizer_mul_shiftedResolvent R hSA hpos hnorm ha]
  unfold normalizer
  push_cast
  module

/-- Explicit bounded inverse on the LEFT, proved from R_a B=R. -/
theorem explicitInverse_mul_normalizer (R : H →L[ℂ] H) (hSA : IsSelfAdjoint R)
    (hpos : 0 ≤ R) (hnorm : ‖R‖ ≤ 1) {a : ℝ} (ha : 0 < a) :
    (1 + (((1 - a : ℝ) : ℂ) • shiftedResolvent R a)) * normalizer R a = 1 := by
  rw [add_mul,one_mul,smul_mul_assoc,shiftedResolvent_mul_normalizer R hSA hpos hnorm ha]
  unfold normalizer
  push_cast
  module

/-- The already constructed inverse CLM is EXACTLY I+(1-a)R_a; no
inverse formula is supplied by the caller. -/
theorem inverseNormalizer_eq_explicitInverse (R : H →L[ℂ] H) (hSA : IsSelfAdjoint R)
    (hpos : 0 ≤ R) (hnorm : ‖R‖ ≤ 1) {a : ℝ} (ha : 0 < a) :
    inverseNormalizer R a = 1 + (((1 - a : ℝ) : ℂ) • shiftedResolvent R a) := by
  let C : H →L[ℂ] H := 1 + (((1 - a : ℝ) : ℂ) • shiftedResolvent R a)
  have hleft : C * normalizer R a = 1 := explicitInverse_mul_normalizer R hSA hpos hnorm ha
  calc
    inverseNormalizer R a = (C * normalizer R a) * inverseNormalizer R a := by rw [hleft,one_mul]
    _ = C * (normalizer R a * inverseNormalizer R a) := mul_assoc _ _ _
    _ = C := by rw [normalizer_mul_inverseNormalizer R hSA hpos hnorm ha,mul_one]

theorem complexInverseNormalizer_neg_real_explicit (R : H →L[ℂ] H) (hSA : IsSelfAdjoint R)
    (hpos : 0 ≤ R) (hnorm : ‖R‖ ≤ 1) {a : ℝ} (ha : 0 < a) :
    complexInverseNormalizer R (-(a : ℂ)) =
      1 + (((1 - a : ℝ) : ℂ) • shiftedResolvent R a) := by
  rw [complexInverseNormalizer_neg_real, inverseNormalizer_eq_explicitInverse R hSA hpos hnorm ha]

theorem complexInverseNormalizer_neg_real_mul (R : H →L[ℂ] H) (hSA : IsSelfAdjoint R)
    (hpos : 0 ≤ R) (hnorm : ‖R‖ ≤ 1) {a : ℝ} (ha : 0 < a) :
    complexInverseNormalizer R (-(a : ℂ)) * complexNormalizer R (-(a : ℂ)) = 1 := by
  rw [complexInverseNormalizer_neg_real R hSA a,complexNormalizer_neg_real]
  exact inverseNormalizer_mul_normalizer R hSA hpos hnorm ha

theorem complexNormalizer_neg_real_mul_inverse (R : H →L[ℂ] H) (hSA : IsSelfAdjoint R)
    (hpos : 0 ≤ R) (hnorm : ‖R‖ ≤ 1) {a : ℝ} (ha : 0 < a) :
    complexNormalizer R (-(a : ℂ)) * complexInverseNormalizer R (-(a : ℂ)) = 1 := by
  rw [complexNormalizer_neg_real,complexInverseNormalizer_neg_real R hSA a]
  exact normalizer_mul_inverseNormalizer R hSA hpos hnorm ha

theorem complexResolvent_neg_real_eq_inverse_mul (R : H →L[ℂ] H) (hSA : IsSelfAdjoint R)
    (hpos : 0 ≤ R) (hnorm : ‖R‖ ≤ 1) {a : ℝ} (ha : 0 < a) :
    complexResolvent R (-(a : ℂ)) = complexInverseNormalizer R (-(a : ℂ)) * R := by
  rw [complexResolvent_neg_real R hSA a,complexInverseNormalizer_neg_real R hSA a]
  exact shiftedResolvent_eq_inverseNormalizer_mul R hSA hpos hnorm ha

theorem complexResolvent_neg_real_norm_le (R : H →L[ℂ] H) (hSA : IsSelfAdjoint R)
    (hpos : 0 ≤ R) (hnorm : ‖R‖ ≤ 1) {a : ℝ} (ha : 0 < a) :
    ‖complexResolvent R (-(a : ℂ))‖ ≤ 1 / a := by
  rw [complexResolvent_neg_real R hSA a]
  exact shiftedResolvent_norm_le R hpos hnorm ha

theorem complexResolvent_neg_real_on_graph (R : H →L[ℂ] H) (hSA : IsSelfAdjoint R)
    (hpos : 0 ≤ R) (hnorm : ‖R‖ ≤ 1) {a : ℝ} (ha : 0 < a)
    {u v : H} (huv : (u,v) ∈ resolventGraph R) :
    complexResolvent R (-(a : ℂ)) (v + (a : ℂ) • u) = u := by
  rw [complexResolvent_neg_real R hSA a]
  simpa only [add_comm] using shiftedResolvent_on_graph R hSA hpos hnorm ha huv

theorem complexResolvent_neg_real_graph_pair (R : H →L[ℂ] H) (hSA : IsSelfAdjoint R)
    (hpos : 0 ≤ R) (hnorm : ‖R‖ ≤ 1) {a : ℝ} (ha : 0 < a) (f : H) :
    (complexResolvent R (-(a : ℂ)) f,
      f - (a : ℂ) • complexResolvent R (-(a : ℂ)) f) ∈ resolventGraph R := by
  rw [complexResolvent_neg_real R hSA a]
  exact shiftedResolvent_graph_pair R hSA hpos hnorm ha f

end
end ImbalancedChen.Part3.NegativeRealComplexResolvent20261025a
