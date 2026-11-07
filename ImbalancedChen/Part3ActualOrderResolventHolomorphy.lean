import ImbalancedChen.Part3ActualRadialComplexResolventBinding
import Mathlib.Analysis.Analytic.Constructions

/-!
# Actual order-resolvent holomorphy across the positive real order axis

SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

For Re nu>0, the true normalizer at z=-nu^2 has both inverse directions:
the nonreal CFC identities apply off the real order axis; on that axis the
proved negative-real/positive-shift CFC bridge supplies the identities.
Banach-algebra inverse analyticity therefore holds on ONE whole half-plane.
No boundary identity theorem or assumed resolvent analyticity is used.
The actual radial result uses its single native R1 and proved shift binding.
-/

namespace ImbalancedChen.Part3.ActualOrderResolventHolomorphy20261025a

noncomputable section
open Set
open scoped Topology
open PositiveContractionResolventCalculus20261025a
open ComplexContractionResolvent20261025a NegativeRealComplexResolvent20261025a
open RadialSchrodingerL2Form20261025a

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def positiveOrderHalfPlane : Set ℂ := {nu | 0 < nu.re}

theorem isOpen_positiveOrderHalfPlane : IsOpen positiveOrderHalfPlane :=
  isOpen_lt continuous_const Complex.continuous_re

private theorem neg_square_im_ne_zero {nu : ℂ} (hre : 0 < nu.re) (him : nu.im ≠ 0) :
    (-(nu ^ 2)).im ≠ 0 := by
  have heq : (-(nu ^ 2)).im = -(2 * nu.re * nu.im) := by
    simp only [pow_two, Complex.neg_im, Complex.mul_im]
    ring
  rw [heq]
  exact neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero (by norm_num) hre.ne') him)

private theorem order_real_of_im_zero {nu : ℂ} (him : nu.im = 0) :
    nu = (nu.re : ℂ) := by
  apply Complex.ext
  · simp
  · simp only [Complex.ofReal_im, him]

/-- Both inverse directions are derived for the same literal CFC normalizer
at every positive-real-part order, including real orders. -/
theorem orderNormalizer_inverse_identities
    (R : H →L[ℂ] H) (hSA : IsSelfAdjoint R) (hpos : 0 ≤ R) (hnorm : ‖R‖ ≤ 1)
    {nu : ℂ} (hre : 0 < nu.re) :
    complexNormalizer R (-(nu ^ 2)) * complexInverseNormalizer R (-(nu ^ 2)) = 1 ∧
      complexInverseNormalizer R (-(nu ^ 2)) * complexNormalizer R (-(nu ^ 2)) = 1 := by
  by_cases him : nu.im = 0
  · have heq := order_real_of_im_zero him
    rw [heq]
    have hsq : 0 < nu.re ^ 2 := sq_pos_of_pos hre
    simpa only [← Complex.ofReal_pow] using
      And.intro
        (complexNormalizer_neg_real_mul_inverse R hSA hpos hnorm hsq)
        (complexInverseNormalizer_neg_real_mul R hSA hpos hnorm hsq)
  · exact ⟨complexNormalizer_mul_inverse R hSA (neg_square_im_ne_zero hre him),
      complexInverseNormalizer_mul R hSA (neg_square_im_ne_zero hre him)⟩

theorem isUnit_orderNormalizer
    (R : H →L[ℂ] H) (hSA : IsSelfAdjoint R) (hpos : 0 ≤ R) (hnorm : ‖R‖ ≤ 1)
    {nu : ℂ} (hre : 0 < nu.re) : IsUnit (complexNormalizer R (-(nu ^ 2))) := by
  obtain ⟨hleft, hright⟩ := orderNormalizer_inverse_identities R hSA hpos hnorm hre
  exact ⟨⟨complexNormalizer R (-(nu ^ 2)), complexInverseNormalizer R (-(nu ^ 2)),
    hleft, hright⟩, rfl⟩

theorem orderResolvent_eq_Banach_inverse
    (R : H →L[ℂ] H) (hSA : IsSelfAdjoint R) (hpos : 0 ≤ R) (hnorm : ‖R‖ ≤ 1)
    {nu : ℂ} (hre : 0 < nu.re) :
    complexResolvent R (-(nu ^ 2)) = Ring.inverse (complexNormalizer R (-(nu ^ 2))) * R := by
  have hu := isUnit_orderNormalizer R hSA hpos hnorm hre
  have hinv : Ring.inverse (complexNormalizer R (-(nu ^ 2))) =
      complexInverseNormalizer R (-(nu ^ 2)) := by
    have hm := (orderNormalizer_inverse_identities R hSA hpos hnorm hre).1
    calc
      _ = Ring.inverse (complexNormalizer R (-(nu ^ 2))) * 1 := (mul_one _).symm
      _ = Ring.inverse (complexNormalizer R (-(nu ^ 2))) *
          (complexNormalizer R (-(nu ^ 2)) * complexInverseNormalizer R (-(nu ^ 2))) := by rw [hm]
      _ = (Ring.inverse (complexNormalizer R (-(nu ^ 2))) *
          complexNormalizer R (-(nu ^ 2))) * complexInverseNormalizer R (-(nu ^ 2)) :=
        (mul_assoc _ _ _).symm
      _ = _ := by rw [Ring.inverse_mul_cancel _ hu, one_mul]
  rw [hinv]
  by_cases him : nu.im = 0
  · rw [order_real_of_im_zero him]
    simpa only [← Complex.ofReal_pow] using complexResolvent_neg_real_eq_inverse_mul
      R hSA hpos hnorm (sq_pos_of_pos hre)
  · exact complexResolvent_eq_inverse_mul R hSA (neg_square_im_ne_zero hre him)

/-- Actual generic order-resolvent analyticity on one connected half-plane.
The proof crosses real positive orders through genuine Banach inverses. -/
theorem analyticOnNhd_complexOrderResolvent
    (R : H →L[ℂ] H) (hSA : IsSelfAdjoint R) (hpos : 0 ≤ R) (hnorm : ‖R‖ ≤ 1) :
    AnalyticOnNhd ℂ (fun nu => complexResolvent R (-(nu ^ 2))) positiveOrderHalfPlane := by
  have hN (nu : ℂ) : AnalyticAt ℂ (fun z => complexNormalizer R (-(z ^ 2))) nu := by
    unfold complexNormalizer
    exact analyticAt_const.sub
      ((analyticAt_const.add (analyticAt_id.pow 2).neg).smul analyticAt_const)
  have hmodel : AnalyticOnNhd ℂ
      (fun nu => Ring.inverse (complexNormalizer R (-(nu ^ 2))) * R) positiveOrderHalfPlane := by
    intro nu hnu
    have hi := analyticOnNhd_inverse (𝕜 := ℂ) (complexNormalizer R (-(nu ^ 2)))
      (isUnit_orderNormalizer R hSA hpos hnorm hnu)
    exact (hi.comp nu (hN nu)).mul analyticAt_const
  apply AnalyticOnNhd.congr isOpen_positiveOrderHalfPlane hmodel
  intro nu hnu
  exact (orderResolvent_eq_Banach_inverse R hSA hpos hnorm hnu).symm

theorem analyticOnNhd_actualRadialOrderResolvent :
    AnalyticOnNhd ℂ actualRadialOrderResolvent positiveOrderHalfPlane := by
  exact analyticOnNhd_complexOrderResolvent radialUnitShiftResolvent
    radialUnitShiftResolvent_selfAdjoint radialUnitShiftResolvent_nonneg
    radialUnitShiftResolvent_opNorm_le_one

/-- The actual scalar native-resolvent pairing, with both L2 vectors fixed,
inherits the operator analyticity rather than assuming it. -/
theorem analyticOnNhd_actualRadialOrder_pairing (F G : RadialL2) :
    AnalyticOnNhd ℂ (fun nu => inner ℂ G (actualRadialOrderResolvent nu F))
      positiveOrderHalfPlane := by
  intro nu hnu
  have hu := ((ContinuousLinearMap.apply ℂ RadialL2 F).analyticAt _).comp nu
    (analyticOnNhd_actualRadialOrderResolvent nu hnu)
  exact ((innerSL ℂ G).analyticAt _).comp nu hu

end
end ImbalancedChen.Part3.ActualOrderResolventHolomorphy20261025a
