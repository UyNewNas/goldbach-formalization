import ImbalancedChen.Part3ImaginaryOrderKSecondQDerivative
import Mathlib.Tactic

/-!
CODE_ONLY / SOURCEONLY / UNCOMPILED, 2026-10-24.  No acceptance credit.

This is an independent diagonal radial energy calculation for the actual
imaginary-order K integral.  It uses the previously derived q-derivatives
and modified-Bessel ODE.  All integrals are over finite positive intervals;
no endpoint decay, coincident-parameter limit, or spectral normalization is
claimed.
-/

namespace ImbalancedChen.Part3.ActualKRadialEnergyIdentity20261024zz

noncomputable section

open Set
open ImaginaryOrderKBesselSourceOnly
open ImaginaryOrderKQDerivativeSourceOnly
open ImaginaryOrderKSecondQDerivativeSourceOnly

/-- Boundary flux for the actual real K mode. -/
def kFlux (t q : ℝ) : ℝ :=
  q * imaginaryOrderK t q * qDerivative t q

/-- The ODE gives the radial energy derivative, including the negative
`4t²/q` term from imaginary order `2 i t`. -/
theorem kFlux_hasDerivAt (t : ℝ) {q : ℝ} (hq : 0 < q) :
    HasDerivAt (kFlux t)
      (q * (qDerivative t q) ^ 2 +
        q * (imaginaryOrderK t q) ^ 2 -
          4 * t ^ 2 * (imaginaryOrderK t q) ^ 2 / q) q := by
  have hK := imaginaryOrderK_hasDerivAt_q_integral t hq
  have hD := qDerivative_hasDerivAt_qSecond t hq
  have hproduct := ((hasDerivAt_id q).mul hK).mul hD
  have hraw : HasDerivAt (kFlux t)
      (imaginaryOrderK t q * qDerivative t q +
        q * (qDerivative t q) ^ 2 +
          q * imaginaryOrderK t q * qSecond t q) q := by
    convert hproduct using 1
    · funext r
      rfl
    · ring
  have hODE := actual_K_modifiedBessel_equation_integral t hq
  have hmul : q *
      (imaginaryOrderK t q * qDerivative t q +
        q * (qDerivative t q) ^ 2 +
          q * imaginaryOrderK t q * qSecond t q) =
      q ^ 2 * (qDerivative t q) ^ 2 +
        q ^ 2 * (imaginaryOrderK t q) ^ 2 -
          4 * t ^ 2 * (imaginaryOrderK t q) ^ 2 := by
    linear_combination (imaginaryOrderK t q) * hODE
  apply hraw.congr_deriv
  calc
    imaginaryOrderK t q * qDerivative t q +
        q * (qDerivative t q) ^ 2 +
          q * imaginaryOrderK t q * qSecond t q =
      (q ^ 2 * (qDerivative t q) ^ 2 +
        q ^ 2 * (imaginaryOrderK t q) ^ 2 -
          4 * t ^ 2 * (imaginaryOrderK t q) ^ 2) / q :=
            (eq_div_iff hq.ne').2 hmul
    _ = q * (qDerivative t q) ^ 2 +
        q * (imaginaryOrderK t q) ^ 2 -
          4 * t ^ 2 * (imaginaryOrderK t q) ^ 2 / q := by
            field_simp [hq.ne']
            ring

theorem kFlux_deriv (t : ℝ) {q : ℝ} (hq : 0 < q) :
    deriv (kFlux t) q =
      q * (qDerivative t q) ^ 2 +
        q * (imaginaryOrderK t q) ^ 2 -
          4 * t ^ 2 * (imaginaryOrderK t q) ^ 2 / q :=
  (kFlux_hasDerivAt t hq).deriv

private theorem energy_continuousOn (t : ℝ) :
    ContinuousOn
      (fun q : ℝ => q * (qDerivative t q) ^ 2 +
        q * (imaginaryOrderK t q) ^ 2) (Ioi 0) := by
  have hK : ContinuousOn (imaginaryOrderK t) (Ioi 0) :=
    (imaginaryOrderK_differentiableOn_q t).continuousOn
  have hD := qDerivative_continuousOn t
  exact (continuousOn_id.mul (hD.pow 2)).add
    (continuousOn_id.mul (hK.pow 2))

private theorem weighted_mass_continuousOn (t : ℝ) :
    ContinuousOn
      (fun q : ℝ => (imaginaryOrderK t q) ^ 2 / q) (Ioi 0) := by
  have hK : ContinuousOn (imaginaryOrderK t) (Ioi 0) :=
    (imaginaryOrderK_differentiableOn_q t).continuousOn
  exact (hK.pow 2).div continuousOn_id (fun q hq => hq.ne')

/-- The finite positive-interval energy identity.  The right integral uses
the same `dq/q` weight as the radial Sturm--Liouville equation. -/
theorem k_energy_finite (t : ℝ) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    (∫ q in a..b,
      q * (qDerivative t q) ^ 2 +
        q * (imaginaryOrderK t q) ^ 2) =
      kFlux t b - kFlux t a +
        4 * t ^ 2 *
          (∫ q in a..b, (imaginaryOrderK t q) ^ 2 / q) := by
  have hsub : Icc a b ⊆ Ioi (0 : ℝ) := by
    intro q hq
    exact ha.trans_le hq.1
  have hE : IntervalIntegrable
      (fun q : ℝ => q * (qDerivative t q) ^ 2 +
        q * (imaginaryOrderK t q) ^ 2) volume a b :=
    ((energy_continuousOn t).mono hsub).intervalIntegrable_of_Icc hab
  have hM : IntervalIntegrable
      (fun q : ℝ => 4 * t ^ 2 * (imaginaryOrderK t q) ^ 2 / q)
      volume a b := by
    have hc : ContinuousOn
        (fun q : ℝ => 4 * t ^ 2 * (imaginaryOrderK t q) ^ 2 / q)
        (Ioi 0) := by
      have hK : ContinuousOn (imaginaryOrderK t) (Ioi 0) :=
        (imaginaryOrderK_differentiableOn_q t).continuousOn
      exact (continuousOn_const.mul (hK.pow 2)).div continuousOn_id
        (fun q hq => hq.ne')
    exact (hc.mono hsub).intervalIntegrable_of_Icc hab
  have hd : ∀ q ∈ uIcc a b,
      HasDerivAt (kFlux t)
        (q * (qDerivative t q) ^ 2 +
          q * (imaginaryOrderK t q) ^ 2 -
            4 * t ^ 2 * (imaginaryOrderK t q) ^ 2 / q) q := by
    intro q hq
    have hqI : q ∈ Icc a b := by
      simpa only [uIcc_of_le hab] using hq
    exact kFlux_hasDerivAt t (ha.trans_le hqI.1)
  have hFTC :
      (∫ q in a..b,
        (q * (qDerivative t q) ^ 2 +
          q * (imaginaryOrderK t q) ^ 2) -
            4 * t ^ 2 * (imaginaryOrderK t q) ^ 2 / q) =
        kFlux t b - kFlux t a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hE.sub hM)
  rw [intervalIntegral.integral_sub hE hM] at hFTC
  have hscale :
      (∫ q in a..b,
        4 * t ^ 2 * (imaginaryOrderK t q) ^ 2 / q) =
      4 * t ^ 2 *
        (∫ q in a..b, (imaginaryOrderK t q) ^ 2 / q) := by
    calc
      (∫ q in a..b,
        4 * t ^ 2 * (imaginaryOrderK t q) ^ 2 / q) =
          ∫ q in a..b,
            (4 * t ^ 2) * ((imaginaryOrderK t q) ^ 2 / q) := by
              apply intervalIntegral.integral_congr
              intro q
              ring
      _ = _ := intervalIntegral.integral_const_mul
  rw [hscale] at hFTC
  linear_combination hFTC

/-- Both integrals appearing in the finite energy identity are nonnegative. -/
theorem k_energy_and_weighted_mass_nonneg (t : ℝ) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    0 ≤ (∫ q in a..b,
      q * (qDerivative t q) ^ 2 +
        q * (imaginaryOrderK t q) ^ 2) ∧
    0 ≤ (∫ q in a..b, (imaginaryOrderK t q) ^ 2 / q) := by
  constructor
  · apply intervalIntegral.integral_nonneg hab
    intro q hq
    have hqpos : 0 < q := ha.trans_le hq.1
    exact add_nonneg
      (mul_nonneg hqpos.le (sq_nonneg _))
      (mul_nonneg hqpos.le (sq_nonneg _))
  · apply intervalIntegral.integral_nonneg hab
    intro q hq
    exact div_nonneg (sq_nonneg _) (ha.trans_le hq.1).le

/-- A finite-interval control with explicit endpoint fluxes.  At nonzero
order this bounds the actual weighted K-square mass after division by `4t²`. -/
theorem k_weighted_mass_finite_control (t : ℝ) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    0 ≤ 4 * t ^ 2 *
        (∫ q in a..b, (imaginaryOrderK t q) ^ 2 / q) ∧
    4 * t ^ 2 *
        (∫ q in a..b, (imaginaryOrderK t q) ^ 2 / q) ≤
      (∫ q in a..b,
        q * (qDerivative t q) ^ 2 +
          q * (imaginaryOrderK t q) ^ 2) +
        |kFlux t a| + |kFlux t b| := by
  have hmass := (k_energy_and_weighted_mass_nonneg t ha hab).2
  have hEq := k_energy_finite t ha hab
  constructor
  · exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) hmass
  · have hA : kFlux t a ≤ |kFlux t a| := le_abs_self _
    have hB : -kFlux t b ≤ |kFlux t b| := neg_le_abs _
    linarith

end

end ImbalancedChen.Part3.ActualKRadialEnergyIdentity20261024zz
