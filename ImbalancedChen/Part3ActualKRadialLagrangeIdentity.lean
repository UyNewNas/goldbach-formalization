import ImbalancedChen.Part3ImaginaryOrderKSecondQDerivative
import Mathlib.Tactic

/-!
CODE_ONLY / SOURCEONLY / UNCOMPILED, 2026-10-24.  No acceptance credit.

The modes here are the actual positive-axis imaginary-order K integrals of
order `2 i t`, not abstract solutions to an assumed Sturm--Liouville ODE.
The input ODE, two q-derivative identities, and continuity all come from
`Part3ImaginaryOrderKSecondQDerivative` and its imports.  This module proves
the two-mode Lagrange identity and its finite positive-interval integral.
Neither an endpoint limit nor orthogonality is asserted.
-/

namespace ImbalancedChen.Part3.ActualKRadialLagrangeIdentity20261024zz

noncomputable section

open Set
open ImaginaryOrderKBesselSourceOnly
open ImaginaryOrderKQDerivativeSourceOnly
open ImaginaryOrderKSecondQDerivativeSourceOnly

/-- The Sturm--Liouville boundary concomitant for the actual K modes.
Its orientation fixes the sign in the spectral difference below. -/
def kBoundary (t s q : ℝ) : ℝ :=
  q * (qDerivative t q * imaginaryOrderK s q -
    imaginaryOrderK t q * qDerivative s q)

/-- Pointwise Lagrange identity for two real imaginary-order parameters.
The sign follows from `q²K''+qK'-(q²-4t²)K=0`. -/
theorem kBoundary_hasDerivAt (t s : ℝ) {q : ℝ} (hq : 0 < q) :
    HasDerivAt (kBoundary t s)
      (4 * (s ^ 2 - t ^ 2) *
        imaginaryOrderK t q * imaginaryOrderK s q / q) q := by
  have hKt := imaginaryOrderK_hasDerivAt_q_integral t hq
  have hKs := imaginaryOrderK_hasDerivAt_q_integral s hq
  have hDt := qDerivative_hasDerivAt_qSecond t hq
  have hDs := qDerivative_hasDerivAt_qSecond s hq
  have hproduct := (hasDerivAt_id q).mul
    ((hDt.mul hKs).sub (hKt.mul hDs))
  have hW : HasDerivAt (kBoundary t s)
      (qDerivative t q * imaginaryOrderK s q -
          imaginaryOrderK t q * qDerivative s q +
        q * (qSecond t q * imaginaryOrderK s q -
          imaginaryOrderK t q * qSecond s q)) q := by
    convert hproduct using 1
    · funext r
      rfl
    · ring
  have ht := actual_K_modifiedBessel_equation_integral t hq
  have hs := actual_K_modifiedBessel_equation_integral s hq
  have hmul : q *
      (qDerivative t q * imaginaryOrderK s q -
          imaginaryOrderK t q * qDerivative s q +
        q * (qSecond t q * imaginaryOrderK s q -
          imaginaryOrderK t q * qSecond s q)) =
      4 * (s ^ 2 - t ^ 2) *
        imaginaryOrderK t q * imaginaryOrderK s q := by
    linear_combination (imaginaryOrderK s q) * ht -
      (imaginaryOrderK t q) * hs
  apply hW.congr_deriv
  apply (eq_div_iff hq.ne').2
  exact hmul

theorem kBoundary_deriv (t s : ℝ) {q : ℝ} (hq : 0 < q) :
    deriv (kBoundary t s) q =
      4 * (s ^ 2 - t ^ 2) *
        imaginaryOrderK t q * imaginaryOrderK s q / q :=
  (kBoundary_hasDerivAt t s hq).deriv

/-- A finite-interval Green identity on the positive q-axis.  The integrand
has precisely the multiplicative `dq/q` Sturm--Liouville weight. -/
theorem k_green_finite (t s : ℝ) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    (∫ q in a..b,
      4 * (s ^ 2 - t ^ 2) *
        imaginaryOrderK t q * imaginaryOrderK s q / q) =
      kBoundary t s b - kBoundary t s a := by
  have ht : ContinuousOn (imaginaryOrderK t) (Ioi 0) :=
    (imaginaryOrderK_differentiableOn_q t).continuousOn
  have hs : ContinuousOn (imaginaryOrderK s) (Ioi 0) :=
    (imaginaryOrderK_differentiableOn_q s).continuousOn
  have hcont : ContinuousOn
      (fun q : ℝ => 4 * (s ^ 2 - t ^ 2) *
        imaginaryOrderK t q * imaginaryOrderK s q / q) (Ioi 0) :=
    ((continuousOn_const.mul ht).mul hs).div continuousOn_id
      (fun q hq => hq.ne')
  have hsub : Icc a b ⊆ Ioi (0 : ℝ) := by
    intro q hq
    exact ha.trans_le hq.1
  have hint : IntervalIntegrable
      (fun q : ℝ => 4 * (s ^ 2 - t ^ 2) *
        imaginaryOrderK t q * imaginaryOrderK s q / q) volume a b :=
    (hcont.mono hsub).intervalIntegrable_of_Icc hab
  have hd : ∀ q ∈ uIcc a b,
      HasDerivAt (kBoundary t s)
        (4 * (s ^ 2 - t ^ 2) *
          imaginaryOrderK t q * imaginaryOrderK s q / q) q := by
    intro q hq
    have hqI : q ∈ Icc a b := by
      simpa only [uIcc_of_le hab] using hq
    exact kBoundary_hasDerivAt t s (ha.trans_le hqI.1)
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint

/-- The equivalent form with the parameter difference outside the weighted
integral.  No distinctness condition on the two parameters is needed. -/
theorem k_green_finite_weighted (t s : ℝ) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    4 * (s ^ 2 - t ^ 2) *
      (∫ q in a..b,
        imaginaryOrderK t q * imaginaryOrderK s q / q) =
      kBoundary t s b - kBoundary t s a := by
  calc
    4 * (s ^ 2 - t ^ 2) *
        (∫ q in a..b,
          imaginaryOrderK t q * imaginaryOrderK s q / q) =
      ∫ q in a..b,
        4 * (s ^ 2 - t ^ 2) *
          (imaginaryOrderK t q * imaginaryOrderK s q / q) := by
            rw [intervalIntegral.integral_const_mul]
    _ = ∫ q in a..b,
        4 * (s ^ 2 - t ^ 2) *
          imaginaryOrderK t q * imaginaryOrderK s q / q := by
            apply intervalIntegral.integral_congr
            intro q
            ring
    _ = kBoundary t s b - kBoundary t s a := k_green_finite t s ha hab

end

end ImbalancedChen.Part3.ActualKRadialLagrangeIdentity20261024zz
