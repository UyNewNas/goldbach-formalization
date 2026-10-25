import ImbalancedChen.Part3GeneralISmallQWronskian
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Conjugation and an actual oscillatory asymptotic for the general I-series

SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
Conjugation is proved term by term from the actual reciprocal-Gamma
coefficients, then transported through the actual tsum and positive-base
complex power. The oscillatory asymptotic is a norm error tending to zero;
no nonexistent unscaled pointwise limit is claimed at imaginary order.
No scattering measure, KL identity, or P3 saving is assumed or concluded.
-/

namespace ImbalancedChen.Part3.GeneralIConjugation20261025a

noncomputable section
open Complex Filter Set Topology
open GeneralComplexISeriesSourceOnly GeneralIQODE20261025a
open GeneralISmallQWronskian20261025a

theorem conj_generalICoeff (nu : ℂ) (n : ℕ) :
    conj (generalICoeff nu n) = generalICoeff (conj nu) n := by
  simp [generalICoeff, ← Complex.Gamma_conj]

theorem conj_generalICore (nu z : ℂ) :
    conj (generalICore nu z) = generalICore (conj nu) (conj z) := by
  simp only [generalICore, Complex.conj_tsum]
  apply tsum_congr
  intro n
  rw [map_mul, conj_generalICoeff, map_pow]

/-- Positive real bases do not meet the principal logarithm cut. -/
theorem conj_positive_cpow (nu : ℂ) {x : ℝ} (hx : 0 < x) :
    conj ((x : ℂ) ^ nu) = (x : ℂ) ^ (conj nu) := by
  have harg : (x : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hx.le]
    exact Real.pi_ne_zero.symm
  simpa only [Complex.conj_ofReal] using (Complex.cpow_conj (x : ℂ) nu harg).symm

/-- Actual series conjugation; the identity itself needs no order-strip
restriction, since conjugation also preserves the tsum convention. -/
theorem conj_generalI (nu : ℂ) {q : ℝ} (hq : 0 < q) :
    conj (generalI nu q) = generalI (conj nu) q := by
  simp only [generalI, map_mul, conj_positive_cpow nu (div_pos hq (by norm_num)),
    conj_generalICore, map_pow, Complex.conj_ofReal]

/-- Conjugation of the actual real-q derivative on its convergence strip. -/
theorem deriv_generalI_conj {nu : ℂ} (hnu : -1 < nu.re) {q : ℝ} (hq : 0 < q) :
    deriv (generalI (conj nu)) q = conj (deriv (generalI nu) q) := by
  have h := (generalI_differentiableAt hnu hq).hasDerivAt.star
  have hconj : HasDerivAt (generalI (conj nu)) (conj (deriv (generalI nu) q)) q := by
    apply h.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hq] with x hx
    exact (conj_generalI nu hx).symm
  exact hconj.deriv

theorem generalI_neg_imaginary_eq_conj (tau : ℝ) {q : ℝ} (hq : 0 < q) :
    generalI (-((tau : ℂ) * I)) q = conj (generalI ((tau : ℂ) * I) q) := by
  simpa using (conj_generalI ((tau : ℂ) * I) hq).symm

theorem deriv_generalI_neg_imaginary_eq_conj (tau : ℝ) {q : ℝ} (hq : 0 < q) :
    deriv (generalI (-((tau : ℂ) * I))) q =
      conj (deriv (generalI ((tau : ℂ) * I)) q) := by
  have hnu : -1 < ((tau : ℂ) * I).re := by simp
  simpa using deriv_generalI_conj hnu hq

/-- Genuine oscillatory leading term: the unit-modulus phase is retained
and the norm of the actual remainder tends to zero as q tends to 0+. -/
theorem tendsto_imaginaryI_oscillatory_error_zero (tau : ℝ) :
    Tendsto (fun q : ℝ => ‖generalI ((tau : ℂ) * I) q -
      (((q / 2 : ℝ) : ℂ) ^ ((tau : ℂ) * I)) *
        (Complex.Gamma ((tau : ℂ) * I + 1))⁻¹‖)
      (𝓝[>] 0) (𝓝 0) := by
  have hnu : -1 < ((tau : ℂ) * I).re := by simp
  have hlim : Tendsto
      (fun q : ℝ => ‖generalICore ((tau : ℂ) * I)
        (((q / 2 : ℝ) : ℂ) ^ (2 : ℕ)) -
          (Complex.Gamma ((tau : ℂ) * I + 1))⁻¹‖)
      (𝓝[>] 0) (𝓝 0) := by
    simpa only [sub_self, norm_zero] using
      ((tendsto_generalICore_small_q hnu).sub tendsto_const_nhds).norm
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with q hq
  symm
  rw [generalI, ← mul_sub, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos (div_pos hq (by norm_num))]
  simp

end
end ImbalancedChen.Part3.GeneralIConjugation20261025a
