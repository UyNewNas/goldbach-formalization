import ImbalancedChen.P0RamanujanMultiplicativeGcdBound
import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
The actual nonzero-frequency Ramanujan Dirichlet series.
The project finite Ramanujan sum is already identified with the true
Moebius convolution. Its actual gcd bound proves absolute convergence;
Mathlib's absolutely convergent convolution theorem performs the divisor
rearrangement. The finite divisor gate and the proved reciprocal-Moebius
zeta identity yield the literal divisor-sum / Riemann-zeta quotient.

No series summability, series evaluation or divisor rearrangement is an
input. The result holds on Re(z)>1, hence includes every real w>2.
SOURCE_WRITTEN_UNCOMPILED / NOT ROOT ACCEPTED.
-/

namespace ImbalancedChen.Part3ActualRamanujanDirichletSeries

noncomputable section

open Finset
open scoped BigOperators
open ImbalancedChen.Part3.OriginalSmoothPoissonTail.Physical.ZeroMode
open ImbalancedChen.Part3.RamanujanMultiplicativeGcdBound20261025a

/-- The actual finite generalized divisor factor sigma_(1-z)(N). -/
def divisorFactor (N : ℕ) (z : ℂ) : ℂ :=
  ∑ d ∈ N.divisors, (d : ℂ) ^ (1 - z)

private theorem gated_norm_bound {N : ℕ} (hN : 0 < N) (d : ℕ) :
    ‖divisorGatedId N d‖ ≤ (N : ℝ) := by
  by_cases hd : d ∣ N
  · simp only [divisorGatedId, ArithmeticFunction.coe_mk, if_pos hd, Complex.norm_natCast]
    exact_mod_cast Nat.le_of_dvd hN hd
  · simp only [divisorGatedId, ArithmeticFunction.coe_mk, if_neg hd, norm_zero]
    exact Nat.cast_nonneg _

/-- Convergence is proved from the real finite gcd bound, rather than
passed as a hypothesis to a Dirichlet-series multiplication theorem. -/
theorem ramanujan_LSeriesSummable (n : ℤ) (hn : n ≠ 0)
    {z : ℂ} (hz : 1 < z.re) :
    LSeriesSummable (fun c : ℕ => ramanujan c n) z := by
  apply LSeriesSummable_of_bounded_of_one_lt_re (m := (n.natAbs : ℝ)) _ hz
  intro c _hc
  exact (norm_ramanujan_le_gcd c n).trans
    (by exact_mod_cast Nat.gcd_le_right c (Int.natAbs_pos.mpr hn))

private theorem ramanujan_zero (n : ℤ) : ramanujan 0 n = 0 := by
  simp [ramanujan, kloosterman]

/-- The raw complex-power series, including its zero summand at c=0,
is genuinely absolutely convergent. -/
theorem ramanujan_power_summable (n : ℤ) (hn : n ≠ 0)
    {z : ℂ} (hz : 1 < z.re) :
    Summable (fun c : ℕ => ramanujan c n * (c : ℂ) ^ (-z)) := by
  exact (ramanujan_LSeriesSummable n hn hz).congr
    (fun c => LSeries.term_def₀ (ramanujan_zero n) z c)

theorem ramanujan_power_norm_summable (n : ℤ) (hn : n ≠ 0)
    {z : ℂ} (hz : 1 < z.re) :
    Summable (fun c : ℕ => ‖ramanujan c n * (c : ℂ) ^ (-z)‖) :=
  summable_norm_iff.mpr (ramanujan_power_summable n hn hz)

/-- The divisor-gated arithmetic function has literal finite support.
Its L-series is evaluated as an actual finite generalized divisor sum. -/
theorem LSeries_divisorGatedId {N : ℕ} (hN : N ≠ 0) (z : ℂ) :
    LSeries (divisorGatedId N) z = divisorFactor N z := by
  classical
  calc
    _ = ∑ d ∈ N.divisors, LSeries.term (divisorGatedId N) z d := by
      apply tsum_eq_sum
      intro d hd
      by_cases hd0 : d = 0
      · subst d
        exact LSeries.term_zero _ _
      · have hnot : ¬ d ∣ N := fun h => hd (Nat.mem_divisors.mpr ⟨h, hN⟩)
        simp only [LSeries.term_of_ne_zero hd0, divisorGatedId,
          ArithmeticFunction.coe_mk, if_neg hnot, zero_div]
    _ = divisorFactor N z := by
      apply Finset.sum_congr rfl
      intro d hd
      have hd0 : d ≠ 0 := (Nat.pos_of_mem_divisors hd).ne'
      have hdC : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd0
      have hdiv := Nat.dvd_of_mem_divisors hd
      rw [LSeries.term_of_ne_zero hd0]
      simp only [divisorGatedId, ArithmeticFunction.coe_mk, if_pos hdiv]
      rw [div_eq_mul_inv, ← Complex.cpow_neg]
      rw [sub_eq_add_neg, Complex.cpow_add _ _ hdC, Complex.cpow_one]

/-- True Moebius divisor rearrangement with all convergence hypotheses
proved from coefficients, not supplied by a caller. -/
theorem ramanujan_LSeries_factor (n : ℤ) (hn : n ≠ 0)
    {z : ℂ} (hz : 1 < z.re) :
    LSeries (fun c : ℕ => ramanujan c n) z =
      LSeries (ArithmeticFunction.moebius : ArithmeticFunction ℂ) z *
        divisorFactor n.natAbs z := by
  have hN : 0 < n.natAbs := Int.natAbs_pos.mpr hn
  have hgate : LSeriesSummable (divisorGatedId n.natAbs) z :=
    LSeriesSummable_of_bounded_of_one_lt_re (fun d _ => gated_norm_bound hN d) hz
  have hmu : LSeriesSummable (ArithmeticFunction.moebius : ArithmeticFunction ℂ) z :=
    ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hz
  calc
    _ = LSeries (ramanujanArithmetic n.natAbs) z := by
      apply LSeries_congr
      intro c _hc
      exact (ramanujanArithmetic_apply c n).symm
    _ = LSeries (ArithmeticFunction.moebius : ArithmeticFunction ℂ) z *
        LSeries (divisorGatedId n.natAbs) z :=
      ArithmeticFunction.LSeries_mul' hmu hgate
    _ = _ := by rw [LSeries_divisorGatedId hN.ne']

/-- The product-with-zeta identity is derived from the actual Moebius
inverse, prior to dividing by the proved nonzero Riemann zeta value. -/
theorem zeta_mul_ramanujan_LSeries (n : ℤ) (hn : n ≠ 0)
    {z : ℂ} (hz : 1 < z.re) :
    riemannZeta z * LSeries (fun c : ℕ => ramanujan c n) z =
      divisorFactor n.natAbs z := by
  have hmu := ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius hz
  rw [ArithmeticFunction.LSeries_zeta_eq_riemannZeta hz] at hmu
  rw [ramanujan_LSeries_factor n hn hz, ← mul_assoc, hmu, one_mul]

theorem ramanujan_LSeries_eq_divisorFactor_div_zeta (n : ℤ) (hn : n ≠ 0)
    {z : ℂ} (hz : 1 < z.re) :
    LSeries (fun c : ℕ => ramanujan c n) z =
      divisorFactor n.natAbs z / riemannZeta z := by
  have hzeta : riemannZeta z ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hz
  apply (eq_div_iff hzeta).mpr
  simpa only [mul_comm] using zeta_mul_ramanujan_LSeries n hn hz

/-- Real generalized divisor exponents agree with the exact complex
Dirichlet factor, without replacing the literal divisor carrier. -/
theorem divisorFactor_ofReal (N : ℕ) (w : ℝ) :
    divisorFactor N (w : ℂ) =
      ((∑ d ∈ N.divisors, (d : ℝ) ^ (1 - w) : ℝ) : ℂ) := by
  unfold divisorFactor
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro d _hd
  rw [Complex.ofReal_cpow (Nat.cast_nonneg d)]
  simp only [Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_natCast]

private theorem term_ofReal (n : ℤ) (w : ℝ) (c : ℕ) :
    LSeries.term (fun d : ℕ => ramanujan d n) (w : ℂ) c =
      ramanujan c n * (((c : ℝ) ^ (-w) : ℝ) : ℂ) := by
  rw [LSeries.term_def₀ (ramanujan_zero n), Complex.ofReal_cpow (Nat.cast_nonneg c)]
  simp only [Complex.ofReal_neg, Complex.ofReal_natCast]

/-- Absolute convergence for real w>1, hence in the required w>2 range. -/
theorem real_power_norm_summable (n : ℤ) (hn : n ≠ 0)
    {w : ℝ} (hw : 1 < w) :
    Summable (fun c : ℕ => ‖ramanujan c n * (((c : ℝ) ^ (-w) : ℝ) : ℂ)‖) := by
  have hz : 1 < (w : ℂ).re := by simpa using hw
  have h := summable_norm_iff.mpr (ramanujan_LSeriesSummable n hn hz)
  exact h.congr (fun c => congrArg norm (term_ofReal n w c))

/-- The literal actual Ramanujan Dirichlet series equals
sigma_(1-w)(abs n)/zeta(w). All sums are actual finite/infinite sums.
The coefficient gcd bound proves the absolute convergence separately. -/
theorem real_ramanujan_dirichlet_formula (n : ℤ) (hn : n ≠ 0)
    {w : ℝ} (hw : 1 < w) :
    (∑' c : ℕ, ramanujan c n * (((c : ℝ) ^ (-w) : ℝ) : ℂ)) =
      ((∑ d ∈ n.natAbs.divisors, (d : ℝ) ^ (1 - w) : ℝ) : ℂ) /
        riemannZeta (w : ℂ) := by
  have hz : 1 < (w : ℂ).re := by simpa using hw
  have h := ramanujan_LSeries_eq_divisorFactor_div_zeta n hn hz
  have hraw : LSeries (fun c : ℕ => ramanujan c n) (w : ℂ) =
      ∑' c : ℕ, ramanujan c n * (((c : ℝ) ^ (-w) : ℝ) : ℂ) := by
    apply tsum_congr
    intro c
    exact term_ofReal n w c
  rw [hraw, divisorFactor_ofReal] at h
  exact h

end

end ImbalancedChen.Part3ActualRamanujanDirichletSeries
