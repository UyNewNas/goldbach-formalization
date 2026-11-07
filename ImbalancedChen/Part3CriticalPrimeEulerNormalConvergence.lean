import ImbalancedChen.Part3ActualCriticalPrimeEulerSeries
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-! Actual normal convergence on every closed X-disk of radius r<1,
uniformly over the entire real critical spectral line. Finite coefficients
are proved continuous from their genuine entire arithmetic construction.
This gives joint continuity of the actual Euler sum, not just the rational
display. SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT. -/

noncomputable section
open Set Filter Complex
open scoped Topology BigOperators
open ImbalancedChen.Part3.NormalizedEisensteinPrimeAmplitude20261026b
open ImbalancedChen.Part3.EntireEisensteinPrimeAmplitude20261026b
open ImbalancedChen.Part3.EisensteinPrimePowerSplitBound20261026b
open ImbalancedChen.Part3.ActualCriticalPrimeEulerSeries20261026b

namespace ImbalancedChen.Part3.CriticalPrimeEulerNormalConvergence20261026b

def diskMajorant (r : ℝ) (k : ℕ) : ℝ := ((k + 1 : ℕ) : ℝ) * r ^ k

theorem diskMajorant_summable {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (diskMajorant r) := by
  have hr : ‖r‖ < 1 := by simpa only [Real.norm_eq_abs, abs_of_nonneg hr0] using hr1
  have hnat : Summable (fun k : ℕ => (k : ℝ) * r ^ k) :=
    (hasSum_coe_mul_geometric_of_norm_lt_one hr).summable
  have hgeom : Summable (fun k : ℕ => r ^ k) := summable_geometric_of_norm_lt_one hr
  simpa only [diskMajorant, Nat.cast_add, Nat.cast_one, add_mul, one_mul] using hnat.add hgeom

theorem criticalEulerTerm_continuous (p k : ℕ) :
    Continuous (fun q : ℝ × ℂ =>
      normalizedDivisorAmplitude (p ^ k) (1 / 2 + (q.1 : ℂ) * Complex.I) * q.2 ^ k) := by
  have hparam : Continuous (fun q : ℝ × ℂ => (1 / 2 : ℂ) + (q.1 : ℂ) * Complex.I) := by
    fun_prop
  exact ((normalizedDivisorAmplitude_differentiable (p ^ k)).continuous.comp hparam).mul
    (continuous_snd.pow k)

theorem criticalEulerTerm_disk_bound {p : ℕ} (hp : p.Prime)
    {r : ℝ} (hr0 : 0 ≤ r) (k : ℕ) (q : ℝ × ℂ) (hq : ‖q.2‖ ≤ r) :
    ‖normalizedDivisorAmplitude (p ^ k) (1 / 2 + (q.1 : ℂ) * Complex.I) * q.2 ^ k‖ ≤
      diskMajorant r k := by
  rw [norm_mul, norm_pow]
  calc
    _ ≤ ((k + 1 : ℕ) : ℝ) * ‖q.2‖ ^ k :=
      mul_le_mul_of_nonneg_right (normalizedAmplitude_prime_power_critical_norm hp k q.1)
        (pow_nonneg (norm_nonneg _) k)
    _ ≤ diskMajorant r k := by
      unfold diskMajorant
      gcongr

/-- The actual local series converges uniformly even with t unrestricted.
Only the closed X-disk radius is bounded away from one. -/
theorem criticalLocalEuler_uniform_disk {p : ℕ} (hp : p.Prime)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    TendstoUniformlyOn
      (fun H : ℕ => fun q : ℝ × ℂ =>
        ∑ k ∈ Finset.range H,
          normalizedDivisorAmplitude (p ^ k) (1 / 2 + (q.1 : ℂ) * Complex.I) * q.2 ^ k)
      (fun q : ℝ × ℂ => actualCriticalLocalEulerSeries p q.1 q.2)
      atTop {q : ℝ × ℂ | ‖q.2‖ ≤ r} := by
  exact tendstoUniformlyOn_tsum_nat (diskMajorant_summable hr0 hr1)
    (fun k q hq => criticalEulerTerm_disk_bound hp hr0 k q hq)

/-- Joint continuity belongs to the original infinite coefficient series;
it is justified by actual uniform summable bounds and term continuity. -/
theorem criticalLocalEuler_continuousOn_disk {p : ℕ} (hp : p.Prime)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ContinuousOn (fun q : ℝ × ℂ => actualCriticalLocalEulerSeries p q.1 q.2)
      {q : ℝ × ℂ | ‖q.2‖ ≤ r} := by
  exact continuousOn_tsum (fun k => (criticalEulerTerm_continuous p k).continuousOn)
    (diskMajorant_summable hr0 hr1) (fun k q hq => criticalEulerTerm_disk_bound hp hr0 k q hq)

end ImbalancedChen.Part3.CriticalPrimeEulerNormalConvergence20261026b
