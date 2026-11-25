import Mathlib

/-!
# Cauchy for the printed continuous trace

This is the manuscript-internal Cauchy step in Appendix A.5 of the
2026-11-06 manuscript, using the continuous measure `dt / pi` in
Appendix B, (104). The literal paired row and both energies have the
same `1 / pi` normalization. The left row remains conjugated.

The finite Cauchy inequality and integral Holder inequality are both
reused directly from Mathlib. No unrelated sieve import is required.
The final theorem consumes separate cumulative energy estimates, not
an estimate for the paired trace. It pays a squared source-row divisor
price exactly once after taking square roots. No classical spectral
estimate, actual automorphic instance, or full P3.5 closure is asserted.
-/

namespace ImbalancedChen.Part3.ContinuousTraceCauchy

noncomputable section

open MeasureTheory Set
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-- Finite-cusp Cauchy in the printed normalization, including empty
families and zero-energy rows. -/
theorem printed_trace_norm_le (left right : ι → ℂ) :
    ‖∑ i, star (left i) * right i / (Real.pi : ℂ)‖ ≤
      Real.sqrt (∑ i, ‖left i‖ ^ 2 / Real.pi) *
        Real.sqrt (∑ i, ‖right i‖ ^ 2 / Real.pi) := by
  have hnormal (z : ℂ) :
      Real.sqrt (‖z‖ ^ 2 / Real.pi) = ‖z‖ / Real.sqrt Real.pi := by
    rw [Real.sqrt_div (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]
  calc
    _ ≤ ∑ i, ‖star (left i) * right i / (Real.pi : ℂ)‖ := norm_sum_le _ _
    _ = ∑ i, Real.sqrt (‖left i‖ ^ 2 / Real.pi) *
        Real.sqrt (‖right i‖ ^ 2 / Real.pi) := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [hnormal, norm_div, norm_mul, norm_star, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos Real.pi_pos]
      rw [div_mul_div_comm, ← pow_two, Real.sq_sqrt Real.pi_pos.le]
    _ ≤ _ := Real.sum_sqrt_mul_sqrt_le Finset.univ
      (fun i => by positivity) (fun i => by positivity)

/-- Integral Cauchy on one common compact height window. In particular,
the same measure and the same original rows appear in all three integrals. -/
theorem integral_printed_trace_norm_le
    (left right : ι → ℝ → ℂ)
    (hleft : ∀ i, Continuous (left i)) (hright : ∀ i, Continuous (right i))
    (T : ℝ) :
    (∫ t in Icc (-T) T, ‖∑ i, star (left i t) * right i t / (Real.pi : ℂ)‖) ≤
      Real.sqrt (∫ t in Icc (-T) T, ∑ i, ‖left i t‖ ^ 2 / Real.pi) *
        Real.sqrt (∫ t in Icc (-T) T, ∑ i, ‖right i t‖ ^ 2 / Real.pi) := by
  let μ := volume.restrict (Icc (-T) T)
  let L : ℝ → ℝ := fun t => ∑ i, ‖left i t‖ ^ 2 / Real.pi
  let R : ℝ → ℝ := fun t => ∑ i, ‖right i t‖ ^ 2 / Real.pi
  have hL : Continuous L :=
    continuous_finsetSum _ (fun i _ => ((hleft i).norm.pow 2).div_const _)
  have hR : Continuous R :=
    continuous_finsetSum _ (fun i _ => ((hright i).norm.pow 2).div_const _)
  have hL0 (t : ℝ) : 0 ≤ L t := by dsimp [L]; positivity
  have hR0 (t : ℝ) : 0 ≤ R t := by dsimp [R]; positivity
  have hLs : (fun t => (Real.sqrt (L t)) ^ 2) = L :=
    funext fun t => Real.sq_sqrt (hL0 t)
  have hRs : (fun t => (Real.sqrt (R t)) ^ 2) = R :=
    funext fun t => Real.sq_sqrt (hR0 t)
  have hLm : MemLp (fun t => Real.sqrt (L t)) 2 μ := by
    apply (memLp_two_iff_integrable_sq hL.sqrt.aestronglyMeasurable).2
    rw [hLs]
    exact hL.continuousOn.integrableOn_compact isCompact_Icc
  have hRm : MemLp (fun t => Real.sqrt (R t)) 2 μ := by
    apply (memLp_two_iff_integrable_sq hR.sqrt.aestronglyMeasurable).2
    rw [hRs]
    exact hR.continuousOn.integrableOn_compact isCompact_Icc
  have hHolder := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall fun t => Real.sqrt_nonneg (L t))
    (Filter.Eventually.of_forall fun t => Real.sqrt_nonneg (R t))
    (by simpa only [ENNReal.ofReal_ofNat] using hLm)
    (by simpa only [ENNReal.ofReal_ofNat] using hRm)
  have hHolder' : (∫ t, Real.sqrt (L t) * Real.sqrt (R t) ∂μ) ≤
      Real.sqrt (∫ t, L t ∂μ) * Real.sqrt (∫ t, R t ∂μ) := by
    simpa only [Real.rpow_ofNat, ← Real.sqrt_eq_rpow, hLs, hRs] using hHolder
  have hp : Continuous (fun t => ‖∑ i,
      star (left i t) * right i t / (Real.pi : ℂ)‖) :=
    (continuous_finsetSum _ (fun i _ => ((hleft i).star.mul (hright i)).div_const _)).norm
  have hb : Continuous (fun t => Real.sqrt (L t) * Real.sqrt (R t)) :=
    hL.sqrt.mul hR.sqrt
  have hcomp := integral_mono_ae (μ := μ)
    (hp.continuousOn.integrableOn_compact isCompact_Icc)
    (hb.continuousOn.integrableOn_compact isCompact_Icc)
    (Filter.Eventually.of_forall fun t => printed_trace_norm_le (fun i => left i t) (fun i => right i t))
  exact hcomp.trans hHolder'

/-- A bounded physical test remains outside the Cauchy energies. The bound
is used only on the common integration window. -/
theorem norm_integral_test_mul_printed_trace_le
    (left right : ι → ℝ → ℂ)
    (hleft : ∀ i, Continuous (left i)) (hright : ∀ i, Continuous (right i))
    (test : ℝ → ℂ) (htest : Continuous test) (T B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ t ∈ Icc (-T) T, ‖test t‖ ≤ B) :
    ‖∫ t in Icc (-T) T,
      test t * (∑ i, star (left i t) * right i t / (Real.pi : ℂ))‖ ≤
      B * (Real.sqrt (∫ t in Icc (-T) T, ∑ i, ‖left i t‖ ^ 2 / Real.pi) *
        Real.sqrt (∫ t in Icc (-T) T, ∑ i, ‖right i t‖ ^ 2 / Real.pi)) := by
  let μ := volume.restrict (Icc (-T) T)
  let P : ℝ → ℂ := fun t => ∑ i, star (left i t) * right i t / (Real.pi : ℂ)
  have hP : Continuous P :=
    continuous_finsetSum _ (fun i _ => ((hleft i).star.mul (hright i)).div_const _)
  have htestP : Integrable (fun t => ‖test t * P t‖) μ :=
    (htest.mul hP).norm.continuousOn.integrableOn_compact isCompact_Icc
  have hBP : Integrable (fun t => B * ‖P t‖) μ :=
    (hP.norm.const_mul B).continuousOn.integrableOn_compact isCompact_Icc
  have hcomp : (∫ t, ‖test t * P t‖ ∂μ) ≤ ∫ t, B * ‖P t‖ ∂μ := by
    apply integral_mono_ae htestP hBP
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hbound t ht) (norm_nonneg _)
  calc
    ‖∫ t, test t * P t ∂μ‖ ≤ ∫ t, ‖test t * P t‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ t, B * ‖P t‖ ∂μ := hcomp
    _ = B * (∫ t, ‖P t‖ ∂μ) := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (integral_printed_trace_norm_le left right hleft hright T) hB

/-- Exact payment of the cumulative source-row invoice. The two energies
are bounded separately. A divisor price squared on the source side becomes
one divisor price in the actual tested trace; the common sieve constant also
appears once. No paired-trace estimate is assumed. -/
theorem norm_integral_test_mul_printed_trace_le_of_energy_bounds
    (left right : ι → ℝ → ℂ)
    (hleft : ∀ i, Continuous (left i)) (hright : ∀ i, Continuous (right i))
    (test : ℝ → ℂ) (htest : Continuous test)
    (T B C d Eleft Eright : ℝ)
    (hB : 0 ≤ B) (hC : 0 ≤ C) (hd : 0 ≤ d)
    (hbound : ∀ t ∈ Icc (-T) T, ‖test t‖ ≤ B)
    (hleftEnergy : (∫ t in Icc (-T) T, ∑ i, ‖left i t‖ ^ 2 / Real.pi) ≤ C * Eleft)
    (hrightEnergy : (∫ t in Icc (-T) T, ∑ i, ‖right i t‖ ^ 2 / Real.pi) ≤
      d ^ 2 * (C * Eright)) :
    ‖∫ t in Icc (-T) T,
      test t * (∑ i, star (left i t) * right i t / (Real.pi : ℂ))‖ ≤
      B * d * C * (Real.sqrt Eleft * Real.sqrt Eright) := by
  have hroots : Real.sqrt (C * Eleft) * Real.sqrt (d ^ 2 * (C * Eright)) =
      d * C * (Real.sqrt Eleft * Real.sqrt Eright) := by
    rw [Real.sqrt_mul hC, Real.sqrt_mul (sq_nonneg d), Real.sqrt_mul hC,
      Real.sqrt_sq hd]
    calc
      _ = d * (Real.sqrt C) ^ 2 * (Real.sqrt Eleft * Real.sqrt Eright) := by ring
      _ = _ := by rw [Real.sq_sqrt hC]
  calc
    _ ≤ B * (Real.sqrt (∫ t in Icc (-T) T, ∑ i, ‖left i t‖ ^ 2 / Real.pi) *
        Real.sqrt (∫ t in Icc (-T) T, ∑ i, ‖right i t‖ ^ 2 / Real.pi)) :=
      norm_integral_test_mul_printed_trace_le left right hleft hright test htest T B hB hbound
    _ ≤ B * (Real.sqrt (C * Eleft) * Real.sqrt (d ^ 2 * (C * Eright))) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul (Real.sqrt_le_sqrt hleftEnergy) (Real.sqrt_le_sqrt hrightEnergy)
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hB
    _ = _ := by rw [hroots]; ring

end
end ImbalancedChen.Part3.ContinuousTraceCauchy
