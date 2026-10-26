import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-26.

The logarithmic endpoint majorant is genuinely L1 for positive Mellin
real part. The proof spends half the positive exponent to absorb log(q).
The integration interval is open at zero; no boundedness there is asserted.
-/

namespace ImbalancedChen.Part3.LogWeightedMellinL120261026b

noncomputable section
open Set Filter MeasureTheory
open scoped Topology

def logMellinWeight (sigma q : ℝ) : ℝ :=
  q ^ (sigma - 1) * (1 + |Real.log q|)

theorem logMellinWeight_nonneg {q : ℝ} (hq : 0 ≤ q) (sigma : ℝ) :
    0 ≤ logMellinWeight sigma q := by
  exact mul_nonneg (Real.rpow_nonneg hq _) (by positivity)

theorem measurable_logMellinWeight (sigma : ℝ) :
    Measurable (logMellinWeight sigma) := by
  unfold logMellinWeight
  fun_prop

/-- Explicit integrable power majorant; the constant diverges as sigma
approaches zero, as required by the actual endpoint threshold. -/
theorem logMellinWeight_le_power {sigma q : ℝ} (hs : 0 < sigma)
    (hq : 0 < q) (hq1 : q ≤ 1) :
    logMellinWeight sigma q ≤ (1 + 2 / sigma) * q ^ (sigma / 2 - 1) := by
  have hh : 0 < sigma / 2 := by linarith
  have hp : 0 ≤ q ^ (sigma / 2 - 1) := Real.rpow_nonneg hq.le _
  have hu : q ^ (sigma / 2) ≤ 1 := Real.rpow_le_one hq.le hq1 hh.le
  have hl := (Real.abs_log_mul_self_rpow_lt q (sigma / 2) hq hq1 hh).le
  rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hq.le _)] at hl
  have he : (1 : ℝ) / (sigma / 2) = 2 / sigma := by
    field_simp
  rw [he] at hl
  have hspl : q ^ (sigma - 1) = q ^ (sigma / 2 - 1) * q ^ (sigma / 2) := by
    rw [← Real.rpow_add hq.le]
    congr 1
    ring
  unfold logMellinWeight
  rw [hspl]
  have h := mul_le_mul_of_nonneg_left (add_le_add hu hl) hp
  nlinarith

/-- Genuine logarithmically weighted L1 at q=0, for every sigma>0. -/
theorem integrableOn_logMellinWeight {sigma B : ℝ} (hs : 0 < sigma)
    (hB : 0 < B) (hB1 : B ≤ 1) :
    IntegrableOn (logMellinWeight sigma) (Ioo 0 B) := by
  have hp : IntegrableOn (fun q : ℝ => q ^ (sigma / 2 - 1)) (Ioo 0 B) :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff hB).2 (by linarith)
  apply (hp.const_mul (1 + 2 / sigma)).mono'
    (measurable_logMellinWeight sigma).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with q hq
  rw [Real.norm_eq_abs, abs_of_nonneg (logMellinWeight_nonneg hq.1.le sigma)]
  exact logMellinWeight_le_power hs hq.1 (hq.2.le.trans hB1)

/-- This is the norm of the literal complex Mellin power times the
logarithmic factor, rather than a real-power replacement of that power. -/
theorem complexMellin_norm {s : ℂ} {q : ℝ} (hq : 0 < q) :
    ‖(q : ℂ) ^ (s - 1)‖ * (1 + |Real.log q|) = logMellinWeight s.re q := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hq]
  simp [logMellinWeight]

theorem integrableOn_complexMellin_log_norm {s : ℂ} {B : ℝ}
    (hs : 0 < s.re) (hB : 0 < B) (hB1 : B ≤ 1) :
    IntegrableOn (fun q : ℝ => ‖(q : ℂ) ^ (s - 1)‖ * (1 + |Real.log q|))
      (Ioo 0 B) := by
  apply (integrableOn_logMellinWeight hs hB hB1).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with q hq
  exact (complexMellin_norm hq.1).symm

end
end ImbalancedChen.Part3.LogWeightedMellinL120261026b
