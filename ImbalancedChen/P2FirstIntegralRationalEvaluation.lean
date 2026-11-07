import ImbalancedChen.P2FirstIntegralSeries
import Mathlib.Tactic

/-!
SOURCE ONLY / NOT ELABORATED / no producer or numerical replay.
Prospective import: stage the sibling P2FirstIntegralSeries.lean at
ImbalancedChen/P2FirstIntegralSeries.lean before an authorized future build.

This continues the actual integral enclosure, replacing the unevaluated
finite rational-function integrals by explicit rational endpoint sums.
Every uniform mesh has exactly the original endpoints 2 and Theta/rho-1;
`originalFirstIntegral_rational_mesh` proves soundness directly for the actual
logarithmic integral. `originalFirstIntegral_dyadic_enclosure` instantiates a
whole-domain dyadic subdivision, not a sampled or cropped domain.

The ℚ formulas are finite sums, powers and divisions.  No integral value or
endpoint certificate is assumed.  We do not execute or claim a selected U1
decimal comparison: the catalog's frozen positive-series source/output payload
is unavailable, and no numeric replay is permitted in this phase.
-/

namespace ImbalancedChen.P2FirstIntegralRationalEvaluationSourceOnly

noncomputable section

open Set MeasureTheory
open P2FirstIntegralSeriesSourceOnly OriginalThirdPositiveLogSourceOnly

def logLo (n : ℕ) (s : ℝ) : ℝ := logPartial (coordinate s) n

def logHi (n : ℕ) (s : ℝ) : ℝ :=
  logLo n s + coordinate s ^ (n + 1) / (((n : ℝ) + 1) * (1 - coordinate s))

theorem endpoint_log_bounds (n : ℕ) {s : ℝ} (hs : s ∈ Icc (2 : ℝ) stop) :
    logLo n s ≤ Real.log (s - 1) ∧ Real.log (s - 1) ≤ logHi n s := by
  have hz := coordinate_bounds hs
  have h := positive_series_bounds hz.1 (lt_of_le_of_lt hz.2 q_lt_one) n
  have he : 1 - coordinate s = (s - 1)⁻¹ := by
    dsimp [coordinate]
    ring
  simpa only [he, Real.log_inv, neg_neg, logLo, logHi] using h

theorem logLo_nonneg (n : ℕ) {s : ℝ} (hs : s ∈ Icc (2 : ℝ) stop) :
    0 ≤ logLo n s := by
  dsimp [logLo, logPartial]
  exact Finset.sum_nonneg fun i hi =>
    div_nonneg (pow_nonneg (coordinate_bounds hs).1 _) (by positivity)

def cellLo (n : ℕ) (a b : ℝ) : ℝ := (b - a) * (logLo n a / b)

def cellHi (n : ℕ) (a b : ℝ) : ℝ := (b - a) * (logHi n b / a)

theorem cell_intervalIntegrable {a b : ℝ}
    (ha : 2 ≤ a) (hab : a ≤ b) (hb : b ≤ stop) :
    IntervalIntegrable kernel volume a b := by
  apply ContinuousOn.intervalIntegrable_of_Icc hab
  apply continuousOn_kernel.mono
  intro s hs
  exact ⟨ha.trans hs.1, hs.2.trans hb⟩

/-- Rational endpoint rules bound the actual logarithmic integrand throughout
the closed cell.  No monotonicity of the quotient itself is asserted. -/
theorem cell_pointwise_bounds (n : ℕ) {a b s : ℝ}
    (ha : 2 ≤ a) (hab : a ≤ b) (hb : b ≤ stop) (hs : s ∈ Icc a b) :
    logLo n a / b ≤ kernel s ∧ kernel s ≤ logHi n b / a := by
  have haDomain : a ∈ Icc (2 : ℝ) stop := ⟨ha, hab.trans hb⟩
  have hbDomain : b ∈ Icc (2 : ℝ) stop := ⟨ha.trans hab, hb⟩
  have haPos : 0 < a := by linarith
  have hsPos : 0 < s := by linarith [hs.1]
  have haLogPos : 0 < a - 1 := by linarith
  have hsLogPos : 0 < s - 1 := by linarith [hs.1]
  have hlo := (endpoint_log_bounds n haDomain).1
  have hhi := (endpoint_log_bounds n hbDomain).2
  have hnumLo : logLo n a ≤ Real.log (s - 1) :=
    hlo.trans (Real.log_le_log haLogPos (by linarith [hs.1]))
  have hnumHi : Real.log (s - 1) ≤ logHi n b :=
    (Real.log_le_log hsLogPos (by linarith [hs.2])).trans hhi
  have hhiNonneg : 0 ≤ logHi n b :=
    (Real.log_nonneg (by linarith [ha.trans hab] : 1 ≤ b - 1)).trans hhi
  constructor
  · exact (div_le_div_of_nonneg_left (logLo_nonneg n haDomain) hsPos hs.2).trans
      ((div_le_div_iff_of_pos_right hsPos).2 hnumLo)
  · exact ((div_le_div_iff_of_pos_right hsPos).2 hnumHi).trans
      (div_le_div_of_nonneg_left hhiNonneg haPos hs.1)

/-- Both endpoints are included in the analytic comparison and the exact width
multiplies each bound.  The result is also valid for a zero-width cell. -/
theorem integral_cell_bounds (n : ℕ) {a b : ℝ}
    (ha : 2 ≤ a) (hab : a ≤ b) (hb : b ≤ stop) :
    cellLo n a b ≤ (∫ s in a..b, kernel s) ∧
      (∫ s in a..b, kernel s) ≤ cellHi n a b := by
  have hk := cell_intervalIntegrable ha hab hb
  have hl : IntervalIntegrable (fun _ : ℝ => logLo n a / b) volume a b :=
    intervalIntegrable_const
  have hu : IntervalIntegrable (fun _ : ℝ => logHi n b / a) volume a b :=
    intervalIntegrable_const
  constructor
  · have h := intervalIntegral.integral_mono_on hab hl hk
      (fun s hs => (cell_pointwise_bounds n ha hab hb hs).1)
    simpa only [intervalIntegral.integral_const, smul_eq_mul, cellLo] using h
  · have h := intervalIntegral.integral_mono_on hab hk hu
      (fun s hs => (cell_pointwise_bounds n ha hab hb hs).2)
    simpa only [intervalIntegral.integral_const, smul_eq_mul, cellHi] using h

def meshPoint (M i : ℕ) : ℝ := 2 + (stop - 2) * (i : ℝ) / (M : ℝ)

theorem meshPoint_zero (M : ℕ) : meshPoint M 0 = 2 := by simp [meshPoint]

theorem meshPoint_end {M : ℕ} (hM : 0 < M) : meshPoint M M = stop := by
  have hM0 : (M : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hM)
  simp only [meshPoint, mul_div_cancel_right₀ _ hM0]
  ring

theorem meshPoint_mono {M i j : ℕ} (hM : 0 < M) (hij : i ≤ j) :
    meshPoint M i ≤ meshPoint M j := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hijr : (i : ℝ) ≤ j := by exact_mod_cast hij
  have h := (div_le_div_iff_of_pos_right hMr).2
    (mul_le_mul_of_nonneg_left hijr (sub_nonneg.mpr two_le_stop))
  dsimp [meshPoint]
  linarith

theorem meshPoint_mem {M i : ℕ} (hM : 0 < M) (hi : i ≤ M) :
    meshPoint M i ∈ Icc (2 : ℝ) stop := by
  constructor
  · simpa only [meshPoint_zero] using meshPoint_mono hM (Nat.zero_le i)
  · simpa only [meshPoint_end hM] using meshPoint_mono hM hi

theorem mesh_integral_sum {M : ℕ} (hM : 0 < M) :
    (∑ i ∈ Finset.range M,
      ∫ s in meshPoint M i..meshPoint M (i + 1), kernel s) =
        ∫ s in (2 : ℝ)..stop, kernel s := by
  have h := intervalIntegral.sum_integral_adjacent_intervals
    (a := meshPoint M) (f := kernel) (μ := volume) (n := M) (fun i hi =>
      cell_intervalIntegrable (meshPoint_mem hM (Nat.le_of_lt hi)).1
        (meshPoint_mono hM (Nat.le_succ i))
        (meshPoint_mem hM (Nat.succ_le_of_lt hi)).2)
  simpa only [meshPoint_zero, meshPoint_end hM] using h

def realMeshLo (M n : ℕ) : ℝ :=
  (4 / theta) * ∑ i ∈ Finset.range M, cellLo n (meshPoint M i) (meshPoint M (i + 1))

def realMeshHi (M n : ℕ) : ℝ :=
  (4 / theta) * ∑ i ∈ Finset.range M, cellHi n (meshPoint M i) (meshPoint M (i + 1))

/-- Whole-domain finite-sum enclosure.  The only input is a positive number of
cells and a series order, never an assumed integral or a target constant. -/
theorem originalFirstIntegral_mesh_enclosure {M : ℕ} (hM : 0 < M) (n : ℕ) :
    realMeshLo M n ≤ originalFirstIntegral ∧ originalFirstIntegral ≤ realMeshHi M n := by
  have hc (i : ℕ) (hi : i ∈ Finset.range M) :=
    integral_cell_bounds n (meshPoint_mem hM (Nat.le_of_lt (Finset.mem_range.mp hi))).1
      (meshPoint_mono hM (Nat.le_succ i))
      (meshPoint_mem hM (Nat.succ_le_of_lt (Finset.mem_range.mp hi))).2
  have hlo := Finset.sum_le_sum (fun i hi => (hc i hi).1)
  have hhi := Finset.sum_le_sum (fun i hi => (hc i hi).2)
  rw [mesh_integral_sum hM] at hlo hhi
  exact ⟨mul_le_mul_of_nonneg_left hlo prefactor_pos.le,
    mul_le_mul_of_nonneg_left hhi prefactor_pos.le⟩

/-! Fully rational versions: evaluation of these expressions does not require
any quadrature, logarithm oracle, or floating-point arithmetic. -/

def coordinateQ (s : ℚ) : ℚ := 1 - 1 / (s - 1)

def logLoQ (n : ℕ) (s : ℚ) : ℚ :=
  ∑ i ∈ Finset.range n, coordinateQ s ^ (i + 1) / ((i : ℚ) + 1)

def logHiQ (n : ℕ) (s : ℚ) : ℚ :=
  logLoQ n s + coordinateQ s ^ (n + 1) / (((n : ℚ) + 1) * (1 - coordinateQ s))

def meshPointQ (M i : ℕ) : ℚ := 2 + (51 / 2375) * (i : ℚ) / (M : ℚ)

def cellLoQ (n : ℕ) (a b : ℚ) : ℚ := (b - a) * (logLoQ n a / b)

def cellHiQ (n : ℕ) (a b : ℚ) : ℚ := (b - a) * (logHiQ n b / a)

def rationalMeshLo (M n : ℕ) : ℚ :=
  (2000 / 299) * ∑ i ∈ Finset.range M,
    cellLoQ n (meshPointQ M i) (meshPointQ M (i + 1))

def rationalMeshHi (M n : ℕ) : ℚ :=
  (2000 / 299) * ∑ i ∈ Finset.range M,
    cellHiQ n (meshPointQ M i) (meshPointQ M (i + 1))

theorem coordinateQ_cast (s : ℚ) : (coordinateQ s : ℝ) = coordinate (s : ℝ) := by
  simp [coordinateQ, coordinate]

theorem logLoQ_cast (n : ℕ) (s : ℚ) : (logLoQ n s : ℝ) = logLo n (s : ℝ) := by
  simp [logLoQ, logLo, logPartial, coordinateQ_cast]

theorem logHiQ_cast (n : ℕ) (s : ℚ) : (logHiQ n s : ℝ) = logHi n (s : ℝ) := by
  simp [logHiQ, logHi, logLoQ_cast, coordinateQ_cast]

theorem meshPointQ_cast (M i : ℕ) : (meshPointQ M i : ℝ) = meshPoint M i := by
  simp only [meshPointQ, meshPoint, width_eq]
  push_cast <;> rfl

theorem cellLoQ_cast (n : ℕ) (a b : ℚ) :
    (cellLoQ n a b : ℝ) = cellLo n (a : ℝ) (b : ℝ) := by
  simp [cellLoQ, cellLo, logLoQ_cast]

theorem cellHiQ_cast (n : ℕ) (a b : ℚ) :
    (cellHiQ n a b : ℝ) = cellHi n (a : ℝ) (b : ℝ) := by
  simp [cellHiQ, cellHi, logHiQ_cast]

theorem rationalMeshLo_cast (M n : ℕ) : (rationalMeshLo M n : ℝ) = realMeshLo M n := by
  simp [rationalMeshLo, realMeshLo, cellLoQ_cast, meshPointQ_cast, theta] <;> ring

theorem rationalMeshHi_cast (M n : ℕ) : (rationalMeshHi M n : ℝ) = realMeshHi M n := by
  simp [rationalMeshHi, realMeshHi, cellHiQ_cast, meshPointQ_cast, theta] <;> ring

/-- The output is a pair of actual rationals enclosing the original integral. -/
theorem originalFirstIntegral_rational_mesh {M : ℕ} (hM : 0 < M) (n : ℕ) :
    (rationalMeshLo M n : ℝ) ≤ originalFirstIntegral ∧
      originalFirstIntegral ≤ (rationalMeshHi M n : ℝ) := by
  simpa only [rationalMeshLo_cast, rationalMeshHi_cast] using
    originalFirstIntegral_mesh_enclosure hM n

/-- Every dyadic level is a proved complete covering instance, including the
single-cell level m=0.  This theorem does not run a certificate producer. -/
theorem originalFirstIntegral_dyadic_enclosure (m n : ℕ) :
    (rationalMeshLo (2 ^ m) n : ℝ) ≤ originalFirstIntegral ∧
      originalFirstIntegral ≤ (rationalMeshHi (2 ^ m) n : ℝ) := by
  exact originalFirstIntegral_rational_mesh (pow_pos (by norm_num : 0 < (2 : ℕ)) m) n

end

end ImbalancedChen.P2FirstIntegralRationalEvaluationSourceOnly
