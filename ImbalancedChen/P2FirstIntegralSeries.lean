import ImbalancedChen.ActualThirdOriginalPositive256Log
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

/-!
SOURCE ONLY / NOT ELABORATED / no numerical producer or endpoint replay.

Catalog U1 (`docs/part2/adopted-evidence-catalog.json`): the complete original
first integral, with Theta = 299/500 and rho = 19/96.  The catalog's original
positive-series Python payload is absent.  This file instead reuses the actual
Lean logarithm theorem `OriginalThirdPositiveLogSourceOnly.positive_series_bounds`
and supplies the missing full-domain integration step.

`originalFirstIntegral_series_enclosure` encloses the actual manuscript integral
between an integral of a finite rational function and that same integral plus
an explicit geometric tail.  There are no numerical endpoint assumptions.
`originalFirstIntegral_translate` is an exact full-domain change of variable.

OPEN GAP: evaluation/enclosure of the finite rational-function integral and
comparison with the selected frozen U1 decimal endpoints are not supplied.
In particular, no catalog endpoint, hUpper, currentK, or global theorem follows
from this file alone.  All declarations below have complete proof bodies;
kernel elaboration remains intentionally unexecuted under CODE_ONLY.
-/

namespace ImbalancedChen.P2FirstIntegralSeriesSourceOnly

noncomputable section

open Set MeasureTheory
open OriginalThirdPositiveLogSourceOnly

def theta : ℝ := 299 / 500

def rho : ℝ := 19 / 96

/-- The upper endpoint is retained in the original Theta/rho normalization. -/
def stop : ℝ := theta / rho - 1

def kernel (s : ℝ) : ℝ := Real.log (s - 1) / s

/-- Exactly the original first integral, including its original prefactor. -/
def originalFirstIntegral : ℝ := (4 / theta) * ∫ s in 2..stop, kernel s

def coordinate (s : ℝ) : ℝ := 1 - 1 / (s - 1)

/-- Exact maximum of the positive-series coordinate on the full domain. -/
def q : ℝ := 51 / 2426

def partialKernel (n : ℕ) (s : ℝ) : ℝ := logPartial (coordinate s) n / s

def partialIntegral (n : ℕ) : ℝ :=
  (4 / theta) * ∫ s in 2..stop, partialKernel n s

/-- Uniform error for the integrand, with both factors 1/(n+1) and 1/2. -/
def pointTail (n : ℕ) : ℝ := q ^ (n + 1) / (((n : ℝ) + 1) * (1 - q) * 2)

def integralTail (n : ℕ) : ℝ := (4 / theta) * ((stop - 2) * pointTail n)

theorem stop_eq : stop = (4801 / 2375 : ℝ) := by
  norm_num [stop, theta, rho]

theorem width_eq : stop - 2 = (51 / 2375 : ℝ) := by
  rw [stop_eq]
  norm_num

theorem two_le_stop : (2 : ℝ) ≤ stop := by
  rw [stop_eq]
  norm_num

theorem q_nonneg : 0 ≤ q := by norm_num [q]

theorem q_lt_one : q < 1 := by norm_num [q]

theorem prefactor_pos : (0 : ℝ) < 4 / theta := by norm_num [theta]

theorem originalFirstIntegral_semantics :
    originalFirstIntegral =
      (4 / (299 / 500 : ℝ)) *
        ∫ s in (2 : ℝ)..((299 / 500 : ℝ) / (19 / 96 : ℝ) - 1),
          Real.log (s - 1) / s := by
  rfl

/-- This includes both endpoints; no crop or omitted boundary interval occurs. -/
theorem coordinate_bounds {s : ℝ} (hs : s ∈ Icc (2 : ℝ) stop) :
    0 ≤ coordinate s ∧ coordinate s ≤ q := by
  have hp : 0 < s - 1 := by linarith [hs.1]
  have hsmall : (1 : ℝ) / (s - 1) ≤ 1 :=
    (div_le_iff₀ hp).2 (by linarith [hs.1])
  have hs' : s ≤ (4801 / 2375 : ℝ) := by simpa [stop_eq] using hs.2
  have hlarge : (2375 / 2426 : ℝ) ≤ 1 / (s - 1) :=
    (le_div_iff₀ hp).2 (by nlinarith)
  constructor
  · dsimp [coordinate]
    linarith
  · dsimp [coordinate, q]
    linarith

theorem continuousOn_coordinate : ContinuousOn coordinate (Icc (2 : ℝ) stop) := by
  apply continuousOn_const.sub
  apply continuousOn_const.div (continuousOn_id.sub continuousOn_const)
  intro s hs
  have hp : 0 < s - 1 := by linarith [hs.1]
  exact ne_of_gt hp

theorem continuousOn_kernel : ContinuousOn kernel (Icc (2 : ℝ) stop) := by
  apply ((continuousOn_id.sub continuousOn_const).log ?_).div continuousOn_id ?_
  · intro s hs
    have hp : 0 < s - 1 := by linarith [hs.1]
    exact ne_of_gt hp
  · intro s hs
    have hp : 0 < s := by linarith [hs.1]
    exact ne_of_gt hp

private theorem continuousOn_partialLog (n : ℕ) :
    ContinuousOn (fun s => logPartial (coordinate s) n) (Icc (2 : ℝ) stop) := by
  induction n with
  | zero =>
      simpa [logPartial] using
        (continuousOn_const : ContinuousOn (fun _ : ℝ => (0 : ℝ)) (Icc 2 stop))
  | succ n ih =>
      simpa only [logPartial, Finset.sum_range_succ] using
        ih.add ((continuousOn_coordinate.pow (n + 1)).div_const ((n : ℝ) + 1))

theorem continuousOn_partialKernel (n : ℕ) :
    ContinuousOn (partialKernel n) (Icc (2 : ℝ) stop) := by
  apply (continuousOn_partialLog n).div continuousOn_id
  intro s hs
  have hp : 0 < s := by linarith [hs.1]
  exact ne_of_gt hp

theorem intervalIntegrable_kernel : IntervalIntegrable kernel volume 2 stop := by
  exact ContinuousOn.intervalIntegrable_of_Icc two_le_stop continuousOn_kernel

theorem intervalIntegrable_partialKernel (n : ℕ) :
    IntervalIntegrable (partialKernel n) volume 2 stop := by
  exact ContinuousOn.intervalIntegrable_of_Icc two_le_stop (continuousOn_partialKernel n)

/-- Rebind the existing proved logarithm series to the actual first integrand. -/
theorem kernel_series_pointwise (n : ℕ) {s : ℝ}
    (hs : s ∈ Icc (2 : ℝ) stop) :
    partialKernel n s ≤ kernel s ∧ kernel s ≤ partialKernel n s + pointTail n := by
  have hz := coordinate_bounds hs
  have hz1 : coordinate s < 1 := lt_of_le_of_lt hz.2 q_lt_one
  have hspos : 0 < s := by linarith [hs.1]
  have hn : 0 < (n : ℝ) + 1 := by positivity
  have hdz : 0 < ((n : ℝ) + 1) * (1 - coordinate s) :=
    mul_pos hn (by linarith)
  have hdq : 0 < ((n : ℝ) + 1) * (1 - q) :=
    mul_pos hn (by linarith [q_lt_one])
  have hpq : 0 ≤ q ^ (n + 1) := pow_nonneg q_nonneg _
  have hpow : coordinate s ^ (n + 1) ≤ q ^ (n + 1) :=
    pow_le_pow_left₀ hz.1 hz.2 _
  have hden : ((n : ℝ) + 1) * (1 - q) ≤
      ((n : ℝ) + 1) * (1 - coordinate s) :=
    mul_le_mul_of_nonneg_left (by linarith [hz.2]) hn.le
  have htail :
      (coordinate s ^ (n + 1) / (((n : ℝ) + 1) * (1 - coordinate s))) / s ≤
        pointTail n := by
    calc
      _ ≤ (q ^ (n + 1) / (((n : ℝ) + 1) * (1 - q))) / s := by
        apply (div_le_div_iff_of_pos_right hspos).2
        exact (div_le_div_of_nonneg_right hpow hdz.le).trans
          (div_le_div_of_nonneg_left hpq hdq hden)
      _ ≤ (q ^ (n + 1) / (((n : ℝ) + 1) * (1 - q))) / 2 :=
        div_le_div_of_nonneg_left (div_nonneg hpq hdq.le) (by norm_num) hs.1
      _ = pointTail n := by rw [pointTail, div_div]
  have hb := positive_series_bounds hz.1 hz1 n
  have hlog : -Real.log (1 - coordinate s) = Real.log (s - 1) := by
    have he : 1 - coordinate s = (s - 1)⁻¹ := by
      dsimp [coordinate]
      ring
    rw [he, Real.log_inv, neg_neg]
  rw [hlog] at hb
  constructor
  · exact (div_le_div_iff_of_pos_right hspos).2 hb.1
  · have hu := (div_le_div_iff_of_pos_right hspos).2 hb.2
    rw [add_div] at hu
    exact hu.trans (add_le_add_left htail _)

/-- Integrating the actual full domain preserves the explicit geometric error. -/
theorem originalFirstIntegral_series_enclosure (n : ℕ) :
    partialIntegral n ≤ originalFirstIntegral ∧
      originalFirstIntegral ≤ partialIntegral n + integralTail n := by
  have hi := intervalIntegrable_kernel
  have hp := intervalIntegrable_partialKernel n
  have hc : IntervalIntegrable (fun _ : ℝ => pointTail n) volume 2 stop :=
    intervalIntegrable_const
  have hlo := intervalIntegral.integral_mono_on two_le_stop hp hi
    (fun s hs => (kernel_series_pointwise n hs).1)
  have hup := intervalIntegral.integral_mono_on two_le_stop hi (hp.add hc)
    (fun s hs => (kernel_series_pointwise n hs).2)
  rw [intervalIntegral.integral_add hp hc, intervalIntegral.integral_const,
    smul_eq_mul] at hup
  constructor
  · exact mul_le_mul_of_nonneg_left hlo prefactor_pos.le
  · have h := mul_le_mul_of_nonneg_left hup prefactor_pos.le
    simpa only [originalFirstIntegral, partialIntegral, integralTail, mul_add] using h

/-- The normalization and the width can be read off without a numeric replay. -/
theorem integralTail_rational_formula (n : ℕ) :
    integralTail n =
      (2000 / 299 : ℝ) * (51 / 2375) *
        ((51 / 2426 : ℝ) ^ (n + 1) /
          (((n : ℝ) + 1) * (1 - 51 / 2426) * 2)) := by
  rw [integralTail, width_eq]
  norm_num only [theta, pointTail, q, div_div, div_one, mul_one]
  ring

/-- A completely rational, deliberately coarse consequence, with no unevaluated
integral on the right.  This is not the catalog's selected sharp endpoint. -/
theorem originalFirstIntegral_rational_coarse :
    0 ≤ originalFirstIntegral ∧
      originalFirstIntegral ≤
        (2000 / 299 : ℝ) * (51 / 2375) * (51 / 4750) := by
  have hp : partialIntegral 0 = 0 := by
    simp [partialIntegral, partialKernel, logPartial]
  have ht : integralTail 0 =
      (2000 / 299 : ℝ) * (51 / 2375) * (51 / 4750) := by
    rw [integralTail_rational_formula]
    norm_num
  simpa only [hp, ht, zero_add] using originalFirstIntegral_series_enclosure 0

/-- An exact translation, with both original endpoints accounted for. -/
theorem originalFirstIntegral_translate :
    originalFirstIntegral =
      (4 / theta) * ∫ t in (0 : ℝ)..(stop - 2), Real.log (1 + t) / (2 + t) := by
  have hc := intervalIntegral.integral_comp_add_right
    (f := kernel) (a := (0 : ℝ)) (b := stop - 2) (2 : ℝ)
  have he : (∫ s in (2 : ℝ)..stop, kernel s) =
      ∫ t in (0 : ℝ)..(stop - 2), kernel (t + 2) := by
    simpa only [zero_add, sub_add_cancel] using hc.symm
  rw [originalFirstIntegral, he]
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp [kernel]
  have harg : t + 2 - 1 = 1 + t := by ring
  rw [harg, add_comm t 2]

end

end ImbalancedChen.P2FirstIntegralSeriesSourceOnly
