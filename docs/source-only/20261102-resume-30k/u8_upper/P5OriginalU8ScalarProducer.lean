import ImbalancedChen.P2NegativeDomainCover
import ImbalancedChen.CurrentChenUpsilon9HarmonicIntegral
import ImbalancedChen.P2U8UniformRationalCover

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

The original U8 producer uses log(2-3t)/(t*(1-t)) on [417/5000,1/3].
This file derives that scalar from the true original two-dimensional
integral and proves the producer's explicit first and second derivatives.
The full moving domain, including the weak y=1/3 wall, is inherited from
P2NegativeDomainCover. The generic proved inner primitive is reused at
d=1/3; no U9 domain or U9 integral replaces U8.

The original 1024 midpoint cells are also an exact integral partition.
No numerical endpoint, midpoint remainder bound, or finite guard is assumed
or asserted. The producer's Q80 interval execution remains unverified.
-/

namespace ImbalancedChen.P5OriginalU8ScalarProducer

noncomputable section

open MeasureTheory Set
open scoped BigOperators
open P2NegativeDomainCover P2U8UniformRationalCover

def logDensity (t : ℝ) : ℝ := Real.log (2 - 3 * t) / (t * (1 - t))

/-- The archived producer's scalar, derived from the actual harmonic U8. -/
theorem original_integral_eq_logIntegral :
    currentChenUpsilon8HarmonicIntegral =
      ∫ t in Ico (417 / 5000 : ℝ) (1 / 3 : ℝ), logDensity t := by
  rw [eighthHarmonicIntegral_eq_nested]
  apply setIntegral_congr_fun measurableSet_Ico
  intro t ht
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 417 / 5000) ht.1
  have ht1 : t < 1 := by linarith only [ht.2]
  rw [currentChenUpsilon9Harmonic_inner_integral ht0 ht1 (by norm_num)
    (by linarith only [ht.2] : (1 / 3 : ℝ) ≤ (1 - t) / 2)]
  unfold logDensity
  congr 2
  ring

theorem original_interval_guards {t : ℝ}
    (ht : t ∈ Icc (417 / 5000 : ℝ) (1 / 3 : ℝ)) :
    0 < t ∧ 0 < 1 - t ∧ 1 ≤ 2 - 3 * t := by
  constructor
  · linarith only [ht.1]
  constructor <;> linarith only [ht.2]

theorem continuousOn_logDensity :
    ContinuousOn logDensity (Icc (417 / 5000 : ℝ) (1 / 3 : ℝ)) := by
  apply ((continuousOn_const.sub (continuousOn_const.mul continuousOn_id)).log
    (fun t ht => (zero_lt_one.trans_le (original_interval_guards ht).2.2).ne')).div
      (continuousOn_id.mul (continuousOn_const.sub continuousOn_id))
  intro t ht
  exact (mul_pos (original_interval_guards ht).1 (original_interval_guards ht).2.1).ne'

def producerLog (t : ℝ) : ℝ := Real.log (2 - 3 * t)
def producerLogFirst (t : ℝ) : ℝ := -3 / (2 - 3 * t)
def producerLogSecond (t : ℝ) : ℝ := -9 / (2 - 3 * t) ^ 2
def reciprocal (t : ℝ) : ℝ := 1 / t + 1 / (1 - t)
def reciprocalFirst (t : ℝ) : ℝ := -1 / t ^ 2 + 1 / (1 - t) ^ 2
def reciprocalSecond (t : ℝ) : ℝ := 2 / t ^ 3 + 2 / (1 - t) ^ 3
def producerValue (t : ℝ) : ℝ := producerLog t * reciprocal t
def producerFirst (t : ℝ) : ℝ :=
  producerLogFirst t * reciprocal t + producerLog t * reciprocalFirst t
def producerSecond (t : ℝ) : ℝ :=
  producerLogSecond t * reciprocal t +
    2 * producerLogFirst t * reciprocalFirst t + producerLog t * reciprocalSecond t

theorem producerSecond_eq_archived_expression (t : ℝ) :
    producerSecond t =
      (-9 / (2 - 3 * t) ^ 2) * (1 / t + 1 / (1 - t)) +
        2 * (-3 / (2 - 3 * t)) * (-1 / t ^ 2 + 1 / (1 - t) ^ 2) +
        Real.log (2 - 3 * t) * (2 / t ^ 3 + 2 / (1 - t) ^ 3) := rfl

theorem producerValue_eq_logDensity {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    producerValue t = logDensity t := by
  unfold producerValue producerLog reciprocal logDensity
  field_simp [ht.ne', (sub_pos.mpr ht1).ne']
  <;> ring

theorem producerLog_hasDerivAt {t : ℝ} (ht : 0 < 2 - 3 * t) :
    HasDerivAt producerLog (producerLogFirst t) t := by
  have h := (((hasDerivAt_id t).const_mul 3).const_sub 2).log ht.ne'
  simpa only [producerLog, producerLogFirst, mul_one] using h

theorem producerLogFirst_hasDerivAt {t : ℝ} (ht : 0 < 2 - 3 * t) :
    HasDerivAt producerLogFirst (producerLogSecond t) t := by
  have h := (hasDerivAt_const t (-3 : ℝ)).div
    (((hasDerivAt_id t).const_mul 3).const_sub 2) ht.ne'
  apply h.congr_deriv
  dsimp only [producerLogSecond]
  ring

theorem reciprocal_hasDerivAt {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    HasDerivAt reciprocal (reciprocalFirst t) t := by
  have hleft := (hasDerivAt_const t (1 : ℝ)).div (hasDerivAt_id t) ht.ne'
  have hright := (hasDerivAt_const t (1 : ℝ)).div
    ((hasDerivAt_id t).const_sub 1) (sub_pos.mpr ht1).ne'
  apply (hleft.add hright).congr_deriv
  dsimp only [reciprocalFirst]
  ring

theorem reciprocalFirst_hasDerivAt {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    HasDerivAt reciprocalFirst (reciprocalSecond t) t := by
  have hleft := (hasDerivAt_const t (-1 : ℝ)).div
    ((hasDerivAt_id t).pow 2) (pow_ne_zero 2 ht.ne')
  have hright := (hasDerivAt_const t (1 : ℝ)).div
    (((hasDerivAt_id t).const_sub 1).pow 2) (pow_ne_zero 2 (sub_pos.mpr ht1).ne')
  apply (hleft.add hright).congr_deriv
  dsimp only [reciprocalSecond]
  field_simp [ht.ne', (sub_pos.mpr ht1).ne']
  <;> ring

theorem producerValue_hasDerivAt {t : ℝ}
    (ht : 0 < t) (ht1 : t < 1) (harg : 0 < 2 - 3 * t) :
    HasDerivAt producerValue (producerFirst t) t := by
  exact (producerLog_hasDerivAt harg).mul (reciprocal_hasDerivAt ht ht1)

/-- Exactly main_second(t,8) in certify_sharp_switch_midpoint.py.
Both derivatives are proved for the true logarithm, with no interpolant. -/
theorem producerFirst_hasDerivAt {t : ℝ}
    (ht : 0 < t) (ht1 : t < 1) (harg : 0 < 2 - 3 * t) :
    HasDerivAt producerFirst (producerSecond t) t := by
  have h := ((producerLogFirst_hasDerivAt harg).mul (reciprocal_hasDerivAt ht ht1)).add
    ((producerLog_hasDerivAt harg).mul (reciprocalFirst_hasDerivAt ht ht1))
  apply h.congr_deriv
  unfold producerSecond
  ring

theorem continuousOn_producerSecond :
    ContinuousOn producerSecond (Icc (417 / 5000 : ℝ) (1 / 3 : ℝ)) := by
  let S := Icc (417 / 5000 : ℝ) (1 / 3 : ℝ)
  have ht : ∀ t ∈ S, t ≠ 0 := fun t ht => (original_interval_guards ht).1.ne'
  have hw : ∀ t ∈ S, 1 - t ≠ 0 := fun t ht => (original_interval_guards ht).2.1.ne'
  have ha : ∀ t ∈ S, 2 - 3 * t ≠ 0 := fun t ht =>
    (zero_lt_one.trans_le (original_interval_guards ht).2.2).ne'
  have hlin : ContinuousOn (fun t : ℝ => 2 - 3 * t) S :=
    continuousOn_const.sub (continuousOn_const.mul continuousOn_id)
  have hlog : ContinuousOn producerLog S := hlin.log ha
  have hlog1 : ContinuousOn producerLogFirst S := continuousOn_const.div hlin ha
  have hlog2 : ContinuousOn producerLogSecond S :=
    continuousOn_const.div (hlin.pow 2) (fun t ht => pow_ne_zero 2 (ha t ht))
  have hrec : ContinuousOn reciprocal S :=
    (continuousOn_const.div continuousOn_id ht).add
      (continuousOn_const.div (continuousOn_const.sub continuousOn_id) hw)
  have hrec1 : ContinuousOn reciprocalFirst S :=
    (continuousOn_const.div (continuousOn_id.pow 2) (fun t h => pow_ne_zero 2 (ht t h))).add
      (continuousOn_const.div ((continuousOn_const.sub continuousOn_id).pow 2)
        (fun t h => pow_ne_zero 2 (hw t h)))
  have hrec2 : ContinuousOn reciprocalSecond S :=
    (continuousOn_const.div (continuousOn_id.pow 3) (fun t h => pow_ne_zero 3 (ht t h))).add
      (continuousOn_const.div ((continuousOn_const.sub continuousOn_id).pow 3)
        (fun t h => pow_ne_zero 3 (hw t h)))
  exact ((hlog2.mul hrec).add ((continuousOn_const.mul hlog1).mul hrec1)).add
    (hlog.mul hrec2)

def mesh (m k : ℕ) : ℚ := node alpha cubeWall m k
def midpoint (m k : ℕ) : ℚ := (mesh m k + mesh m (k + 1)) / 2

/-- Exact Fraction arithmetic used for l=left+j*step in the archive. -/
theorem mesh_eq_archived_node (m k : ℕ) :
    mesh m k = (417 / 5000 : ℚ) + (k : ℚ) * ((1 / 3 - 417 / 5000) / m) := by
  unfold mesh node step alpha cubeWall
  ring

/-- The producer's r=l+step is precisely the next common mesh endpoint. -/
theorem mesh_successor_width (m k : ℕ) :
    mesh m (k + 1) - mesh m k = (1 / 3 - 417 / 5000 : ℚ) / m := by
  rw [mesh_eq_archived_node, mesh_eq_archived_node]
  push_cast
  ring

theorem mesh_zero (m : ℕ) : mesh m 0 = alpha := by simp [mesh, node]
theorem mesh_last (m : ℕ) (hm : 0 < m) : mesh m m = cubeWall := node_last _ _ hm
theorem mesh_monotone (m : ℕ) (hm : 0 < m) : Monotone (mesh m) := by
  intro j k hjk
  exact node_mono alpha_lt_cubeWall hm hjk
theorem mesh_bounds (m : ℕ) (hm : 0 < m) (k : ℕ) (hk : k ≤ m) :
    alpha ≤ mesh m k ∧ mesh m k ≤ cubeWall :=
  ⟨start_le_node alpha_lt_cubeWall hm k, node_le_end alpha_lt_cubeWall hm hk⟩

theorem midpoint_bounds (m : ℕ) (hm : 0 < m) (k : ℕ) (hk : k < m) :
    alpha ≤ midpoint m k ∧ midpoint m k ≤ cubeWall := by
  have hl := mesh_bounds m hm k hk.le
  have hr := mesh_bounds m hm (k + 1) (by omega)
  dsimp only [midpoint]
  constructor <;> linarith only [hl.1, hl.2, hr.1, hr.2]

theorem logDensity_cell_integrable (m : ℕ) (hm : 0 < m) (k : ℕ) (hk : k < m) :
    IntervalIntegrable logDensity volume (mesh m k : ℝ) (mesh m (k + 1) : ℝ) := by
  have hl := (mesh_bounds m hm k hk.le).1
  have hr := (mesh_bounds m hm (k + 1) (by omega)).2
  have horder : (mesh m k : ℝ) ≤ (mesh m (k + 1) : ℝ) := by
    exact_mod_cast mesh_monotone m hm (Nat.le_succ k)
  apply (continuousOn_logDensity.mono ?_).intervalIntegrable_of_Icc horder
  intro t ht
  have hlR : (417 / 5000 : ℝ) ≤ (mesh m k : ℝ) := by
    exact_mod_cast (show (417 / 5000 : ℚ) ≤ mesh m k from hl)
  have hrR : (mesh m (k + 1) : ℝ) ≤ (1 / 3 : ℝ) := by
    exact_mod_cast (show mesh m (k + 1) ≤ (1 / 3 : ℚ) from hr)
  exact ⟨hlR.trans ht.1, ht.2.trans hrR⟩

/-- The archived partition, for any positive size and hence its 1024 cells.
No endpoint overlap changes the integral and no degenerate final slice is
lost when t=1/3. -/
theorem original_integral_eq_cell_sum (m : ℕ) (hm : 0 < m) :
    currentChenUpsilon8HarmonicIntegral =
      ∑ k ∈ Finset.range m,
        ∫ t in (mesh m k : ℝ)..(mesh m (k + 1) : ℝ), logDensity t := by
  have h := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun k => (mesh m k : ℝ)) (logDensity_cell_integrable m hm)
  rw [mesh_zero, mesh_last m hm] at h
  rw [original_integral_eq_logIntegral, integral_Ico_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (417 / 5000 : ℝ) ≤ 1 / 3)]
  exact h.symm

theorem original_1024_partition :
    currentChenUpsilon8HarmonicIntegral =
      ∑ k ∈ Finset.range 1024,
        ∫ t in (mesh 1024 k : ℝ)..(mesh 1024 (k + 1) : ℝ), logDensity t :=
  original_integral_eq_cell_sum 1024 (by norm_num)

end

end ImbalancedChen.P5OriginalU8ScalarProducer
