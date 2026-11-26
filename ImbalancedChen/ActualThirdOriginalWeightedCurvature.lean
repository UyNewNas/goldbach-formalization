import ImbalancedChen.ActualThirdOriginalWeights

/-!
SOURCEONLY / UNCOMPILED / OPEN30.
Original weighted curvature remainder: integrate the actual sharp quadratic
chord bound against1/u, retaining1/(12*n*j*(j-n)),n=16384. This tail uses
the actual L,H and endpointChord of the exact weights successor2f17f123.
The all-node author owns integer ceilings, rounded products, initial logs,
the max update and prefix induction. None is changed or claimed here.
-/

namespace ImbalancedChen.OriginalU2CoupledRecurrenceSourceOnly

noncomputable section
open Set MeasureTheory

/-- The ORIGINAL weighted local allowance, with no replacement constant. -/
def originalWeightedCurvatureAllowance (j : ℕ) : ℝ :=
  1/(12*16384*(j : ℝ)*((j : ℝ)-16384))

/-- The exact polynomial integral responsible for the denominator12.
This integrates the quadratic shape itself, before any supremum estimate. -/
theorem quadraticChordMajorant_integral (M : ℝ) {a b : ℝ}
    (ha : 0 < a) :
    (∫ u in a..b, M*(u-a)*(b-u)/(2*a)) = M*(b-a)^3/(12*a) := by
  let F : ℝ → ℝ := fun u =>
    (M/(2*a))*((a+b)*u^2/2-u^3/3-a*b*u)
  have hint : IntervalIntegrable (fun u => M*(u-a)*(b-u)/(2*a)) volume a b :=
    (((continuous_const.mul (continuous_id.sub continuous_const)).mul
      (continuous_const.sub continuous_id)).div_const (2*a)).intervalIntegrable a b
  have hd : ∀ u ∈ uIcc a b,
      HasDerivAt F (M*(u-a)*(b-u)/(2*a)) u := by
    intro u hu
    have h := (((((hasDerivAt_id u).pow 2).const_mul (a+b)).div_const 2).sub
      (((hasDerivAt_id u).pow 3).div_const 3)).sub
      ((hasDerivAt_id u).const_mul (a*b))
    apply (h.const_mul (M/(2*a))).congr_deriv
    change (M/(2*a))*(((a+b)*((2 : ℝ)*u^(2-1)*1)/2
      - (3 : ℝ)*u^(3-1)*1/3) - (a*b)*1) =
        M*(u-a)*(b-u)/(2*a)
    ring
  calc
    (∫ u in a..b, M*(u-a)*(b-u)/(2*a)) = F b-F a :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint
    _ = M*(b-a)^3/(12*a) := by
      dsimp [F]
      field_simp [ha.ne']
      ring

/-- Internal analytic step. Its pointwise quadratic premise is supplied
from actual sharp-chord theorems in BOTH actual wrappers below; the final
actual statements do not expose this premise or an integral-error premise. -/
private theorem weighted_quadratic_remainder_integral
    {e : ℝ → ℝ} {a b M : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hM : 0 ≤ M)
    (hint : IntervalIntegrable (fun u => e u/u) volume a b)
    (he : ∀ u ∈ Icc a b,
      0 ≤ e u ∧ e u ≤ M*(u-a)*(b-u)/2) :
    0 ≤ (∫ u in a..b, e u/u) ∧
      (∫ u in a..b, e u/u) ≤ M*(b-a)^3/(12*a) := by
  have hg : IntervalIntegrable (fun u => M*(u-a)*(b-u)/(2*a)) volume a b :=
    (((continuous_const.mul (continuous_id.sub continuous_const)).mul
      (continuous_const.sub continuous_id)).div_const (2*a)).intervalIntegrable a b
  have hnonneg : 0 ≤ (∫ u in a..b, e u/u) :=
    intervalIntegral.integral_nonneg hab (fun u hu =>
      div_nonneg (he u hu).1 (ha.trans_le hu.1).le)
  have hbound := intervalIntegral.integral_mono_on hab hint hg (by
    intro u hu
    have hu0 : 0 < u := ha.trans_le hu.1
    have hquad : 0 ≤ M*(u-a)*(b-u)/2 :=
      div_nonneg (mul_nonneg (mul_nonneg hM (sub_nonneg.mpr hu.1))
        (sub_nonneg.mpr hu.2)) (by norm_num)
    calc
      e u/u ≤ (M*(u-a)*(b-u)/2)/u :=
        div_le_div_of_nonneg_right (he u hu).2 hu0.le
      _ ≤ (M*(u-a)*(b-u)/2)/a :=
        div_le_div_of_nonneg_left hquad ha hu.1
      _ = M*(u-a)*(b-u)/(2*a) := by
        rw [div_div])
  exact ⟨hnonneg, hbound.trans_eq (quadraticChordMajorant_integral M ha)⟩

/-- Exact original-grid algebra after integrating the QUADRATIC shape. -/
theorem original_cell_weighted_curvature_allowance (j : ℕ) (hj : 32768 ≤ j) :
    cellCurvature j*(cellRight j-cellLeft j)^3/(12*cellLeft j) =
      originalWeightedCurvatureAllowance j := by
  have hJ : (32768 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have hJ0 : (j : ℝ) ≠ 0 := by linarith
  have hJn : (j : ℝ)-16384 ≠ 0 := by linarith
  have ha1 : (j : ℝ)/16384-1 ≠ 0 := by linarith
  rw [original_cell_width]
  dsimp [cellCurvature, cellLeft, originalWeightedCurvatureAllowance]
  field_simp [hJ0, hJn, ha1]

/-- Actual L/u,H/u integrability on every complete original cell above2.
This uses the already proved genuine normalized-factor order, including
the closed endpoint2 and constant-H cells. No target integral is assumed. -/
theorem original_actual_cell_quotients_integrable (j : ℕ) (hj : 32768 ≤ j) :
    IntervalIntegrable (fun u => L u/u) volume (cellLeft j) (cellRight j) ∧
    IntervalIntegrable (fun u => H u/u) volume (cellLeft j) (cellRight j) := by
  have hJ : (32768 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have htwo (u : ℝ) (hu : u ∈ uIcc (cellLeft j) (cellRight j)) : 2 ≤ u := by
    rw [uIcc_of_le (original_cell_lt j).le] at hu
    dsimp [cellLeft] at hu
    linarith [hu.1]
  have hL : MonotoneOn (fun u => L u/u) (uIcc (cellLeft j) (cellRight j)) := by
    intro x hx y hy hxy
    have hx2 := htwo x hx
    have hy2 := htwo y hy
    have hx0 : x ≠ 0 := by linarith
    have hy0 : y ≠ 0 := by linarith
    have h := lower_monotone (show x ∈ Ici 2 from hx2)
      (show y ∈ Ici 2 from hy2) hxy
    simpa [L, hx0, hy0] using h
  have hH : AntitoneOn (fun u => H u/u) (uIcc (cellLeft j) (cellRight j)) := by
    intro x hx y hy hxy
    have hx2 := htwo x hx
    have hy2 := htwo y hy
    have hx0 : x ≠ 0 := by linarith
    have hy0 : y ≠ 0 := by linarith
    have h := upper_antitone (show x ∈ Ici 2 from hx2)
      (show y ∈ Ici 2 from hy2) hxy
    simpa [H, hx0, hy0] using h
  exact ⟨hL.intervalIntegrable, hH.intervalIntegrable⟩

/-- A quotient of an endpoint chord is integrable independently of any
regularity of f: only its two fixed real endpoint values are used. -/
theorem original_cell_chord_quotient_integrable
    (f : ℝ → ℝ) (j : ℕ) (hj : 32768 ≤ j) :
    IntervalIntegrable (fun u => endpointChord f (cellLeft j) (cellRight j) u/u)
      volume (cellLeft j) (cellRight j) := by
  have hJ : (32768 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  apply ContinuousOn.intervalIntegrable
  refine ContinuousOn.div ?_ continuousOn_id ?_
  · unfold endpointChord
    exact (((continuousOn_const.sub continuousOn_id).div_const
        (cellRight j-cellLeft j)).mul continuousOn_const).add
      (((continuousOn_id.sub continuousOn_const).div_const
        (cellRight j-cellLeft j)).mul continuousOn_const)
  · intro u hu
    change u ≠ 0
    rw [uIcc_of_le (original_cell_lt j).le] at hu
    dsimp [cellLeft] at hu
    have hu0 : 0 < u := by linarith [hu.1]
    exact hu0.ne'

/-- Concave actual L: its chord/u integral UNDERESTIMATES by at most the
original1/(12*n*j*(j-n)). Only the actual sharp quadratic bound is used. -/
theorem original_L_weighted_chord_remainder (j : ℕ) (hj : 32768 ≤ j) :
    0 ≤ (∫ u in (cellLeft j)..(cellRight j),
      (L u-endpointChord L (cellLeft j) (cellRight j) u)/u) ∧
    (∫ u in (cellLeft j)..(cellRight j),
      (L u-endpointChord L (cellLeft j) (cellRight j) u)/u) ≤
        originalWeightedCurvatureAllowance j := by
  have hJ : (32768 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have ha : 0 < cellLeft j := by dsimp [cellLeft]; linarith
  have hL := (original_actual_cell_quotients_integrable j hj).1
  have hc := original_cell_chord_quotient_integrable L j hj
  have hi : IntervalIntegrable
      (fun u => (L u-endpointChord L (cellLeft j) (cellRight j) u)/u)
      volume (cellLeft j) (cellRight j) := by
    simpa only [sub_div] using hL.sub hc
  have h := weighted_quadratic_remainder_integral ha (original_cell_lt j).le
    (original_cell_curvature_nonneg j hj) hi (by
      intro u hu
      have hs := original_L_cell_chord j hj hu
      exact ⟨hs.1, hs.2.1⟩)
  simpa only [original_cell_weighted_curvature_allowance j hj] using h

/-- Convex actual H: its chord/u integral OVERESTIMATES by at most the
original1/(12*n*j*(j-n)). This includes H's constant initial cells below3. -/
theorem original_H_weighted_chord_remainder (j : ℕ) (hj : 32768 ≤ j) :
    0 ≤ (∫ u in (cellLeft j)..(cellRight j),
      (endpointChord H (cellLeft j) (cellRight j) u-H u)/u) ∧
    (∫ u in (cellLeft j)..(cellRight j),
      (endpointChord H (cellLeft j) (cellRight j) u-H u)/u) ≤
        originalWeightedCurvatureAllowance j := by
  have hJ : (32768 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have ha : 0 < cellLeft j := by dsimp [cellLeft]; linarith
  have hH := (original_actual_cell_quotients_integrable j hj).2
  have hc := original_cell_chord_quotient_integrable H j hj
  have hi : IntervalIntegrable
      (fun u => (endpointChord H (cellLeft j) (cellRight j) u-H u)/u)
      volume (cellLeft j) (cellRight j) := by
    simpa only [sub_div] using hc.sub hH
  have h := weighted_quadratic_remainder_integral ha (original_cell_lt j).le
    (original_cell_curvature_nonneg j hj) hi (by
      intro u hu
      have hs := original_H_cell_chord j hj hu
      exact ⟨hs.1, hs.2.1⟩)
  simpa only [original_cell_weighted_curvature_allowance j hj] using h

/-- Node-author interface for the actual delayed L integrals. The only
caller hypothesis is the original integer cell condition. -/
theorem original_L_weighted_chord_integral_bounds (j : ℕ) (hj : 32768 ≤ j) :
    (∫ u in (cellLeft j)..(cellRight j),
      endpointChord L (cellLeft j) (cellRight j) u/u) ≤
      (∫ u in (cellLeft j)..(cellRight j), L u/u) ∧
    (∫ u in (cellLeft j)..(cellRight j), L u/u) ≤
      (∫ u in (cellLeft j)..(cellRight j),
        endpointChord L (cellLeft j) (cellRight j) u/u) +
          originalWeightedCurvatureAllowance j := by
  have h := original_L_weighted_chord_remainder j hj
  have heq : (∫ u in (cellLeft j)..(cellRight j),
      (L u-endpointChord L (cellLeft j) (cellRight j) u)/u) =
      (∫ u in (cellLeft j)..(cellRight j), L u/u) -
      (∫ u in (cellLeft j)..(cellRight j),
        endpointChord L (cellLeft j) (cellRight j) u/u) := by
    simp_rw [sub_div]
    exact intervalIntegral.integral_sub
      (original_actual_cell_quotients_integrable j hj).1
      (original_cell_chord_quotient_integrable L j hj)
  rw [heq] at h
  constructor <;> linarith only [h.1, h.2]

/-- Node-author interface for actual delayed H integrals. This is stronger
than the required nonconstant-cell interfacej>=49152; H's initial exact
constant cells are included by the actual parent theorem. -/
theorem original_H_weighted_chord_integral_bounds (j : ℕ) (hj : 32768 ≤ j) :
    (∫ u in (cellLeft j)..(cellRight j),
      endpointChord H (cellLeft j) (cellRight j) u/u) -
        originalWeightedCurvatureAllowance j ≤
      (∫ u in (cellLeft j)..(cellRight j), H u/u) ∧
    (∫ u in (cellLeft j)..(cellRight j), H u/u) ≤
      (∫ u in (cellLeft j)..(cellRight j),
        endpointChord H (cellLeft j) (cellRight j) u/u) := by
  have h := original_H_weighted_chord_remainder j hj
  have heq : (∫ u in (cellLeft j)..(cellRight j),
      (endpointChord H (cellLeft j) (cellRight j) u-H u)/u) =
      (∫ u in (cellLeft j)..(cellRight j),
        endpointChord H (cellLeft j) (cellRight j) u/u) -
      (∫ u in (cellLeft j)..(cellRight j), H u/u) := by
    simp_rw [sub_div]
    exact intervalIntegral.integral_sub
      (original_cell_chord_quotient_integrable H j hj)
      (original_actual_cell_quotients_integrable j hj).2
  rw [heq] at h
  constructor <;> linarith only [h.1, h.2]

/-- Exact unrounded112-bit form. This scales the integrated quadratic
allowance; its later integer ceiling remains the node author's task. -/
theorem original_weighted_chord_remainders_112bit (j : ℕ) (hj : 32768 ≤ j) :
    (originalWeightP : ℝ) *
      (∫ u in (cellLeft j)..(cellRight j),
        (L u-endpointChord L (cellLeft j) (cellRight j) u)/u) ≤
      (2^112 : ℝ)/(12*16384*(j : ℝ)*((j : ℝ)-16384)) ∧
    (originalWeightP : ℝ) *
      (∫ u in (cellLeft j)..(cellRight j),
        (endpointChord H (cellLeft j) (cellRight j) u-H u)/u) ≤
      (2^112 : ℝ)/(12*16384*(j : ℝ)*((j : ℝ)-16384)) := by
  have hP : (originalWeightP : ℝ) = (2^112 : ℝ) := by norm_num [originalWeightP]
  have hp : (0 : ℝ) ≤ (originalWeightP : ℝ) := by norm_num [originalWeightP]
  have hL := mul_le_mul_of_nonneg_left (original_L_weighted_chord_remainder j hj).2 hp
  have hH := mul_le_mul_of_nonneg_left (original_H_weighted_chord_remainder j hj).2 hp
  constructor
  · simpa only [originalWeightedCurvatureAllowance, hP, mul_one_div] using hL
  · simpa only [originalWeightedCurvatureAllowance, hP, mul_one_div] using hH

end
end ImbalancedChen.OriginalU2CoupledRecurrenceSourceOnly
