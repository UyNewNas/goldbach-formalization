/-!
SOURCE_WRITTEN / UNCOMPILED. Historic Q80 ordinary-trapezoid supplier.

Frozen producer: certify_extended_prefix.py, SHA256
1b77aa5deb90e0f39e06c776847a7e9fff27e23d584036955741b015ca05ad29.
The historical Ordinary call uses SieveTable(16384,8).

The frozen certify_extended_prefix.py uses g=16384, errors ceil(Q/(6g^3))
and ceil(Q/(12g^3)). Its L update integrates the ACTUAL normalized upper
factor F, whose convex curvature is bounded by2. Its H update integrates
the ACTUAL normalized lower factor f, whose concave curvature magnitude
is bounded by1. These are ordinary trapezoids, not the unrelated P112
weighted numerator chords. Existing actual DDE/chord calculus is reused.

At the delayed upper endpoint1 the theorem uses the explicit reciprocal
endpoint value1. The actual upper integral is unchanged by that endpoint;
no unsupported assertion about the canonical source's value at1 occurs.
No sf/table soundness or desired node enclosure is a premise.
-/
import ImbalancedChen.ActualThirdOriginalWeightedCurvature

set_option Elab.async false

namespace ImbalancedChen.P2HistoricSieveTrapezoidError

noncomputable section
open Set MeasureTheory
open OriginalU2CoupledRecurrenceSourceOnly

def trapezoid (f : ℝ → ℝ) (a b : ℝ) : ℝ := (b-a)*(f a+f b)/2

theorem continuousOn_endpointChord (f : ℝ → ℝ) (a b : ℝ) :
    ContinuousOn (endpointChord f a b) (Icc a b) :=
  (((continuousOn_const.sub continuousOn_id).div_const (b-a)).mul continuousOn_const).add
    (((continuousOn_id.sub continuousOn_const).div_const (b-a)).mul continuousOn_const)

/-- Exact ordinary chord integral, retaining the physical cell width. -/
theorem integral_endpointChord (f : ℝ → ℝ) {a b : ℝ} (hab : a < b) :
    (∫ x in a..b, endpointChord f a b x) = trapezoid f a b := by
  let P : ℝ → ℝ := fun x =>
    (f a/(b-a))*(b*x-x^2/2)+(f b/(b-a))*(x^2/2-a*x)
  have hd : ∀ x ∈ uIcc a b, HasDerivAt P (endpointChord f a b x) x := by
    intro x hx
    have h1 := ((hasDerivAt_id x).const_mul b).sub
      (((hasDerivAt_id x).pow 2).div_const 2)
    have h2 := (((hasDerivAt_id x).pow 2).div_const 2).sub
      ((hasDerivAt_id x).const_mul a)
    apply ((h1.const_mul (f a/(b-a))).add (h2.const_mul (f b/(b-a)))).congr_deriv
    dsimp [endpointChord]
    ring
  have hi : IntervalIntegrable (endpointChord f a b) volume a b :=
    (continuousOn_endpointChord f a b).intervalIntegrable_of_Icc hab.le
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi]
  dsimp [P, trapezoid]
  field_simp [ne_of_gt (sub_pos.mpr hab)]
  ring

/-- The denominator12 comes from integrating the quadratic shape exactly;
it is not a sup-norm bound with denominator8. -/
theorem integral_quadratic_remainder (M : ℝ) {a b : ℝ} (ha : 0 < a) :
    (∫ x in a..b, M*(x-a)*(b-x)/2) = M*(b-a)^3/12 := by
  have h := quadraticChordMajorant_integral (M*a) (b := b) ha
  have heq : (fun x : ℝ => (M*a)*(x-a)*(b-x)/(2*a)) =
      (fun x : ℝ => M*(x-a)*(b-x)/2) := by
    funext x
    field_simp [ha.ne']
    ring
  rw [heq] at h
  convert h using 1 <;> field_simp [ha.ne'] <;> ring

private theorem integrate_remainder {e : ℝ → ℝ} {a b M : ℝ}
    (ha : 0 < a) (hab : a < b) (he : ContinuousOn e (Icc a b))
    (hpoint : ∀ x ∈ Icc a b, 0 ≤ e x ∧ e x ≤ M*(x-a)*(b-x)/2) :
    0 ≤ (∫ x in a..b, e x) ∧ (∫ x in a..b, e x) ≤ M*(b-a)^3/12 := by
  have hi := he.intervalIntegrable_of_Icc hab.le
  have hg : IntervalIntegrable (fun x : ℝ => M*(x-a)*(b-x)/2) volume a b :=
    (((continuous_const.mul (continuous_id.sub continuous_const)).mul
      (continuous_const.sub continuous_id)).div_const 2).intervalIntegrable a b
  constructor
  · exact intervalIntegral.integral_nonneg hab.le (fun x hx => (hpoint x hx).1)
  · exact (intervalIntegral.integral_mono_on hab.le hi hg
      (fun x hx => (hpoint x hx).2)).trans_eq (integral_quadratic_remainder M ha)

/-- Concave actual integrands lie ABOVE the ordinary trapezoid. -/
theorem concave_trapezoid_error {f f' f'' : ℝ → ℝ} {a b M : ℝ}
    (ha : 0 < a) (hab : a < b) (hM : 0 ≤ M)
    (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x)
    (hf'' : ∀ x ∈ Ioo a b, HasDerivAt f' (f'' x) x)
    (hbound : ∀ x ∈ Ioo a b, -M ≤ f'' x ∧ f'' x ≤ 0) :
    trapezoid f a b ≤ (∫ x in a..b, f x) ∧
      (∫ x in a..b, f x) ≤ trapezoid f a b + M*(b-a)^3/12 := by
  have hrem := integrate_remainder ha hab
    (hf.sub (continuousOn_endpointChord f a b)) (fun x hx => by
      have h := concave_chord_of_local_second_bounds hab hM hf hf' hf'' hbound hx
      exact ⟨h.1, h.2.1⟩)
  rw [intervalIntegral.integral_sub (hf.intervalIntegrable_of_Icc hab.le)
    ((continuousOn_endpointChord f a b).intervalIntegrable_of_Icc hab.le),
    integral_endpointChord f hab] at hrem
  constructor <;> linarith only [hrem.1, hrem.2]

/-- Convex actual integrands lie BELOW the ordinary trapezoid. -/
theorem convex_trapezoid_error {f f' f'' : ℝ → ℝ} {a b M : ℝ}
    (ha : 0 < a) (hab : a < b) (hM : 0 ≤ M)
    (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x)
    (hf'' : ∀ x ∈ Ioo a b, HasDerivAt f' (f'' x) x)
    (hbound : ∀ x ∈ Ioo a b, 0 ≤ f'' x ∧ f'' x ≤ M) :
    trapezoid f a b - M*(b-a)^3/12 ≤ (∫ x in a..b, f x) ∧
      (∫ x in a..b, f x) ≤ trapezoid f a b := by
  have hrem := integrate_remainder ha hab
    ((continuousOn_endpointChord f a b).sub hf) (fun x hx => by
      have h := convex_chord_of_local_second_bounds hab hM hf hf' hf'' hbound hx
      exact ⟨h.1, h.2.1⟩)
  rw [intervalIntegral.integral_sub
    ((continuousOn_endpointChord f a b).intervalIntegrable_of_Icc hab.le)
    (hf.intervalIntegrable_of_Icc hab.le), integral_endpointChord f hab] at hrem
  constructor <;> linarith only [hrem.1, hrem.2]

/-- The true factor curvatures obtained by differentiating the normalized
coupled equations, rather than confusing them with numerator curvatures. -/
def lowerCurvature (s : ℝ) : ℝ := (Lcurvature s - 2*lowerSlope s)/s
def upperTailCurvature (s : ℝ) : ℝ := (Hcurvature s - 2*upperSlope s)/s

theorem hasDerivAt_lowerSlope {s : ℝ} (hs : 2 < s)
    (hp : HasDerivAt (fun u => upper (u-1)) (Lcurvature s) s) :
    HasDerivAt lowerSlope (lowerCurvature s) s := by
  have hd := (hp.sub (hasDerivAt_lower hs)).fun_div (hasDerivAt_id s)
    (by linarith : s ≠ 0)
  apply hd.congr_deriv
  dsimp [lowerCurvature, lowerSlope]
  field_simp [show s ≠ 0 by linarith]
  ring

theorem hasDerivAt_upperSlope {s : ℝ} (hs : 3 < s) :
    HasDerivAt upperSlope (upperTailCurvature s) s := by
  have hd := ((hasDerivAt_Hprime hs).sub (hasDerivAt_upper_tail hs)).fun_div
    (hasDerivAt_id s) (by linarith : s ≠ 0)
  apply hd.congr_deriv
  dsimp [upperTailCurvature, upperSlope]
  field_simp [show s ≠ 0 by linarith]
  ring

/-- The actual local lower-factor curvature bound needed by Q80 is1. -/
theorem lowerCurvature_bounds {s : ℝ} (hs : 2 < s)
    (hc : -1 ≤ Lcurvature s ∧ Lcurvature s ≤ 0) :
    -1 ≤ lowerCurvature s ∧ lowerCurvature s ≤ 0 := by
  have hsl := lowerSlope_bounds hs
  have hinv : 1/s ≤ (1 : ℝ)/2 := one_div_le_one_div_of_le (by norm_num) hs.le
  have hhalf : lowerSlope s ≤ 1/2 := hsl.2.trans hinv
  have hspos : 0 < s := by linarith
  constructor
  · unfold lowerCurvature
    apply (le_div_iff₀ hspos).2
    linarith only [hc.1, hhalf, hs]
  · exact div_nonpos_of_nonpos_of_nonneg
      (by linarith only [hc.2, hsl.1]) hspos.le

/-- The actual tail upper-factor curvature is nonnegative and at most2. -/
theorem upperTailCurvature_bounds {s : ℝ} (hs : 3 < s) :
    0 ≤ upperTailCurvature s ∧ upperTailCurvature s ≤ 2 := by
  have hc := Hcurvature_bounds hs
  have hsl := upperSlope_bounds hs
  have hi1 : 1/(s-1) ≤ (1 : ℝ) := by
    simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1)
      (by linarith : (1 : ℝ) ≤ s-1)
  have hi2 : 1/s ≤ (1 : ℝ) := by
    simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1)
      (by linarith : (1 : ℝ) ≤ s)
  have hspos : 0 < s := by linarith
  constructor
  · exact div_nonneg (by linarith only [hc.1, hsl.2]) hspos.le
  · unfold upperTailCurvature
    apply (div_le_iff₀ hspos).2
    linarith only [hc.2, hi1, hsl.1, hi2, hs]

theorem hasDerivAt_inverseSlope {s : ℝ} (hs : 0 < s) :
    HasDerivAt (fun u : ℝ => -((u^2)⁻¹)) (2/s^3) s := by
  have hd := ((((hasDerivAt_id s).pow 2).inv (pow_ne_zero 2 hs.ne')).neg)
  apply hd.congr_deriv
  field_simp [hs.ne']
  ring

/-- The initial upper strip uses its exact reciprocal, including the chosen
historical endpoint at1. Canonical upper(1) is never used in this equality. -/
theorem upper_initial_integral_eq_reciprocal {a b : ℝ}
    (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ 3) :
    (∫ x in a..b, upper x) = ∫ x in a..b, 1/x := by
  simp only [intervalIntegral.integral_of_le hab]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro x hx
  exact upper_eq_inv (by linarith only [ha, hx.1]) (hx.2.trans hb)

theorem upper_initial_trapezoid_error {a b : ℝ}
    (ha : 1 ≤ a) (hab : a < b) (hb : b ≤ 3) :
    trapezoid (fun x : ℝ => 1/x) a b - 2*(b-a)^3/12 ≤ (∫ x in a..b, upper x) ∧
      (∫ x in a..b, upper x) ≤ trapezoid (fun x : ℝ => 1/x) a b := by
  rw [upper_initial_integral_eq_reciprocal ha hab.le hb]
  apply convex_trapezoid_error (f' := fun x : ℝ => -((x^2)⁻¹))
    (f'' := fun x : ℝ => 2/x^3) (by linarith) hab (by norm_num)
  · exact continuousOn_const.div continuousOn_id
      (fun x hx => (lt_of_lt_of_le (by linarith : 0 < a) hx.1).ne')
  · intro x hx
    simpa only [one_div] using hasDerivAt_inv (show x ≠ 0 by linarith [hx.1])
  · intro x hx
    exact hasDerivAt_inverseSlope (by linarith [hx.1])
  · intro x hx
    have hx1 : 1 ≤ x := ha.trans hx.1.le
    have hxpos : 0 < x := by linarith
    have hx3 : (1 : ℝ) ≤ x^3 := by
      simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hx1 3
    constructor
    · positivity
    · apply (div_le_iff₀ (pow_pos hxpos 3)).2
      linarith only [hx3]

/-- Q80 H-update integrand: f is concave with |f''|<=1 on every complete
original grid cell. The knot4 is excluded only from the open interior. -/
theorem lower_cell_trapezoid_error (j : ℕ) (hj : 32768 ≤ j) :
    trapezoid lower (cellLeft j) (cellRight j) ≤
        (∫ x in (cellLeft j)..(cellRight j), lower x) ∧
      (∫ x in (cellLeft j)..(cellRight j), lower x) ≤
        trapezoid lower (cellLeft j) (cellRight j) + 1/(12*(16384 : ℝ)^3) := by
  have hjR : (32768 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have ha : 2 ≤ cellLeft j := by dsimp [cellLeft]; linarith
  have hcont : ContinuousOn lower (Icc (cellLeft j) (cellRight j)) := by
    apply continuousOn_thirdTailLowerFactor.mono
    intro x hx
    exact ha.trans hx.1
  have h := concave_trapezoid_error (f' := lowerSlope) (f'' := lowerCurvature)
    (by linarith) (original_cell_lt j) (by norm_num : (0 : ℝ) ≤ 1) hcont
    (fun x hx => hasDerivAt_lower (by linarith [hx.1]))
    (fun x hx => hasDerivAt_lowerSlope (by linarith [hx.1])
      (original_L_cell_curvature j hj hx).2.1)
    (fun x hx => by
      have hlocal := (original_L_cell_curvature j hj hx).2.2
      have hinv : 1/(cellLeft j-1) ≤ (1 : ℝ) := by
        simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1)
          (by linarith : (1 : ℝ) ≤ cellLeft j-1)
      exact lowerCurvature_bounds (by linarith [hx.1])
        ⟨by linarith only [hlocal.1, hinv], hlocal.2⟩)
  have herror : (1 : ℝ)*(cellRight j-cellLeft j)^3/12 = 1/(12*(16384 : ℝ)^3) := by
    rw [original_cell_width]
    norm_num
  simpa only [herror] using h

/-- Q80 L-update tail integrand: F is convex with F''<=2 on every cell>=3. -/
theorem upper_tail_cell_trapezoid_error (j : ℕ) (hj : 49152 ≤ j) :
    trapezoid upper (cellLeft j) (cellRight j) - 1/(6*(16384 : ℝ)^3) ≤
        (∫ x in (cellLeft j)..(cellRight j), upper x) ∧
      (∫ x in (cellLeft j)..(cellRight j), upper x) ≤
        trapezoid upper (cellLeft j) (cellRight j) := by
  have hjR : (49152 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have ha : 3 ≤ cellLeft j := by dsimp [cellLeft]; linarith
  have hcont : ContinuousOn upper (Icc (cellLeft j) (cellRight j)) := by
    intro x hx
    exact (continuousAt_upper (by linarith [hx.1])).continuousWithinAt
  have h := convex_trapezoid_error (f' := upperSlope) (f'' := upperTailCurvature)
    (by linarith) (original_cell_lt j) (by norm_num : (0 : ℝ) ≤ 2) hcont
    (fun x hx => hasDerivAt_upper_tail (by linarith [hx.1]))
    (fun x hx => hasDerivAt_upperSlope (by linarith [hx.1]))
    (fun x hx => upperTailCurvature_bounds (by linarith [hx.1]))
  have herror : 2*(cellRight j-cellLeft j)^3/12 = 1/(6*(16384 : ℝ)^3) := by
    rw [original_cell_width]
    norm_num
  simpa only [herror] using h

/-- Q80 L-update initial integrand, including its first delayed left endpoint1.
Both trapezoid endpoint values are literal reciprocals from initialized H. -/
theorem upper_initial_cell_trapezoid_error (j : ℕ)
    (hj : 16384 ≤ j) (hj3 : j < 49152) :
    trapezoid (fun x : ℝ => 1/x) (cellLeft j) (cellRight j) - 1/(6*(16384 : ℝ)^3) ≤
        (∫ x in (cellLeft j)..(cellRight j), upper x) ∧
      (∫ x in (cellLeft j)..(cellRight j), upper x) ≤
        trapezoid (fun x : ℝ => 1/x) (cellLeft j) (cellRight j) := by
  have hjR : (16384 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have hj3R : (j : ℝ)+1 ≤ 49152 := by exact_mod_cast (show j+1 ≤ 49152 by omega)
  have ha : 1 ≤ cellLeft j := by dsimp [cellLeft]; linarith
  have hb : cellRight j ≤ 3 := by dsimp [cellRight]; linarith
  have h := upper_initial_trapezoid_error ha (original_cell_lt j) hb
  have herror : 2*(cellRight j-cellLeft j)^3/12 = 1/(6*(16384 : ℝ)^3) := by
    rw [original_cell_width]
    norm_num
  simpa only [herror] using h

/-- The first numerator strip is paid from the actual logarithmic formula,
including L(2). No version of L_sub below its proved domain is invoked. -/
theorem L_initial_increment_eq_upper_integral {a b : ℝ}
    (ha : 1 ≤ a) (hab : a < b) (hb : b ≤ 2) :
    L (b+1) - L (a+1) = ∫ x in a..b, upper x := by
  have hla : L (a+1) = Real.log a := by
    simpa only [add_sub_cancel_right] using
      L_eq_log (s := a+1) (by linarith) (by linarith)
  have hlb : L (b+1) = Real.log b := by
    simpa only [add_sub_cancel_right] using
      L_eq_log (s := b+1) (by linarith) (by linarith)
  have hapos : 0 < a := by linarith
  have hbpos : 0 < b := hapos.trans hab
  rw [hla, hlb, upper_initial_integral_eq_reciprocal ha hab.le (by linarith),
    integral_one_div_of_pos hapos hbpos, Real.log_div hbpos.ne' hapos.ne']

/-- Every actual L increment in the historic recurrence is the delayed
upper-factor cell integral, including the very first update from L(2). -/
theorem L_cell_increment_eq_upper_integral (j : ℕ) (hj : 16384 ≤ j) :
    L (cellRight j+1) - L (cellLeft j+1) =
      ∫ x in (cellLeft j)..(cellRight j), upper x := by
  have hjR : (16384 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  by_cases hj2 : j < 32768
  · have hj2R : (j : ℝ)+1 ≤ 32768 := by
      exact_mod_cast (show j+1 ≤ 32768 by omega)
    apply L_initial_increment_eq_upper_integral
    · dsimp [cellLeft]
      linarith
    · exact original_cell_lt j
    · dsimp [cellRight]
      linarith
  · have hj2R : (32768 : ℝ) ≤ (j : ℝ) := by
      exact_mod_cast (Nat.le_of_not_gt hj2)
    have ha : 3 ≤ cellLeft j+1 := by dsimp [cellLeft]; linarith
    have h := L_sub (x := cellLeft j+1) (y := cellRight j+1) ha
      (by linarith [original_cell_lt j])
    rw [intervalIntegral.integral_comp_sub_right] at h
    simpa only [add_sub_cancel_right] using h

/-- The actual H increment in every nonconstant historic update. -/
theorem H_cell_increment_eq_lower_integral (j : ℕ) (hj : 32768 ≤ j) :
    H (cellRight j+1) - H (cellLeft j+1) =
      ∫ x in (cellLeft j)..(cellRight j), lower x := by
  have hjR : (32768 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have ha : 3 ≤ cellLeft j+1 := by dsimp [cellLeft]; linarith
  have h := H_sub (x := cellLeft j+1) (y := cellRight j+1) ha
    (by linarith [original_cell_lt j])
  rw [intervalIntegral.integral_comp_sub_right] at h
  simpa only [add_sub_cancel_right] using h

theorem H_cell_increment_trapezoid_error (j : ℕ) (hj : 32768 ≤ j) :
    trapezoid lower (cellLeft j) (cellRight j) ≤
        H (cellRight j+1) - H (cellLeft j+1) ∧
      H (cellRight j+1) - H (cellLeft j+1) ≤
        trapezoid lower (cellLeft j) (cellRight j) + 1/(12*(16384 : ℝ)^3) := by
  rw [H_cell_increment_eq_lower_integral j hj]
  exact lower_cell_trapezoid_error j hj

theorem L_initial_cell_increment_trapezoid_error (j : ℕ)
    (hj : 16384 ≤ j) (hj3 : j < 49152) :
    trapezoid (fun x : ℝ => 1/x) (cellLeft j) (cellRight j) - 1/(6*(16384 : ℝ)^3) ≤
        L (cellRight j+1) - L (cellLeft j+1) ∧
      L (cellRight j+1) - L (cellLeft j+1) ≤
        trapezoid (fun x : ℝ => 1/x) (cellLeft j) (cellRight j) := by
  rw [L_cell_increment_eq_upper_integral j hj]
  exact upper_initial_cell_trapezoid_error j hj hj3

theorem L_tail_cell_increment_trapezoid_error (j : ℕ) (hj : 49152 ≤ j) :
    trapezoid upper (cellLeft j) (cellRight j) - 1/(6*(16384 : ℝ)^3) ≤
        L (cellRight j+1) - L (cellLeft j+1) ∧
      L (cellRight j+1) - L (cellLeft j+1) ≤
        trapezoid upper (cellLeft j) (cellRight j) := by
  rw [L_cell_increment_eq_upper_integral j (by omega)]
  exact upper_tail_cell_trapezoid_error j hj

end
end ImbalancedChen.P2HistoricSieveTrapezoidError
