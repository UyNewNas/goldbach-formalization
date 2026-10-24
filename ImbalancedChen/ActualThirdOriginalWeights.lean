import ImbalancedChen.ActualThirdOriginalSharpChord
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic


/-!
SOURCEONLY / UNCOMPILED / OPEN30.
Original numerator-chord integration weights, including the literal six
112-bit integers returned by weights(j) in
numerical-primitive-adversarial-20261009.py. This is one weight supplier.
It does not prove any table node, query, adaptive leaf, or saved U2 bound.
Append after the actual sharp-chord supplier; see the sibling recipe/CP.
-/

namespace ImbalancedChen.OriginalU2CoupledRecurrenceSourceOnly

noncomputable section
open Set MeasureTheory

/-- The real logarithm appearing in the original weights(j). -/
def originalCellLog (j : ℕ) : ℝ := Real.log (1 + 1 / (j : ℝ))

/-- Integral of the LEFT affine numerator basis divided by u. -/
def originalWeight0 (j : ℕ) : ℝ := ((j : ℝ) + 1) * originalCellLog j - 1

/-- Integral of the RIGHT affine numerator basis divided by u. -/
def originalWeight1 (j : ℕ) : ℝ := 1 - (j : ℝ) * originalCellLog j

/-- FTC evaluates the chord with its actual real endpoint values. No
integrability assertion or claimed quadrature identity is a premise. -/
theorem endpointChord_div_integral (f : ℝ → ℝ) {a b : ℝ}
    (ha : 0 < a) (hab : a < b) :
    (∫ u in a..b, endpointChord f a b u / u) =
      ((b * Real.log (b/a) - (b-a))/(b-a)) * f a +
      (((b-a) - a * Real.log (b/a))/(b-a)) * f b := by
  have hd : b-a ≠ 0 := ne_of_gt (sub_pos.mpr hab)
  have hb : 0 < b := ha.trans hab
  let c : ℝ := (b*f a-a*f b)/(b-a)
  let d : ℝ := (f b-f a)/(b-a)
  let F : ℝ → ℝ := fun u => c * Real.log u + d*u
  have hu : ∀ u ∈ uIcc a b, u ≠ 0 := by
    intro u hu
    rw [uIcc_of_le hab.le] at hu
    exact ne_of_gt (ha.trans_le hu.1)
  have hint : IntervalIntegrable (fun u => endpointChord f a b u / u)
      volume a b := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div _ continuousOn_id hu
    exact (((continuousOn_const.sub continuousOn_id).div_const (b-a)).mul
      continuousOn_const).add
      (((continuousOn_id.sub continuousOn_const).div_const (b-a)).mul
        continuousOn_const)
  have hderiv : ∀ u ∈ uIcc a b,
      HasDerivAt F (endpointChord f a b u / u) u := by
    intro u hu'
    have h := ((Real.hasDerivAt_log (hu u hu')).const_mul c).add
      ((hasDerivAt_id u).const_mul d)
    apply h.congr_deriv
    dsimp [c, d, endpointChord]
    field [hd, hu u hu']
  calc
    (∫ u in a..b, endpointChord f a b u / u) = F b-F a :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
    _ = _ := by
      dsimp [F, c, d]
      rw [Real.log_div hb.ne' ha.ne']
      field [hd]

/-- The original n=16384 chord identity, at every positive index.
The two coefficients are exactly weights(j)'s mathematical weights. -/
theorem original_grid_chord_integral (f : ℝ → ℝ) (j : ℕ) (hj : 1 ≤ j) :
    (∫ u in (cellLeft j)..(cellRight j),
      endpointChord f (cellLeft j) (cellRight j) u / u) =
      originalWeight0 j * f (cellLeft j) +
      originalWeight1 j * f (cellRight j) := by
  have hjR : (0 : ℝ) < (j : ℝ) := by exact_mod_cast (by omega : 0 < j)
  have ha : 0 < cellLeft j := by dsimp [cellLeft]; positivity
  have hratio : cellRight j / cellLeft j = 1 + 1/(j : ℝ) := by
    dsimp [cellRight, cellLeft]
    field_simp [hjR.ne']
  rw [endpointChord_div_integral f ha (original_cell_lt j)]
  simp only [hratio, original_cell_width]
  dsimp [originalWeight0, originalWeight1, originalCellLog, cellLeft, cellRight]
  field_simp [hjR.ne']

/-- Both real normalized JR/Suzuki numerator chords use the SAME weights.
These are the actual L,H from the source supplier, with no model choice. -/
theorem original_actual_chord_integrals (j : ℕ) (hj : 32768 ≤ j) :
    ((∫ u in (cellLeft j)..(cellRight j),
      endpointChord L (cellLeft j) (cellRight j) u / u) =
      originalWeight0 j * L (cellLeft j) +
      originalWeight1 j * L (cellRight j)) ∧
    ((∫ u in (cellLeft j)..(cellRight j),
      endpointChord H (cellLeft j) (cellRight j) u / u) =
      originalWeight0 j * H (cellLeft j) +
      originalWeight1 j * H (cellRight j)) := by
  exact ⟨original_grid_chord_integral L j (by omega),
    original_grid_chord_integral H j (by omega)⟩

theorem original_weights_positive (j : ℕ) (hj : 1 ≤ j) :
    0 < originalWeight0 j ∧ 0 < originalWeight1 j := by
  have hJ : (0 : ℝ) < (j : ℝ) := by exact_mod_cast (by omega : 0 < j)
  have hJ1 : 0 < (j : ℝ)+1 := by linarith
  have hx : (0 : ℝ) < 1/(j : ℝ) := by positivity
  have hq : (0 : ℝ) < 1+1/(j : ℝ) := by positivity
  have hl := Real.lt_log_one_add_of_pos hx
  have he : 2*(1/(j : ℝ))/(1/(j : ℝ)+2) = 2/(2*(j : ℝ)+1) := by
    field [hJ.ne']
  rw [he] at hl
  have hbase : (1 : ℝ) < ((j : ℝ)+1)*(2/(2*(j : ℝ)+1)) := by
    rw [← mul_div_assoc]
    apply (lt_div_iff₀ (by linarith : (0 : ℝ) < 2*(j : ℝ)+1)).2
    linarith
  have hm0 := mul_lt_mul_of_pos_left hl hJ1
  have hu := Real.log_lt_sub_one_of_pos hq (by linarith : 1+1/(j : ℝ) ≠ 1)
  have hm1 := mul_lt_mul_of_pos_left hu hJ
  have hcancel : (j : ℝ)*(1/(j : ℝ)) = 1 := by field_simp [hJ.ne']
  dsimp [originalWeight0, originalWeight1, originalCellLog]
  constructor <;> nlinarith only [hbase, hm0, hm1, hcancel]

/-- Exact partition of the positive integral mass. -/
theorem original_weights_sum (j : ℕ) :
    originalWeight0 j + originalWeight1 j = originalCellLog j := by
  unfold originalWeight0 originalWeight1
  ring

/- Fourth/fifth alternating bounds. Their finite remainders are proved by
derivatives; no infinite-series convergence or supplied log enclosure is used. -/

private def log4 (x : ℝ) : ℝ := x-x^2/2+x^3/3-x^4/4
private def log5 (x : ℝ) : ℝ := log4 x+x^5/5
private def numerator04 (x : ℝ) : ℝ := x^2/2-x^3/6+x^4/12-x^5/20
private def numerator05 (x : ℝ) : ℝ := numerator04 x+x^6/30
private def numerator14 (x : ℝ) : ℝ := x^2/2-x^3/3+x^4/4-x^5/5
private def numerator15 (x : ℝ) : ℝ := numerator14 x+x^6/6
private def numerator0 (x : ℝ) : ℝ := (1+x)*Real.log (1+x)-x
private def numerator1 (x : ℝ) : ℝ := x-Real.log (1+x)

private theorem nonneg_from_zero {f f' : ℝ → ℝ}
    (hzero : f 0 = 0)
    (hd : ∀ x, 0 ≤ x → HasDerivAt f (f' x) x)
    (hpos : ∀ x, 0 ≤ x → 0 ≤ f' x) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ f x := by
  have hm : MonotoneOn f (Ici 0) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
      (fun y hy => (hd y hy).continuousAt.continuousWithinAt)
      (fun y hy => (hd y (interior_subset hy)).hasDerivWithinAt)
      (fun y hy => hpos y (interior_subset hy))
  have h := hm (show (0 : ℝ) ∈ Ici 0 by simp) hx hx
  simpa only [hzero] using h

private theorem logAdd_deriv {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt (fun y : ℝ => Real.log (1+y)) (1/(1+x)) x := by
  have hne : (1 : ℝ)+x ≠ 0 := by linarith
  exact ((hasDerivAt_id' x).const_add 1).log hne

private theorem log4_deriv (x : ℝ) :
    HasDerivAt log4 (1-x+x^2-x^3) x := by
  unfold log4
  have hd := (((hasDerivAt_id' x).sub (((hasDerivAt_id' x).pow 2).div_const 2)).add
    (((hasDerivAt_id' x).pow 3).div_const 3)).sub
    (((hasDerivAt_id' x).pow 4).div_const 4)
  apply hd.congr_deriv
  ring

private theorem log5_deriv (x : ℝ) :
    HasDerivAt log5 (1-x+x^2-x^3+x^4) x := by
  unfold log5
  have hd := (log4_deriv x).add (((hasDerivAt_id' x).pow 5).div_const 5)
  apply hd.congr_deriv
  ring

private theorem numerator04_deriv (x : ℝ) :
    HasDerivAt numerator04 (log4 x) x := by
  unfold numerator04
  have hd := (((((hasDerivAt_id' x).pow 2).div_const 2).sub
    (((hasDerivAt_id' x).pow 3).div_const 6)).add
    (((hasDerivAt_id' x).pow 4).div_const 12)).sub
    (((hasDerivAt_id' x).pow 5).div_const 20)
  apply hd.congr_deriv
  dsimp [log4]
  ring

private theorem numerator05_deriv (x : ℝ) :
    HasDerivAt numerator05 (log5 x) x := by
  unfold numerator05
  have hd := (numerator04_deriv x).add (((hasDerivAt_id' x).pow 6).div_const 30)
  apply hd.congr_deriv
  dsimp [log5]
  ring

private theorem numerator14_deriv (x : ℝ) :
    HasDerivAt numerator14 (x-x^2+x^3-x^4) x := by
  unfold numerator14
  have hd := (((((hasDerivAt_id' x).pow 2).div_const 2).sub
    (((hasDerivAt_id' x).pow 3).div_const 3)).add
    (((hasDerivAt_id' x).pow 4).div_const 4)).sub
    (((hasDerivAt_id' x).pow 5).div_const 5)
  apply hd.congr_deriv
  ring

private theorem numerator15_deriv (x : ℝ) :
    HasDerivAt numerator15 (x-x^2+x^3-x^4+x^5) x := by
  unfold numerator15
  have hd := (numerator14_deriv x).add (((hasDerivAt_id' x).pow 6).div_const 6)
  apply hd.congr_deriv
  ring

private theorem numerator0_deriv {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt numerator0 (Real.log (1+x)) x := by
  unfold numerator0
  have hd := (((hasDerivAt_id' x).const_add 1).mul (logAdd_deriv hx)).sub
    (hasDerivAt_id' x)
  apply hd.congr_deriv
  field [ne_of_gt (by linarith : (0 : ℝ) < 1+x)]

private theorem numerator1_deriv {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt numerator1 (x/(1+x)) x := by
  unfold numerator1
  have hd := (hasDerivAt_id' x).sub (logAdd_deriv hx)
  apply hd.congr_deriv
  field [ne_of_gt (by linarith : (0 : ℝ) < 1+x)]

private theorem original_log_polynomial_bounds {x : ℝ} (hx : 0 ≤ x) :
    log4 x ≤ Real.log (1+x) ∧ Real.log (1+x) ≤ log5 x := by
  constructor
  · have h := nonneg_from_zero
      (f := fun y => Real.log (1+y)-log4 y)
      (f' := fun y => y^4/(1+y)) (by norm_num [log4])
      (by
        intro y hy
        apply ((logAdd_deriv hy).sub (log4_deriv y)).congr_deriv
        field [ne_of_gt (by linarith : (0 : ℝ) < 1+y)])
      (by intro y hy; positivity) hx
    exact sub_nonneg.mp h
  · have h := nonneg_from_zero
      (f := fun y => log5 y-Real.log (1+y))
      (f' := fun y => y^5/(1+y)) (by norm_num [log5, log4])
      (by
        intro y hy
        apply ((log5_deriv y).sub (logAdd_deriv hy)).congr_deriv
        field [ne_of_gt (by linarith : (0 : ℝ) < 1+y)])
      (by intro y hy; positivity) hx
    exact sub_nonneg.mp h

private theorem original_weight0_polynomial_bounds {x : ℝ} (hx : 0 ≤ x) :
    numerator04 x ≤ numerator0 x ∧ numerator0 x ≤ numerator05 x := by
  constructor
  · have h := nonneg_from_zero
      (f := fun y => numerator0 y-numerator04 y)
      (f' := fun y => Real.log (1+y)-log4 y)
      (by norm_num [numerator0, numerator04])
      (fun y hy => (numerator0_deriv hy).sub (numerator04_deriv y))
      (fun y hy => sub_nonneg.mpr (original_log_polynomial_bounds hy).1) hx
    exact sub_nonneg.mp h
  · have h := nonneg_from_zero
      (f := fun y => numerator05 y-numerator0 y)
      (f' := fun y => log5 y-Real.log (1+y))
      (by norm_num [numerator0, numerator05, numerator04])
      (fun y hy => (numerator05_deriv y).sub (numerator0_deriv hy))
      (fun y hy => sub_nonneg.mpr (original_log_polynomial_bounds hy).2) hx
    exact sub_nonneg.mp h

private theorem original_weight1_polynomial_bounds {x : ℝ} (hx : 0 ≤ x) :
    numerator14 x ≤ numerator1 x ∧ numerator1 x ≤ numerator15 x := by
  constructor
  · have h := nonneg_from_zero
      (f := fun y => numerator1 y-numerator14 y)
      (f' := fun y => y^5/(1+y)) (by norm_num [numerator1, numerator14])
      (by
        intro y hy
        apply ((numerator1_deriv hy).sub (numerator14_deriv y)).congr_deriv
        field [ne_of_gt (by linarith : (0 : ℝ) < 1+y)])
      (by intro y hy; positivity) hx
    exact sub_nonneg.mp h
  · have h := nonneg_from_zero
      (f := fun y => numerator15 y-numerator1 y)
      (f' := fun y => y^6/(1+y))
      (by norm_num [numerator1, numerator15, numerator14])
      (by
        intro y hy
        apply ((numerator15_deriv y).sub (numerator1_deriv hy)).congr_deriv
        field [ne_of_gt (by linarith : (0 : ℝ) < 1+y)])
      (by intro y hy; positivity) hx
    exact sub_nonneg.mp h

/-- Literal original integer polynomials, evaluated in Z to avoid truncated
natural subtraction. They are exactly a,b,c,den from weights(j). -/
def originalWeightA (j : ℕ) : ℤ :=
  30*(j : ℤ)^4-10*(j : ℤ)^3+5*(j : ℤ)^2-3*(j : ℤ)
def originalWeightB (j : ℕ) : ℤ :=
  30*(j : ℤ)^4-20*(j : ℤ)^3+15*(j : ℤ)^2-12*(j : ℤ)
def originalWeightC (j : ℕ) : ℤ :=
  60*(j : ℤ)^4-30*(j : ℤ)^3+20*(j : ℤ)^2-15*(j : ℤ)
def originalWeightDen (j : ℕ) : ℤ := 60*(j : ℤ)^5

/-- All six UNROUNDED original rational endpoints enclose their real
weights/logarithm. The caller provides only the original index condition. -/
theorem original_weight_rational_enclosures (j : ℕ) (hj : 1 ≤ j) :
    ((originalWeightA j : ℝ)/(originalWeightDen j : ℝ) ≤ originalWeight0 j ∧
      originalWeight0 j ≤ ((originalWeightA j+2 : ℤ) : ℝ)/(originalWeightDen j : ℝ)) ∧
    ((originalWeightB j : ℝ)/(originalWeightDen j : ℝ) ≤ originalWeight1 j ∧
      originalWeight1 j ≤ ((originalWeightB j+10 : ℤ) : ℝ)/(originalWeightDen j : ℝ)) ∧
    ((originalWeightC j : ℝ)/(originalWeightDen j : ℝ) ≤ originalCellLog j ∧
      originalCellLog j ≤ ((originalWeightC j+12 : ℤ) : ℝ)/(originalWeightDen j : ℝ)) := by
  have hJ : (0 : ℝ) < (j : ℝ) := by exact_mod_cast (by omega : 0 < j)
  let x : ℝ := 1/(j : ℝ)
  have hx : 0 < x := by dsimp [x]; positivity
  have h0 : numerator0 x/x = originalWeight0 j := by
    dsimp [x, numerator0, originalWeight0, originalCellLog]
    field [hJ.ne']
  have h1 : numerator1 x/x = originalWeight1 j := by
    dsimp [x, numerator1, originalWeight1, originalCellLog]
    field [hJ.ne']
  have h04 : numerator04 x/x =
      (originalWeightA j : ℝ)/(originalWeightDen j : ℝ) := by
    dsimp [x, numerator04, originalWeightA, originalWeightDen]
    push_cast
    field [hJ.ne']
  have h05 : numerator05 x/x =
      ((originalWeightA j+2 : ℤ) : ℝ)/(originalWeightDen j : ℝ) := by
    dsimp [x, numerator05, numerator04, originalWeightA, originalWeightDen]
    push_cast
    field [hJ.ne']
  have h14 : numerator14 x/x =
      (originalWeightB j : ℝ)/(originalWeightDen j : ℝ) := by
    dsimp [x, numerator14, originalWeightB, originalWeightDen]
    push_cast
    field [hJ.ne']
  have h15 : numerator15 x/x =
      ((originalWeightB j+10 : ℤ) : ℝ)/(originalWeightDen j : ℝ) := by
    dsimp [x, numerator15, numerator14, originalWeightB, originalWeightDen]
    push_cast
    field [hJ.ne']
  have hc4 : log4 x = (originalWeightC j : ℝ)/(originalWeightDen j : ℝ) := by
    dsimp [x, log4, originalWeightC, originalWeightDen]
    push_cast
    field [hJ.ne']
  have hc5 : log5 x =
      ((originalWeightC j+12 : ℤ) : ℝ)/(originalWeightDen j : ℝ) := by
    dsimp [x, log5, log4, originalWeightC, originalWeightDen]
    push_cast
    field [hJ.ne']
  have q0 := original_weight0_polynomial_bounds hx.le
  have q1 := original_weight1_polynomial_bounds hx.le
  have qL := original_log_polynomial_bounds hx.le
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · simpa only [h04, h0] using div_le_div_of_nonneg_right q0.1 hx.le
  · simpa only [h05, h0] using div_le_div_of_nonneg_right q0.2 hx.le
  · simpa only [h14, h1] using div_le_div_of_nonneg_right q1.1 hx.le
  · simpa only [h15, h1] using div_le_div_of_nonneg_right q1.2 hx.le
  · simpa only [hc4, x, originalCellLog] using qL.1
  · simpa only [hc5, x, originalCellLog] using qL.2

def originalWeightP : ℤ := 2^112
def originalWeight0Lo (j : ℕ) : ℤ := originalWeightA j*originalWeightP/originalWeightDen j
def originalWeight0Hi (j : ℕ) : ℤ := -(-((originalWeightA j+2)*originalWeightP)/originalWeightDen j)
def originalWeight1Lo (j : ℕ) : ℤ := originalWeightB j*originalWeightP/originalWeightDen j
def originalWeight1Hi (j : ℕ) : ℤ := -(-((originalWeightB j+10)*originalWeightP)/originalWeightDen j)
def originalLogLo (j : ℕ) : ℤ := originalWeightC j*originalWeightP/originalWeightDen j
def originalLogHi (j : ℕ) : ℤ := -(-((originalWeightC j+12)*originalWeightP)/originalWeightDen j)

private theorem int_ediv_cast_le (a d : ℤ) (hd : 0 < d) :
    ((a/d : ℤ) : ℝ) ≤ (a : ℝ)/(d : ℝ) := by
  have hf : ⌊(a : ℚ)/(d : ℚ)⌋ = a/d := by
    simpa using Int.floor_div_cast_of_nonneg (k := ℚ) hd.le (a : ℚ)
  have h := Int.floor_le ((a : ℚ)/(d : ℚ))
  rw [hf] at h
  exact_mod_cast h

private theorem scaled_ediv_bounds (a d : ℤ) (hd : 0 < d) :
    (((a*originalWeightP/d : ℤ) : ℝ)/(originalWeightP : ℝ) ≤
      (a : ℝ)/(d : ℝ)) ∧
    ((a : ℝ)/(d : ℝ) ≤
      ((-(-(a*originalWeightP)/d) : ℤ) : ℝ)/(originalWeightP : ℝ)) := by
  have hp : (0 : ℝ) < (originalWeightP : ℝ) := by norm_num [originalWeightP]
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hl := div_le_div_of_nonneg_right (int_ediv_cast_le (a*originalWeightP) d hd) hp.le
  have hu := int_ediv_cast_le (-(a*originalWeightP)) d hd
  have hu' : ((a*originalWeightP : ℤ) : ℝ)/(d : ℝ) ≤
      ((-(-(a*originalWeightP)/d) : ℤ) : ℝ) := by
    simpa only [Int.cast_neg, neg_div, neg_neg] using neg_le_neg hu
  have hu'' := div_le_div_of_nonneg_right hu' hp.le
  have hcancel : (((a*originalWeightP : ℤ) : ℝ)/(d : ℝ))/(originalWeightP : ℝ) =
      (a : ℝ)/(d : ℝ) := by
    push_cast
    field [hp.ne', hdR]
  constructor
  · simpa only [hcancel] using hl
  · simpa only [hcancel] using hu''

theorem original_weight_den_pos (j : ℕ) (hj : 1 ≤ j) :
    0 < originalWeightDen j := by
  have hJ : (0 : ℤ) < (j : ℤ) := by exact_mod_cast (by omega : 0 < j)
  dsimp [originalWeightDen]
  positivity

/-- The SIX LITERAL integers returned by the original weights(j) enclose
the exact real weights and logarithm after division by P=2^112.
No log/weight/node enclosure condition is an input. -/
theorem original_weight_112bit_enclosures (j : ℕ) (hj : 1 ≤ j) :
    ((originalWeight0Lo j : ℝ)/(originalWeightP : ℝ) ≤ originalWeight0 j ∧
      originalWeight0 j ≤ (originalWeight0Hi j : ℝ)/(originalWeightP : ℝ)) ∧
    ((originalWeight1Lo j : ℝ)/(originalWeightP : ℝ) ≤ originalWeight1 j ∧
      originalWeight1 j ≤ (originalWeight1Hi j : ℝ)/(originalWeightP : ℝ)) ∧
    ((originalLogLo j : ℝ)/(originalWeightP : ℝ) ≤ originalCellLog j ∧
      originalCellLog j ≤ (originalLogHi j : ℝ)/(originalWeightP : ℝ)) := by
  have h := original_weight_rational_enclosures j hj
  have hd := original_weight_den_pos j hj
  have h0l := scaled_ediv_bounds (originalWeightA j) (originalWeightDen j) hd
  have h0u := scaled_ediv_bounds (originalWeightA j+2) (originalWeightDen j) hd
  have h1l := scaled_ediv_bounds (originalWeightB j) (originalWeightDen j) hd
  have h1u := scaled_ediv_bounds (originalWeightB j+10) (originalWeightDen j) hd
  have hLl := scaled_ediv_bounds (originalWeightC j) (originalWeightDen j) hd
  have hLu := scaled_ediv_bounds (originalWeightC j+12) (originalWeightDen j) hd
  exact ⟨⟨h0l.1.trans h.1.1, h.1.2.trans h0u.2⟩,
    ⟨h1l.1.trans h.2.1.1, h.2.1.2.trans h1u.2⟩,
    ⟨hLl.1.trans h.2.2.1, h.2.2.2.trans hLu.2⟩⟩

/-- The original lower weight integers are nonnegative, as required when
forming products with nonnegative numerator endpoint enclosures. -/
theorem original_lower_weight_integers_nonneg (j : ℕ) (hj : 1 ≤ j) :
    0 ≤ originalWeight0Lo j ∧ 0 ≤ originalWeight1Lo j ∧ 0 ≤ originalLogLo j := by
  have hJ : (1 : ℤ) ≤ (j : ℤ) := by exact_mod_cast hj
  have hA : 0 ≤ originalWeightA j := by
    have he : originalWeightA j =
        10*(j : ℤ)^3*(3*(j : ℤ)-1)+(j : ℤ)*(5*(j : ℤ)-3) := by
      dsimp [originalWeightA]
      ring
    rw [he]
    have h3 : 0 ≤ 3*(j : ℤ)-1 := by omega
    have h5 : 0 ≤ 5*(j : ℤ)-3 := by omega
    positivity
  have hB : 0 ≤ originalWeightB j := by
    have he : originalWeightB j =
        10*(j : ℤ)^3*(3*(j : ℤ)-2)+3*(j : ℤ)*(5*(j : ℤ)-4) := by
      dsimp [originalWeightB]
      ring
    rw [he]
    have h3 : 0 ≤ 3*(j : ℤ)-2 := by omega
    have h5 : 0 ≤ 5*(j : ℤ)-4 := by omega
    positivity
  have hC : 0 ≤ originalWeightC j := by
    have he : originalWeightC j =
        30*(j : ℤ)^3*(2*(j : ℤ)-1)+5*(j : ℤ)*(4*(j : ℤ)-3) := by
      dsimp [originalWeightC]
      ring
    rw [he]
    have h2 : 0 ≤ 2*(j : ℤ)-1 := by omega
    have h4 : 0 ≤ 4*(j : ℤ)-3 := by omega
    positivity
  have hp : 0 ≤ originalWeightP := by norm_num [originalWeightP]
  have hd := (original_weight_den_pos j hj).le
  exact ⟨Int.ediv_nonneg (mul_nonneg hA hp) hd,
    Int.ediv_nonneg (mul_nonneg hB hp) hd,
    Int.ediv_nonneg (mul_nonneg hC hp) hd⟩

/-- Original rounded weight evaluation on REAL endpoint values. These
definitions do not refer to or assume a certified table array. -/
def originalChord112Lo (f : ℝ → ℝ) (j : ℕ) : ℝ :=
  ((originalWeight0Lo j : ℝ)/(originalWeightP : ℝ))*f (cellLeft j) +
  ((originalWeight1Lo j : ℝ)/(originalWeightP : ℝ))*f (cellRight j)

def originalChord112Hi (f : ℝ → ℝ) (j : ℕ) : ℝ :=
  ((originalWeight0Hi j : ℝ)/(originalWeightP : ℝ))*f (cellLeft j) +
  ((originalWeight1Hi j : ℝ)/(originalWeightP : ℝ))*f (cellRight j)

/-- Direct actual-function bridge: all original rounded weight evaluations
enclose the exact integral of each actual JR/Suzuki endpoint chord. There
is no target weight, endpoint-node, or quadrature enclosure hypothesis. -/
theorem original_actual_chord_112bit_weight_enclosures
    (j : ℕ) (hj : 32768 ≤ j) :
    (originalChord112Lo L j ≤
      (∫ u in (cellLeft j)..(cellRight j),
        endpointChord L (cellLeft j) (cellRight j) u/u) ∧
      (∫ u in (cellLeft j)..(cellRight j),
        endpointChord L (cellLeft j) (cellRight j) u/u) ≤ originalChord112Hi L j) ∧
    (originalChord112Lo H j ≤
      (∫ u in (cellLeft j)..(cellRight j),
        endpointChord H (cellLeft j) (cellRight j) u/u) ∧
      (∫ u in (cellLeft j)..(cellRight j),
        endpointChord H (cellLeft j) (cellRight j) u/u) ≤ originalChord112Hi H j) := by
  have hj1 : 1 ≤ j := by omega
  have hJ : (32768 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have ha : 2 ≤ cellLeft j := by dsimp [cellLeft]; linarith
  have hb : 2 ≤ cellRight j := by dsimp [cellRight]; linarith
  have hLnonneg : ∀ s : ℝ, 2 ≤ s → 0 ≤ L s := by
    intro s hs
    exact mul_nonneg (by linarith) (lower_nonneg hs)
  have hHnonneg : ∀ s : ℝ, 2 ≤ s → 0 ≤ H s := by
    intro s hs
    exact mul_nonneg (by linarith) ((lower_nonneg hs).trans (lower_le_upper hs))
  have hw := original_weight_112bit_enclosures j hj1
  have hbounds (f : ℝ → ℝ) (hfa : 0 ≤ f (cellLeft j))
      (hfb : 0 ≤ f (cellRight j)) :
      originalChord112Lo f j ≤
        (∫ u in (cellLeft j)..(cellRight j),
          endpointChord f (cellLeft j) (cellRight j) u/u) ∧
      (∫ u in (cellLeft j)..(cellRight j),
          endpointChord f (cellLeft j) (cellRight j) u/u) ≤ originalChord112Hi f j := by
    simp only [original_grid_chord_integral f j hj1]
    exact ⟨add_le_add (mul_le_mul_of_nonneg_right hw.1.1 hfa)
        (mul_le_mul_of_nonneg_right hw.2.1.1 hfb),
      add_le_add (mul_le_mul_of_nonneg_right hw.1.2 hfa)
        (mul_le_mul_of_nonneg_right hw.2.1.2 hfb)⟩
  exact ⟨hbounds L (hLnonneg _ ha) (hLnonneg _ hb),
    hbounds H (hHnonneg _ ha) (hHnonneg _ hb)⟩

end
end ImbalancedChen.OriginalU2CoupledRecurrenceSourceOnly
