import ImbalancedChen.P2U9DirectedRationalCover
import ImbalancedChen.P5zUpsilon9OriginalSlot

/-!
# Independent lower certificates for the original ninth integral

SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

The existing rational cover proves an upper bound for the literal J. This
leaf supplies its missing lower companion: on each complete x interval the
right-endpoint logarithm Taylor polynomial divided by the right-endpoint
denominator is a lower bound. The finite sum covers the same entire original
interval, including the moving y wall through the proved log dictionary.

The final Boolean contains only finite rational expressions and the two
independent ORIGINAL saved endpoints. Its truth is NOT asserted here, and
has not been evaluated. No integral enclosure, U9 mean, PP estimate, or
adopted-K distribution estimate is assumed as a supplier.
-/

namespace ImbalancedChen.P5U9DirectedLowerCertificate

noncomputable section

open Set MeasureTheory
open scoped BigOperators
open P2U9DirectedRationalCover P2ContinuousSieveRational

/-- The right endpoint supplies both lower-oriented factors. -/
def cellLower (n : ℕ) (r : ℚ) : ℚ :=
  logLower n (logQuery r) / (r * (1 - r))

/-- Complete lower sum on the original rational partition. -/
def rationalLower (n m : ℕ) : ℚ :=
  ∑ k ∈ Finset.range m,
    (mesh m (k + 1) - mesh m k) * cellLower n (mesh m (k + 1))

/-- Every point of the full closed cell has the same lower certificate.
There is no denominator sign or monotonicity premise left to a caller. -/
theorem cellLower_le_logDensity (n : ℕ) (r : ℚ) {x : ℝ}
    (hx : (a : ℝ) ≤ x) (hxr : x ≤ (r : ℝ)) (hr : r ≤ b) :
    (cellLower n r : ℝ) ≤ logDensity x := by
  have hrR : (r : ℝ) ≤ (b : ℝ) := by exact_mod_cast hr
  have har : a ≤ r := by exact_mod_cast (hx.trans hxr)
  have hq : 2 ≤ logQuery r := by
    dsimp [logQuery, d]
    norm_num [a, b] at har hr
    linarith
  have hlogLower := (log_bounds n (logQuery r) hq).1
  have harg : (logQuery r : ℝ) - 1 =
      (1 - (r : ℝ) - (d : ℝ)) / (d : ℝ) := by
    dsimp [logQuery]
    push_cast
    <;> ring
  rw [harg] at hlogLower
  have hx0 : 0 < x := by norm_num [a] at hx; linarith only [hx]
  have hr0 : 0 < (r : ℝ) := hx0.trans_le hxr
  have hr1 : (r : ℝ) < 1 := by norm_num [b] at hrR; linarith only [hrR]
  have hx1 : x < 1 := hxr.trans_lt hr1
  have hdenx : 0 < x * (1 - x) := mul_pos hx0 (sub_pos.mpr hx1)
  have hdenr : 0 < (r : ℝ) * (1 - (r : ℝ)) := mul_pos hr0 (sub_pos.mpr hr1)
  have hargR : 1 ≤ (1 - (r : ℝ) - (d : ℝ)) / (d : ℝ) := by
    apply (le_div_iff₀ (by norm_num [d] : (0 : ℝ) < (d : ℝ))).2
    norm_num [b, d] at hrR ⊢
    linarith only [hrR]
  have hratio : (1 - (r : ℝ) - (d : ℝ)) / (d : ℝ) ≤
      (1 - x - (d : ℝ)) / (d : ℝ) :=
    div_le_div_of_nonneg_right (by linarith only [hxr]) (by norm_num [d])
  have hlog := Real.log_le_log (by linarith only [hargR] :
    0 < (1 - (r : ℝ) - (d : ℝ)) / (d : ℝ)) hratio
  have hnum0 : 0 ≤ Real.log ((1 - x - (d : ℝ)) / (d : ℝ)) :=
    Real.log_nonneg (hargR.trans hratio)
  have hden : x * (1 - x) ≤ (r : ℝ) * (1 - (r : ℝ)) := by
    have hprod := mul_nonneg (sub_nonneg.mpr hxr)
      (show 0 ≤ 1 - x - (r : ℝ) by
        norm_num [b] at hrR
        linarith only [hxr, hrR])
    nlinarith only [hprod]
  calc
    (cellLower n r : ℝ) =
        (logLower n (logQuery r) : ℝ) / ((r : ℝ) * (1 - (r : ℝ))) := by
      simp only [cellLower, Rat.cast_div, Rat.cast_mul, Rat.cast_sub, Rat.cast_one]
    _ ≤ Real.log ((1 - (r : ℝ) - (d : ℝ)) / (d : ℝ)) /
        ((r : ℝ) * (1 - (r : ℝ))) :=
      div_le_div_of_nonneg_right hlogLower hdenr.le
    _ ≤ Real.log ((1 - x - (d : ℝ)) / (d : ℝ)) /
        ((r : ℝ) * (1 - (r : ℝ))) :=
      div_le_div_of_nonneg_right hlog hdenr.le
    _ ≤ logDensity x := div_le_div_of_nonneg_left hnum0 hdenx hden

/-- A finite rational lower certificate for the WHOLE literal original J.
The only parameter condition is a nonempty partition. -/
theorem rationalLower_le_actual_integral (n m : ℕ) (hm : 0 < m) :
    (rationalLower n m : ℝ) ≤ currentChenUpsilon9HarmonicIntegral := by
  have hcell (k : ℕ) (hk : k < m) :
      IntervalIntegrable logDensity volume (mesh m k : ℝ) (mesh m (k + 1) : ℝ) := by
    have hl := (mesh_bounds m hm k hk.le).1
    have hr := (mesh_bounds m hm (k + 1) (by omega)).2
    have horder : (mesh m k : ℝ) ≤ (mesh m (k + 1) : ℝ) := by
      exact_mod_cast (mesh_monotone m hm (Nat.le_succ k))
    apply (continuousOn_logDensity.mono ?_).intervalIntegrable_of_Icc horder
    intro x hx
    have hlR : (a : ℝ) ≤ (mesh m k : ℝ) := by exact_mod_cast hl
    have hrR : (mesh m (k + 1) : ℝ) ≤ (b : ℝ) := by exact_mod_cast hr
    exact ⟨hlR.trans hx.1, hx.2.trans hrR⟩
  have hpartition := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun k => (mesh m k : ℝ)) hcell
  rw [mesh_zero, mesh_last m hm] at hpartition
  have hJ : currentChenUpsilon9HarmonicIntegral =
      ∫ x in (a : ℝ)..(b : ℝ), logDensity x := by
    rw [currentChenUpsilon9HarmonicIntegral_eq_logIntegral,
      integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num)]
    rfl
  rw [hJ, ← hpartition]
  have hbound : ∀ k ∈ Finset.range m,
      (((mesh m (k + 1) - mesh m k) * cellLower n (mesh m (k + 1)) : ℚ) : ℝ) ≤
        ∫ x in (mesh m k : ℝ)..(mesh m (k + 1) : ℝ), logDensity x := by
    intro k hk
    have hk' := Finset.mem_range.mp hk
    have hl := (mesh_bounds m hm k hk'.le).1
    have hr := (mesh_bounds m hm (k + 1) (by omega)).2
    have horder : (mesh m k : ℝ) ≤ (mesh m (k + 1) : ℝ) := by
      exact_mod_cast (mesh_monotone m hm (Nat.le_succ k))
    have hlR : (a : ℝ) ≤ (mesh m k : ℝ) := by exact_mod_cast hl
    have h := intervalIntegral.integral_mono_on horder intervalIntegrable_const
      (hcell k hk') (fun x hx =>
        cellLower_le_logDensity n (mesh m (k + 1)) (hlR.trans hx.1) hx.2 hr)
    rw [intervalIntegral.integral_const] at h
    simpa only [smul_eq_mul, Rat.cast_mul, Rat.cast_sub] using h
  have hs := Finset.sum_le_sum hbound
  simpa [rationalLower] using hs

/-- A completely explicit lower certificate already follows from one
logarithm term and one cell. This is weaker than the original stored lower
endpoint, but requires no external Boolean proof or numerical premise. -/
theorem one_third_le_actual_integral :
    (1 / 3 : ℝ) ≤ currentChenUpsilon9HarmonicIntegral := by
  have hr : (1 / 3 : ℝ) ≤ (rationalLower 1 1 : ℝ) := by
    norm_num [rationalLower, cellLower, mesh, a, b, logQuery, d,
      logLower, Finset.sum_range_succ]
  exact hr.trans (rationalLower_le_actual_integral 1 1 (by norm_num))

/-- The companion one-cell upper certificate also gives a coarse exact
two-sided enclosure without adopting either stored endpoint. -/
theorem actual_integral_le_three_quarters :
    currentChenUpsilon9HarmonicIntegral ≤ (3 / 4 : ℝ) := by
  have hr : (P2U9DirectedRationalCover.rationalUpper 1 1 : ℝ) ≤ (3 / 4 : ℝ) := by
    norm_num [P2U9DirectedRationalCover.rationalUpper, cellUpper, mesh, a, b,
      logQuery, d, logUpper, logLower, Finset.sum_range_succ]
  exact (actual_integral_le_rationalUpper 1 1 (by norm_num)).trans hr

/-- Literal independent lower Simpson endpoint, expressed over rationals. -/
def originalLower : ℚ :=
  (16911485600294926597530591281091713 / 5192296858534827628530496329220096) /
    (67619 / 10000)

/-- Literal saved upper endpoint, expressed over rationals. -/
def originalUpper : ℚ :=
  (3937512077512215599969887 / 1208925819614629174706176) / (67619 / 10000)

theorem originalLower_cast : (originalLower : ℝ) =
    P5OriginalCoefficientArithmetic.p5z_originalU9LowerIntegralEndpoint := by
  rw [P5OriginalCoefficientArithmetic.p5z_originalU9LowerIntegralEndpoint_exact]
  norm_num [originalLower]

theorem originalUpper_cast : (originalUpper : ℝ) =
    P5OriginalCoefficientArithmetic.p5z_originalU9UpperIntegralEndpoint := by
  rw [P5OriginalCoefficientArithmetic.p5z_originalU9UpperIntegralEndpoint_exact]
  norm_num [originalUpper]

/-- A finite rational comparison, with no real integral or count in it.
The two meshes and two log precisions can be chosen independently. -/
def independentOriginalCheck (nL mL nU mU : ℕ) : Bool := decide
  (originalLower ≤ rationalLower nL mL ∧
    P2U9DirectedRationalCover.rationalUpper nU mU ≤ originalUpper)

/-- Soundness yields the precise two independent primitive integral inputs
of the original same-k, same-rho h9 consumer. No passing check is claimed. -/
theorem independentOriginalCheck_sound (nL mL nU mU : ℕ)
    (hmL : 0 < mL) (hmU : 0 < mU)
    (hcheck : independentOriginalCheck nL mL nU mU = true) :
    currentChenUpsilon9HarmonicIntegral ≤
        P5OriginalCoefficientArithmetic.p5z_originalU9UpperIntegralEndpoint ∧
      P5OriginalCoefficientArithmetic.p5z_originalU9LowerIntegralEndpoint ≤
        currentChenUpsilon9HarmonicIntegral := by
  have hc : originalLower ≤ rationalLower nL mL ∧
      P2U9DirectedRationalCover.rationalUpper nU mU ≤ originalUpper :=
    of_decide_eq_true hcheck
  have hL : (originalLower : ℝ) ≤ (rationalLower nL mL : ℝ) := by
    exact_mod_cast hc.1
  have hU : (P2U9DirectedRationalCover.rationalUpper nU mU : ℝ) ≤
      (originalUpper : ℝ) := by exact_mod_cast hc.2
  rw [originalLower_cast] at hL
  rw [originalUpper_cast] at hU
  exact ⟨(actual_integral_le_rationalUpper nU mU hmU).trans hU,
    hL.trans (rationalLower_le_actual_integral nL mL hmL)⟩

end

end ImbalancedChen.P5U9DirectedLowerCertificate
