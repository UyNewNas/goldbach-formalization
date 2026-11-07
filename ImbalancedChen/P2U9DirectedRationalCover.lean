import ImbalancedChen.CurrentChenUpsilon9HarmonicIntegral
import ImbalancedChen.CurrentNumericalTransfer
import ImbalancedChen.P2ContinuousSieveRational

/-!
SOURCE_WRITTEN / UNCOMPILED / CODE_ONLY.

The literal ninth domain is x in [19/125,59/250), and y in
[59/250,(1-x)/2).  Its density is 1/(x*y*(1-x-y)).  The moving wall is
the original square-root cutoff in logarithmic coordinates.  The proved
Fubini/log-integral dictionary is reused, not postulated or reproved.

Every positive mesh size gives a complete rational staircase cover,
with a proved whole-box positive denominator guard.  A finite rational
logarithm upper sum bounds the full actual J, and a decidable rational
budget check supplies the correctly directed negative analytic cost.
No adopted numerical endpoint or integral upper bound is a premise.

This is an analytic supplier.  It does not turn the existing ordinary
8*J arithmetic mean into a currentK*J mean: that leading saving remains
a separate P5 obligation.  The frozen catalogue U9 endpoint is not
claimed to pass the checker in this uncompiled source.
-/

namespace ImbalancedChen.P2U9DirectedRationalCover

noncomputable section
open Set MeasureTheory
open scoped BigOperators
open P2ContinuousSieveRational

def a : ℚ := 19 / 125
def b : ℚ := 59 / 250
def d : ℚ := 59 / 250

def mesh (m k : ℕ) : ℚ := a + (b - a) * (k : ℚ) / (m : ℚ)
def cap (m k : ℕ) : ℚ := (1 - mesh m k) / 2

theorem mesh_zero (m : ℕ) : mesh m 0 = a := by simp [mesh]

theorem mesh_last (m : ℕ) (hm : 0 < m) : mesh m m = b := by
  have hn : (m : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hm
  dsimp [mesh]
  field_simp [hn]
  <;> ring

theorem mesh_monotone (m : ℕ) (hm : 0 < m) : Monotone (mesh m) := by
  intro k l hkl
  have hklQ : (k : ℚ) ≤ (l : ℚ) := by exact_mod_cast hkl
  have hmQ : (0 : ℚ) < m := by exact_mod_cast hm
  dsimp [mesh]
  exact add_le_add_left (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hklQ (by norm_num [a, b])) hmQ.le) a

theorem mesh_bounds (m : ℕ) (hm : 0 < m) (k : ℕ) (hk : k ≤ m) :
    a ≤ mesh m k ∧ mesh m k ≤ b := by
  have hl := mesh_monotone m hm (Nat.zero_le k)
  have hu := mesh_monotone m hm hk
  rw [mesh_zero] at hl
  rw [mesh_last m hm] at hu
  exact ⟨hl, hu⟩

/-- Purely rational, decidable whole-box positivity test. -/
def boxGuard (m k : ℕ) : Bool := decide
  (0 < mesh m k ∧ 0 < d ∧ d ≤ cap m k ∧
    mesh m (k + 1) + cap m k < 1)

/-- Every generated box passes, including boxes meeting the moving wall. -/
theorem boxGuard_true (m : ℕ) (hm : 0 < m) (k : ℕ) (hk : k < m) :
    boxGuard m k = true := by
  obtain ⟨hl, hu⟩ := mesh_bounds m hm k hk.le
  have hr := (mesh_bounds m hm (k + 1) (by omega)).2
  rw [boxGuard, decide_eq_true_eq]
  dsimp [a, b, d, cap] at *
  constructor
  · linarith
  constructor
  · norm_num
  constructor <;> linarith

/-- Complete uniform rational cover of the original moving domain.
The y cap uses the LEFT x endpoint and hence includes the entire slice. -/
theorem moving_domain_uniform_cover (m : ℕ) (hm : 0 < m) {x y : ℝ}
    (hx : x ∈ Ico (a : ℝ) (b : ℝ))
    (hy : y ∈ Ico (d : ℝ) ((1 - x) / 2)) :
    ∃ k : ℕ, k < m ∧ (mesh m k : ℝ) ≤ x ∧
      x < (mesh m (k + 1) : ℝ) ∧ (d : ℝ) ≤ y ∧ y < (cap m k : ℝ) := by
  have hw : (0 : ℝ) < (b : ℝ) - (a : ℝ) := by norm_num [a, b]
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  let z : ℝ := (x - (a : ℝ)) * (m : ℝ) / ((b : ℝ) - (a : ℝ))
  have hz0 : 0 ≤ z := div_nonneg (mul_nonneg (sub_nonneg.mpr hx.1) hmR.le) hw.le
  have hzm : z < (m : ℝ) := by
    apply (div_lt_iff₀ hw).2
    have h := mul_lt_mul_of_pos_right (sub_lt_sub_right hx.2 (a : ℝ)) hmR
    nlinarith only [h]
  let k : ℕ := ⌊z⌋₊
  have hk : k < m := (Nat.floor_lt hz0).2 hzm
  have hkl : (k : ℝ) ≤ z := Nat.floor_le hz0
  have hkr : z < (k : ℝ) + 1 := Nat.lt_floor_add_one z
  have hkl' : (k : ℝ) * ((b : ℝ) - (a : ℝ)) ≤ (x - (a : ℝ)) * (m : ℝ) :=
    (le_div_iff₀ hw).1 hkl
  have hkr' : (x - (a : ℝ)) * (m : ℝ) <
      ((k : ℝ) + 1) * ((b : ℝ) - (a : ℝ)) := (div_lt_iff₀ hw).1 hkr
  have hl : (mesh m k : ℝ) ≤ x := by
    dsimp [mesh]
    push_cast
    have hdiv : ((b : ℝ) - (a : ℝ)) * (k : ℝ) / (m : ℝ) ≤ x - (a : ℝ) :=
      (div_le_iff₀ hmR).2 (by nlinarith only [hkl'])
    linarith only [hdiv]
  have hr : x < (mesh m (k + 1) : ℝ) := by
    dsimp [mesh]
    push_cast
    have hdiv : x - (a : ℝ) <
        ((b : ℝ) - (a : ℝ)) * ((k : ℝ) + 1) / (m : ℝ) :=
      (lt_div_iff₀ hmR).2 (by nlinarith only [hkr'])
    linarith only [hdiv]
  refine ⟨k, hk, hl, hr, hy.1, ?_⟩
  have hcap : (cap m k : ℝ) = (1 - (mesh m k : ℝ)) / 2 := by
    simp [cap]
  rw [hcap]
  linarith only [hy.2, hl]

/-- The cover applies to the literal two-dimensional prime-log domain. -/
theorem literal_domain_uniform_cover (m : ℕ) (hm : 0 < m) {x y : ℝ}
    (hxy : ![x, y] ∈ logPrimeBox (fun _ : Fin 2 => (19 / 125 : ℝ))
      (fun _ => (1 / 2 : ℝ)) ∩ currentChenUpsilon9HarmonicRegion) :
    ∃ k : ℕ, k < m ∧ (mesh m k : ℝ) ≤ x ∧
      x < (mesh m (k + 1) : ℝ) ∧ (d : ℝ) ≤ y ∧ y < (cap m k : ℝ) := by
  obtain ⟨hx, hy⟩ := (currentChenUpsilon9HarmonicDomain_vec_iff x y).1 hxy
  exact moving_domain_uniform_cover m hm hx hy

/-- The generated boxes have a uniform strictly positive logarithmic gap. -/
theorem whole_box_positive_gap (m : ℕ) (hm : 0 < m) (k : ℕ) (hk : k < m)
    {x y : ℝ} (hxl : (mesh m k : ℝ) ≤ x)
    (hxr : x ≤ (mesh m (k + 1) : ℝ)) (hyl : (d : ℝ) ≤ y)
    (hyr : y ≤ (cap m k : ℝ)) :
    0 < x ∧ 0 < y ∧ (17 / 50 : ℝ) ≤ 1 - x - y := by
  obtain ⟨hl, _hu⟩ := mesh_bounds m hm k hk.le
  have hr := (mesh_bounds m hm (k + 1) (by omega)).2
  have hlR : (a : ℝ) ≤ (mesh m k : ℝ) := by exact_mod_cast hl
  have hrR : (mesh m (k + 1) : ℝ) ≤ (b : ℝ) := by exact_mod_cast hr
  have hcap : (cap m k : ℝ) = (1 - (mesh m k : ℝ)) / 2 := by simp [cap]
  rw [hcap] at hyr
  norm_num [a, b, d] at hlR hrR hyl
  constructor
  · linarith
  constructor <;> linarith

def boxDensityUpper (m k : ℕ) : ℚ :=
  1 / (mesh m k * d * (1 - mesh m (k + 1) - cap m k))

/-- A rational whole-box majorant for the literal two-prime density,
including all points beyond the slanted wall added by the outer cover. -/
theorem whole_box_density_le (m : ℕ) (hm : 0 < m) (k : ℕ) (hk : k < m)
    {x y : ℝ} (hxl : (mesh m k : ℝ) ≤ x)
    (hxr : x ≤ (mesh m (k + 1) : ℝ)) (hyl : (d : ℝ) ≤ y)
    (hyr : y ≤ (cap m k : ℝ)) :
    1 / (x * y * (1 - x - y)) ≤ (boxDensityUpper m k : ℝ) := by
  have hg : 0 < mesh m k ∧ 0 < d ∧ d ≤ cap m k ∧
      mesh m (k + 1) + cap m k < 1 := of_decide_eq_true (boxGuard_true m hm k hk)
  have hl0 : (0 : ℝ) < (mesh m k : ℝ) := by exact_mod_cast hg.1
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hg.2.1
  have hgap0 : (0 : ℝ) < 1 - (mesh m (k + 1) : ℝ) - (cap m k : ℝ) := by
    have hR : (mesh m (k + 1) : ℝ) + (cap m k : ℝ) < 1 := by exact_mod_cast hg.2.2.2
    linarith
  have hgap : 1 - (mesh m (k + 1) : ℝ) - (cap m k : ℝ) ≤ 1 - x - y := by
    linarith only [hxr, hyr]
  have hxy : (mesh m k : ℝ) * (d : ℝ) ≤ x * y :=
    mul_le_mul hxl hyl hd0.le (hl0.le.trans hxl)
  have hden := mul_le_mul hxy hgap hgap0.le
    (mul_nonneg (hl0.le.trans hxl) (hd0.le.trans hyl))
  have hpos := mul_pos (mul_pos hl0 hd0) hgap0
  have h := div_le_div_of_nonneg_left zero_le_one hpos hden
  simpa [boxDensityUpper] using h

def logDensity (x : ℝ) : ℝ :=
  Real.log ((1 - x - (d : ℝ)) / (d : ℝ)) / (x * (1 - x))

def logQuery (l : ℚ) : ℚ := 1 + (1 - l - d) / d
def cellUpper (n : ℕ) (l : ℚ) : ℚ := logUpper n (logQuery l) / (l * (1 - l))
def rationalUpper (n m : ℕ) : ℚ :=
  ∑ k ∈ Finset.range m, (mesh m (k + 1) - mesh m k) * cellUpper n (mesh m k)

theorem continuousOn_logDensity : ContinuousOn logDensity (Icc (a : ℝ) (b : ℝ)) := by
  have harg : ∀ x ∈ Icc (a : ℝ) (b : ℝ),
      0 < (1 - x - (d : ℝ)) / (d : ℝ) := by
    intro x hx
    apply div_pos _ (by norm_num [d])
    norm_num [b, d] at hx ⊢
    linarith [hx.2]
  have hden : ∀ x ∈ Icc (a : ℝ) (b : ℝ), x * (1 - x) ≠ 0 := by
    intro x hx
    apply ne_of_gt
    apply mul_pos <;> norm_num [a, b] at hx ⊢ <;> linarith [hx.1, hx.2]
  exact ((((continuousOn_const.sub continuousOn_id).sub continuousOn_const).div_const
    (d : ℝ)).log (fun x hx => (harg x hx).ne')).div
      (continuousOn_id.mul (continuousOn_const.sub continuousOn_id)) hden

/-- Each rational cell bounds the full exact moving-slice integral density. -/
theorem logDensity_le_cellUpper (n : ℕ) (l : ℚ) {x : ℝ}
    (hl : a ≤ l) (hlx : (l : ℝ) ≤ x) (hx : x ≤ (b : ℝ)) :
    logDensity x ≤ (cellUpper n l : ℝ) := by
  have hlR : (a : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
  have hlb : l ≤ b := by exact_mod_cast (hlx.trans hx)
  have hq : 2 ≤ logQuery l := by
    dsimp [logQuery, d]
    norm_num [a, b] at hl hlb
    linarith
  have hlogUpper := (log_bounds n (logQuery l) hq).2
  have harg : (logQuery l : ℝ) - 1 = (1 - (l : ℝ) - (d : ℝ)) / (d : ℝ) := by
    dsimp [logQuery]
    push_cast
    <;> ring
  rw [harg] at hlogUpper
  have harg1 : 1 ≤ (1 - x - (d : ℝ)) / (d : ℝ) := by
    apply (le_div_iff₀ (by norm_num [d] : (0 : ℝ) < (d : ℝ))).2
    norm_num [b, d] at hx ⊢
    linarith
  have hnum0 : 0 ≤ Real.log ((1 - x - (d : ℝ)) / (d : ℝ)) := Real.log_nonneg harg1
  have hratio : (1 - x - (d : ℝ)) / (d : ℝ) ≤
      (1 - (l : ℝ) - (d : ℝ)) / (d : ℝ) :=
    div_le_div_of_nonneg_right (by linarith) (by norm_num [d])
  have hnum := (Real.log_le_log (by linarith :
    0 < (1 - x - (d : ℝ)) / (d : ℝ)) hratio).trans hlogUpper
  have hlpos : 0 < (l : ℝ) * (1 - (l : ℝ)) := by
    apply mul_pos <;> norm_num [a, b] at hlR hx ⊢ <;> linarith
  have hden : (l : ℝ) * (1 - (l : ℝ)) ≤ x * (1 - x) := by
    have hprod := mul_nonneg (sub_nonneg.mpr hlx)
      (show 0 ≤ 1 - x - (l : ℝ) by norm_num [b] at hx; linarith)
    nlinarith only [hprod]
  calc
    logDensity x ≤ Real.log ((1 - x - (d : ℝ)) / (d : ℝ)) /
        ((l : ℝ) * (1 - (l : ℝ))) :=
      div_le_div_of_nonneg_left hnum0 hlpos hden
    _ ≤ (logUpper n (logQuery l) : ℝ) / ((l : ℝ) * (1 - (l : ℝ))) :=
      div_le_div_of_nonneg_right hnum hlpos.le
    _ = (cellUpper n l : ℝ) := by simp [cellUpper]

/-- A finite, explicitly computable rational sum covers the WHOLE actual
ninth integral.  No point or moving-boundary slice has been omitted. -/
theorem actual_integral_le_rationalUpper (n m : ℕ) (hm : 0 < m) :
    currentChenUpsilon9HarmonicIntegral ≤ (rationalUpper n m : ℝ) := by
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
  change (∑ k ∈ Finset.range m, ∫ x in (mesh m k : ℝ)..(mesh m (k + 1) : ℝ),
    logDensity x) ≤ (rationalUpper n m : ℝ)
  have hbound : ∀ k ∈ Finset.range m,
      (∫ x in (mesh m k : ℝ)..(mesh m (k + 1) : ℝ), logDensity x) ≤
        (((mesh m (k + 1) - mesh m k) * cellUpper n (mesh m k) : ℚ) : ℝ) := by
    intro k hk
    have hk' := Finset.mem_range.mp hk
    have hl := (mesh_bounds m hm k hk'.le).1
    have hr := (mesh_bounds m hm (k + 1) (by omega)).2
    have horder : (mesh m k : ℝ) ≤ (mesh m (k + 1) : ℝ) := by
      exact_mod_cast (mesh_monotone m hm (Nat.le_succ k))
    have h := intervalIntegral.integral_mono_on horder (hcell k hk')
      intervalIntegrable_const (fun x hx => logDensity_le_cellUpper n (mesh m k) hl
        hx.1 (hx.2.trans (by exact_mod_cast hr)))
    rw [intervalIntegral.integral_const] at h
    simpa only [smul_eq_mul, Rat.cast_mul, Rat.cast_sub] using h
  have hs := Finset.sum_le_sum hbound
  simpa [rationalUpper] using hs

/-- A kernel-checkable rational comparison; it contains no actual integral. -/
def directedCheck (n m : ℕ) (budget : ℚ) : Bool := decide
  ((8452171 / 1250000 : ℚ) * rationalUpper n m ≤ budget)

/-- Soundness for the literal currentK analytic cost.  Arithmetic saving
from the ordinary coefficient eight is deliberately not asserted. -/
theorem directedCheck_sound (n m : ℕ) (budget : ℚ) (hm : 0 < m)
    (hcheck : directedCheck n m budget = true) :
    currentK * currentChenUpsilon9HarmonicIntegral ≤ (budget : ℝ) := by
  have hrat : (8452171 / 1250000 : ℚ) * rationalUpper n m ≤ budget :=
    of_decide_eq_true hcheck
  have hreal : currentK * (rationalUpper n m : ℝ) ≤ (budget : ℝ) := by
    have h : (((8452171 / 1250000 : ℚ) * rationalUpper n m : ℚ) : ℝ) ≤
        (budget : ℝ) := by exact_mod_cast hrat
    simpa [currentK] using h
  exact (mul_le_mul_of_nonneg_left (actual_integral_le_rationalUpper n m hm)
    (by norm_num [currentK])).trans hreal

/-- Correct direction for U9's negative one-quarter contribution. -/
theorem directed_negative_cost_lower (n m : ℕ) (budget : ℚ) (hm : 0 < m)
    (hcheck : directedCheck n m budget = true) :
    -(budget : ℝ) / 4 ≤ -(currentK * currentChenUpsilon9HarmonicIntegral) / 4 := by
  exact div_le_div_of_nonneg_right (neg_le_neg (directedCheck_sound n m budget hm hcheck))
    (by norm_num)

end

end ImbalancedChen.P2U9DirectedRationalCover
