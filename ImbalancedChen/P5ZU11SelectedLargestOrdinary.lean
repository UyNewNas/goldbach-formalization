import ImbalancedChen.P5ZU11ActualH248Ordinary
import Mathlib.Tactic.FunProp

/-!
One literal original ordinary branch: selected singleton I={x}.

Source: chen-imbalanced-semiprimes/proof-library/source/
four-prefix-safe-minimum.tex:12 (four full squares), 29--43 (v, G_I and
strict selected-subproduct gate), 55--58 (interior level), 101--105
(actual reduced cutoff), 139--145 (selected remaining squares).
This file implements exactly that branch, not an asserted exhaustive bank.
The n48 independent review at lines 38--39 uses max(2,R/w), so R/w<2
is retained. Method 0 is switched in the numerical records; no unverified
method-ID-to-subset dictionary is asserted here.

The preceding 10000/417 bound remains a stronger L>=2w subgroup theorem.
For this true full gate the result is L>w and the bound is 20000/417.
The endpoint ordinary kernel still needs the actual averaged policy
license and the interior-level limit. Neither distribution nor that
limit is inferred merely from the geometric inequalities below.
Status: source_written / uncompiled; older source files unchanged.
-/

namespace ImbalancedChen.P5Z.U11SelectedLargest

open Set MeasureTheory
open U11Integral U11Canonical U11H248 Part5UpperTables
open scoped BigOperators

noncomputable section

def prefixSum (v : LogFour) : ℝ := v 0 + v 1 + v 2 + v 3

def cap (v : LogFour) : ℝ := min ((1 + v 0) / 2) (57 / 64 - (3 / 2 : ℝ) * v 0)

def fullSquares (v : LogFour) (nu : ℝ) : Prop :=
  2 * v 0 < nu ∧ v 0 + 2 * v 1 < nu ∧
    v 0 + v 1 + 2 * v 2 < nu ∧ v 0 + v 1 + v 2 + 2 * v 3 < nu

/-- These are exactly G_I's three unselected squares for I={x}. -/
def selectedSquares (v : LogFour) (nu : ℝ) : Prop :=
  v 0 + 2 * v 1 < nu ∧ v 0 + v 1 + 2 * v 2 < nu ∧
    v 0 + v 1 + v 2 + 2 * v 3 < nu

def bank : Finset ℕ := {0}

def eligible (j : ℕ) (v : LogFour) : Prop :=
  j = 0 ∧ (1 / 2 : ℝ) < cap v ∧ fullSquares v (cap v) ∧ selectedSquares v (cap v)

/-- Endpoint residual for this single selected branch. Analytic passage
from strict interior levels to this endpoint remains a separate task. -/
def residual (_j : ℕ) (v : LogFour) : ℝ := cap v - prefixSum v

def gateLevel (v : LogFour) : ℝ :=
  max (1 / 2) (max (2 * v 0) (max (v 0 + 2 * v 1)
    (max (v 0 + v 1 + 2 * v 2) (v 0 + v 1 + v 2 + 2 * v 3))))

def interiorLevel (v : LogFour) : ℝ := (gateLevel v + cap v) / 2

theorem interiorLevel_admissible (j : ℕ) (v : LogFour) (he : eligible j v) :
    (1 / 2 : ℝ) < interiorLevel v ∧ fullSquares v (interiorLevel v) ∧
      selectedSquares v (interiorLevel v) ∧ interiorLevel v < cap v := by
  have hgc : gateLevel v < cap v := by
    simpa only [gateLevel, max_lt_iff, fullSquares] using
      (show (1 / 2 : ℝ) < cap v ∧ fullSquares v (cap v) from ⟨he.2.1, he.2.2.1⟩)
  have hgn : gateLevel v < interiorLevel v := by dsimp [interiorLevel]; linarith
  have hnc : interiorLevel v < cap v := by dsimp [interiorLevel]; linarith
  have hh : (1 / 2 : ℝ) < interiorLevel v ∧ fullSquares v (interiorLevel v) := by
    simpa only [gateLevel, max_lt_iff, fullSquares] using hgn
  exact ⟨hh.1, hh.2, hh.2.2, hnc⟩

theorem continuous_prefixSum : Continuous prefixSum := by unfold prefixSum; fun_prop

theorem continuous_cap : Continuous cap := by unfold cap; fun_prop

theorem continuous_residual (j : ℕ) : Continuous (residual j) :=
  continuous_cap.sub continuous_prefixSum

theorem measurableSet_eligible (j : ℕ) : MeasurableSet {v | eligible j v} := by
  have hc := continuous_cap.measurable
  have h1 : Measurable (fun v : LogFour => 2 * v 0) := by fun_prop
  have h2 : Measurable (fun v : LogFour => v 0 + 2 * v 1) := by fun_prop
  have h3 : Measurable (fun v : LogFour => v 0 + v 1 + 2 * v 2) := by fun_prop
  have h4 : Measurable (fun v : LogFour => v 0 + v 1 + v 2 + 2 * v 3) := by fun_prop
  have hfull : MeasurableSet {v : LogFour | fullSquares v (cap v)} :=
    (measurableSet_lt h1 hc).inter ((measurableSet_lt h2 hc).inter
      ((measurableSet_lt h3 hc).inter (measurableSet_lt h4 hc)))
  have hselected : MeasurableSet {v : LogFour | selectedSquares v (cap v)} :=
    (measurableSet_lt h2 hc).inter ((measurableSet_lt h3 hc).inter (measurableSet_lt h4 hc))
  by_cases hj : j = 0
  · simpa only [eligible, hj, true_and] using
      (measurableSet_lt measurable_const hc).inter (hfull.inter hselected)
  · have hh : {v | eligible j v} = (∅ : Set LogFour) := by ext v; simp [eligible, hj]
    rw [hh]
    exact measurableSet_empty

theorem cap_le_Lambda (v : LogFour) : cap v ≤ (153 / 256 : ℝ) := by
  by_cases hx : v 0 ≤ (25 / 128 : ℝ)
  · exact (min_le_left _ _).trans (by linarith)
  · exact (min_le_right _ _).trans (by linarith)

theorem eligible_residual_gt_smallest (mask : Set (ℝ × ℝ)) (j : ℕ)
    (v : LogFour) (hv : v ∈ originalDomain mask) (he : eligible j v) :
    v 3 < residual j v := by
  have hlast := he.2.2.1.2.2.2
  dsimp [residual, prefixSum]
  linarith

theorem eligible_alpha_ge_two (mask : Set (ℝ × ℝ)) (j : ℕ)
    (v : LogFour) (hv : v ∈ originalDomain mask) (he : eligible j v) :
    2 ≤ (1 - prefixSum v) / residual j v := by
  have hw := (originalDomain_denominators_pos mask v hv).1
  have hr := eligible_residual_gt_smallest mask j v hv he
  have hpos : 0 < residual j v := hw.trans hr
  apply (le_div_iff₀ hpos).2
  have hcap : cap v ≤ (1 + v 0) / 2 := min_le_left _ _
  obtain ⟨ha, h32, h21, h1, h0lo, h0hi, hm⟩ := hv
  dsimp [residual, prefixSum]
  linarith

theorem eligible_physical_ceiling (mask : Set (ℝ × ℝ)) (j : ℕ)
    (v : LogFour) (hv : v ∈ originalDomain mask) (he : eligible j v)
    (r : ℝ) (hr : r ≤ residual j v) :
    prefixSum v + r ≤ cap v ∧ cap v < (3 / 5 : ℝ) := by
  constructor
  · dsimp [residual] at hr
    linarith
  · exact (cap_le_Lambda v).trans_lt (by norm_num)

theorem fullSquares_mono {v u : LogFour} {nu : ℝ} (hvu : v ≤ u)
    (h : fullSquares u nu) : fullSquares v nu := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have h0 := hvu 0
  have h1' := hvu 1
  have h2' := hvu 2
  have h3' := hvu 3
  unfold fullSquares
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem selectedSquares_mono {v u : LogFour} {nu : ℝ} (hvu : v ≤ u)
    (h : selectedSquares u nu) : selectedSquares v nu := by
  obtain ⟨h1, h2, h3⟩ := h
  have h0 := hvu 0
  have h1' := hvu 1
  have h2' := hvu 2
  have h3' := hvu 3
  unfold selectedSquares
  exact ⟨by linarith, by linarith, by linarith⟩

/-- Fixed-parent interval tests: the increasing first cap is tested at
the lower x wall, and the decreasing second cap at the upper x wall. -/
def parentGate (lower upper : LogFour) (nu : ℝ) : Prop :=
  (1 / 2 : ℝ) < nu ∧ fullSquares upper nu ∧ selectedSquares upper nu ∧
    nu < (1 + lower 0) / 2 ∧ nu < 57 / 64 - (3 / 2 : ℝ) * upper 0

theorem parentGate_point {lower upper v : LogFour} {nu : ℝ}
    (hg : parentGate lower upper nu) (hl : lower ≤ v) (hu : v ≤ upper) :
    (1 / 2 : ℝ) < nu ∧ fullSquares v nu ∧ selectedSquares v nu ∧ nu < cap v := by
  obtain ⟨hhalf, hfull, hselected, hcap1, hcap2⟩ := hg
  refine ⟨hhalf, fullSquares_mono hu hfull, selectedSquares_mono hu hselected, ?_⟩
  apply lt_min
  · linarith [hl 0]
  · linarith [hu 0]

theorem parentGate_inherited {lower upper childLower childUpper : LogFour} {nu : ℝ}
    (hg : parentGate lower upper nu) (hl : lower ≤ childLower) (hu : childUpper ≤ upper) :
    parentGate childLower childUpper nu := by
  obtain ⟨hhalf, hfull, hselected, hcap1, hcap2⟩ := hg
  refine ⟨hhalf, fullSquares_mono hu hfull, selectedSquares_mono hu hselected, ?_, ?_⟩
  · linarith [hl 0]
  · linarith [hu 0]

/-- Exactly the reduced cutoff from the source, including its two
independent safety margins. This handles L/w<2 without altering gates. -/
def reducedCutoff (lower upper : LogFour) (nu delta xi rho : ℝ) : ℝ :=
  min (lower 3 - xi) ((nu - prefixSum upper - 20 * delta) / (2 + rho))

theorem reducedCutoff_bounds (lower upper : LogFour) (nu delta xi rho : ℝ)
    (hsmall : 0 < lower 3 - xi) (hmargin : 20 * delta < nu - prefixSum upper)
    (hrho : 0 < rho) :
    0 < reducedCutoff lower upper nu delta xi rho ∧
      reducedCutoff lower upper nu delta xi rho ≤ lower 3 - xi ∧
      2 + rho ≤ (nu - prefixSum upper - 20 * delta) /
        reducedCutoff lower upper nu delta xi rho := by
  have hd : 0 < 2 + rho := by linarith
  have hn : 0 < nu - prefixSum upper - 20 * delta := by linarith
  have hp : 0 < reducedCutoff lower upper nu delta xi rho :=
    lt_min hsmall (div_pos hn hd)
  refine ⟨hp, min_le_left _ _, ?_⟩
  apply (le_div_iff₀ hp).2
  have hh := mul_le_mul_of_nonneg_left
    (min_le_right (lower 3 - xi) ((nu - prefixSum upper - 20 * delta) / (2 + rho))) hd.le
  have heq : (2 + rho) * ((nu - prefixSum upper - 20 * delta) / (2 + rho)) =
      nu - prefixSum upper - 20 * delta := by field_simp [hd.ne']
  exact hh.trans_eq heq

/-- Correct full-gate H248 bound. The clamped table argument covers the
positive-measure state residual/w<2, so the old stronger wall is unused. -/
theorem ordinary_actual_bounds (mask : Set (ℝ × ℝ)) (j : ℕ)
    (v : LogFour) (hv : v ∈ originalDomain mask) (he : eligible j v) :
    0 ≤ ordinaryKernel H248 residual j v ∧
      ordinaryKernel H248 residual j v ≤ (20000 / 417 : ℝ) := by
  have hw := (originalDomain_denominators_pos mask v hv).1
  have hr := eligible_residual_gt_smallest mask j v hv he
  have hp : 0 < residual j v := hw.trans hr
  have ha : (417 / 5000 : ℝ) ≤ v 3 := hv.1
  have hH := H248_max_two_bounds (residual j v / v 3)
  unfold ordinaryKernel
  constructor
  · exact div_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hH.2)) hp.le
  · apply (div_le_iff₀ hp).2
    nlinarith [hH.1]

/-- A fully concrete one-ordinary-policy bank. No free eligible predicate,
H248 range, residual lower wall, or switched-integrability premise remains. -/
theorem integrableOn_actual_selected_largest_envelope (mask : Set (ℝ × ℝ))
    (hm : MeasurableSet mask) :
    IntegrableOn (envelope bank
      (guarded eligible (switchedKernel currentK LiLiuPrereqBuchstab.buchstab)
        (ordinaryKernel H248 residual))) (originalDomain mask) volume := by
  apply integrableOn_original_canonical_envelope mask hm bank eligible currentK
    (by norm_num [currentK]) H248 residual
    (fun j _ => measurableSet_eligible j) measurable_H248
    (fun j _ => (continuous_residual j).measurable)
  intro j hj v hv helig
  exact (ordinary_actual_bounds mask j v hv helig).1

theorem integral_actual_selected_largest_envelope_eq_sum (mask : Set (ℝ × ℝ))
    (hm : MeasurableSet mask) :
    (∫ v in originalDomain mask,
      envelope bank (guarded eligible (switchedKernel currentK LiLiuPrereqBuchstab.buchstab)
        (ordinaryKernel H248 residual)) v) =
      ∑ c ∈ tags bank,
        ∫ v in winner (originalDomain mask) bank
            (guarded eligible (switchedKernel currentK LiLiuPrereqBuchstab.buchstab)
              (ordinaryKernel H248 residual)) c,
          (if c = 0 then switchedKernel currentK LiLiuPrereqBuchstab.buchstab v
            else ordinaryKernel H248 residual c.pred v) := by
  apply integral_original_current_envelope_eq_sum mask hm bank eligible H248 residual
    (fun j _ => measurableSet_eligible j) measurable_H248
    (fun j _ => (continuous_residual j).measurable)
  intro j hj v hv helig
  exact (ordinary_actual_bounds mask j v hv helig).1

end

end ImbalancedChen.P5Z.U11SelectedLargest
