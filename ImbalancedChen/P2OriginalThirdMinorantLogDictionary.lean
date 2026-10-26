import ImbalancedChen.ActualExtendedThirdOrderedIntegral
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic

/-!
SOURCE ONLY / NOT ELABORATED / no producer or numerical replay.

Catalog saving 19, thirteen_third_minorant_final_log.  Frozen source read:
eighth-third-minorant-analytic-review-20261009.tex and the actual physical
`density('nine_ascending', t)` in
eighth-unequal-moment-independent-engine-20261009.py.  Indices here are zero
based.  The physical data are B3=A(t2+t3), R=A(t1+t4),
M=A(t2+t4+t8)-10^-6, selected mask 138, and the ten factors
(R-S8,M-S8,t1,...,t8).

Existing VariableEnvelope/ActualThirdOriginalSixTentCandidates prove generic
pair/tent facts; they do not contain this eight-dimensional selected-family
factor dictionary, current-parent residual comparison, or log normalization.
This file reuses the actual gated third envelope and actual lower factor.
It never identifies B3 with the true third cap or R with the actual parent.

The first theorem chain is unconditional analytic soundness from explicit
physical affine rows: the pair gate has margin 3/256, B3 is a minorant of the
actual capped third envelope, and the resulting kernel majorant is directed
against `actualExtendedThirdOrderedKernel`.  The second chain proves the exact
physical moment factors, positivity and logarithmic product dictionary.

OPEN: the thirteen complete chosen-plane cell covers, the common causal frozen
ancestor construction, and the 28,918 simplex moment/floor certificates are
not proved here.  Structural parent history/cap inequalities are genuine
inputs to the residual comparison; no gain or target integral bound is input.
-/

namespace ImbalancedChen.P2OriginalThirdMinorantLogDictionarySourceOnly

noncomputable section

open Set MeasureTheory VariableEnvelope
open scoped ENNReal

abbrev Point := Fin 8 → ℝ

def eta : ℝ := 1 / 1000000

def thirdMinorant (t : Point) : ℝ := A (t 1 + t 2)

def comparisonCap (t : Point) : ℝ := A (t 0 + t 3)

def selectedSum (t : Point) : ℝ := t 1 + t 3 + t 7

def newCap (t : Point) : ℝ := A (selectedSum t) - eta

def total (t : Point) : ℝ := ∑ i, t i

def history3 (t : Point) : ℝ := t 0 + t 1 + 3 * t 2

def history5 (t : Point) : ℝ := t 0 + t 1 + t 2 + t 3 + 3 * t 4

def history7 (t : Point) : ℝ := t 0 + t 1 + t 2 + t 3 + t 4 + t 5 + 3 * t 6

/-- Explicit closed physical rows shared by the selected A23/low-half cells.
The 63 old-plane assignments and exact simplex covers remain separate data. -/
structure PhysicalRows (t : Point) : Prop where
  ordered : Antitone t
  eighthCutoff : (53 / 13824 : ℝ) ≤ t 7
  thirdCutoff : (1 / 100 : ℝ) ≤ t 2
  largestBelowMu : t 0 ≤ mu
  ascendingThird : t 1 + t 2 ≤ mu
  ascendingOldWinner : t 0 + t 3 ≤ mu
  ascendingNew : selectedSum t ≤ mu
  firstHistory : 3 * t 0 ≤ thirdMinorant t
  thirdHistory : history3 t ≤ thirdMinorant t
  fifthHistory : history5 t ≤ thirdMinorant t
  seventhHistory : history7 t ≤ thirdMinorant t
  comparisonAboveThird : thirdMinorant t ≤ comparisonCap t
  improvement : comparisonCap t ≤ newCap t
  newResidualUpper : newCap t - total t ≤ 3 * t 7

theorem coordinate_pos {t : Point} (ht : PhysicalRows t) (i : Fin 8) : 0 < t i := by
  have hi : i ≤ (7 : Fin 8) := by omega
  have h := ht.ordered hi
  linarith [ht.eighthCutoff]

theorem firstThree_ordered {t : Point} (ht : PhysicalRows t) :
    Ordered (t 0) (t 1) (t 2) := by
  exact ⟨(coordinate_pos ht 2).le, ht.ordered (by norm_num),
    ht.ordered (by norm_num), ht.largestBelowMu⟩

theorem thirdMinorant_active {t : Point} (ht : PhysicalRows t) :
    thirdMinorant t = v (t 1 + t 2) := by
  exact (v_eq_A ht.ascendingThird).symm

theorem comparisonCap_active {t : Point} (ht : PhysicalRows t) :
    comparisonCap t = v (t 0 + t 3) := by
  exact (v_eq_A ht.ascendingOldWinner).symm

theorem newCap_active {t : Point} (ht : PhysicalRows t) :
    newCap t = v (selectedSum t) - eta := by
  rw [newCap, v_eq_A ht.ascendingNew]

/-- Exact selected-subproduct parameter map from the actual producer. -/
theorem selected_mask_dictionary : (2 ^ 1 + 2 ^ 3 + 2 ^ 7 : ℕ) = 138 := by norm_num

theorem ascending_pair_gate_margin {t : Point} (ht : PhysicalRows t) :
    (3 / 256 : ℝ) ≤ thirdMinorant t - (2 * t 0 + t 1 + t 2) := by
  have hx := ht.largestBelowMu
  have hd := ht.ascendingThird
  dsimp [thirdMinorant, A, mu] at *
  linarith

theorem first_three_full_square_margins {t : Point} (ht : PhysicalRows t) :
    2 * t 0 + 3 / 256 ≤ thirdMinorant t ∧
      t 0 + 2 * t 1 + 3 / 256 ≤ thirdMinorant t ∧
      t 0 + t 1 + 2 * t 2 + 3 / 256 ≤ thirdMinorant t := by
  have hg := ascending_pair_gate_margin ht
  have hyx : t 1 ≤ t 0 := ht.ordered (by norm_num)
  have hzx : t 2 ≤ t 0 := ht.ordered (by norm_num)
  have hy0 := coordinate_pos ht 1
  have hz0 := coordinate_pos ht 2
  constructor
  · linarith
  · constructor <;> linarith

theorem pair_gate_retained {t : Point} (ht : PhysicalRows t) :
    psi (v (t 1 + t 2)) (2 * t 0 + t 1 + t 2) = thirdMinorant t := by
  have hg : 2 * t 0 + t 1 + t 2 ≤ v (t 1 + t 2) := by
    rw [← thirdMinorant_active ht]
    linarith [ascending_pair_gate_margin ht]
  rw [psi, if_pos hg, ← thirdMinorant_active ht]

theorem root_margin {t : Point} (ht : PhysicalRows t) :
    (11 / 32000 : ℝ) ≤ thirdPrefixTheta - thirdMinorant t := by
  have hd := ht.ascendingThird
  dsimp [thirdPrefixTheta, thirdMinorant, A, mu] at *
  linarith

/-- Real minorant of the actual original capped, gated third envelope.
No equality with the licensed/raw third level is asserted. -/
theorem thirdMinorant_le_actual_cap {t : Point} (ht : PhysicalRows t) :
    thirdMinorant t ≤ actualExtendedThirdIdealCap (t 0) (t 1) (t 2) := by
  rw [actualExtendedThirdIdealCap_eq]
  apply le_min
  · linarith [root_margin ht]
  · rw [if_pos ht.largestBelowMu, original_eq_six (firstThree_ordered ht),
      thirdMinorant_active ht]
    unfold six
    exact le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
      (le_max_of_le_right (le_max_right _ _))))

theorem physical_histories_le_actual_cap {t : Point} (ht : PhysicalRows t) :
    3 * t 0 ≤ actualExtendedThirdIdealCap (t 0) (t 1) (t 2) ∧
      history3 t ≤ actualExtendedThirdIdealCap (t 0) (t 1) (t 2) ∧
      history5 t ≤ actualExtendedThirdIdealCap (t 0) (t 1) (t 2) ∧
      history7 t ≤ actualExtendedThirdIdealCap (t 0) (t 1) (t 2) := by
  have h := thirdMinorant_le_actual_cap ht
  exact ⟨ht.firstHistory.trans h, ht.thirdHistory.trans h,
    ht.fifthHistory.trans h, ht.seventhHistory.trans h⟩

def minorantArgument (t : Point) : ℝ := (thirdMinorant t - t 0 - t 1 - t 2) / t 2

def minorantThirdKernel (t : Point) : ℝ :=
  4 * (actualExtendedThirdLowerFactor ((thirdPrefixTheta - t 0 - t 1 - t 2) / t 2) -
    actualExtendedThirdLowerFactor (minorantArgument t)) / (t 0 * t 1 * t 2 ^ 2)

theorem minorantArgument_le_actual {t : Point} (ht : PhysicalRows t) :
    minorantArgument t ≤
      (actualExtendedThirdBufferedCap 0 (t 0) (t 1) (t 2) - t 0 - t 1 - t 2) / t 2 := by
  apply (div_le_div_iff_of_pos_right (coordinate_pos ht 2)).2
  have h := thirdMinorant_le_actual_cap ht
  change thirdMinorant t ≤ actualExtendedThirdBufferedCap 0 (t 0) (t 1) (t 2) at h
  linarith

/-- Directed semantic bridge to the ACTUAL original third kernel. -/
theorem actual_third_kernel_le_minorant {t : Point} (ht : PhysicalRows t) :
    actualExtendedThirdOrderedKernel 0 (t 0) (t 1) (t 2) ≤ minorantThirdKernel t := by
  have hf := monotone_actualExtendedThirdLowerFactor (minorantArgument_le_actual ht)
  have hd : 0 < t 0 * t 1 * t 2 ^ 2 :=
    mul_pos (mul_pos (coordinate_pos ht 0) (coordinate_pos ht 1))
      (pow_pos (coordinate_pos ht 2) _)
  rw [actualExtendedThirdOrderedKernel]
  simp only [mul_zero, sub_zero]
  exact (div_le_div_iff_of_pos_right hd).2 (by dsimp [minorantThirdKernel]; nlinarith)

/-- Integrate the actual kernel comparison on any genuine selected cell or
union whose physical rows and integrability have been established. -/
theorem actual_third_integral_le_minorant {D : Set Point}
    (hD : MeasurableSet D) (hRows : ∀ t ∈ D, PhysicalRows t)
    (hActual : IntegrableOn
      (fun t => actualExtendedThirdOrderedKernel 0 (t 0) (t 1) (t 2)) D)
    (hMinorant : IntegrableOn minorantThirdKernel D) :
    (∫ t in D, actualExtendedThirdOrderedKernel 0 (t 0) (t 1) (t 2)) ≤
      ∫ t in D, minorantThirdKernel t := by
  exact setIntegral_mono_on hActual hMinorant hD
    (fun t ht => actual_third_kernel_le_minorant (hRows t ht))

theorem history7_residual (t : Point) : history7 t - total t = 2 * t 6 - t 7 := by
  simp [history7, total, Fin.sum_univ_succ] <;> ring

theorem comparison_residual_lower {t : Point} (ht : PhysicalRows t) :
    t 7 ≤ comparisonCap t - total t := by
  have ho : t 7 ≤ t 6 := ht.ordered (by norm_num)
  have hh := ht.seventhHistory.trans ht.comparisonAboveThird
  linarith [history7_residual t]

theorem physical_residual_range {t : Point} (ht : PhysicalRows t) :
    t 7 ≤ comparisonCap t - total t ∧
      comparisonCap t - total t ≤ newCap t - total t ∧
      newCap t - total t ≤ 3 * t 7 := by
  exact ⟨comparison_residual_lower ht, sub_le_sub_right ht.improvement _, ht.newResidualUpper⟩

def gap (t : Point) : ℝ := newCap t - comparisonCap t

def factors (t : Point) : Fin 10 → ℝ :=
  ![comparisonCap t - total t, newCap t - total t,
    t 0, t 1, t 2, t 3, t 4, t 5, t 6, t 7]

def conservativeDensity (t : Point) : ℝ :=
  4 * gap t / ((comparisonCap t - total t) * (newCap t - total t) * ∏ i, t i)

theorem factors_pos {t : Point} (ht : PhysicalRows t) (j : Fin 10) : 0 < factors t j := by
  have hr : 0 < comparisonCap t - total t :=
    (coordinate_pos ht 7).trans_le (comparison_residual_lower ht)
  have hm : 0 < newCap t - total t := hr.trans_le (sub_le_sub_right ht.improvement _)
  fin_cases j <;> simp only [factors, Matrix.cons_val_zero, Matrix.cons_val_succ]
  · exact hr
  · exact hm
  all_goals exact coordinate_pos ht _

theorem factors_product (t : Point) :
    (∏ j, factors t j) =
      (comparisonCap t - total t) * (newCap t - total t) * ∏ i, t i := by
  simp [factors, Fin.prod_univ_succ] <;> ring

theorem density_factor_dictionary (t : Point) :
    conservativeDensity t = 4 * gap t / ∏ j, factors t j := by
  rw [factors_product]
  rfl

/-- Literal formula returned by density('nine_ascending',t), in physical
coordinates and with its original factor 4 and original 10^-6 buffer. -/
theorem engine_nine_ascending_dictionary (t : Point) :
    conservativeDensity t =
      4 * (((1 + t 1 + t 3 + t 7) / 2 - 1 / 1000000) - (1 + t 0 + t 3) / 2) /
        (((1 + t 0 + t 3) / 2 - ∑ i, t i) *
          ((1 + t 1 + t 3 + t 7) / 2 - 1 / 1000000 - ∑ i, t i) * ∏ i, t i) := by
  have hR : comparisonCap t = (1 + t 0 + t 3) / 2 := by
    dsimp [comparisonCap, A]
    ring
  have hM : newCap t = (1 + t 1 + t 3 + t 7) / 2 - 1 / 1000000 := by
    dsimp [newCap, selectedSum, A, eta]
    ring
  simp only [conservativeDensity, gap, hR, hM, total]

theorem conservativeDensity_nonneg {t : Point} (ht : PhysicalRows t) :
    0 ≤ conservativeDensity t := by
  rw [density_factor_dictionary]
  exact div_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr ht.improvement))
    (Finset.prod_nonneg (fun j hj => (factors_pos ht j).le))

/-- Exactly the ten logarithmic factors used by the frozen moment producer. -/
theorem density_log_dictionary {t : Point} (ht : PhysicalRows t) (hg : 0 < gap t) :
    Real.log (conservativeDensity t) =
      Real.log 4 + Real.log (gap t) - ∑ j, Real.log (factors t j) := by
  have hp : 0 < ∏ j, factors t j := Finset.prod_pos (fun j hj => factors_pos ht j)
  rw [density_factor_dictionary,
    Real.log_div (mul_ne_zero (by norm_num) hg.ne') hp.ne',
    Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hg.ne',
    Real.log_prod (fun j hj => (factors_pos ht j).ne')]

/-- The actual parent is retained as a separate cap, constrained by its true
seventh history and comparison upper bound, never equated to R. -/
def parentDensity (parent : ℝ) (t : Point) : ℝ :=
  4 * (1 / (parent - total t) - 1 / (newCap t - total t)) / ∏ i, t i

theorem parent_residual_range {t : Point} (ht : PhysicalRows t) {parent : ℝ}
    (hHistory : history7 t < parent) (hCap : parent ≤ comparisonCap t) :
    1 < (parent - total t) / t 7 ∧
      (parent - total t) / t 7 ≤ (comparisonCap t - total t) / t 7 ∧
      (comparisonCap t - total t) / t 7 ≤ (newCap t - total t) / t 7 ∧
      (newCap t - total t) / t 7 ≤ 3 := by
  have hr := coordinate_pos ht 7
  have ho : t 7 ≤ t 6 := ht.ordered (by norm_num)
  constructor
  · apply (lt_div_iff₀ hr).2
    linarith [history7_residual t]
  · constructor
    · exact (div_le_div_iff_of_pos_right hr).2 (by linarith)
    · constructor
      · exact (div_le_div_iff_of_pos_right hr).2 (by linarith [ht.improvement])
      · exact (div_le_iff₀ hr).2 (by linarith [ht.newResidualUpper])

theorem conservativeDensity_le_parentDensity {t : Point} (ht : PhysicalRows t) {parent : ℝ}
    (hHistory : history7 t < parent) (hCap : parent ≤ comparisonCap t) :
    conservativeDensity t ≤ parentDensity parent t := by
  have hr := coordinate_pos ht 7
  have hOld : 0 < parent - total t := by
    have ho : t 7 ≤ t 6 := ht.ordered (by norm_num)
    linarith [history7_residual t]
  have hR : 0 < comparisonCap t - total t := hr.trans_le (comparison_residual_lower ht)
  have hM : 0 < newCap t - total t := hR.trans_le (sub_le_sub_right ht.improvement _)
  have hprod : 0 < ∏ i, t i := Finset.prod_pos (fun i hi => coordinate_pos ht i)
  have hinv : 1 / (comparisonCap t - total t) ≤ 1 / (parent - total t) :=
    div_le_div_of_nonneg_left (by norm_num) hOld (by linarith)
  have he : conservativeDensity t =
      4 * (1 / (comparisonCap t - total t) - 1 / (newCap t - total t)) / ∏ i, t i := by
    dsimp [conservativeDensity, gap]
    field_simp [hR.ne', hM.ne', hprod.ne'] <;> ring
  rw [he, parentDensity]
  exact (div_le_div_iff_of_pos_right hprod).2 (by linarith)

/-- Full selected-cell mass domination uses positivity and actual parent
histories, and does not accept a desired gain or integral bound as an input. -/
theorem conservative_mass_le_parent_mass {D : Set Point} (hD : MeasurableSet D)
    (hRows : ∀ t ∈ D, PhysicalRows t) (parent : Point → ℝ)
    (hHistory : ∀ t ∈ D, history7 t < parent t)
    (hCap : ∀ t ∈ D, parent t ≤ comparisonCap t) :
    (∫⁻ t in D, ENNReal.ofReal (conservativeDensity t)) ≤
      ∫⁻ t in D, ENNReal.ofReal (parentDensity (parent t) t) := by
  apply setLIntegral_mono' hD
  intro t ht
  exact ENNReal.ofReal_le_ofReal
    (conservativeDensity_le_parentDensity (hRows t ht) (hHistory t ht) (hCap t ht))

end

end ImbalancedChen.P2OriginalThirdMinorantLogDictionarySourceOnly
