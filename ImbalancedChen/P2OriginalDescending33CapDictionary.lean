import ImbalancedChen.ActualSelectedPrefixCapSelector
import ImbalancedChen.ActualFrozenFrontierDensity
import ImbalancedChen.ActualRosserInitialResidualSaving
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.FinCases

/-!
# Original saving 8: descending33 at the actual sixth frontier

SOURCE ONLY, uncompiled.  Read-only frozen source bindings, all under
`tmp/publication-20261010/verification-renewal-v2/_release/
chen-numerical-evidence-20261010-renewal-v2/goldbach-research/`:

* sixth-tent33-descending-independent-20261009.py:
  81674b91fe26096eedc41af1a2e51ad13f57dd29f84bba8aab9128f5c686bc08;
* sixth-tent33-descending-20261009.py:
  4ba171069f4a88b0b14d7801c37fa5be76b8dcb5e18e99e9a55de80dce815eb4;
* sixth-tent33-descending-20261009.tex:
  cd98de762a53f30ab89c7062354938b431d795ac58cb641edf41cd6c37e416cb.

The frozen family is `new_descending33`, saving 8.  Mask33 is zero-based
`{0,5}`, namely physical slots `{1,6}`.  The cap is chosen at the retained
even sixth prefix, and changes the subsequent odd exclusions.  It is not
a rank-4 or rank-5 cap.  Its literal exponent is
`M=57/64-3*(t0+t5)/2-eta`, with `eta=10^-6`; the old raw parent is
`R0=(1+t0)/2`.  `C`, `A33`, `D33`, and `M` remain distinct quantities.

`SourceGuard` spells out the source's local geometry and support gates.
The old-subset comparison uses weak inequalities to retain its defining
singleton identity.  Strict new selectors and strict support gates are
kept.  No adopted-cell coverage, classification count, Jensen floor,
numerical total, or integral lower bound is assumed or claimed here.

An actual inherited buffered exponent is represented concretely as
`R0-buffer`, with nonnegative buffer.  This retains the true inherited
parent instead of replacing it by R0 in the finite tree.  The exact
rank-six splice is a sum of actual residual densities on the unchanged
parent frontier.  Only inherited prefix admissibility is needed there;
new admissibility is proved by monotonicity of the literal level.  The
ordinary initial-branch normalization and conservative R0 comparison
are proved separately, using the source's residual range.
-/

namespace ImbalancedChen.P2OriginalDescending33CapDictionary

noncomputable section

open Set VariableEnvelope MathlibNt.SieveTheory
open scoped Classical BigOperators

def eta : ℝ := 1 / 1000000
def mu : ℝ := 25 / 128
def mask33 : Finset (Fin 6) := {0, 5}
def totalCoordinates (t : Fin 6 → ℝ) : ℝ := ∑ i, t i
def radialCoordinate (t : Fin 6 → ℝ) : ℝ := t 5
def currentParent (t : Fin 6 → ℝ) : ℝ := (1 + t 0) / 2
def ascending33 (t : Fin 6 → ℝ) : ℝ := (1 + t 0 + t 5) / 2
def descending33 (t : Fin 6 → ℝ) : ℝ := 57 / 64 - 3 / 2 * (t 0 + t 5)
def literalCap (t : Fin 6 → ℝ) : ℝ := descending33 t - eta
def clippedCap (t : Fin 6 → ℝ) : ℝ := totalCoordinates t + 3 * t 5 - eta
def oldThirdHistory (t : Fin 6 → ℝ) : ℝ := t 0 + t 1 + 3 * t 2
def oldFifthHistory (t : Fin 6 → ℝ) : ℝ := t 0 + t 1 + t 2 + t 3 + 3 * t 4
def oldW (t : Fin 6 → ℝ) : ℝ := 153 / 256 - 3 / 8 * t 2
def oldSubsetSum (t : Fin 6 → ℝ) (I : Finset (Fin 5)) : ℝ :=
  ∑ i ∈ I, t i.castSucc

theorem totalCoordinates_six (t : Fin 6 → ℝ) :
    totalCoordinates t = t 0 + t 1 + t 2 + t 3 + t 4 + t 5 := by
  norm_num [totalCoordinates, Fin.sum_univ_succ]
  ring

theorem mask33_sum (t : Fin 6 → ℝ) : (∑ i ∈ mask33, t i) = t 0 + t 5 := by
  norm_num [mask33]

/-- Literal source parameterization, with q3=R0-S5 and q4=R0-H5. -/
def physical (q : Fin 6 → ℝ) : Fin 6 → ℝ :=
  ![q 0, q 1, q 2, (1 - q 0) / 2 - q 1 - q 2 + (q 4 - 3 * q 3) / 2,
    (q 3 - q 4) / 2, q 5]

def parameters (t : Fin 6 → ℝ) : Fin 6 → ℝ :=
  ![t 0, t 1, t 2, currentParent t - (totalCoordinates t - t 5),
    currentParent t - oldFifthHistory t, t 5]

theorem parameters_physical (q : Fin 6 → ℝ) : parameters (physical q) = q := by
  funext i
  fin_cases i <;>
    norm_num [parameters, physical, currentParent, totalCoordinates_six, oldFifthHistory] <;> ring

theorem physical_parameters (t : Fin 6 → ℝ) : physical (parameters t) = t := by
  funext i
  fin_cases i <;>
    norm_num [parameters, physical, currentParent, totalCoordinates_six, oldFifthHistory] <;> ring

theorem physical_injective : Function.Injective physical := by
  intro q r h
  have heq := congrArg parameters h
  simpa only [parameters_physical] using heq

theorem physical_radial (q : Fin 6 → ℝ) : radialCoordinate (physical q) = q 5 := by
  norm_num [radialCoordinate, physical]

theorem physical_currentParent (q : Fin 6 → ℝ) :
    currentParent (physical q) = (1 + q 0) / 2 := by
  norm_num [currentParent, physical]

theorem physical_literalCap (q : Fin 6 → ℝ) :
    literalCap (physical q) = 57 / 64 - 3 / 2 * (q 0 + q 5) - 1 / 1000000 := by
  norm_num [literalCap, descending33, physical, eta]

/-- The linear part of the actual six-coordinate affine map. -/
def physicalLinear : Matrix (Fin 6) (Fin 6) ℝ :=
  ![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0],
    ![-1 / 2, -1, -1, -3 / 2, 1 / 2, 0], ![0, 0, 0, 1 / 2, -1 / 2, 0],
    ![0, 0, 0, 0, 0, 1]]

def physicalOffset : Fin 6 → ℝ := ![0, 0, 0, 1 / 2, 0, 0]

theorem physical_affine (q : Fin 6 → ℝ) (i : Fin 6) :
    physical q i = physicalOffset i + ∑ j, physicalLinear i j * q j := by
  fin_cases i <;>
    norm_num [physical, physicalOffset, physicalLinear, Fin.sum_univ_succ] <;> ring

theorem physicalLinear_det : Matrix.det physicalLinear = (1 / 2 : ℝ) := by
  norm_num [physicalLinear, Matrix.det_succ_row_zero, Matrix.submatrix_apply,
    Fin.sum_univ_succ]

/-- The source's physical-volume factor is 1/2, rather than an extra
factor inserted into the density normalization. -/
theorem physical_abs_jacobian : |Matrix.det physicalLinear| = (1 / 2 : ℝ) := by
  rw [physicalLinear_det]
  norm_num

/-- Source geometry, all full and remaining-selected square gates, and
the complete old subset-envelope comparison.  There is no gain premise. -/
structure SourceGuard (t : Fin 6 → ℝ) : Prop where
  largest : t 0 < mu
  order : StrictAnti t
  radial_pos : 0 < radialCoordinate t
  old_cutoff : radialCoordinate t < 1 / 50
  compact_lower : 53 / 4608 < radialCoordinate t
  third_history : oldThirdHistory t < currentParent t
  fifth_history : oldFifthHistory t < currentParent t
  W_dominated : oldW t ≤ currentParent t
  old_subsets : ∀ I : Finset (Fin 5), I.Nonempty →
    oldSubsetSum t I ≤ t 0 ∨ 25 / 64 ≤ 3 / 2 * oldSubsetSum t I + t 0 / 2
  clipped_above_ascending : ascending33 t < clippedCap t
  descending_selector : descending33 t < ascending33 t - eta
  new_above_old : currentParent t < literalCap t
  full_square : ∀ i, prefixSquareExpr t i < literalCap t
  selected_square : ∀ i ∉ mask33, selectedSquareExpr mask33 t i < literalCap t

theorem coordinates_pos (t : Fin 6 → ℝ) (h : SourceGuard t) (i : Fin 6) : 0 < t i := by
  have hr : 0 < t 5 := h.radial_pos
  by_cases hi : i = 5
  · simpa only [hi] using hr
  · have hi5 : i < (5 : Fin 6) := by omega
    exact hr.trans (h.order hi5)

theorem literalCap_gt_half (t : Fin 6 → ℝ) (h : SourceGuard t) :
    (1 / 2 : ℝ) < literalCap t := by
  have hx := coordinates_pos t h 0
  have hp := h.new_above_old
  unfold currentParent at hp
  linarith

theorem descending_license_identity (t : Fin 6 → ℝ) :
    descending33 t - literalCap t = eta := by unfold literalCap; ring

theorem literalCap_tent_license (t : Fin 6 → ℝ) (h : SourceGuard t) :
    literalCap t < v (∑ i ∈ mask33, t i) := by
  rw [mask33_sum, v_eq_min]
  have hA : A (t 0 + t 5) = ascending33 t := by unfold A ascending33; ring
  have hD : C (t 0 + t 5) = descending33 t := by unfold C descending33; ring
  rw [hA, hD, min_eq_right]
  · unfold literalCap eta
    linarith
  · have hs := h.descending_selector
    unfold eta at hs
    linarith

theorem ascending_license_margin (t : Fin 6 → ℝ) (h : SourceGuard t) :
    2 * eta < ascending33 t - literalCap t := by
  have hs := h.descending_selector
  unfold literalCap
  linarith

/-- Both strict non-overlap selectors retain the previous caps' actual
buffer placements.  Replacing either by C>M would lose this conclusion. -/
theorem previous_ascending33_excluded (t : Fin 6 → ℝ) (h : SourceGuard t) :
    ¬ ascending33 t - eta < descending33 t :=
  not_lt_of_ge h.descending_selector.le

theorem old_subset_cap_le_currentParent (t : Fin 6 → ℝ) (B : ℝ)
    (hbranch : B ≤ t 0 ∨ 25 / 64 ≤ 3 / 2 * B + t 0 / 2) :
    v B ≤ currentParent t := by
  rw [v_eq_min]
  rcases hbranch with h | h
  · apply (min_le_left _ _).trans
    dsimp [A, currentParent]
    linarith
  · apply (min_le_right _ _).trans
    dsimp [C, currentParent]
    linarith

theorem old_singleton_cap_eq_currentParent (t : Fin 6 → ℝ) (h : SourceGuard t) :
    v (t 0) = currentParent t := by
  rw [v_eq_min]
  have hx := h.largest
  unfold mu at hx
  have hAC : A (t 0) ≤ C (t 0) := by dsimp [A, C]; linarith
  rw [min_eq_left hAC]
  rfl

/-- The old raw envelope's singleton reaches R0 and all its other
subset/W candidates are bounded by R0. -/
theorem old_raw_envelope_dictionary (t : Fin 6 → ℝ) (h : SourceGuard t) :
    v (t 0) = currentParent t ∧ oldW t ≤ currentParent t ∧
      ∀ I : Finset (Fin 5), I.Nonempty → v (oldSubsetSum t I) ≤ currentParent t := by
  exact ⟨old_singleton_cap_eq_currentParent t h, h.W_dominated,
    fun I hI => old_subset_cap_le_currentParent t _ (h.old_subsets I hI)⟩

/-- Every old selected sum, after adjoining slot6, fails to license the
previous clipped action.  This handles the full old-subset family. -/
theorem old_clipped_action_excluded (t : Fin 6 → ℝ) (h : SourceGuard t) (B : ℝ)
    (hbranch : B ≤ t 0 ∨ 25 / 64 ≤ 3 / 2 * B + t 0 / 2) :
    v (B + radialCoordinate t) < clippedCap t := by
  rw [v_eq_min]
  have hr := h.radial_pos
  have hclip := h.clipped_above_ascending
  rcases hbranch with hB | hB
  · have hA : A (B + radialCoordinate t) ≤ ascending33 t := by
      dsimp [A, ascending33, radialCoordinate]
      linarith
    exact (min_le_left _ _).trans_lt (hA.trans_lt hclip)
  · have hD : C (B + radialCoordinate t) < currentParent t := by
      dsimp [C, currentParent, radialCoordinate] at *
      linarith
    have h0A : currentParent t < ascending33 t := by
      dsimp [currentParent, ascending33, radialCoordinate] at *
      linarith
    exact (min_le_right _ _).trans_lt (hD.trans (h0A.trans hclip))

/-- The old argument lower bound is derived from the real fifth history
and ordering.  It is not a new supplied residual-range assumption. -/
theorem old_residual_lower (t : Fin 6 → ℝ) (h : SourceGuard t) :
    totalCoordinates t + radialCoordinate t < currentParent t := by
  have hr5 : t 5 < t 4 := h.order (by decide : (4 : Fin 6) < 5)
  have hh := h.fifth_history
  rw [totalCoordinates_six]
  dsimp [radialCoordinate, oldFifthHistory] at *
  linarith

/-- The actual new argument upper bound follows from C>A and D<A-eta,
with three buffers of room before the endpoint 3. -/
theorem new_residual_upper_margin (t : Fin 6 → ℝ) (h : SourceGuard t) :
    literalCap t + 3 * eta < totalCoordinates t + 3 * radialCoordinate t := by
  have hCA := h.clipped_above_ascending
  have hDA := h.descending_selector
  dsimp [literalCap, clippedCap, radialCoordinate] at *
  linarith

theorem residual_range (t : Fin 6 → ℝ) (h : SourceGuard t) :
    0 < radialCoordinate t ∧
    radialCoordinate t < currentParent t - totalCoordinates t ∧
    currentParent t - totalCoordinates t < literalCap t - totalCoordinates t ∧
    literalCap t - totalCoordinates t < 3 * radialCoordinate t := by
  have hlo := old_residual_lower t h
  have hhi := new_residual_upper_margin t h
  have hgain := h.new_above_old
  have he : 0 < eta := by norm_num [eta]
  exact ⟨h.radial_pos, by linarith, by linarith, by linarith⟩

def sourceGain (old new : ℝ) (t : Fin 6 → ℝ) : ℝ :=
  4 * (new - old) / ((old - totalCoordinates t) * (new - totalCoordinates t))

def sourceKernel (t : Fin 6 → ℝ) : ℝ :=
  sourceGain (currentParent t) (literalCap t) t / (∏ i, t i)

theorem sourceGain_eq_difference (old new : ℝ) (t : Fin 6 → ℝ)
    (ho : 0 < old - totalCoordinates t) (hn : 0 < new - totalCoordinates t) :
    sourceGain old new t = 4 / (old - totalCoordinates t) - 4 / (new - totalCoordinates t) := by
  unfold sourceGain
  field_simp [ho.ne', hn.ne'] <;> ring

theorem sourceKernel_literal (t : Fin 6 → ℝ) :
    sourceKernel t = 4 * (literalCap t - currentParent t) /
      ((currentParent t - totalCoordinates t) * (literalCap t - totalCoordinates t) *
        (∏ i, t i)) := by
  simp only [sourceKernel, sourceGain, div_eq_mul_inv, mul_inv_rev]
  ring

theorem sourceKernel_pos (t : Fin 6 → ℝ) (h : SourceGuard t) : 0 < sourceKernel t := by
  have hr := residual_range t h
  have ho : 0 < currentParent t - totalCoordinates t := hr.1.trans hr.2.1
  have hn : 0 < literalCap t - totalCoordinates t := ho.trans hr.2.2.1
  have hp : 0 < ∏ i, t i := Finset.prod_pos (fun i _hi => coordinates_pos t h i)
  rw [sourceKernel_literal]
  exact div_pos (mul_pos (by norm_num) (sub_pos.mpr h.new_above_old))
    (mul_pos (mul_pos ho hn) hp)

/-- A true inherited parent may lie below the raw comparison R0.  Its
residual lower bound is retained, and replacing it by R0 decreases gain. -/
theorem conservative_parent_comparison (t : Fin 6 → ℝ) (h : SourceGuard t)
    (inherited : ℝ) (hparent : inherited ≤ currentParent t)
    (hlegal : radialCoordinate t < inherited - totalCoordinates t) :
    sourceGain (currentParent t) (literalCap t) t ≤ sourceGain inherited (literalCap t) t := by
  have hr := residual_range t h
  have ho : 0 < inherited - totalCoordinates t := hr.1.trans hlegal
  have hR : 0 < currentParent t - totalCoordinates t := hr.1.trans hr.2.1
  have hM : 0 < literalCap t - totalCoordinates t := hR.trans hr.2.2.1
  have hi := one_div_le_one_div_of_le ho (sub_le_sub_right hparent (totalCoordinates t))
  have h4 : 4 / (currentParent t - totalCoordinates t) ≤ 4 / (inherited - totalCoordinates t) := by
    convert mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 4) using 1 <;> ring
  rw [sourceGain_eq_difference _ _ t hR hM, sourceGain_eq_difference _ _ t ho hM]
  exact sub_le_sub_right h4 _

/-- The coefficient 4 is the actual ordinary upper factor on this legal
initial branch, not a coefficient supplied by the numerical certificate. -/
theorem normalized_initial_factors (t : Fin 6 → ℝ) (h : SourceGuard t) :
    (2 * Real.exp (-Real.eulerMascheroniConstant) / radialCoordinate t) *
        suzukiContinuousUpperFactor
          ((currentParent t - totalCoordinates t) / radialCoordinate t) =
      4 / (currentParent t - totalCoordinates t) ∧
    (2 * Real.exp (-Real.eulerMascheroniConstant) / radialCoordinate t) *
        suzukiContinuousUpperFactor
          ((literalCap t - totalCoordinates t) / radialCoordinate t) =
      4 / (literalCap t - totalCoordinates t) := by
  have hr := residual_range t h
  exact ⟨normalized_suzukiUpperFactor_initial _ _ hr.1 hr.2.1
      (hr.2.2.1.trans hr.2.2.2).le,
    normalized_suzukiUpperFactor_initial _ _ hr.1 (hr.2.1.trans hr.2.2.1) hr.2.2.2.le⟩

/-! Exact dictionary on real prime histories and their frozen levels. -/

def historyCoordinates (N : ℝ) (history : List ℕ) : Fin 6 → ℝ :=
  primeHistoryLogCoordinates N 6 history

theorem history_total_dictionary (N : ℝ) (hN : 1 < N) (history : List ℕ)
    (hlen : history.length = 6) (hpos : ∀ p ∈ history, 0 < p) :
    totalCoordinates (historyCoordinates N history) = Real.log (history.prod : ℝ) / Real.log N :=
  sum_primeHistoryLogCoordinates N hN hlen hpos

theorem history_radial_dictionary (N : ℝ) (history : List ℕ) (hlen : history.length = 6) :
    radialCoordinate (historyCoordinates N history) = Real.log (history.headD 0 : ℝ) / Real.log N := by
  change Real.log (primeHistoryTuple 6 history (Fin.last 5) : ℝ) / Real.log N = _
  rw [primeHistoryTuple_last hlen]

theorem history_quotient_dictionary (N : ℝ) (hN : 1 < N) (history : List ℕ)
    (hlen : history.length = 6) (hpos : ∀ p ∈ history, 0 < p) (lambda : ℝ) :
    actualRosserQuotientParameters N (history.prod : ℝ) (history.headD 0 : ℝ) lambda =
      (lambda - totalCoordinates (historyCoordinates N history),
        radialCoordinate (historyCoordinates N history)) := by
  rw [history_total_dictionary N hN history hlen hpos,
    history_radial_dictionary N history hlen]
  rfl

/-- Actual parent-frontier geometry supplies length, primality, and
positivity; neither the coordinate tuple nor its radial cutoff is a
caller-provided surrogate. -/
theorem actual_frontier_quotient_dictionary (N cap : ℕ) (hN : 1 < (N : ℝ))
    (z : ℝ) (parent : Bool → List ℕ → Bool) (state : FirstExitDepthState ℕ)
    (hstate : state ∈ firstExitDepthFrontier 6 parent
      (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z))
    (lambda : ℝ) :
    state.selectedPrefix.length = 6 ∧
    StrictAnti (historyCoordinates (N : ℝ) state.selectedPrefix) ∧
    (∀ i, 0 < historyCoordinates (N : ℝ) state.selectedPrefix i) ∧
    actualRosserQuotientParameters (N : ℝ) (state.selectedPrefix.prod : ℝ)
        (state.selectedPrefix.headD 0 : ℝ) lambda =
      (lambda - totalCoordinates (historyCoordinates (N : ℝ) state.selectedPrefix),
        radialCoordinate (historyCoordinates (N : ℝ) state.selectedPrefix)) := by
  have hlen := firstExitDepthFrontier_selected_length 6 parent
    (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] (roughPrimeUniverse N cap 0 z) true 1
    (by simp) state hstate
  have hsub := mem_firstExitDepthFrontier_selected_reverse_sublist 6 parent
    (fun p : ℕ => 1 / ((p : ℝ) - 1)) (roughPrimeUniverse N cap 0 z) state hstate
  have hpos : ∀ p ∈ state.selectedPrefix, 0 < p := by
    intro p hp
    exact (mem_roughPrimeUniverse_prime (hsub.subset (List.mem_reverse.mpr hp))).pos
  have hc := primeHistoryLogCoordinates_frontier 6 parent
    (fun p : ℕ => 1 / ((p : ℝ) - 1)) N cap hN 0 z state hstate
  exact ⟨hlen, hc.1, fun i => (hc.2 i).1,
    history_quotient_dictionary (N : ℝ) hN state.selectedPrefix hlen hpos lambda⟩

def sourceLevel (N : ℝ) (history : List ℕ) : ℝ :=
  N ^ literalCap (historyCoordinates N history)

def inheritedExponent (N : ℝ) (buffer : List ℕ → ℝ) (history : List ℕ) : ℝ :=
  currentParent (historyCoordinates N history) - buffer history

def inheritedLevel (N : ℝ) (buffer : List ℕ → ℝ) (history : List ℕ) : ℝ :=
  N ^ inheritedExponent N buffer history

/-- Every concrete inherited exponent has this representation; the
buffer does not encode a desired residual identity or gain. -/
def inheritedBuffer (N : ℝ) (actualExponent : List ℕ → ℝ) (history : List ℕ) : ℝ :=
  currentParent (historyCoordinates N history) - actualExponent history

theorem inheritedBuffer_nonneg (N : ℝ) (actualExponent : List ℕ → ℝ)
    (hparent : ∀ history, actualExponent history ≤ currentParent (historyCoordinates N history))
    (history : List ℕ) : 0 ≤ inheritedBuffer N actualExponent history :=
  sub_nonneg.mpr (hparent history)

theorem inheritedExponent_actual (N : ℝ) (actualExponent : List ℕ → ℝ) (history : List ℕ) :
    inheritedExponent N (inheritedBuffer N actualExponent) history = actualExponent history := by
  unfold inheritedExponent inheritedBuffer
  ring

theorem inheritedLevel_actual (N : ℝ) (actualExponent : List ℕ → ℝ) (history : List ℕ) :
    inheritedLevel N (inheritedBuffer N actualExponent) history = N ^ actualExponent history := by
  unfold inheritedLevel
  rw [inheritedExponent_actual]

def guardedSourceLevel (N : ℝ) (buffer : List ℕ → ℝ) (history : List ℕ) : ℝ :=
  if SourceGuard (historyCoordinates N history) then sourceLevel N history
  else inheritedLevel N buffer history

theorem guardedSourceLevel_outside (N : ℝ) (buffer : List ℕ → ℝ) (history : List ℕ)
    (h : ¬ SourceGuard (historyCoordinates N history)) :
    guardedSourceLevel N buffer history = inheritedLevel N buffer history := by
  simp only [guardedSourceLevel, if_neg h]

theorem inheritedLevel_le_guardedSourceLevel (N : ℝ) (hN : 1 ≤ N)
    (buffer : List ℕ → ℝ) (hbuffer : ∀ history, 0 ≤ buffer history) (history : List ℕ) :
    inheritedLevel N buffer history ≤ guardedSourceLevel N buffer history := by
  unfold guardedSourceLevel
  split_ifs with h
  · apply Real.rpow_le_rpow_of_exponent_le hN
    have hg := h.new_above_old
    have hb := hbuffer history
    dsimp [inheritedExponent]
    linarith
  · exact le_rfl

theorem sourceLevel_square_gates (N : ℝ) (hN : 1 < N) (history : List ℕ)
    (hlen : history.length = 6) (hpos : ∀ p ∈ history, 0 < p)
    (h : SourceGuard (historyCoordinates N history)) :
    (∀ i : Fin 6, ((∏ k ∈ Finset.univ.filter (fun k => k < i),
        primeHistoryTuple 6 history k : ℕ) : ℝ) *
      (primeHistoryTuple 6 history i : ℝ) ^ 2 < sourceLevel N history) ∧
    (∀ i ∉ mask33, ((∏ k ∈ mask33, primeHistoryTuple 6 history k : ℕ) : ℝ) *
      ((∏ k ∈ Finset.univ.filter (fun k => k < i ∧ k ∉ mask33),
        primeHistoryTuple 6 history k : ℕ) : ℝ) *
      (primeHistoryTuple 6 history i : ℝ) ^ 2 < sourceLevel N history) := by
  have hp : ∀ i, (primeHistoryTuple 6 history i : ℝ) ≤
      N ^ historyCoordinates N history i := by
    intro i
    rw [rpow_primeHistoryLogCoordinates N hN hlen hpos i]
  exact ⟨fun i => prefixSquareExpr_actual_gate N hN _ _ hp i (h.full_square i),
    fun i hi => selectedSquareExpr_actual_gate mask33 N hN _ _ hp i hi (h.selected_square i hi)⟩

def sourcePolicy (N : ℝ) (buffer : List ℕ → ℝ) (parent : Bool → List ℕ → Bool) :
    Bool → List ℕ → Bool :=
  firstExitDepthSplicePolicy 6 parent (frozenParityRosserPolicy false 6 (guardedSourceLevel N buffer))

theorem sourcePolicy_frontier_six (N : ℝ) (buffer : List ℕ → ℝ)
    (parent : Bool → List ℕ → Bool) (weight : ℕ → ℝ) (pre carrier : List ℕ)
    (positive : Bool) (mass : ℝ) :
    firstExitDepthFrontier 6 (sourcePolicy N buffer parent) weight pre positive mass carrier =
      firstExitDepthFrontier 6 parent weight pre positive mass carrier :=
  firstExitDepthFrontier_depthSplice_eq 6 6 le_rfl parent _ weight pre carrier positive mass

/-- At rank six the sign is positive and the residual branch is upper.
The prefix mass is the literal reciprocal `(p-1)` product. -/
theorem actualFrozenTerm_six (N cap : ℕ) (Q : List ℕ → ℝ) (history : List ℕ)
    (hlen : history.length = 6) :
    actualFrozenFrontierDensityTerm false N cap Q history =
      (history.map (fun p : ℕ => 1 / ((p : ℝ) - 1))).prod *
        actualSmallRosserPlusDensity N cap (history.headD 0 : ℝ)
          (Q history / (history.prod : ℝ)) := by
  unfold actualFrozenFrontierDensityTerm
  rw [signedTreeCoefficient_evenListLength_eq_negOnePow, hlen]
  norm_num [ordinaryRosserResidualLower]

theorem actualFrozenDifference_six (N cap : ℕ) (Qold Qnew : List ℕ → ℝ)
    (history : List ℕ) (hlen : history.length = 6) :
    actualFrozenFrontierDensityTerm false N cap Qold history -
        actualFrozenFrontierDensityTerm false N cap Qnew history =
      (history.map (fun p : ℕ => 1 / ((p : ℝ) - 1))).prod *
        (actualSmallRosserPlusDensity N cap (history.headD 0 : ℝ)
            (Qold history / (history.prod : ℝ)) -
          actualSmallRosserPlusDensity N cap (history.headD 0 : ℝ)
            (Qnew history / (history.prod : ℝ))) := by
  rw [actualFrozenTerm_six N cap Qold history hlen,
    actualFrozenTerm_six N cap Qnew history hlen]
  ring

/-- The full actual residual dictionary preserves the same real parent
frontier and derives the new admission from the literal cap increase. -/
theorem actual_sixth_splice_saving (N cap : ℕ) (hN : 1 ≤ (N : ℝ)) (z : ℝ)
    (buffer : List ℕ → ℝ) (hbuffer : ∀ history, 0 ≤ buffer history)
    (parent : Bool → List ℕ → Bool)
    (hold : ∀ state ∈ firstExitDepthFrontier 6 parent
      (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z),
      ordinaryRosserPrefixAdmissible false (inheritedLevel (N : ℝ) buffer state.selectedPrefix)
        state.selectedPrefix) :
    firstExitRetainedPolynomial
        (firstExitDepthSplicePolicy 6 parent
          (frozenParityRosserPolicy false 6 (inheritedLevel (N : ℝ) buffer)))
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z) -
      firstExitRetainedPolynomial (sourcePolicy (N : ℝ) buffer parent)
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z) =
      ((firstExitDepthFrontier 6 parent (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1
        (roughPrimeUniverse N cap 0 z)).map (fun state =>
          actualFrozenFrontierDensityTerm false N cap (inheritedLevel (N : ℝ) buffer) state.selectedPrefix -
            actualFrozenFrontierDensityTerm false N cap (guardedSourceLevel (N : ℝ) buffer)
              state.selectedPrefix)).sum := by
  apply firstExitRetainedPolynomial_frozenParity_splice_sub_eq_density_sum false 6 (by omega)
    parent (guardedSourceLevel (N : ℝ) buffer) (inheritedLevel (N : ℝ) buffer) N cap z
  · intro state hstate
    exact ordinaryRosserPrefixAdmissible_mono false state.selectedPrefix
      (inheritedLevel_le_guardedSourceLevel (N : ℝ) hN buffer hbuffer state.selectedPrefix)
      (hold state hstate)
  · exact hold

/-- The actual initial upper-density threshold supplies the conservative
source gain against a genuine inherited exponent.  Its range condition
concerns the inherited argument, not an assumed saving or integral. -/
theorem exists_actual_descending33_increment_threshold (t : Fin 6 → ℝ)
    (h : SourceGuard t) (inherited : ℝ) (hparent : inherited ≤ currentParent t)
    (hlegal : radialCoordinate t < inherited - totalCoordinates t)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ P y : ℝ, 0 < P → 0 < y →
        Real.log P / Real.log (N : ℝ) = totalCoordinates t →
        Real.log y / Real.log (N : ℝ) = radialCoordinate t →
        ∀ cap : ℕ, y ≤ (cap : ℝ) →
          sourceGain (currentParent t) (literalCap t) t - epsilon <
            (actualSmallRosserPlusDensity N cap y ((N : ℝ) ^ inherited / P) -
              actualSmallRosserPlusDensity N cap y ((N : ℝ) ^ literalCap t / P)) *
                Real.log (N : ℝ) / singularSeries N := by
  let T : Set (ℝ × ℝ) :=
    {(inherited - totalCoordinates t, radialCoordinate t)} ∪
      {(literalCap t - totalCoordinates t, radialCoordinate t)}
  have hT : IsCompact T := isCompact_singleton.union isCompact_singleton
  have hr := residual_range t h
  have hparam : ∀ p ∈ T, 0 < p.2 ∧ p.2 < p.1 ∧ p.1 ≤ 3 * p.2 := by
    intro p hp
    rcases hp with hp | hp
    · have heq := Set.mem_singleton_iff.mp hp
      subst p
      exact ⟨hr.1, hlegal, by linarith [hr.2.2.1, hr.2.2.2]⟩
    · have heq := Set.mem_singleton_iff.mp hp
      subst p
      exact ⟨hr.1, hr.2.1.trans hr.2.2.1, hr.2.2.2.le⟩
  obtain ⟨N0, hN0, hbound⟩ :=
    exists_actualSmallRosserPlusDensity_initial_quotient_saving_threshold T hT hparam epsilon hepsilon
  refine ⟨N0, hN0, ?_⟩
  intro N hN hEven P y hP hy hlogP hlogy cap hcap
  have hOld : actualRosserQuotientParameters (N : ℝ) P y inherited ∈ T := by
    simp only [actualRosserQuotientParameters, hlogP, hlogy]
    exact Or.inl (Set.mem_singleton _)
  have hNew : actualRosserQuotientParameters (N : ℝ) P y (literalCap t) ∈ T := by
    simp only [actualRosserQuotientParameters, hlogP, hlogy]
    exact Or.inr (Set.mem_singleton _)
  have hb := abs_lt.mp (hbound N hN hEven P y inherited (literalCap t) hP hy hOld hNew cap hcap)
  rw [hlogP] at hb
  have hc := conservative_parent_comparison t h inherited hparent hlegal
  unfold sourceGain at hc ⊢
  linarith [hb.1]

end

end ImbalancedChen.P2OriginalDescending33CapDictionary
