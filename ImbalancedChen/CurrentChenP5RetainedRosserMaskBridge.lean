import ImbalancedChen.CurrentChenP5SelectedMaskTransport
import ImbalancedChen.CurrentChenUpsilon6FiniteMean

/-!
# Direct lower Rosser restriction on the original retained sixth row

The full and selected estimator masses below use the same actual lower
Rosser coefficients, at each pair's true rounded quotient level. Their
difference is exactly the estimator on the complement mask. Applying the
proved per-pair lower sieve there gives the actual retained sixth count.
No upper bound for the actual selected Y6 count is used or asserted.

The physical product gate is exactly the corrected Runbo buffered gate,
with the original endpoint conventions. Signed prime-AP remainders and
prime-centre corrections are retained in the finite theorem. A separate
corollary uses the already proved all-subselector BV payment, with the
same mask and physical modulus, to obtain a uniform normalized error.

SOURCE ONLY: uncompiled; imports its companion draft transport module.
-/

namespace ImbalancedChen.P5RetainedRosserMaskBridge

open scoped BigOperators
open Classical Filter Topology
open P5SelectedMaskTransport
open MathlibNt.SieveTheory.BombieriVinogradov (trueLogarithmicIntegral)

noncomputable section

abbrev cutoff (N : ℕ) : ℝ := (N : ℝ) ^ (417 / 5000 : ℝ)
abbrev cap (N : ℕ) : ℕ := Nat.ceil (cutoff N)
abbrev multiplier (t : ℕ × ℕ) : ℕ := t.1 * t.2
abbrev level (B : ℝ) (N : ℕ) (t : ℕ × ℕ) : ℕ :=
  chenQuotientRosserD B N (multiplier t)

/-- The literal lower Rosser coefficient is shared by the main term,
the signed AP remainder and the signed centre correction. -/
def rho (B : ℝ) (N : ℕ) (t : ℕ × ℕ) (d : ℕ) : ℝ :=
  actualSmallRosserMinus N (cap N) (cutoff N) (level B N t : ℝ) d

abbrev active (B : ℝ) (N : ℕ) (t : ℕ × ℕ) : Finset ℕ :=
  currentChenQuotientRosserActive N (multiplier t) (cap N)
    (chenInitialLevelCap B N) (cutoff N)

def rowMain (B : ℝ) (N : ℕ) (t : ℕ × ℕ) : ℝ :=
  trueLogarithmicIntegral N / (Nat.totient (multiplier t) : ℝ) *
    actualSmallRosserMinusDensity N (cap N) (cutoff N) (level B N t : ℝ)

def rowSignedAP (B : ℝ) (N : ℕ) (t : ℕ × ℕ) : ℝ :=
  ∑ d ∈ active B N t, rho B N t d *
    chenQuotientPrimeAPError N (trueLogarithmicIntegral N) (multiplier t * d)

def rowSignedCentre (B : ℝ) (N : ℕ) (t : ℕ × ℕ) : ℝ :=
  ∑ d ∈ active B N t, rho B N t d *
    chenCentrePrimeAPCount N N (multiplier t * d)

def rowEstimator (B : ℝ) (N : ℕ) (t : ℕ × ℕ) : ℝ :=
  rowMain B N t + rowSignedAP B N t - rowSignedCentre B N t

theorem active_physical_modulus (B : ℝ) (N : ℕ) (t : ℕ × ℕ)
    (ht : t ∈ sixthSupport N) {d : ℕ} (hd : d ∈ active B N t) :
    multiplier t * d ≤ chenInitialLevelCap B N := by
  exact currentChenQuotientRosserActive_physical_cap
    (Nat.zero_lt_one.trans (chenY6PrimeSelector_sieve_data ht).1) hd

/-- A concrete proved minorant, not a premise asserting the desired
selected mean. All displayed terms use exactly the actual rho above. -/
theorem rowEstimator_le_card (B : ℝ) (N : ℕ) (t : ℕ × ℕ)
    (ht : t ∈ sixthSupport N)
    (hlevel : 1 < (level B N t : ℝ) ∧ cutoff N ≤ (level B N t : ℝ)) :
    rowEstimator B N t ≤ sixthWeight N t := by
  have h := currentChen_quotient_actualRosser_density_lower N (multiplier t) (cap N)
    (cutoff N) (level B N t : ℝ) (Nat.le_ceil _)
    (chenY6PrimeSelector_sieve_data ht).2.2 hlevel.1 hlevel.2
  rw [currentChen_quotientRosser_sum_eq_active,
    currentChen_quotientRosser_sum_eq_active] at h
  exact h

def estimatorSum (B : ℝ) (N : ℕ) (T : Finset (ℕ × ℕ)) : ℝ :=
  ∑ t ∈ T, rowEstimator B N t

def mainSum (B : ℝ) (N : ℕ) (T : Finset (ℕ × ℕ)) : ℝ :=
  ∑ t ∈ T, rowMain B N t

def signedAPSum (B : ℝ) (N : ℕ) (T : Finset (ℕ × ℕ)) : ℝ :=
  ∑ t ∈ T, rowSignedAP B N t

def signedCentreSum (B : ℝ) (N : ℕ) (T : Finset (ℕ × ℕ)) : ℝ :=
  ∑ t ∈ T, rowSignedCentre B N t

theorem estimatorSum_eq_signed_terms (B : ℝ) (N : ℕ) (T : Finset (ℕ × ℕ)) :
    estimatorSum B N T = mainSum B N T + signedAPSum B N T - signedCentreSum B N T := by
  simp only [estimatorSum, rowEstimator, mainSum, signedAPSum, signedCentreSum,
    Finset.sum_sub_distrib, Finset.sum_add_distrib]

/-- The unmasked reference estimator is restricted to the same corrected
physical-product support as the retained original count. -/
def fullEstimator (B : ℝ) (N : ℕ) (eta : ℝ) : ℝ :=
  estimatorSum B N (retainedSupport N eta)

def selectedEstimator (B : ℝ) (N : ℕ) (eta : ℝ) (E : ℕ × ℕ → Prop) : ℝ :=
  estimatorSum B N ((retainedSupport N eta).filter E)

def retainedEstimator (B : ℝ) (N : ℕ) (eta : ℝ) (E : ℕ × ℕ → Prop) : ℝ :=
  estimatorSum B N (currentChenUpsilon6RetainedSelector N E eta)

theorem retainedSelector_eq_compl (N : ℕ) (eta : ℝ) (E : ℕ × ℕ → Prop) :
    currentChenUpsilon6RetainedSelector N E eta =
      (retainedSupport N eta).filter (fun t => ¬ E t) := by
  unfold currentChenUpsilon6RetainedSelector retainedSupport
  simp only [Finset.filter_filter, and_comm]

theorem retainedSelector_subset_original (N : ℕ) (eta : ℝ)
    (E : ℕ × ℕ → Prop) :
    currentChenUpsilon6RetainedSelector N E eta ⊆ sixthSupport N := by
  rw [retainedSelector_eq_compl]
  exact (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)

/-- Signed estimator partition: no positivity assertion about an
estimator, saved floor, or selected actual count is needed. -/
theorem fullEstimator_sub_selectedEstimator (B : ℝ) (N : ℕ) (eta : ℝ)
    (E : ℕ × ℕ → Prop) :
    fullEstimator B N eta - selectedEstimator B N eta E =
      retainedEstimator B N eta E := by
  have h := Finset.sum_filter_add_sum_filter_not (retainedSupport N eta) E
    (rowEstimator B N)
  unfold fullEstimator selectedEstimator retainedEstimator estimatorSum
  rw [retainedSelector_eq_compl]
  linarith only [h]

/-- The minorant is reapplied directly on the retained complement, so
the selected estimator mass is never read as an actual-count upper bound. -/
theorem retainedEstimator_le_actual (B : ℝ) (N : ℕ) (eta : ℝ)
    (E : ℕ × ℕ → Prop)
    (hlevels : ∀ t ∈ currentChenUpsilon6RetainedSelector N E eta,
      1 < (level B N t : ℝ) ∧ cutoff N ≤ (level B N t : ℝ)) :
    retainedEstimator B N eta E ≤ currentChenUpsilon6Retained N E eta := by
  apply Finset.sum_le_sum
  intro t ht
  exact rowEstimator_le_card B N t
    (retainedSelector_subset_original N eta E ht) (hlevels t ht)

theorem fullEstimator_sub_selectedEstimator_le_actual (B : ℝ) (N : ℕ) (eta : ℝ)
    (E : ℕ × ℕ → Prop)
    (hlevels : ∀ t ∈ currentChenUpsilon6RetainedSelector N E eta,
      1 < (level B N t : ℝ) ∧ cutoff N ≤ (level B N t : ℝ)) :
    fullEstimator B N eta - selectedEstimator B N eta E ≤
      currentChenUpsilon6Retained N E eta := by
  rw [fullEstimator_sub_selectedEstimator]
  exact retainedEstimator_le_actual B N eta E hlevels

/-- Explicit finite signed AP and centre version on the literal original
mask complement and corrected product support. -/
theorem retained_signed_main_AP_centre_le_actual (B : ℝ) (N : ℕ) (eta : ℝ)
    (E : ℕ × ℕ → Prop)
    (hlevels : ∀ t ∈ currentChenUpsilon6RetainedSelector N E eta,
      1 < (level B N t : ℝ) ∧ cutoff N ≤ (level B N t : ℝ)) :
    mainSum B N (currentChenUpsilon6RetainedSelector N E eta) +
      signedAPSum B N (currentChenUpsilon6RetainedSelector N E eta) -
      signedCentreSum B N (currentChenUpsilon6RetainedSelector N E eta) ≤
      currentChenUpsilon6Retained N E eta := by
  rw [← estimatorSum_eq_signed_terms]
  exact retainedEstimator_le_actual B N eta E hlevels

/-- The genuine rounded-level supplier proves all row premises before
both masks and every product buffer are chosen. -/
theorem eventually_uniform_full_sub_selected_le_actual (B : ℝ) :
    ∀ᶠ N : ℕ in atTop, ∀ eta : ℝ, ∀ E : ℕ × ℕ → Prop,
      fullEstimator B N eta - selectedEstimator B N eta E ≤
        currentChenUpsilon6Retained N E eta := by
  filter_upwards [eventually_currentChenUpsilon6_ordinary_row_level B] with N hlevels
  intro eta E
  apply fullEstimator_sub_selectedEstimator_le_actual
  intro t ht
  exact hlevels t (retainedSelector_subset_original N eta E ht)

/-- Density partition on the same product support; the selected mass
here is an actual Rosser estimator coefficient sum, not selected Y6. -/
theorem density_full_sub_selected_eq_retained (B : ℝ) (N : ℕ) (eta : ℝ)
    (E : ℕ × ℕ → Prop) :
    currentChenUpsilon6OrdinaryDensitySum B N (retainedSupport N eta) -
      currentChenUpsilon6OrdinaryDensitySum B N ((retainedSupport N eta).filter E) =
        currentChenUpsilon6OrdinaryDensitySum B N
          (currentChenUpsilon6RetainedSelector N E eta) := by
  have h := Finset.sum_filter_add_sum_filter_not (retainedSupport N eta) E (rowMain B N)
  change currentChenUpsilon6OrdinaryDensitySum B N ((retainedSupport N eta).filter E) +
    currentChenUpsilon6OrdinaryDensitySum B N
      ((retainedSupport N eta).filter (fun t => ¬ E t)) =
    currentChenUpsilon6OrdinaryDensitySum B N (retainedSupport N eta) at h
  rw [retainedSelector_eq_compl]
  linarith only [h]

/-- Finite ordinary AP and complete centre payments on the original
masked retained rows, with no actual selected-count upper premise. -/
theorem retained_density_sub_full_costs_le_actual (B : ℝ) (N : ℕ) (eta : ℝ)
    (E : ℕ × ℕ → Prop)
    (hlevels : ∀ t ∈ currentChenUpsilon6RetainedSelector N E eta,
      1 < (level B N t : ℝ) ∧ cutoff N ≤ (level B N t : ℝ)) :
    currentChenUpsilon6OrdinaryDensitySum B N (retainedSupport N eta) -
      currentChenUpsilon6OrdinaryDensitySum B N ((retainedSupport N eta).filter E) -
      part3CurrentLowerAPError N (fun _ => ∅) (fun _ => ∅) (fun _ => ∅)
        (currentChenUpsilon6OrdinaryRows N (chenInitialLevelCap B N)
          (currentChenUpsilon6RetainedSelector N E eta)) -
      part3CurrentLowerCentreCost N (fun _ => ∅) (fun _ => ∅) (fun _ => ∅)
        (currentChenUpsilon6OrdinaryRows N (chenInitialLevelCap B N)
          (currentChenUpsilon6RetainedSelector N E eta)) ≤
      currentChenUpsilon6Retained N E eta := by
  rw [density_full_sub_selected_eq_retained]
  exact currentChenUpsilon6_ge_ordinary_density_sub_costs B N
    (currentChenUpsilon6RetainedSelector N E eta)
    (retainedSelector_subset_original N eta E) hlevels

/-- The already proved physical-modulus BV supplier pays the retained
rows uniformly before eta and E. This is the direct original-mask route,
not a transfer of a saved-floor loss into a selected-count upper bound. -/
theorem eventually_uniform_density_full_sub_selected_le_actual :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N : ℕ in atTop, Even N → ∀ eta : ℝ, ∀ E : ℕ × ℕ → Prop,
        currentChenUpsilon6OrdinaryDensitySum B N (retainedSupport N eta) -
          currentChenUpsilon6OrdinaryDensitySum B N ((retainedSupport N eta).filter E) -
          epsilon * singularNormalization N ≤ currentChenUpsilon6Retained N E eta := by
  obtain ⟨B, hB, hpaid⟩ :=
    eventually_currentChenUpsilon6_subselector_ge_ordinary_density_sum
  refine ⟨B, hB, ?_⟩
  intro epsilon hepsilon
  filter_upwards [hpaid epsilon hepsilon] with N hN
  intro hEven eta E
  rw [density_full_sub_selected_eq_retained]
  exact hN hEven (currentChenUpsilon6RetainedSelector N E eta)
    (retainedSelector_subset_original N eta E)

end

end ImbalancedChen.P5RetainedRosserMaskBridge
