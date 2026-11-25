import ImbalancedChen.P2FiniteMarkedGamma5ActualInnerComparison
import ImbalancedChen.P2FiniteMarkedGamma5ActualProperPayment

/-!
SOURCE ONLY / UNCOMPILED / ZERO NEW FORMAL CREDIT.

The original all-depth raw selected physical-profile mass is at most
the original all-depth marked ordinaryBad mass plus one absolute
normalized epsilon. The same original root prime, dependent selected
positions, positive levelMark, old coordinates and depth budget remain.

A single physical width is chosen before N. The radial, complete-product
noncoprime and proper-strip errors each receive epsilon/3. Their existing
uniform estimates are combined without summing an epsilon once per
moving prime or history position. The original sharp base coefficient
remains one.

This is an ordinary finite marked-mass comparison. It does not construct
a globally admitted smooth selected-history mask, identify the original
J constant, supply a prime-product licence, or discharge W1/W2.
-/
namespace ImbalancedChen.P2FiniteMarkedGamma5ActualProfileMassComparison

noncomputable section
open Filter Finset Real
open Part5OriginalH430FrozenIntegerSupport (rootQ)
open Part5OriginalH430TaggedArithmeticReceivers (originalBand)
open Part5OriginalH430RequestedHistory (LevelIndex levelMark)
open Part5OriginalH430SeedHistoryMass (wordProduct)
open P2EnhancedBadGamma5ArithmeticGeometry (ordinaryBad)
open P2FiniteMarkedGamma5RadialRoughMass (norm)
open P2FiniteMarkedGamma5ActualRadialAggregate
  (allDepthSelectedProfileMass allDepthSelectedInnerMass allDepthSelectedOuterMass
    allDepthSelectedProfileMass_split absolute_all_depth_selected_outer_payment)
open P2FiniteMarkedGamma5ActualTargetExclusion
  (allDepthSelectedNoncoprimeMass absolute_all_depth_selected_noncoprime_payment)
open P2FiniteMarkedGamma5ActualInnerComparison
  (allDepthSelectedProperStripMass allDepthSelectedProperStripMass_eq_cells
    allDepthSelectedInnerMass_le_original_add_errors)
open P2FiniteMarkedGamma5ActualProperPayment
  (absolute_all_depth_cell_proper_payment)
open scoped Classical BigOperators Topology

/-- At fixed original refinement parameter n, first choose one positive
width and then one threshold uniform in every allowed t and every original
B dep p. The right-hand base is the literal original marked ordinaryBad
sum, with coefficient one and no replacement J or source-quality premise. -/
theorem actual_selected_profile_le_original_plus_epsilon
    (n : ℕ) (hn : 1 / ((n : ℝ) + 1) ≤ 11 / 384)
    {ε : ℝ} (he : 0 < ε) :
    ∃ h : ℝ, 0 < h ∧ h ≤ 1 / 8 ∧
      ∀ᶠ N : ℕ in atTop, ∀ t : ℝ, 0 ≤ t → t ≤ 1 / 12 →
        ∀ (B : (dep : Fin 431) → (p : ℕ) →
          Finset (LevelIndex N n .U4 t p dep.val)),
          norm N * allDepthSelectedProfileMass N n t h B ≤
            norm N * (∑ dep : Fin 431, ∑ p ∈ originalBand N .U4, ∑ l ∈ B dep p,
              levelMark l * ordinaryBad N (rootQ N n .U4 t p) (wordProduct l)) + ε := by
  have he3 : 0 < ε / (3 : ℝ) := div_pos he (by norm_num)
  obtain ⟨h, hh, h8, _hw, _hw1, Houter⟩ :=
    absolute_all_depth_selected_outer_payment n he3
  refine ⟨h, hh, h8, ?_⟩
  filter_upwards [Houter,
    absolute_all_depth_selected_noncoprime_payment n he3,
    absolute_all_depth_cell_proper_payment n hn he3,
    eventually_ge_atTop (2 : ℕ)] with N houter hnoncoprime hproper hN
  intro t ht ht' B
  let originalMass : ℝ :=
    ∑ dep : Fin 431, ∑ p ∈ originalBand N .U4, ∑ l ∈ B dep p,
      levelMark l * ordinaryBad N (rootQ N n .U4 t p) (wordProduct l)
  change norm N * allDepthSelectedProfileMass N n t h B ≤ norm N * originalMass + ε
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hnorm : 0 ≤ norm N := div_nonneg (log_pos hNr).le (Nat.cast_nonneg _)
  have hradial : norm N * allDepthSelectedOuterMass N n t h B ≤ ε / 3 :=
    houter t B
  have htarget : norm N * allDepthSelectedNoncoprimeMass N n t h B ≤ ε / 3 :=
    hnoncoprime t h hh h8 B
  have hwall : norm N * allDepthSelectedProperStripMass N n t h B ≤ ε / 3 := by
    rw [allDepthSelectedProperStripMass_eq_cells]
    exact hproper t h ht ht' hh h8 B
  have hinner := allDepthSelectedInnerMass_le_original_add_errors
    N n t h B hn hN ht ht' hh
  have hweighted := mul_le_mul_of_nonneg_left hinner hnorm
  calc
    _ = norm N * allDepthSelectedInnerMass N n t h B +
        norm N * allDepthSelectedOuterMass N n t h B := by
      rw [allDepthSelectedProfileMass_split, mul_add]
    _ ≤ norm N * (originalMass + allDepthSelectedNoncoprimeMass N n t h B +
        allDepthSelectedProperStripMass N n t h B) +
        norm N * allDepthSelectedOuterMass N n t h B :=
      add_le_add_right hweighted _
    _ = norm N * originalMass +
        (norm N * allDepthSelectedNoncoprimeMass N n t h B +
        norm N * allDepthSelectedProperStripMass N n t h B +
        norm N * allDepthSelectedOuterMass N n t h B) := by ring
    _ ≤ norm N * originalMass + ε := by
      linarith only [htarget, hwall, hradial]

end
end ImbalancedChen.P2FiniteMarkedGamma5ActualProfileMassComparison
