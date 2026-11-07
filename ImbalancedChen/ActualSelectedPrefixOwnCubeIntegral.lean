import ImbalancedChen.ActualSelectedPrefixUpperCellSum
import ImbalancedChen.ActualPrimeOwnCubeIcoIntegral
import ImbalancedChen.ActualRosserUpperGeneralLimit

/-!
# The actual selected fifth-prefix density and its cell integrals

For a fixed finite family of owned cells, the complete saving from the
ordinary parent has the sum of genuine cell integrals as its limit. The
actual retained polynomial then has the ordinary density limit minus
this saving. No selected-cap limit or arithmetic distribution estimate
is assumed. This remains a single fifth-prefix replacement of the
ordinary parent, not the manuscript's entire historical construction.
-/

namespace ImbalancedChen

noncomputable section

open Filter Topology
open MathlibNt.SieveTheory
open scoped Classical BigOperators

/-- The genuine integral correction from the owned fifth-prefix cells. -/
def selectedPrefixUpperSavingIntegral (I : Finset (Fin 5)) (old nu a b : ℚ)
    (m : ℕ) (J : Finset (Fin 5 → Fin (m + 1))) : ℝ :=
  ∑ j ∈ J,
    (primeOwnCubeIcoIntegral (a : ℝ) (b : ℝ)
      (selectedPrefixCellCap I old nu a b m j : ℝ) m j
      ordinaryUpperFiveGateForms (ordinaryUpperFiveGateBounds old) -
    primeOwnCubeIcoIntegral (a : ℝ) (b : ℝ) (old : ℝ) m j
      ordinaryUpperFiveGateForms (ordinaryUpperFiveGateBounds old))

/-- The literal full selected saving, rather than a localized substitute,
converges to the finite sum of its owned-cell integrals. -/
theorem tendsto_actualSelectedPrefixUpperOwnCubeSum
    (I : Finset (Fin 5)) (old nu a b : ℚ)
    (ha : 0 < a) (hab : a < b) (hold : 0 < old)
    (m : ℕ) (J : Finset (Fin 5 → Fin (m + 1))) (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ (b : ℝ) ≤ (cap N : ℝ)) :
    Tendsto (fun N : ℕ =>
      actualSelectedPrefixOwnCubeSum false N (cap N) ((N : ℝ) ^ (b : ℝ))
        I old nu a b m J * Real.log (N : ℝ) / singularSeries N)
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
      (𝓝 (selectedPrefixUpperSavingIntegral I old nu a b m J)) := by
  have hlim := tendsto_finsetSum J (fun j _hj =>
    tendsto_actualPrimeBoxOwnCubeMinus_difference_IcoCell_affineGates 4
      (a : ℝ) (b : ℝ) (old : ℝ) (selectedPrefixCellCap I old nu a b m j : ℝ)
      (by exact_mod_cast ha) (by exact_mod_cast hab) m j
      ordinaryUpperFiveGateForms (ordinaryUpperFiveGateBounds old)
      ordinaryUpperFiveGateForms_ne_zero cap hcap)
  change Tendsto _ _ (𝓝 (selectedPrefixUpperSavingIntegral I old nu a b m J)) at hlim
  apply hlim.congr'
  have hlarge : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}, 1 < N :=
    (eventually_gt_atTop 1).filter_mono inf_le_left
  filter_upwards [hlarge, hcap] with N hN hc
  exact (actualSelectedPrefixUpperOwnCubeSum_eq_cells N (cap N) I old nu a b
    hab hN hold hc m J).symm

/-- This is the same retained polynomial as the finite selector identity,
with the actual target-deleted prime carrier. -/
def actualSelectedPrefixUpperDensity (N cap : ℕ) (I : Finset (Fin 5))
    (old nu a b : ℚ) (m : ℕ) (J : Finset (Fin 5 → Fin (m + 1))) : ℝ :=
  firstExitRetainedPolynomial
    (actualSelectedPrefixSplicePolicy false (N : ℝ) I old nu a b m J)
    (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1
    (roughPrimeUniverse N cap 0 ((N : ℝ) ^ (b : ℝ)))

/-- Checked selected caps give the actual tree-density saving. The
checks are finite rational computations, not an analytic limit premise. -/
theorem tendsto_actualSelectedPrefixUpperDensity_saving
    (I : Finset (Fin 5)) (old nu a b : ℚ)
    (ha : 0 < a) (hab : a < b) (hold : 0 < old)
    (m : ℕ) (J : Finset (Fin 5 → Fin (m + 1)))
    (hchecks : ∀ j ∈ J, selectedBoxCapCheck I old nu
      (qLogPrimeMeshLo a b m j) (qLogPrimeMeshHi a b m j) = true)
    (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ (b : ℝ) ≤ (cap N : ℝ)) :
    Tendsto (fun N : ℕ =>
      (actualSmallRosserPlusDensity N (cap N) ((N : ℝ) ^ (b : ℝ)) ((N : ℝ) ^ (old : ℝ)) -
        actualSelectedPrefixUpperDensity N (cap N) I old nu a b m J) *
        Real.log (N : ℝ) / singularSeries N)
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
      (𝓝 (selectedPrefixUpperSavingIntegral I old nu a b m J)) := by
  apply (tendsto_actualSelectedPrefixUpperOwnCubeSum I old nu a b ha hab hold m J cap hcap).congr'
  have hlarge : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}, 1 < N :=
    (eventually_gt_atTop 1).filter_mono inf_le_left
  filter_upwards [hlarge] with N hN
  simp only [actualSelectedPrefixUpperDensity,
    actualSelectedPrefix_upper_five_saving N (cap N) (by exact_mod_cast hN)
      ((N : ℝ) ^ (b : ℝ)) I old nu a b hold m J hchecks]

/-- In the legal ordinary upper-sieve range, the actual selected tree
has the ordinary normalized density minus the proved integral saving. -/
theorem tendsto_actualSelectedPrefixUpperDensity_normalized
    (I : Finset (Fin 5)) (old nu a b : ℚ)
    (ha : 0 < a) (hab : a < b) (hbo : b < old)
    (m : ℕ) (J : Finset (Fin 5 → Fin (m + 1)))
    (hchecks : ∀ j ∈ J, selectedBoxCapCheck I old nu
      (qLogPrimeMeshLo a b m j) (qLogPrimeMeshHi a b m j) = true)
    (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ (b : ℝ) ≤ (cap N : ℝ)) :
    Tendsto (fun N : ℕ => actualSelectedPrefixUpperDensity N (cap N) I old nu a b m J *
      Real.log (N : ℝ) / singularSeries N)
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
      (𝓝 ((2 * Real.exp (-Real.eulerMascheroniConstant) / (b : ℝ)) *
        suzukiContinuousUpperFactor ((old : ℝ) / (b : ℝ)) -
        selectedPrefixUpperSavingIntegral I old nu a b m J)) := by
  have hb : (0 : ℝ) < b := by exact_mod_cast ha.trans hab
  have hs : (1 : ℝ) < (old : ℝ) / (b : ℝ) := by
    rw [lt_div_iff₀ hb, one_mul]
    exact_mod_cast hbo
  have hbaseline := tendsto_actualSmallRosserPlusDensity_general_normalized
    (b : ℝ) hb ((old : ℝ) / (b : ℝ)) hs cap hcap
  rw [div_mul_cancel₀ _ hb.ne'] at hbaseline
  have hsaving := tendsto_actualSelectedPrefixUpperDensity_saving
    I old nu a b ha hab (ha.trans (hab.trans hbo)) m J hchecks cap hcap
  apply (hbaseline.sub hsaving).congr'
  exact Eventually.of_forall (fun N => by dsimp only; ring)

end

end ImbalancedChen
