import ImbalancedChen.ActualSelectedPrefixLowerCellSum
import ImbalancedChen.ActualPrimeOwnCubeIcoIntegral
import ImbalancedChen.ActualRosserLowerLimit

/-!
# Genuine integrals for the actual selected lower fourth prefix

The selected data and finite owned Ico family are fixed before the target
varies. The full actual lower restoration converges to the sum of genuine
cell integrals. Each old/new residual retains its own strict fourth-cube
indicator, and exact outside fallback was proved before taking the limit.

The prime integral supplier controls discrete prime atoms at the cell and
affine boundaries by a pointwise sandwich. Its subsequent continuous
null-wall identities do not discard any unestimated arithmetic boundary.
This closes the ordinary-parent lower-fourth component; it does not yet
identify all of the manuscript's historical policies or numerical tables.
-/

namespace ImbalancedChen

noncomputable section

open Filter Topology
open MathlibNt.SieveTheory
open scoped Classical BigOperators

/-- The genuine new-minus-old integral on the owned lower-fourth cells. -/
def selectedPrefixLowerRestorationIntegral (I : Finset (Fin 4)) (old nu a b : ℚ)
    (m : ℕ) (J : Finset (Fin 4 → Fin (m + 1))) : ℝ :=
  ∑ j ∈ J,
    (primeOwnCubeIcoIntegral (a : ℝ) (b : ℝ)
      (selectedPrefixCellCap I old nu a b m j : ℝ) m j
      ordinaryLowerFourGateForms (ordinaryLowerFourGateBounds old) -
    primeOwnCubeIcoIntegral (a : ℝ) (b : ℝ) (old : ℝ) m j
      ordinaryLowerFourGateForms (ordinaryLowerFourGateBounds old))

/-- A common owned cell carries both strict own-cube indicators.  This
is the literal integral formula to which a lower-fourth certificate must
be bound; neither side is defined by its limiting prime sum. -/
theorem selectedPrefixLowerRestorationIntegral_eq_integrals
    (I : Finset (Fin 4)) (old nu a b : ℚ) (ha : 0 < a) (hab : a < b)
    (m : ℕ) (J : Finset (Fin 4 → Fin (m + 1))) :
    selectedPrefixLowerRestorationIntegral I old nu a b m J =
      ∑ j ∈ J, ∫ t in logPrimeMeshCell (a : ℝ) (b : ℝ) m j ∩
          primeAffineGateRegion ordinaryLowerFourGateForms (ordinaryLowerFourGateBounds old),
        (primeOwnCubeGatedProfile (selectedPrefixCellCap I old nu a b m j : ℝ) t -
          primeOwnCubeGatedProfile (old : ℝ) t) * ∏ i, 1 / t i := by
  apply Finset.sum_congr rfl
  intro j _hj
  exact primeOwnCubeIcoIntegral_sub_eq_integral
    (by exact_mod_cast ha) (by exact_mod_cast hab) (old : ℝ)
    (selectedPrefixCellCap I old nu a b m j : ℝ) m j
    ordinaryLowerFourGateForms (ordinaryLowerFourGateBounds old)

/-- The complete finite-family restoration has a genuine integral limit.
This prime-sum identity does not assume that the selected caps are legal,
nor that either signed density difference is nonnegative. -/
theorem tendsto_actualSelectedPrefixLowerOwnCubeSum
    (I : Finset (Fin 4)) (old nu a b : ℚ)
    (ha : 0 < a) (hab : a < b)
    (m : ℕ) (J : Finset (Fin 4 → Fin (m + 1))) (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ (b : ℝ) ≤ (cap N : ℝ)) :
    Tendsto (fun N : ℕ =>
      actualSelectedPrefixOwnCubeSum true N (cap N) ((N : ℝ) ^ (b : ℝ))
        I old nu a b m J * Real.log (N : ℝ) / singularSeries N)
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
      (𝓝 (selectedPrefixLowerRestorationIntegral I old nu a b m J)) := by
  have hlim := tendsto_finsetSum J (fun j _hj =>
    tendsto_actualPrimeBoxOwnCubeMinus_difference_IcoCell_affineGates 3
      (a : ℝ) (b : ℝ) (old : ℝ) (selectedPrefixCellCap I old nu a b m j : ℝ)
      (by exact_mod_cast ha) (by exact_mod_cast hab) m j
      ordinaryLowerFourGateForms (ordinaryLowerFourGateBounds old)
      ordinaryLowerFourGateForms_ne_zero cap hcap)
  change Tendsto _ _ (𝓝 (selectedPrefixLowerRestorationIntegral I old nu a b m J)) at hlim
  apply hlim.congr'
  have hlarge : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}, 1 < N :=
    (eventually_gt_atTop 1).filter_mono inf_le_left
  filter_upwards [hlarge, hcap] with N hN hc
  exact (actualSelectedPrefixLowerOwnCubeSum_eq_cells N (cap N) I old nu a b
    hab hN hc m J).symm

/-- The literal selected lower tree with the same target-deleted carrier. -/
def actualSelectedPrefixLowerDensity (N cap : ℕ) (I : Finset (Fin 4))
    (old nu a b : ℚ) (m : ℕ) (J : Finset (Fin 4 → Fin (m + 1))) : ℝ :=
  firstExitRetainedPolynomial
    (actualSelectedPrefixSplicePolicy true (N : ℝ) I old nu a b m J)
    (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1
    (roughPrimeUniverse N cap 0 ((N : ℝ) ^ (b : ℝ)))

/-- Finite rational box checks connect the integral to the actual lower
tree, retaining the lower root's explicit cutoff condition `b ≤ old`. -/
theorem tendsto_actualSelectedPrefixLowerDensity_restoration
    (I : Finset (Fin 4)) (old nu a b : ℚ)
    (ha : 0 < a) (hab : a < b) (hbo : b ≤ old)
    (m : ℕ) (J : Finset (Fin 4 → Fin (m + 1)))
    (hchecks : ∀ j ∈ J, selectedBoxCapCheck I old nu
      (qLogPrimeMeshLo a b m j) (qLogPrimeMeshHi a b m j) = true)
    (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ (b : ℝ) ≤ (cap N : ℝ)) :
    Tendsto (fun N : ℕ =>
      (actualSelectedPrefixLowerDensity N (cap N) I old nu a b m J -
        actualSmallRosserMinusDensity N (cap N) ((N : ℝ) ^ (b : ℝ))
          ((N : ℝ) ^ (old : ℝ))) * Real.log (N : ℝ) / singularSeries N)
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
      (𝓝 (selectedPrefixLowerRestorationIntegral I old nu a b m J)) := by
  apply (tendsto_actualSelectedPrefixLowerOwnCubeSum I old nu a b ha hab m J cap hcap).congr'
  have hold : 0 < old := (ha.trans hab).trans_le hbo
  have hlarge : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}, 1 < N :=
    (eventually_gt_atTop 1).filter_mono inf_le_left
  filter_upwards [hlarge] with N hN
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN
  have hz : (N : ℝ) ^ (b : ℝ) ≤ (N : ℝ) ^ (old : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hNr.le (by exact_mod_cast hbo)
  simp only [actualSelectedPrefixLowerDensity,
    actualSelectedPrefix_lower_four_restoration N (cap N) hNr
      ((N : ℝ) ^ (b : ℝ)) I old nu a b hold hz m J hchecks]

/-- In the legal ordinary lower range, the same selected density has the
proved ordinary lower limit plus the genuine fourth-prefix restoration.
The local cube endpoint `b` is not the manuscript's imbalance exponent. -/
theorem tendsto_actualSelectedPrefixLowerDensity_normalized
    (I : Finset (Fin 4)) (old nu a b : ℚ)
    (ha : 0 < a) (hab : a < b) (hbo : 2 * b ≤ old)
    (m : ℕ) (J : Finset (Fin 4 → Fin (m + 1)))
    (hchecks : ∀ j ∈ J, selectedBoxCapCheck I old nu
      (qLogPrimeMeshLo a b m j) (qLogPrimeMeshHi a b m j) = true)
    (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ (b : ℝ) ≤ (cap N : ℝ)) :
    Tendsto (fun N : ℕ => actualSelectedPrefixLowerDensity N (cap N) I old nu a b m J *
      Real.log (N : ℝ) / singularSeries N)
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
      (𝓝 ((2 * Real.exp (-Real.eulerMascheroniConstant) / (b : ℝ)) *
        suzukiContinuousLowerFactor ((old : ℝ) / (b : ℝ)) +
        selectedPrefixLowerRestorationIntegral I old nu a b m J)) := by
  have hb : (0 : ℝ) < b := by exact_mod_cast ha.trans hab
  have hs : (2 : ℝ) ≤ (old : ℝ) / (b : ℝ) := by
    rw [le_div_iff₀ hb]
    exact_mod_cast hbo
  have hbaseline := tendsto_actualSmallRosserMinusDensity_normalized
    (b : ℝ) hb ((old : ℝ) / (b : ℝ)) hs cap hcap
  rw [div_mul_cancel₀ _ hb.ne'] at hbaseline
  have hrestoration := tendsto_actualSelectedPrefixLowerDensity_restoration
    I old nu a b ha hab (by linarith) m J hchecks cap hcap
  apply (hbaseline.add hrestoration).congr'
  exact Eventually.of_forall (fun N => by dsimp only; ring)

/-- A literal finite enumeration covering the strict cutoff removes the
cap-coverage premise. Only the fixed geometric range and finite box
checks remain; no analytic convergence input is supplied by the caller. -/
theorem tendsto_actualSelectedPrefixLowerDensity_ceil_normalized
    (I : Finset (Fin 4)) (old nu a b : ℚ)
    (ha : 0 < a) (hab : a < b) (hbo : 2 * b ≤ old)
    (m : ℕ) (J : Finset (Fin 4 → Fin (m + 1)))
    (hchecks : ∀ j ∈ J, selectedBoxCapCheck I old nu
      (qLogPrimeMeshLo a b m j) (qLogPrimeMeshHi a b m j) = true) :
    Tendsto (fun N : ℕ =>
      actualSelectedPrefixLowerDensity N (Nat.ceil ((N : ℝ) ^ (b : ℝ)))
        I old nu a b m J * Real.log (N : ℝ) / singularSeries N)
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
      (𝓝 ((2 * Real.exp (-Real.eulerMascheroniConstant) / (b : ℝ)) *
        suzukiContinuousLowerFactor ((old : ℝ) / (b : ℝ)) +
        selectedPrefixLowerRestorationIntegral I old nu a b m J)) :=
  tendsto_actualSelectedPrefixLowerDensity_normalized I old nu a b ha hab hbo
    m J hchecks _
    (Eventually.of_forall (fun N => Nat.le_ceil ((N : ℝ) ^ (b : ℝ))))

end

end ImbalancedChen
