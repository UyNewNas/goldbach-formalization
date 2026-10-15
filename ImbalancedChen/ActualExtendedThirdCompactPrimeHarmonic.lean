import ImbalancedChen.ActualExtendedThirdCompactHarmonicProfile

/-!
# Actual prime harmonic sums for the fixed-cutoff cell policy

Every summand is the literal prime-box test with the actual owned ordered
cell and actual physical cell level. Its limit is the previously proved
integrable cell cap kernel. Only finite sums are interchanged.

The final tolerance chooses the cutoff, positive buffer and finite grid
before N. This is a prime harmonic mean, not yet an identification with
the signed arithmetic first-exit sieve density or its counting error.
-/

namespace ImbalancedChen

noncomputable section

open Set Filter Topology MeasureTheory
open VariableEnvelope
open scoped Classical BigOperators

def actualExtendedThirdCompactCellPrimeSum (N : ℕ) (e h : ℝ) (m : ℕ)
    (j : ActualExtendedThirdDyadicLabel m) : ℝ :=
  actualPrimeBoxTestSum N (fun _ : Fin 3 => h / 2) (fun _ => thirdPrefixRho + 1)
    ((actualExtendedThirdCompactCellPrimeRegion m j).indicator
      (actualExtendedThirdCompactHarmonicProfile e h (actualExtendedThirdPhysicalLevel e m j)))

theorem tendsto_actualExtendedThirdCompactCellPrimeSum {e h : ℝ} {m : ℕ}
    (hh : 0 < h) {j : ActualExtendedThirdDyadicLabel m}
    (hj : j ∈ actualExtendedThirdCompactCells e h m) :
    Tendsto (fun N : ℕ => actualExtendedThirdCompactCellPrimeSum N e h m j) atTop
      (𝓝 (actualExtendedThirdRetainedCellIntegral e m j)) := by
  have hhrho : h ≤ thirdPrefixRho :=
    (Finset.mem_filter.mp hj).2.trans
      ((actualExtendedThirdDyadic_bounds m j 2).2.1.le.trans
        (actualExtendedThirdDyadic_bounds m j 2).2.2)
  have hab : h / 2 < thirdPrefixRho + 1 := by linarith
  have hsand := actualExtendedThirdCompactCellPrimeRegion_sandwich hh hj
  have hlim := tendsto_actualPrimeBoxTestSum_cube_affineSandwich (half_pos hh) hab
    actualExtendedThirdCompactCellForms (actualExtendedThirdCompactCellBounds m j)
    actualExtendedThirdCompactCellForms_ne_zero (actualExtendedThirdCompactCellPrimeRegion m j)
    (measurableSet_actualExtendedThirdCompactCellPrimeRegion m j) hsand.1 hsand.2
    (actualExtendedThirdCompactHarmonicProfile e h (actualExtendedThirdPhysicalLevel e m j))
    (continuous_actualExtendedThirdCompactHarmonicProfile hh e
      (actualExtendedThirdPhysicalLevel e m j)).continuousOn
  have hdomain : logPrimeBox (fun _ : Fin 3 => h / 2) (fun _ => thirdPrefixRho + 1) ∩
      actualExtendedThirdCompactCellPrimeRegion m j = actualExtendedThirdCompactCellPrimeRegion m j :=
    inter_eq_right.mpr (actualExtendedThirdCompactCellPrimeRegion_subset_cube hh hj)
  have hintegral :
      (∫ t in logPrimeBox (fun _ : Fin 3 => h / 2) (fun _ => thirdPrefixRho + 1) ∩
          actualExtendedThirdCompactCellPrimeRegion m j,
        actualExtendedThirdCompactHarmonicProfile e h (actualExtendedThirdPhysicalLevel e m j) t *
          ∏ i : Fin 3, 1 / t i) = actualExtendedThirdRetainedCellIntegral e m j := by
    rw [hdomain]
    change (∫ t in actualExtendedThirdCompactCellPrimeRegion m j,
      actualExtendedThirdCompactHarmonicProfile e h (actualExtendedThirdPhysicalLevel e m j) t *
        ∏ i : Fin 3, 1 / t i) =
      ∫ t in actualExtendedThirdCompactCellPrimeRegion m j,
        actualExtendedThirdCapKernel e (actualExtendedThirdPhysicalLevel e m j) (t 0) (t 1) (t 2)
    apply setIntegral_congr_fun (measurableSet_actualExtendedThirdCompactCellPrimeRegion m j)
    intro t ht
    exact actualExtendedThirdCompactHarmonicProfile_density hh ht.2
      ((Finset.mem_filter.mp hj).2.trans (ht.1.1 2 (mem_univ _)).1)
  simpa only [actualExtendedThirdCompactCellPrimeSum, hintegral] using hlim

def actualExtendedThirdCompactPrimeSum (N : ℕ) (e h : ℝ) (m : ℕ) : ℝ :=
  ∑ j ∈ actualExtendedThirdCompactCells e h m, actualExtendedThirdCompactCellPrimeSum N e h m j

theorem tendsto_actualExtendedThirdCompactPrimeSum {e h : ℝ}
    (hh : 0 < h) (he0 : 0 ≤ e) (he : e ≤ 1 / 384) (m : ℕ) :
    Tendsto (fun N : ℕ => actualExtendedThirdCompactPrimeSum N e h m) atTop
      (𝓝 (actualExtendedThirdCompactCellFunctional e h m)) := by
  rw [actualExtendedThirdCompactCellFunctional_eq_sum_cells he0 he m]
  exact tendsto_finsetSum _ (fun _j hj => tendsto_actualExtendedThirdCompactCellPrimeSum hh hj)

/-- The finite actual prime tests recover the same manuscript functional.
All policy parameters precede the sufficiently large arithmetic target. -/
theorem exists_actualExtendedThirdCompactPrimeSum_approx_ideal {ε : ℝ} (hε : 0 < ε) :
    ∃ h : ℝ, 0 < h ∧ ∃ e : ℝ, 0 < e ∧ e ≤ 1 / 384 ∧ ∃ m : ℕ,
      ∀ᶠ N : ℕ in atTop,
        |actualExtendedThirdCompactPrimeSum N e h m - actualExtendedThirdIdealFunctional| ≤ ε := by
  obtain ⟨h, hh, e₀, he₀, he₀cap, m₀, hb⟩ :=
    actualExtendedThirdCompactCellFunctional_uniform_approx (half_pos hε)
  have hepos : 0 < e₀ / 2 := half_pos he₀
  have hecap : e₀ / 2 ≤ 1 / 384 := (by linarith : e₀ / 2 ≤ e₀).trans he₀cap
  have hcont : |actualExtendedThirdCompactCellFunctional (e₀ / 2) h m₀ -
      actualExtendedThirdIdealFunctional| ≤ ε / 2 :=
    hb (e₀ / 2) hepos.le (by linarith) m₀ le_rfl
  have hprime : ∀ᶠ N : ℕ in atTop,
      |actualExtendedThirdCompactPrimeSum N (e₀ / 2) h m₀ -
        actualExtendedThirdCompactCellFunctional (e₀ / 2) h m₀| < ε / 2 := by
    simpa only [Real.dist_eq] using Metric.tendsto_nhds.mp
      (tendsto_actualExtendedThirdCompactPrimeSum hh hepos.le hecap m₀)
        (ε / 2) (half_pos hε)
  refine ⟨h, hh, e₀ / 2, hepos, hecap, m₀, ?_⟩
  filter_upwards [hprime] with N hN
  apply (abs_sub_le _ (actualExtendedThirdCompactCellFunctional (e₀ / 2) h m₀) _).trans
  exact (add_le_add hN.le hcont).trans (by linarith)

end

end ImbalancedChen
