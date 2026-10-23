import ImbalancedChen.ActualExtendedThirdCompactCellCutoff

/-!
# The fixed-cutoff cell policy recovers the manuscript functional

The cutoff is chosen before the buffer and mesh. Dropping an entire cell
costs at most the full kernel on z <= h + mesh, rather than z <= h.
The already proved uniform physical tail pays this actual loss. Every
retained cell then has a fixed positive third lower endpoint.

This is a continuous integral theorem for the newly constructed lookup.
Its signed arithmetic policy, factorization and arithmetic mean still need
their own proofs; no identity with the old arithmetic weights is claimed.
-/

namespace ImbalancedChen

noncomputable section

open Set Filter Topology MeasureTheory
open VariableEnvelope
open scoped Classical BigOperators ENNReal

def actualExtendedThirdCompactCellLoss (e h : ℝ) (m : ℕ) : ℝ≥0∞ :=
  ∫⁻ t in actualExtendedThirdClosedOrderRegion thirdPrefixRho,
    ENNReal.ofReal |actualExtendedThirdFiniteKernel e m t -
      actualExtendedThirdCompactCellKernel e h m t|

theorem actualExtendedThirdCompactCellLoss_le_tail {e h H : ℝ} {m : ℕ}
    (hmesh : h + actualExtendedThirdDyadicStep m ≤ H) :
    actualExtendedThirdCompactCellLoss e h m ≤ actualExtendedThirdFiniteClosedTailMass e m H := by
  let S := actualExtendedThirdClosedOrderRegion H
  have hS : MeasurableSet S := measurableSet_actualExtendedThirdClosedOrderRegion H
  calc
    actualExtendedThirdCompactCellLoss e h m ≤
        ∫⁻ t in actualExtendedThirdClosedOrderRegion thirdPrefixRho,
          S.indicator (fun t => ENNReal.ofReal |actualExtendedThirdFiniteKernel e m t|) t := by
      apply setLIntegral_mono' (measurableSet_actualExtendedThirdClosedOrderRegion thirdPrefixRho)
      intro t ht
      by_cases htS : t ∈ S
      · rw [indicator_of_mem htS]
        apply ENNReal.ofReal_le_ofReal
        obtain ⟨hc0, hcf⟩ := actualExtendedThirdCompactCellKernel_bounds (e := e) (h := h) (m := m) ht
        have hf0 := actualExtendedThirdFiniteKernel_nonneg (e := e) (m := m)
          ht.1 ht.2.2.1 ht.2.2.2.1
        rw [abs_of_nonneg (sub_nonneg.mpr hcf), abs_of_nonneg hf0]
        linarith
      · rw [indicator_of_notMem htS]
        have hz : H < t 2 := by
          by_contra hn
          exact htS ⟨ht.1, le_of_not_gt hn, ht.2.2.1, ht.2.2.2.1, ht.2.2.2.2⟩
        rw [actualExtendedThirdCompactCellKernel_eq_full (hmesh.trans hz.le),
          sub_self, abs_zero, ENNReal.ofReal_zero]
    _ = ∫⁻ t in S ∩ actualExtendedThirdClosedOrderRegion thirdPrefixRho,
        ENNReal.ofReal |actualExtendedThirdFiniteKernel e m t| := by
      rw [lintegral_indicator hS, Measure.restrict_restrict hS]
    _ ≤ actualExtendedThirdFiniteClosedTailMass e m H :=
      lintegral_mono_set Set.inter_subset_left

theorem actualExtendedThirdCompactCellFunctional_abs_sub_le {e h : ℝ}
    (he0 : 0 ≤ e) (he : e ≤ 1 / 384) (m : ℕ) :
    |actualExtendedThirdFiniteFunctional e m - actualExtendedThirdCompactCellFunctional e h m| ≤
      (actualExtendedThirdCompactCellLoss e h m).toReal := by
  unfold actualExtendedThirdFiniteFunctional actualExtendedThirdCompactCellFunctional
  rw [← integral_sub (integrableOn_actualExtendedThirdFiniteKernel_full he0 he m)
    (integrableOn_actualExtendedThirdCompactCellKernel he0 he)]
  simpa only [actualExtendedThirdCompactCellLoss, Real.norm_eq_abs] using
    norm_integral_le_lintegral_norm
      (μ := volume.restrict (actualExtendedThirdClosedOrderRegion thirdPrefixRho))
      (fun t : Fin 3 → ℝ => actualExtendedThirdFiniteKernel e m t -
        actualExtendedThirdCompactCellKernel e h m t)

/-- Fixed positive lower endpoints suffice for arbitrarily accurate recovery
of the same unbuffered functional; the mesh is chosen after this cutoff. -/
theorem actualExtendedThirdCompactCellFunctional_uniform_approx {ε : ℝ} (hε : 0 < ε) :
    ∃ h : ℝ, 0 < h ∧ ∃ e₀ : ℝ, 0 < e₀ ∧ e₀ ≤ 1 / 384 ∧ ∃ m₀ : ℕ,
      ∀ e : ℝ, 0 ≤ e → e ≤ e₀ → ∀ m : ℕ, m₀ ≤ m →
        |actualExtendedThirdCompactCellFunctional e h m - actualExtendedThirdIdealFunctional| ≤ ε := by
  obtain ⟨H, hH, _hHcap, htail⟩ :=
    actualExtendedThirdFiniteClosedTailMass_uniform_small (half_pos hε)
  obtain ⟨e₀, he₀, he₀cap, m₁, hfull⟩ :=
    actualExtendedThirdFiniteFunctional_uniform_approx (half_pos hε)
  obtain ⟨m₂, hm₂⟩ := Filter.eventually_atTop.mp
    (tendsto_actualExtendedThirdDyadicStep.eventually (gt_mem_nhds (half_pos hH)))
  refine ⟨H / 2, half_pos hH, e₀, he₀, he₀cap, max m₁ m₂, ?_⟩
  intro e he0 he m hm
  have hecap : e ≤ 1 / 384 := he.trans he₀cap
  have hmesh : H / 2 + actualExtendedThirdDyadicStep m ≤ H := by
    have hsmall := hm₂ m ((le_max_right _ _).trans hm)
    linarith
  have hloss : actualExtendedThirdCompactCellLoss e (H / 2) m ≤ ENNReal.ofReal (ε / 2) :=
    (actualExtendedThirdCompactCellLoss_le_tail hmesh).trans (htail e he0 hecap m)
  have hdiff : |actualExtendedThirdFiniteFunctional e m -
      actualExtendedThirdCompactCellFunctional e (H / 2) m| ≤ ε / 2 := by
    apply (actualExtendedThirdCompactCellFunctional_abs_sub_le he0 hecap m).trans
    calc
      _ ≤ (ENNReal.ofReal (ε / 2)).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hloss
      _ = ε / 2 := ENNReal.toReal_ofReal (half_pos hε).le
  calc
    |actualExtendedThirdCompactCellFunctional e (H / 2) m - actualExtendedThirdIdealFunctional| ≤
        |actualExtendedThirdCompactCellFunctional e (H / 2) m - actualExtendedThirdFiniteFunctional e m| +
          |actualExtendedThirdFiniteFunctional e m - actualExtendedThirdIdealFunctional| :=
      abs_sub_le _ _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add (by simpa only [abs_sub_comm] using hdiff)
      (hfull e he0 he m ((le_max_left _ _).trans hm))
    _ = ε := by ring

theorem actualExtendedThirdCompactCellIntegral_sum_uniform_approx {ε : ℝ} (hε : 0 < ε) :
    ∃ h : ℝ, 0 < h ∧ ∃ e₀ : ℝ, 0 < e₀ ∧ e₀ ≤ 1 / 384 ∧ ∃ m₀ : ℕ,
      ∀ e : ℝ, 0 ≤ e → e ≤ e₀ → ∀ m : ℕ, m₀ ≤ m →
        |(∑ j ∈ actualExtendedThirdCompactCells e h m, actualExtendedThirdRetainedCellIntegral e m j) -
          actualExtendedThirdIdealFunctional| ≤ ε := by
  obtain ⟨h, hh, e₀, he₀, he₀cap, m₀, hb⟩ :=
    actualExtendedThirdCompactCellFunctional_uniform_approx hε
  refine ⟨h, hh, e₀, he₀, he₀cap, m₀, ?_⟩
  intro e he0 he m hm
  rw [← actualExtendedThirdCompactCellFunctional_eq_sum_cells he0 (he.trans he₀cap) m]
  exact hb e he0 he m hm

end

end ImbalancedChen
