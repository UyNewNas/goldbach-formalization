import ImbalancedChen.P2Winner9OriginalSourceGates

/-! Integrability and finite almost-disjoint lower bounds on the original Winner9 source. -/

namespace ImbalancedChen.P2Winner9OriginalSourceIntegral

noncomputable section

open Set MeasureTheory
open scoped BigOperators
open P2Winner9SeedVertexAnalyticGuards (VertexIndex originalPoint)
open P2Winner9SelectedRowRealJacobian (RationalVertices sourceSupport)
open P2Winner9SelectedRowAnalyticCaps (continuous_physicalGap continuous_physicalFactor)
open P2Winner9PhysicalAffineTransfer
open P2Winner9OriginalSourceGates

theorem originalClosedSource_isClosed : IsClosed originalClosedSource := by
  unfold originalClosedSource
  simp only [Set.ofPred_forall]
  exact isClosed_iInter (fun g => isClosed_le continuous_const (gate g).continuous)

theorem originalPhysicalSource_subset_closed : originalPhysicalSource ⊆ originalClosedSource :=
  fun _ hx g => (hx g).le

theorem closed_source_coordinate_bounds {x : Ambient} (hx : x ∈ originalClosedSource)
    (j : Fin 8) : 53/13824 ≤ x j ∧ x j ≤ 25/128 := by
  have hlo : (53/13824 : ℝ) ≤ x 7 := by
    simpa [gate, sub_nonneg] using hx .eighth
  have hhi : x 0 ≤ (25/128 : ℝ) := by
    simpa [gate, sub_nonneg] using hx .largest
  have ho (k : Fin 7) : x k.succ ≤ x k.castSucc := by
    simpa [gate, sub_nonneg] using hx (.order k)
  have ha : Antitone x := Fin.antitone_iff_succ_le.mpr ho
  exact ⟨hlo.trans (ha (Fin.le_last j)), (ha (Fin.zero_le j)).trans hhi⟩

theorem originalClosedSource_compact : IsCompact originalClosedSource := by
  apply (isCompact_Icc : IsCompact
    (Icc (fun _ : Fin 8 => (53/13824 : ℝ)) (fun _ => (25/128 : ℝ)))).of_isClosed_subset
    originalClosedSource_isClosed
  intro x hx
  exact ⟨fun j => (closed_source_coordinate_bounds hx j).1,
    fun j => (closed_source_coordinate_bounds hx j).2⟩

theorem S_is_original (x : Ambient) : S.eval x = coordinateSum x := by
  simp [S, Row.sum, Row.eval, coordinateSum]

theorem closed_source_cap_bounds {x : Ambient} (hx : x ∈ originalClosedSource) :
    0 ≤ physicalGap x ∧ x 7 ≤ physicalR x - coordinateSum x ∧
      x 7 ≤ physicalM x - coordinateSum x := by
  have hg : physicalR x ≤ physicalM x := by
    simpa [gate, M_is_original, R_is_original, sub_nonneg] using hx .improvement
  have hr : x 7 ≤ physicalR x - coordinateSum x := by
    simpa [gate, R_is_original, S_is_original, sub_nonneg] using hx .oldResidual
  exact ⟨by simpa [physicalGap] using sub_nonneg.mpr hg, hr, by linarith⟩

theorem closed_source_factor_lower {x : Ambient} (hx : x ∈ originalClosedSource)
    (j : Fin 10) : (53/13824 : ℝ) ≤ physicalFactor j x := by
  have hl := (closed_source_coordinate_bounds hx 7).1
  obtain ⟨_, hr, hm⟩ := closed_source_cap_bounds hx
  refine Fin.cases ?_ (fun j => ?_) j
  · simpa only [physicalFactor_zero] using hl.trans hr
  · refine Fin.cases ?_ (fun j => ?_) j
    · change (53/13824 : ℝ) ≤ physicalFactor 1 x
      simpa only [physicalFactor_one] using hl.trans hm
    · simpa only [physicalFactor_succ_succ] using (closed_source_coordinate_bounds hx j).1

theorem original_closed_source_density_integrable :
    IntegrableOn physicalUpperIntegrand originalClosedSource := by
  have hfac : ∀ j : Fin 10, Continuous (physicalFactor j) := continuous_physicalFactor
  have hc : ContinuousOn physicalUpperIntegrand originalClosedSource := by
    apply (continuous_const.mul continuous_physicalGap).continuousOn.div
      (show Continuous (fun x : Ambient => ∏ j : Fin 10, physicalFactor j x) by
        fun_prop).continuousOn
    intro x hx
    apply ne_of_gt
    apply Finset.prod_pos
    intro j _
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 53/13824)
      (closed_source_factor_lower hx j)
  exact hc.integrableOn_compact originalClosedSource_compact

theorem original_source_density_integrable :
    IntegrableOn physicalUpperIntegrand originalPhysicalSource :=
  original_closed_source_density_integrable.mono_set originalPhysicalSource_subset_closed

theorem original_source_density_nonneg {x : Ambient} (hx : x ∈ originalPhysicalSource) :
    0 ≤ physicalUpperIntegrand x := by
  have hclosed := originalPhysicalSource_subset_closed hx
  unfold physicalUpperIntegrand
  apply div_nonneg
  · exact mul_nonneg (by norm_num) (closed_source_cap_bounds hclosed).1
  · exact Finset.prod_nonneg (fun j _ =>
      le_trans (by norm_num : (0 : ℝ) ≤ 53/13824) (closed_source_factor_lower hclosed j))

/-- The original integral bounds any finite, almost-disjoint family of
simplices with vertices in the original table. -/
theorem sum_source_integrals_le_original {ι : Type*} [Fintype ι]
    (v : ι → RationalVertices) (ids : ι → Fin 9 → VertexIndex)
    (hvertex : ∀ i k, v i k = originalPoint (ids i k))
    (hshape : ∀ i, MeasurableSet (sourceSupport (v i)))
    (hdisjoint : Pairwise (fun i j => volume (sourceSupport (v i) ∩ sourceSupport (v j)) = 0)) :
    (∑ i, ∫ x in sourceSupport (v i), physicalUpperIntegrand x) ≤
      ∫ x in originalPhysicalSource, physicalUpperIntegrand x := by
  classical
  have hsub : (⋃ i, sourceSupport (v i)) ⊆ originalClosedSource := by
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    exact all_supports_in_closed_source (v i) (ids i) (hvertex i) hi
  have hnull : ∀ᵐ x : Ambient ∂volume, x ∉ sourceWalls := by
    rw [ae_iff]
    simpa only [not_not, Set.ofPred_mem_eq] using sourceWalls_null
  have hae : (⋃ i, sourceSupport (v i)) ≤ᵐ[volume] originalPhysicalSource := by
    filter_upwards [hnull] with x hx
    intro hx'
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx'
    exact support_off_walls_in_original_source (v i) (ids i) (hvertex i) ⟨hi, hx⟩
  calc
    (∑ i, ∫ x in sourceSupport (v i), physicalUpperIntegrand x) =
        ∫ x in ⋃ i, sourceSupport (v i), physicalUpperIntegrand x := by
      rw [integral_iUnion_ae (fun i => (hshape i).nullMeasurableSet) hdisjoint
        (original_closed_source_density_integrable.mono_set hsub), tsum_fintype]
    _ ≤ _ := by
      apply setIntegral_mono_set original_source_density_integrable _ hae
      filter_upwards [ae_restrict_mem originalPhysicalSource_measurable] with x hx
      exact original_source_density_nonneg hx

end
end ImbalancedChen.P2Winner9OriginalSourceIntegral
