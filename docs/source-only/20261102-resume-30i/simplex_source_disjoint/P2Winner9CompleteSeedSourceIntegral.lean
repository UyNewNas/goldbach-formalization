import ImbalancedChen.P2Winner9CompleteSeedNullOverlaps
import ImbalancedChen.P2Winner9CompleteSeedSelectedFloors

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The whole11026 analytic lower floors are now consumed on one legal subset
of the independently specified original physical minorant cell. The subset
has disjoint pieces, and the removed source/overlap walls have zero volume.
Full coverage is unnecessary for this positive saving and is NOT asserted.
Actual causal finite-policy/count/mean compilation remains a separate task.
-/
namespace ImbalancedChen.P2Winner9CompleteSeedSourceIntegral

noncomputable section
open Set MeasureTheory
open scoped BigOperators
open P2Winner9CompleteSeedData P2Winner9CompleteSeedPositiveDomains
open P2Winner9CompleteSeedSourceGates P2Winner9CompleteSeedNullOverlaps
open P2Winner9CompleteSeedGapReserve P2Winner9CompleteSeedSelectedFloors
open P2Winner9SelectedRowAnalyticCaps P2Winner9PhysicalAffineTransfer

theorem originalClosedSource_isClosed : IsClosed originalClosedSource := by
  change IsClosed {x : Ambient | ∀ g : Gate, 0 ≤ (gate g).eval x}
  simp only [setOf_forall]
  exact isClosed_iInter (fun g => isClosed_le continuous_const (gate g).continuous)

theorem originalPhysicalSource_measurable : MeasurableSet originalPhysicalSource := by
  change MeasurableSet {x : Ambient | ∀ g : Gate, 0 < (gate g).eval x}
  simp only [setOf_forall]
  exact MeasurableSet.iInter (fun g =>
    (isOpen_lt continuous_const (gate g).continuous).measurableSet)

theorem originalPhysicalSource_subset_closed : originalPhysicalSource ⊆ originalClosedSource :=
  fun _ hx g => (hx g).le

/-- The compact lower cutoff is the actual 53/13824, with the original
largest-slot ceiling 25/128; no smaller source domain is substituted. -/
theorem closed_source_coordinate_bounds {x : Ambient} (hx : x ∈ originalClosedSource)
    (j : Fin 8) : 53/13824 ≤ x j ∧ x j ≤ 25/128 := by
  have hlo : (53/13824 : ℝ) ≤ x 7 := by
    simpa [gate] using hx .eighth
  have hhi : x 0 ≤ (25/128 : ℝ) := by
    simpa [gate] using hx .largest
  have ho (k : Fin 7) : x k.succ ≤ x k.castSucc := by
    simpa [gate] using hx (.order k)
  fin_cases j <;>
    simp only [Fin.succ_mk, Fin.castSucc_mk] at * <;>
    constructor <;> linarith [ho 0, ho 1, ho 2, ho 3, ho 4, ho 5, ho 6]

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
    have h := hx .improvement
    simpa [gate, M_is_original, R_is_original] using h
  have hr : x 7 ≤ physicalR x - coordinateSum x := by
    have h := hx .oldResidual
    simpa [gate, R_is_original, S_is_original] using h
  exact ⟨by unfold physicalGap; linarith, hr, by linarith⟩

theorem closed_source_factor_lower {x : Ambient} (hx : x ∈ originalClosedSource)
    (j : Fin 10) : (53/13824 : ℝ) ≤ physicalFactor j x := by
  have hl := (closed_source_coordinate_bounds hx 7).1
  obtain ⟨_, hr, hm⟩ := closed_source_cap_bounds hx
  refine Fin.cases ?_ (fun j => ?_) j
  · simpa only [physicalFactor_zero] using hl.trans hr
  · refine Fin.cases ?_ (fun j => ?_) j
    · simpa only [physicalFactor_one] using hl.trans hm
    · simpa only [physicalFactor_succ_succ] using (closed_source_coordinate_bounds hx j).1

theorem original_source_density_integrable :
    IntegrableOn physicalUpperIntegrand originalPhysicalSource := by
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
  exact (hc.integrableOn_compact originalClosedSource_compact).mono_set
    originalPhysicalSource_subset_closed

theorem original_source_density_nonneg {x : Ambient} (hx : x ∈ originalPhysicalSource) :
    0 ≤ physicalUpperIntegrand x := by
  have hclosed := originalPhysicalSource_subset_closed hx
  unfold physicalUpperIntegrand
  apply div_nonneg
  · exact mul_nonneg (by norm_num) (closed_source_cap_bounds hclosed).1
  · exact Finset.prod_nonneg (fun j _ =>
      le_trans (by norm_num : (0 : ℝ) ≤ 53/13824) (closed_source_factor_lower hclosed j))

def legalSelectedSource : Set Ambient := ⋃ i : RowIndex, legalOwnedSupport i
def originalSourceSaving : ℝ := ∫ x in originalPhysicalSource, physicalUpperIntegrand x

theorem legalSelectedSource_subset_original : legalSelectedSource ⊆ originalPhysicalSource := by
  intro x hx
  obtain ⟨i, hi⟩ := mem_iUnion.mp hx
  exact legalOwnedSupport_subset_source i hi

theorem legalOwnedSupport_integral (i : RowIndex) :
    (∫ x in legalOwnedSupport i, physicalUpperIntegrand x) = fullMass i := by
  exact setIntegral_congr_set (legalOwnedSupport_ae_eq i)

/-- Exact finite additive ownership of the genuine physical integrals. -/
theorem legalSelectedSource_integral :
    (∫ x in legalSelectedSource, physicalUpperIntegrand x) = ∑ i : RowIndex, fullMass i := by
  rw [legalSelectedSource, integral_iUnion_fintype legalOwnedSupport_measurable
    legalOwnedSupport_pairwise_disjoint
    (fun i => (all_actual_density_integrable i).mono_set sdiff_subset)]
  exact Finset.sum_congr rfl (fun i _ => legalOwnedSupport_integral i)

/-- No coverage claim is needed: the direction is a lower bound for a
positive saving, so any legal disjoint subset supplies this inequality. -/
theorem full_physical_row_sum_le_original :
    (∑ i : RowIndex, fullMass i) ≤ originalSourceSaving := by
  rw [← legalSelectedSource_integral]
  apply setIntegral_mono_set original_source_density_integrable
  · filter_upwards [ae_restrict_mem originalPhysicalSource_measurable] with x hx
    exact original_source_density_nonneg hx
  · exact Filter.Eventually.of_forall legalSelectedSource_subset_original

/-- Actual whole11026 selected floor consumer. Its premises do not contain
a row enclosure, a physical cover, a source-equality or a disjointness
certificate. The explicit finite source proof bodies in both I tasks are
still unexecuted; this is not a kernel-verified numerical certificate. -/
theorem all_original_selected_floors_on_original_source :
    (∑ i : RowIndex, ((entry i).mixedSelected : ℝ) /
      (P2Winner9CompleteSeedMomentDecoder.q96 : ℝ)) ≤ originalSourceSaving := by
  exact (Finset.sum_le_sum (fun i _ => all_original_selected_floors i)).trans
    full_physical_row_sum_le_original

end
end ImbalancedChen.P2Winner9CompleteSeedSourceIntegral
