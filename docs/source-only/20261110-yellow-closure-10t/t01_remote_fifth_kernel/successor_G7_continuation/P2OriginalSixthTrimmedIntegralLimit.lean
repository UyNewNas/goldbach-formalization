import ImbalancedChen.P2OriginalSixthCompactTrim
import ImbalancedChen.P1QuantizedActionLicense
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! SOURCE_ONLY / UNEVALUATED / UNCOMPILED.
The ACTUAL compact trims exhaust the original owned physical density
away from the proved null walls. Dominated convergence recovers the full
original Q96 endpoint up to any positive tolerance. No omitted-mass or
trim-floor licence is an input, and none of the2631 volumes is replaced.
-/
namespace ImbalancedChen.P2OriginalSixthTrimmedIntegralLimit
noncomputable section
open Set Filter MeasureTheory
open scoped Classical BigOperators Topology
open P2OriginalSixthMomentRow (Point)
open P2OriginalSixthLogArchive (sourceCell)
open P2OriginalSixthPullingUnion (eval originalInnerUnion)
open P2OriginalSixthCompactTrim (trim trim_antitone trim_subset_source)
open P2OriginalSixthOwnedPhysicalIntegral (owned boundary density)
open P4AOriginalFull87HistoryCore (width width_pos width_tendsto)
open Certificates.P2OriginalSixthElevenLogSemantics (PhysicalCell savingKernel sourceIntegral)

theorem source_mem_some_trim {i : Fin 11} {t : Point}
    (hi : t∈originalInnerUnion i) (hc : PhysicalCell (sourceCell i) t) :
    ∃ delta : ℝ, 0<delta ∧ t∈trim i delta := by
  have hv := (P2OriginalSixthPhysicalGateRows.physicalCell_iff_rows (sourceCell i) t).mp hc
  obtain ⟨delta,hdelta,hfloor⟩ := P1QuantizedActionLicense.exists_positive_floor
    (Finset.univ : Finset P2OriginalSixthPhysicalGateRows.Gate) (fun g => g.strict=true)
    (fun g => eval (P2OriginalSixthPhysicalGateRows.row (sourceCell i) g) t)
    (fun g _ hg => by simpa only [hg,if_true] using hv g)
  refine ⟨delta,hdelta,hi,?_⟩
  intro g
  cases hg : g.strict
  · simpa only [hg,if_false] using hv g
  · simpa only [hg,if_true] using hfloor g (Finset.mem_univ _) hg

theorem source_eventually_in_trim {i : Fin 11} {t : Point}
    (hi : t∈originalInnerUnion i) (hc : PhysicalCell (sourceCell i) t) :
    ∀ᶠ n : ℕ in atTop,t∈trim i (width n) := by
  obtain ⟨delta,hdelta,ht⟩ := source_mem_some_trim hi hc
  filter_upwards [width_tendsto.eventually (gt_mem_nhds hdelta)] with n hn
  exact trim_antitone i hn.le ht

def trimmedDensity (n : ℕ) (t : Point) : ℝ :=
  ∑ i : Fin 11,(trim i (width n)).indicator (savingKernel (sourceCell i)) t

theorem indicator_eventually_eq {t : Point} (hb : t∉boundary) (i : Fin 11) :
    ∀ᶠ n : ℕ in atTop,(trim i (width n)).indicator (savingKernel (sourceCell i)) t=
      (owned i).indicator (savingKernel (sourceCell i)) t := by
  by_cases hi : t∈originalInnerUnion i
  · have ho : t∈owned i := ⟨hi,hb⟩
    have hc := P2OriginalSixthOwnedPhysicalIntegral.owned_subset_physicalCell i ho
    filter_upwards [source_eventually_in_trim hi hc] with n hn
    simp only [Set.indicator_of_mem hn,Set.indicator_of_mem ho]
  · have ho : t∉owned i := fun h => hi h.1
    exact Filter.Eventually.of_forall (fun n => by
      have ht : t∉trim i (width n) := fun h => hi h.1
      simp only [Set.indicator_of_not_mem ht,Set.indicator_of_not_mem ho])

theorem trimmed_kernel_integrable (i : Fin 11) (n : ℕ) :
    IntegrableOn (savingKernel (sourceCell i)) (trim i (width n)) :=
  (P2OriginalSixthOwnedPhysicalIntegral.inner_kernel_integrable i).mono_set (fun _ ht => ht.1)

theorem trimmed_density_integrable (n : ℕ) : Integrable (trimmedDensity n) volume :=
  integrable_finsetSum Finset.univ (fun i _ => (trimmed_kernel_integrable i n).integrable_indicator
    (P2OriginalSixthCompactTrim.trim_compact i (width n)).measurableSet)

theorem trimmed_norm_bound (n : ℕ) {t : Point} (hb : t∉boundary) : ‖trimmedDensity n t‖≤density t := by
  have hh (i : Fin 11) :
      0≤(trim i (width n)).indicator (savingKernel (sourceCell i)) t ∧
      (trim i (width n)).indicator (savingKernel (sourceCell i)) t≤
        (owned i).indicator (savingKernel (sourceCell i)) t := by
    by_cases ht : t∈trim i (width n)
    · have ho : t∈owned i := ⟨ht.1,hb⟩
      have hk := (PhysicalCell.savingKernel_pos (trim_subset_source i (width_pos n) ht)).le
      simp only [Set.indicator_of_mem ht,Set.indicator_of_mem ho]
      exact ⟨hk,le_rfl⟩
    · simp only [Set.indicator_of_not_mem ht]
      refine ⟨le_rfl,?_⟩
      by_cases ho : t∈owned i
      · rw [Set.indicator_of_mem ho]
        exact (PhysicalCell.savingKernel_pos (P2OriginalSixthOwnedPhysicalIntegral.owned_subset_physicalCell i ho)).le
      · simp only [Set.indicator_of_not_mem ho,le_refl]
  have hn : 0≤trimmedDensity n t := Finset.sum_nonneg (fun i _ => (hh i).1)
  have hle : trimmedDensity n t≤density t := Finset.sum_le_sum (fun i _ => (hh i).2)
  simpa only [Real.norm_eq_abs,abs_of_nonneg hn] using hle

theorem trimmed_integral_tendsto :
    Tendsto (fun n : ℕ => ∫ t : Point,trimmedDensity n t) atTop (𝓝 (∫ t : Point,density t)) := by
  have hb : ∀ᵐ t : Point ∂volume,t∉boundary := by
    rw [ae_iff]
    simpa only [not_not] using P2OriginalSixthOwnedPhysicalIntegral.boundary_null
  apply tendsto_integral_of_dominated_convergence (μ:=volume) (F:=trimmedDensity) (f:=density) density
    (fun n => (trimmed_density_integrable n).aestronglyMeasurable)
    P2OriginalSixthOwnedPhysicalIntegral.density_integrable
  · intro n
    exact hb.mono (fun _ ht => trimmed_norm_bound n ht)
  · filter_upwards [hb] with t ht
    exact tendsto_finsetSum _ (fun i _ => tendsto_const_nhds.congr' (indicator_eventually_eq ht i).symm)

theorem integral_trimmedDensity (n : ℕ) :
    (∫ t : Point,trimmedDensity n t)=∑ i : Fin 11,sourceIntegral (sourceCell i) (trim i (width n)) := by
  unfold trimmedDensity
  rw [integral_finsetSum Finset.univ (fun i _ => (trimmed_kernel_integrable i n).integrable_indicator
    (P2OriginalSixthCompactTrim.trim_compact i (width n)).measurableSet)]
  apply Finset.sum_congr rfl
  intro i _
  exact integral_indicator (P2OriginalSixthCompactTrim.trim_compact i (width n)).measurableSet

/-- A concrete positive ORIGINAL trim carries all but epsilon of the
full2631 Q96 replacement endpoint. No numerical replay is used. -/
theorem exists_original_G7_trim_floor (epsilon : ℝ) (hepsilon : 0<epsilon) :
    ∃ delta : ℝ, 0<delta ∧
      (1208544915921356327515701 : ℝ)/(2:ℝ)^96-epsilon<
        ∑ i : Fin 11,sourceIntegral (sourceCell i) (trim i delta) := by
  have hh := trimmed_integral_tendsto.eventually (lt_mem_nhds (by
    have h := P2OriginalSixthOwnedPhysicalIntegral.original_G7_physical_floor
    linarith))
  obtain ⟨n,hn⟩ := hh.exists
  rw [integral_trimmedDensity] at hn
  exact ⟨width n,width_pos n,hn⟩

end
end ImbalancedChen.P2OriginalSixthTrimmedIntegralLimit
