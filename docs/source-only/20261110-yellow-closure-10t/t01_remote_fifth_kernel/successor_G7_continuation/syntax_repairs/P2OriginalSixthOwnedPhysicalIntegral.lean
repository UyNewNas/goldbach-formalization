import ImbalancedChen.P2OriginalSixthCrossCellOwnership

/-! SOURCE_ONLY / UNEVALUATED / UNCOMPILED.
All ownership removals below are proved null from the actual original
source walls and cross-cell intersections. No positive-volume source is
discarded, no new small cell is substituted, and no old endpoint is added.
The resulting integral is a single, explicitly dispatched original G7
physical density. This is still before the separate prime-history mean.
-/
namespace ImbalancedChen.P2OriginalSixthOwnedPhysicalIntegral
noncomputable section
open Set MeasureTheory
open scoped Classical BigOperators
open P2OriginalSixthMomentRow (Point)
open P2OriginalSixthLogArchive (archive sourceCell)
open P2OriginalSixthPullingUnion (eval originalInnerUnion)
theorem inner_measurable (i : Fin 11) : MeasurableSet (originalInnerUnion i) := by
  apply MeasurableSet.iUnion
  intro s
  exact P2OriginalSixthSimplexMoments.support_measurable _ _

theorem walls_measurable (i : Fin 11) : MeasurableSet (ImbalancedChen.P2OriginalSixthInnerPhysicalCell.walls i) := by
  apply MeasurableSet.iUnion
  intro g
  cases hg : g.strict
  · simp [hg]
  · simp only [hg,if_true]
    apply IsClosed.measurableSet
    apply isClosed_eq _ continuous_const
    simp only [ImbalancedChen.P2OriginalSixthPullingUnion.eval_eq_affine]
    fun_prop

def boundary : Set Point :=
  (⋃ i : Fin 11, ImbalancedChen.P2OriginalSixthInnerPhysicalCell.walls i) ∪
    ⋃ i : Fin 11, ⋃ j : Fin 11, if i=j then ∅ else originalInnerUnion i ∩ originalInnerUnion j

theorem boundary_null : volume boundary=0 := by
  apply measure_union_null
  · exact measure_iUnion_null ImbalancedChen.P2OriginalSixthInnerPhysicalCell.walls_null
  · apply measure_iUnion_null
    intro i
    apply measure_iUnion_null
    intro j
    by_cases hij : i=j
    · simp [hij]
    · simp only [if_neg hij]
      exact ImbalancedChen.P2OriginalSixthCrossCellOwnership.original_inner_unions_pairwise_null hij

theorem boundary_measurable : MeasurableSet boundary := by
  apply MeasurableSet.union (MeasurableSet.iUnion walls_measurable)
  apply MeasurableSet.iUnion
  intro i
  apply MeasurableSet.iUnion
  intro j
  by_cases hij : i=j
  · simp [hij]
  · simp only [if_neg hij]
    exact (inner_measurable i).inter (inner_measurable j)

def owned (i : Fin 11) : Set Point := originalInnerUnion i \ boundary

theorem owned_measurable (i : Fin 11) : MeasurableSet (owned i) :=
  (inner_measurable i).diff boundary_measurable

theorem owned_subset_physicalCell (i : Fin 11) : owned i ⊆ {t | ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.PhysicalCell (sourceCell i) t} := by
  rintro t ⟨ht,hb⟩
  apply ImbalancedChen.P2OriginalSixthInnerPhysicalCell.innerUnion_off_walls_physicalCell i
  refine ⟨ht,?_⟩
  intro hw
  exact hb (Or.inl (mem_iUnion.mpr ⟨i,hw⟩))

theorem owned_pairwise_disjoint : Pairwise (fun i j : Fin 11 => Disjoint (owned i) (owned j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  rintro t ⟨hi,hb⟩ ⟨hj,_⟩
  apply hb
  exact Or.inr (mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨j,by simpa only [if_neg hij] using And.intro hi hj⟩⟩)

theorem owned_ae_inner (i : Fin 11) : owned i =ᵐ[volume] originalInnerUnion i := by
  have hne : ∀ᵐ t : Point ∂volume, t ∉ boundary := by
    rw [ae_iff]
    simpa only [not_not] using boundary_null
  filter_upwards [hne] with t ht
  simp [owned,ht]

theorem owned_integral_eq (i : Fin 11) :
    ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.sourceIntegral (sourceCell i) (owned i)=ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.sourceIntegral (sourceCell i) (originalInnerUnion i) :=
  setIntegral_congr_set (owned_ae_inner i)

private theorem integrableOn_finite_union {ι : Type*} (F : Point → ℝ) (A : ι → Set Point)
    (s : Finset ι) (h : ∀ i ∈ s, IntegrableOn F (A i)) : IntegrableOn F (⋃ i ∈ s,A i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      have hs := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
      have he : (⋃ j ∈ insert i s,A j)=A i ∪ ⋃ j ∈ s,A j := by ext t; simp
      rw [he]
      exact (h i (Finset.mem_insert_self _ _)).union hs

theorem inner_kernel_integrable (i : Fin 11) :
    IntegrableOn (ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.savingKernel (sourceCell i)) (originalInnerUnion i) := by
  have h := integrableOn_finite_union (ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.savingKernel (sourceCell i))
    (P2OriginalSixthSimplexFloorIntegral.support i) (Finset.univ : Finset (Fin (archive i).simplices.size))
    (fun s _ => ImbalancedChen.P2OriginalSixthPullingUnion.kernel_integrable_on_row i s)
  simpa [originalInnerUnion] using h

theorem owned_kernel_integrable (i : Fin 11) : IntegrableOn (ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.savingKernel (sourceCell i)) (owned i) :=
  (inner_kernel_integrable i).mono_set Set.diff_subset

/-- One actual physical source density, with unique cell away from the
proved null original boundaries. The coefficient remains exactly4. -/
def density (t : Point) : ℝ := ∑ i : Fin 11, (owned i).indicator (ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.savingKernel (sourceCell i)) t

theorem density_nonneg (t : Point) : 0 ≤ density t := by
  apply Finset.sum_nonneg
  intro i _
  by_cases ht : t ∈ owned i
  · rw [Set.indicator_of_mem ht]
    exact (ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.PhysicalCell.savingKernel_pos (owned_subset_physicalCell i ht)).le
  · simp only [Set.indicator_of_not_mem ht,le_refl]

theorem density_integrable : Integrable density volume := by
  exact integrable_finsetSum Finset.univ (fun i _ =>
    (owned_kernel_integrable i).integrable_indicator (owned_measurable i))

theorem integral_density : (∫ t : Point,density t)=
    ∑ i : Fin 11, ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.sourceIntegral (sourceCell i) (originalInnerUnion i) := by
  unfold density
  rw [integral_finsetSum Finset.univ (fun i _ =>
    (owned_kernel_integrable i).integrable_indicator (owned_measurable i))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_indicator (owned_measurable i)]
  exact owned_integral_eq i

/-- Full original G7 replacement endpoint on a single true physical
source density, with all2631 genuine6D simplex volumes retained. -/
theorem original_G7_physical_floor :
    (1208544915921356327515701 : ℝ)/(2:ℝ)^96 ≤ ∫ t : Point,density t := by
  rw [integral_density]
  exact ImbalancedChen.P2OriginalSixthPullingUnion.original_all2631_inner_union_floor

end
end ImbalancedChen.P2OriginalSixthOwnedPhysicalIntegral
