import ImbalancedChen.P2OriginalSaving15RadialFastBounds

/-! SOURCE_ONLY / UNEVALUATED / UNCOMPILED.
The SAME original stage15 Source integral and once-floored endpoint,
using the determinant-free scalar guards of the separate supplement.
The frozen slow RadialIntegral is intentionally absent from imports.
Physical rows, affine source gates and all four null-separator proofs
are reused. Only the cheap width-nonzero finite index is enumerated.
-/
namespace ImbalancedChen.P2OriginalSaving15RadialFastIntegral
noncomputable section
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Set MeasureTheory
open scoped Classical BigOperators
open P2OriginalSaving15RadialArchive
open P2OriginalSaving15RadialProfile (seedCell actualPieceRow actual_piece_density piece_vertex_closed_rows)
open P2OriginalSaving15RadialFastBounds
open P2OriginalSaving16OriginalArchive (castPoint)
open P2OriginalPhysicalSimplexMomentRow (row_vertices)
open P2OriginalPhysicalSimplexJensenRow (rowJensenQ row_unrounded_jensen_sound)
open P4AOriginalFull87StrictActionTrim (sourceSet sourceSet_measurable)
open P4AOriginalFull87EighthKernelControl (kernel integrableOn_kernel kernel_bounds)
namespace Bary
export P2OriginalSaving19SimplexMoments
  (bary bary_nonneg vertices_interpolate support_measurable)
end Bary

def fastSupport (i : FastPiece) : Set (Fin 8 → ℝ) :=
  P2OriginalRadialPieceSeparation.pieceSupport (toOriginal i)
theorem fast_pairwise_null : Pairwise (fun i j : FastPiece => volume (fastSupport i ∩ fastSupport j) = 0) := by
  intro i j hij
  exact P2OriginalRadialPieceSeparation.piece_pairwise_null
    (fun he => hij (pieceEquiv.injective he))

abbrev evalRow := P2OriginalSaving16FourteenPhysicalAtlas.evalRow
def seedWalls : Set (Fin 8 → ℝ) := ⋃ g : Fin 96, {t | evalRow (seedRows g) t = 0}
theorem seed_gate_null (g : Fin 96) : volume {t : Fin 8 → ℝ | evalRow (seedRows g) t = 0} = 0 := by
  apply P2OriginalSaving19OwnedSource.affine_zero_volume
  refine ⟨P4AOriginalFull87KernelPositiveWitness.originalCentre seedCell,?_⟩
  have h := P4AOriginalFull87KernelPositiveWitness.originalCentre_mem_source seedCell
  exact (h g).ne'
theorem seedWalls_null : volume seedWalls = 0 := measure_iUnion_null seed_gate_null
theorem seedWalls_measurable : MeasurableSet seedWalls :=
  MeasurableSet.iUnion (fun g => (isClosed_eq
    (P2OriginalSaving16FourteenPhysicalAtlas.continuous_evalRow _) continuous_const).measurableSet)

theorem support_closed_rows (i : FastPiece) {t : Fin 8 → ℝ} (ht : t ∈ fastSupport i) (g : Fin 96) :
    0 ≤ evalRow (seedRows g) t := by
  obtain ⟨x,hx,rfl⟩ := ht
  rw [← Bary.vertices_interpolate,P2OriginalSaving19OwnedSource.eval_interpolate,row_vertices]
  change 0 ≤ ∑ j : Fin 9, Bary.bary j x * evalRow (seedRows g) (castPoint ((fastRow i).verticesQ j))
  apply Finset.sum_nonneg
  intro j _
  apply mul_nonneg (Bary.bary_nonneg hx j)
  rw [P2OriginalSaving15RadialProfile.evalQ_cast]
  exact_mod_cast piece_vertex_closed_rows i.val.1 i.val.2.1 i.val.2.2.1 i.val.2.2.2 j g

theorem support_off_walls_source (i : FastPiece) : fastSupport i \ seedWalls ⊆ sourceSet seedCell := by
  rintro t ⟨ht,hw⟩ g
  have hge := support_closed_rows i ht g
  have hne : evalRow (seedRows g) t ≠ 0 := fun he => hw (mem_iUnion.mpr ⟨g,he⟩)
  exact hge.lt_of_ne hne.symm

def overlapSet : Set (Fin 8 → ℝ) :=
  ⋃ i : FastPiece, ⋃ j : FastPiece, if i = j then ∅ else fastSupport i ∩ fastSupport j
def exceptionalSet : Set (Fin 8 → ℝ) := seedWalls ∪ overlapSet
def ownedSupport (i : FastPiece) : Set (Fin 8 → ℝ) := fastSupport i \ exceptionalSet
theorem overlapSet_null : volume overlapSet = 0 := by
  apply measure_iUnion_null
  intro i
  apply measure_iUnion_null
  intro j
  by_cases hij : i = j
  · simp [hij]
  · simp only [if_neg hij]
    exact fast_pairwise_null hij
theorem exceptionalSet_null : volume exceptionalSet = 0 := measure_union_null seedWalls_null overlapSet_null
theorem fastSupport_measurable (i : FastPiece) : MeasurableSet (fastSupport i) := Bary.support_measurable _ _
theorem exceptionalSet_measurable : MeasurableSet exceptionalSet := by
  apply seedWalls_measurable.union
  apply MeasurableSet.iUnion
  intro i
  apply MeasurableSet.iUnion
  intro j
  by_cases hij : i = j
  · simp [hij]
  · simp only [if_neg hij]
    exact (fastSupport_measurable i).inter (fastSupport_measurable j)
theorem ownedSupport_measurable (i : FastPiece) : MeasurableSet (ownedSupport i) :=
  (fastSupport_measurable i).diff exceptionalSet_measurable
theorem ownedSupport_source (i : FastPiece) : ownedSupport i ⊆ sourceSet seedCell := by
  rintro t ⟨ht,hw⟩
  exact support_off_walls_source i ⟨ht,fun h => hw (Or.inl h)⟩
theorem ownedSupport_integrable (i : FastPiece) : IntegrableOn (kernel seedCell) (ownedSupport i) :=
  (integrableOn_kernel seedCell).mono_set (ownedSupport_source i)
theorem ownedSupport_pairwise_disjoint : Pairwise (fun i j : FastPiece => Disjoint (ownedSupport i) (ownedSupport j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  rintro t ⟨hti,he⟩ ⟨htj,_⟩
  apply he
  right
  exact mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨j,by simpa only [if_neg hij] using And.intro hti htj⟩⟩
theorem ownedSupport_ae (i : FastPiece) : ownedSupport i =ᵐ[volume] fastSupport i := by
  have hn : ∀ᵐ t : Fin 8 → ℝ ∂volume, t ∉ exceptionalSet := by
    rw [ae_iff]
    simpa only [not_not] using exceptionalSet_null
  filter_upwards [hn] with t ht
  simp [ownedSupport,ht]
theorem ownedSupport_integral (i : FastPiece) :
    (∫ t in ownedSupport i, kernel seedCell t) = ∫ t in fastSupport i, kernel seedCell t :=
  setIntegral_congr_set (ownedSupport_ae i)

theorem sum_fast_integrals_le_source :
    (∑ i : FastPiece, ∫ t in fastSupport i, kernel seedCell t) ≤ ∫ t in sourceSet seedCell, kernel seedCell t := by
  have hu := integral_iUnion_fintype ownedSupport_measurable ownedSupport_pairwise_disjoint ownedSupport_integrable
  simp_rw [ownedSupport_integral] at hu
  rw [← hu]
  apply setIntegral_mono_set (integrableOn_kernel seedCell)
  · filter_upwards [ae_restrict_mem (sourceSet_measurable seedCell)] with t ht
    exact (kernel_bounds ht).1
  · exact Filter.Eventually.of_forall (iUnion_subset ownedSupport_source)

theorem fast_jensen_le_kernel_integral (i : FastPiece) :
    (rowJensenQ (fastRow i) : ℝ) ≤ ∫ t in fastSupport i, kernel seedCell t := by
  have h := row_unrounded_jensen_sound (fastRow i)
  change (rowJensenQ (fastRow i) : ℝ) ≤ ∫ t in fastSupport i,
    P2OriginalPhysicalSimplexMomentRow.rowDensity (actualPieceRow i.val.1 i.val.2.1 i.val.2.2.1 i.val.2.2.2
      (toOriginal i).property) t at h
  simp_rw [actual_piece_density] at h
  exact h

theorem original_radial_saved_floor_le_source_integral :
    (74558208451675327462975 : ℝ)/(2 : ℝ)^96 ≤ ∫ t in sourceSet seedCell, kernel seedCell t := by
  have hn : (savedNumerator : ℝ)/(2 : ℝ)^96 ≤ ∑ i : FastPiece, (rowJensenQ (fastRow i) : ℝ) := by
    exact_mod_cast original_saved_floor_le_fast_jensen_sum
  rw [original_selected_numerator] at hn
  exact hn.trans ((Finset.sum_le_sum (fun i _ => fast_jensen_le_kernel_integral i)).trans
    sum_fast_integrals_le_source)

/-- Same original archived seed maximum and same actual source integral. -/
theorem original_radial_archived_cell_le_source_integral :
    ((P4AOriginalFull87ArchiveSourceIndex.archivedRecordForOriginalCell (.remaining .seed)).2 : ℝ) ≤
      ∫ t in sourceSet (.remaining .seed), kernel (.remaining .seed) t := by
  rw [original_selected_seed_record,original_selected_numerator]
  exact_mod_cast original_radial_saved_floor_le_source_integral

end
end ImbalancedChen.P2OriginalSaving15RadialFastIntegral
