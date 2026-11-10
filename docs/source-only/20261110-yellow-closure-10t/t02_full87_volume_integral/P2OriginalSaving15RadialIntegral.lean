import ImbalancedChen.P2OriginalRadialPieceSeparation
import Mathlib.Data.Fintype.BigOperators

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.
The actual selected four-panel saving15 endpoint, including its seed7
archive record, on the same original full87 Source kernel integral.
The original panel is floored once; the eight staircase pieces use
unrounded true physical Jensen bounds. Degenerate pieces are omitted.
No geometry/ownership/integral estimate is an input to the terminal.
-/
namespace ImbalancedChen.P2OriginalSaving15RadialIntegral
noncomputable section
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Set MeasureTheory
open scoped Classical BigOperators
open P2OriginalSaving15RadialArchive
open P2OriginalSaving15RadialProfile (seedCell actualPieceRow actual_piece_density piece_vertex_closed_rows)
open P2OriginalRadialPieceSeparation
open P2OriginalSaving16OriginalArchive (castPoint evalQ edgeMatrix)
open P2OriginalPhysicalSimplexMomentRow (rowSupport row_vertices)
open P2OriginalPhysicalSimplexJensenRow (rowJensenQ row_unrounded_jensen_sound)
open P4AOriginalFull87StrictActionTrim (sourceSet sourceSet_measurable)
open P4AOriginalFull87EighthKernelControl (kernel integrableOn_kernel kernel_bounds)
namespace Bary
export P2OriginalSaving19SimplexMoments
  (bary bary_nonneg interpolate pointInterpolate vertices_interpolate support_measurable)
end Bary

def indexedJensenQ (i : Index) : ℚ :=
  if h : (edgeMatrix (indexVertices i)).det ≠ 0 then rowJensenQ (pieceRow ⟨i,h⟩) else 0
def pieceJensenQ (c : Fin 4) (s : BaseRow c) (p : Fin 4) (k : Fin 8) : ℚ := indexedJensenQ ⟨c,s,p,k⟩

/-- Exactly one original saved floor for this actual panel, compared
with the sum of the eight UNROUNDED physical simplex Jensen values.
This is a finite rational check, not an integral hypothesis. -/
theorem original_panel_floor_checks : ∀ (c : Fin 4) (s : BaseRow c) (p : Fin 4),
    ((panelRecord c s p).floor : ℚ)/(2 : ℚ)^96 ≤ ∑ k : Fin 8, pieceJensenQ c s p k := by decide

theorem flattened_jensen_sum :
    (∑ c : Fin 4, ∑ s : BaseRow c, ∑ p : Fin 4, ∑ k : Fin 8, pieceJensenQ c s p k) =
      ∑ i : Piece, rowJensenQ (pieceRow i) := by
  have he : (∑ c : Fin 4, ∑ s : BaseRow c, ∑ p : Fin 4, ∑ k : Fin 8, pieceJensenQ c s p k) =
      ∑ i : Index, indexedJensenQ i := by
    simp only [Index,Fintype.sum_sigma,Fintype.sum_prod_type,pieceJensenQ]
  rw [he,indexedJensenQ,Fintype.sum_dite]
  simp

theorem original_saved_floor_le_jensen_sum :
    (savedNumerator : ℚ)/(2 : ℚ)^96 ≤ ∑ i : Piece, rowJensenQ (pieceRow i) := by
  calc
    _ = ∑ c : Fin 4, ∑ s : BaseRow c, ∑ p : Fin 4,
        ((panelRecord c s p).floor : ℚ)/(2 : ℚ)^96 := by simp [savedNumerator,Finset.sum_div]
    _ ≤ ∑ c : Fin 4, ∑ s : BaseRow c, ∑ p : Fin 4, ∑ k : Fin 8, pieceJensenQ c s p k :=
      Finset.sum_le_sum (fun c _ => Finset.sum_le_sum (fun s _ =>
        Finset.sum_le_sum (fun p _ => original_panel_floor_checks c s p)))
    _ = _ := flattened_jensen_sum

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

theorem support_closed_rows (i : Piece) {t : Fin 8 → ℝ} (ht : t ∈ pieceSupport i) (g : Fin 96) :
    0 ≤ evalRow (seedRows g) t := by
  obtain ⟨x,hx,rfl⟩ := ht
  rw [← Bary.vertices_interpolate,P2OriginalSaving19OwnedSource.eval_interpolate,row_vertices]
  change 0 ≤ ∑ j : Fin 9, Bary.bary j x * evalRow (seedRows g) (castPoint ((pieceRow i).verticesQ j))
  apply Finset.sum_nonneg
  intro j _
  apply mul_nonneg (Bary.bary_nonneg hx j)
  rw [P2OriginalSaving15RadialProfile.evalQ_cast]
  exact_mod_cast piece_vertex_closed_rows i.val.1 i.val.2.1 i.val.2.2.1 i.val.2.2.2 j g

theorem support_off_walls_source (i : Piece) : pieceSupport i \ seedWalls ⊆ sourceSet seedCell := by
  rintro t ⟨ht,hw⟩ g
  have hge := support_closed_rows i ht g
  have hne : evalRow (seedRows g) t ≠ 0 := fun he => hw (mem_iUnion.mpr ⟨g,he⟩)
  exact hge.lt_of_ne hne.symm

def overlapSet : Set (Fin 8 → ℝ) :=
  ⋃ i : Piece, ⋃ j : Piece, if i = j then ∅ else pieceSupport i ∩ pieceSupport j
def exceptionalSet : Set (Fin 8 → ℝ) := seedWalls ∪ overlapSet
def ownedSupport (i : Piece) : Set (Fin 8 → ℝ) := pieceSupport i \ exceptionalSet
theorem overlapSet_null : volume overlapSet = 0 := by
  apply measure_iUnion_null
  intro i
  apply measure_iUnion_null
  intro j
  by_cases hij : i = j
  · simp [hij]
  · simp only [if_neg hij]
    exact piece_pairwise_null hij
theorem exceptionalSet_null : volume exceptionalSet = 0 := measure_union_null seedWalls_null overlapSet_null
theorem pieceSupport_measurable (i : Piece) : MeasurableSet (pieceSupport i) := Bary.support_measurable _ _
theorem exceptionalSet_measurable : MeasurableSet exceptionalSet := by
  apply seedWalls_measurable.union
  apply MeasurableSet.iUnion
  intro i
  apply MeasurableSet.iUnion
  intro j
  by_cases hij : i = j
  · simp [hij]
  · simp only [if_neg hij]
    exact (pieceSupport_measurable i).inter (pieceSupport_measurable j)
theorem ownedSupport_measurable (i : Piece) : MeasurableSet (ownedSupport i) :=
  (pieceSupport_measurable i).diff exceptionalSet_measurable
theorem ownedSupport_source (i : Piece) : ownedSupport i ⊆ sourceSet seedCell := by
  rintro t ⟨ht,hw⟩
  exact support_off_walls_source i ⟨ht,fun h => hw (Or.inl h)⟩
theorem ownedSupport_integrable (i : Piece) : IntegrableOn (kernel seedCell) (ownedSupport i) :=
  (integrableOn_kernel seedCell).mono_set (ownedSupport_source i)
theorem ownedSupport_pairwise_disjoint : Pairwise (fun i j : Piece => Disjoint (ownedSupport i) (ownedSupport j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  rintro t ⟨hti,he⟩ ⟨htj,_⟩
  apply he
  right
  exact mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨j,by simpa only [if_neg hij] using And.intro hti htj⟩⟩
theorem ownedSupport_ae (i : Piece) : ownedSupport i =ᵐ[volume] pieceSupport i := by
  have hn : ∀ᵐ t : Fin 8 → ℝ ∂volume, t ∉ exceptionalSet := by
    rw [ae_iff]
    simpa only [not_not] using exceptionalSet_null
  filter_upwards [hn] with t ht
  simp [ownedSupport,ht]
theorem ownedSupport_integral (i : Piece) :
    (∫ t in ownedSupport i, kernel seedCell t) = ∫ t in pieceSupport i, kernel seedCell t :=
  setIntegral_congr_set (ownedSupport_ae i)

theorem sum_piece_integrals_le_source :
    (∑ i : Piece, ∫ t in pieceSupport i, kernel seedCell t) ≤ ∫ t in sourceSet seedCell, kernel seedCell t := by
  have hu := integral_iUnion_fintype ownedSupport_measurable ownedSupport_pairwise_disjoint ownedSupport_integrable
  simp_rw [ownedSupport_integral] at hu
  rw [← hu]
  apply setIntegral_mono_set (integrableOn_kernel seedCell)
  · filter_upwards [ae_restrict_mem (sourceSet_measurable seedCell)] with t ht
    exact (kernel_bounds ht).1
  · exact Filter.Eventually.of_forall (iUnion_subset ownedSupport_source)

theorem piece_jensen_le_kernel_integral (i : Piece) :
    (rowJensenQ (pieceRow i) : ℝ) ≤ ∫ t in pieceSupport i, kernel seedCell t := by
  have h := row_unrounded_jensen_sound (pieceRow i)
  change (rowJensenQ (pieceRow i) : ℝ) ≤ ∫ t in pieceSupport i,
    P2OriginalPhysicalSimplexMomentRow.rowDensity (actualPieceRow i.val.1 i.val.2.1 i.val.2.2.1 i.val.2.2.2 i.property) t at h
  simp_rw [actual_piece_density] at h
  exact h

theorem original_radial_saved_floor_le_source_integral :
    (74558208451675327462975 : ℝ)/(2 : ℝ)^96 ≤ ∫ t in sourceSet seedCell, kernel seedCell t := by
  have hn : (savedNumerator : ℝ)/(2 : ℝ)^96 ≤ ∑ i : Piece, (rowJensenQ (pieceRow i) : ℝ) := by
    exact_mod_cast original_saved_floor_le_jensen_sum
  rw [original_selected_numerator] at hn
  exact hn.trans ((Finset.sum_le_sum (fun i _ => piece_jensen_le_kernel_integral i)).trans
    sum_piece_integrals_le_source)

/-- The original saved seed Cell, not an extra radial cap action or
increment added to a predecessor. Its four-panel maximum is paid once. -/
theorem original_radial_archived_cell_le_source_integral :
    ((P4AOriginalFull87ArchiveSourceIndex.archivedRecordForOriginalCell (.remaining .seed)).2 : ℝ) ≤
      ∫ t in sourceSet (.remaining .seed), kernel (.remaining .seed) t := by
  rw [original_selected_seed_record,original_selected_numerator]
  exact_mod_cast original_radial_saved_floor_le_source_integral

end
end ImbalancedChen.P2OriginalSaving15RadialIntegral
