import ImbalancedChen.P2OriginalSaving18UnequalIntegral
import ImbalancedChen.P2Winner9CompleteSeedSourceGates
import ImbalancedChen.P2Winner9CompleteSeedSelectedFloors

/-! The last two original eighth ledger entries replace successive
lower bounds on the already counted winner9 seed at physical index 41.
The same 97 strict half-spaces and the same ten physical factors occur
in the complete 11,026-row enclosure and in the original 87-cell policy. -/
namespace ImbalancedChen.P4AOriginalFull87SeedRefinements
noncomputable section
open scoped BigOperators
open Set MeasureTheory
open P4AOriginalFull87SourceDictionary P4AOriginalFull87StrictActionTrim
open P4AOriginalFull87EighthKernelControl (kernel residual total product)
open P4AOriginalFull87SourcePrimeTests (cellIntegral)
open P4AOriginalFull87ArchivedIntegralRows (archived)
open P2OriginalFull87PullingCell (originalGate gate_eval rowVertices rowSupport row_det sum_support_integrals_le)
open P2OriginalSaving19OwnedSource (AffineRow eval)
open P2OriginalSaving18UnequalArchive (data original_geometry)
open P2Winner9CompleteSeedData (RowIndex entry physicalVertices)
open P2Winner9CompleteSeedPositiveDomains (originalPoint actualSupport actual_vertex_lookup)
open P2Winner9CompleteSeedGapReserve (fullMass)
open P2Winner9CompleteSeedSourceGates (Gate gate originalPhysicalSource)
open P2Winner9PhysicalAffineTransfer (physicalR physicalM physicalGap physicalFactor
  coordinateSum physicalUpperIntegrand canonicalSupport)
open P2Winner9CompleteSeedSelectedFloors (selectedFloorSum original_slot_normalization complete_selected_floor_sum)
open P2OriginalCertificateBudget (savingLower)
open P2OriginalSeedChronologicalMaxArithmetic (slot21 slot22)

def seed : Cell := .remaining (.nine 11)

def seedGate (g : Gate) : AffineRow := Fin.cases (gate g).constant (gate g).coefficient

private theorem seedGate_eval (g : Gate) (t : Point) :
    eval (seedGate g) t = (gate g).eval t := by
  simp [seedGate,eval,OriginalDescendingFifteenLiteralAffineRows.evaluateCoefficients,
    P2Winner9CompleteSeedSourceGates.Row.eval]

/-- Choosing a nonzero rational coefficient fixes the scale. All nine
coordinates, including the constant term, must agree at this positive scale. -/
def positiveMultiple (a b : AffineRow) : Prop :=
  ∃ j : Fin 9, 0 < a j / b j ∧ ∀ k : Fin 9, a k = (a j / b j) * b k

instance (a b : AffineRow) : Decidable (positiveMultiple a b) := by
  unfold positiveMultiple
  infer_instance

private theorem positiveMultiple_sign {a b : AffineRow} (h : positiveMultiple a b) (t : Point) :
    0 < eval a t ↔ 0 < eval b t := by
  obtain ⟨j,hs,he⟩ := h
  let s : ℚ := a j / b j
  have ha : a = fun k => s * b k := funext he
  have hev : eval a t = (s : ℝ) * eval b t := by
    conv_lhs => rw [ha]
    simp [eval,OriginalDescendingFifteenLiteralAffineRows.evaluateCoefficients,
      mul_add,Finset.mul_sum,mul_assoc]
  rw [hev]
  exact mul_pos_iff_of_pos_left (show (0 : ℝ) < (s : ℝ) by exact_mod_cast hs)

/-- Bidirectional comparison of the 97 proper affine source rows, in
their two original encodings. No fitted point determines a half-space. -/
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem original_97_gates :
    (∀ j : Fin (rowCount seed), ∃ g : Gate, positiveMultiple (originalGate seed j) (seedGate g)) ∧
    (∀ g : Gate, ∃ j : Fin (rowCount seed), positiveMultiple (originalGate seed j) (seedGate g)) := by
  decide

theorem original_seed_source_eq : originalPhysicalSource = sourceSet seed := by
  ext t
  change (∀ g : Gate, 0 < (gate g).eval t) ↔ Source seed t
  rw [source_iff_rows]
  constructor
  · intro hg j
    obtain ⟨g,h⟩ := original_97_gates.1 j
    rw [← gate_eval]
    exact (positiveMultiple_sign h t).mpr ((seedGate_eval g t).symm ▸ hg g)
  · intro hj g
    obtain ⟨j,h⟩ := original_97_gates.2 g
    rw [← seedGate_eval]
    exact (positiveMultiple_sign h t).mp ((gate_eval seed j t).symm ▸ hj j)

theorem original_seed_caps (t : Point) :
    physicalR t = comparison seed t ∧ physicalM t = newCap seed t := by
  constructor
  · rw [← P2OriginalSaving18UnequalIntegral.eval_R (.nine 11) t]
    norm_num [P2OriginalSaving18UnequalArchive.R,eval,
      OriginalDescendingFifteenLiteralAffineRows.evaluateCoefficients,physicalR,Fin.sum_univ_succ] <;> ring
  · rw [← P2OriginalSaving18UnequalIntegral.eval_M (.nine 11) t]
    norm_num [P2OriginalSaving18UnequalArchive.M,eval,
      OriginalDescendingFifteenLiteralAffineRows.evaluateCoefficients,physicalM,Fin.sum_univ_succ] <;> ring

theorem original_seed_density_eq (t : Point) : physicalUpperIntegrand t = kernel seed t := by
  have hf : (∏ j : Fin 10, physicalFactor j t) =
      (physicalR t - total t) * (physicalM t - total t) * product t := by
    rw [Fin.prod_univ_succ,Fin.prod_univ_succ]
    simp only [P2Winner9PhysicalAffineTransfer.physicalFactor_zero,
      P2Winner9PhysicalAffineTransfer.physicalFactor_one,
      P2Winner9PhysicalAffineTransfer.physicalFactor_succ_succ]
    change (physicalR t - total t) * ((physicalM t - total t) * product t) = _
    ring
  rw [physicalUpperIntegrand,hf,physicalGap,kernel,residual,
    (original_seed_caps t).1,(original_seed_caps t).2]

theorem original_seed_integral_eq :
    (∫ t in originalPhysicalSource, physicalUpperIntegrand t) = cellIntegral seed := by
  simp only [cellIntegral,original_seed_source_eq,original_seed_density_eq]

/-! The seed has already paid for the original max-pulling ownership in
stage 18. Bind its literal 201 vertices and 11,026 ordered vertex-ID lists
to the existing complete log/curvature/mixed row proofs. -/
abbrev seedData := data (.nine 11)
abbrev SeedRow := Fin seedData.rows.size

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem original_seed_row_count : seedData.rows.size = 11026 := by decide

def sourceOrdinal : SeedRow ≃ RowIndex where
  toFun s := ⟨s.val,original_seed_row_count ▸ s.isLt⟩
  invFun i := ⟨i.val,original_seed_row_count.symm ▸ i.isLt⟩
  left_inv _ := Fin.ext rfl
  right_inv _ := Fin.ext rfl

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem original_seed_vertex_bindings : seedData.vertices.size = 201 ∧
    (∀ v : Fin 201, P2OriginalFull87PullingCell.vertex seedData v = originalPoint v) ∧
    (∀ (s : SeedRow) (k : Fin 9), P2OriginalFull87PullingCell.idAt seedData s k =
      (entry (sourceOrdinal s)).vertexIds k) := by decide

theorem original_seed_row_vertices (s : SeedRow) (k : Fin 9) :
    physicalVertices (sourceOrdinal s) k = rowVertices seedData s k := by
  rw [actual_vertex_lookup]
  unfold rowVertices
  rw [original_seed_vertex_bindings.2.2 s k]
  exact (original_seed_vertex_bindings.2.1 _).symm

theorem original_seed_row_support (s : SeedRow) :
    actualSupport (sourceOrdinal s) = rowSupport seedData s (row_det (original_geometry (.nine 11)) s) := by
  let v := rowVertices seedData s
  let L := P2OriginalSaving16SimplexBinding.edgeEquiv v (row_det (original_geometry (.nine 11)) s)
  let b := P2OriginalSaving16OriginalArchive.castPoint (v 0)
  let W := P2Winner9SelectedRowRealJacobian.realVertices (physicalVertices (sourceOrdinal s))
  change (P2Winner9PhysicalVertexInterpolation.vertexMap W '' canonicalSupport) =
    (fun x => b + L x) '' P2OriginalSaving19SimplexMoments.canonical
  apply congrArg (fun f : Point → Point => f '' P2OriginalSaving19SimplexMoments.canonical)
  funext x
  rw [← P2OriginalSaving19SimplexMoments.vertices_interpolate L b x]
  have hv : P2OriginalSaving19SimplexMoments.vertices L b =
      fun k => P2OriginalSaving16OriginalArchive.castPoint (v k) :=
    P2OriginalSaving16SimplexBinding.edge_vertices v (row_det (original_geometry (.nine 11)) s)
  rw [hv]
  ext j
  rw [P2Winner9PhysicalVertexInterpolation.vertexMap_coordinate,
    P2OriginalSaving19SimplexMoments.pointInterpolate_apply]
  unfold P2Winner9BarycentricMixedDegreeOne.affine P2OriginalSaving19SimplexMoments.interpolate
  apply Finset.sum_congr rfl
  intro k _
  change (physicalVertices (sourceOrdinal s) k j : ℝ) * _ = _ * (rowVertices seedData s k j : ℝ)
  rw [original_seed_row_vertices]
  exact mul_comm _ _

theorem selected_floor_sum_le_seed_integral : selectedFloorSum ≤ cellIntegral seed := by
  have hr (s : SeedRow) : fullMass (sourceOrdinal s) =
      ∫ t in rowSupport seedData s (row_det (original_geometry (.nine 11)) s), kernel seed t := by
    simp only [fullMass,original_seed_row_support,original_seed_density_eq]
  refine complete_selected_floor_sum.trans ?_
  calc
    (∑ i : RowIndex, fullMass i) = ∑ s : SeedRow, fullMass (sourceOrdinal s) :=
      (sourceOrdinal.sum_comp fullMass).symm
    _ = _ := Finset.sum_congr rfl (fun s _ => hr s)
    _ ≤ cellIntegral seed := sum_support_integrals_le seed seedData (original_geometry (.nine 11))

theorem original_seed_log_selected :
    archived seed = P2Winner9CompleteSeedChronology.adoptedLogTotal := by
  rw [P2Winner9CompleteSeedChronology.full_literal_totals.1]
  decide

/-- The selected log floor at original index 41 is replaced, on the
very same eight-dimensional integral, by the complete mixed maximum. -/
theorem original_seed_refined_floor :
    (archived seed : ℝ) + (savingLower slot21 : ℝ) + (savingLower slot22 : ℝ) ≤ cellIntegral seed := by
  simpa only [original_slot_normalization,original_seed_log_selected] using selected_floor_sum_le_seed_integral

def refinedRecord (c : Cell) : ℚ :=
  archived c + if c = seed then savingLower slot21 + savingLower slot22 else 0

theorem refined_seed_le_integral : (refinedRecord seed : ℝ) ≤ cellIntegral seed := by
  simpa [refinedRecord,add_assoc] using original_seed_refined_floor

theorem original_increment_values :
    savingLower slot21 = (77410436074156865471 : ℚ)/2^96 ∧
    savingLower slot22 = (481322793305152847935 : ℚ)/2^96 := by decide

theorem refined_record_sum :
    (∑ c : Cell, refinedRecord c) =
      (3111307568597708509491143 : ℚ)/2^96 + savingLower slot21 + savingLower slot22 := by
  classical
  have h : (∑ c : Cell, archived c) = (3111307568597708509491143 : ℚ)/2^96 :=
    P4AOriginalFull87CellIndexedArchiveWeight.original_cell_archive_selected_sum_exact
  simp [refinedRecord,Finset.sum_add_distrib,h,add_assoc]

end
end ImbalancedChen.P4AOriginalFull87SeedRefinements
