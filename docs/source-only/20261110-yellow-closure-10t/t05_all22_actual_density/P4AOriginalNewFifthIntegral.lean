import ImbalancedChen.P4AOriginalNewFifthCoverage
import ImbalancedChen.P5FullArchiveOwnerIntegralAssembly

/-! The genuine corrected fifth sum contains both the old selected source
and the disjoint newly archived rows. Separate old/new label sets prevent
charging even one formerly selected cell a second time. -/
namespace ImbalancedChen.P4AOriginalNewFifthIntegral
noncomputable section
open Set MeasureTheory Filter Topology
open scoped Classical BigOperators
open P4AOriginalNewFifthArchiveData P4AOriginalNewFifthArchive P4AOriginalNewFifthOwners
open P4AOriginalNewFifthUnion P4AOriginalNewFifthCoverage P4AOriginalNewFifthMean (unionIntegral)
open P1OriginalPrefixRowDecodeSoundness
open P1OriginalFifthGrid400RefinedFullBoxCover (refinedMesh RefinedCell)
open P1OriginalFifthRawBoxSelectorEquivalence (rawCandidate rawCandidate_eq_candidate)
open P1OriginalCoarseFifthContinuation (selectedFifthCells mem_selectedFifthCells)
open P1OriginalVariableFifthContinuation (FifthRow candidate)
open P1OriginalVariableFourthContinuation (finiteMax_le finiteMax_seed_le finiteMax_row_le)
open P1OriginalFifthUntruncatedIntegral (fullCell fullCell_measurable)
open P1ActualVariableFifthProfiles (actualNext5 ownerEligible)
open P1ActualVariableFifthUntruncatedDomination
  (fullCellIntegral fullSelectedIntegral actualKernel_domination integrableOn_actualKernel_fullCell)
open P1CorrectedFifthDensityDictionary (originalVariableFourthProfile)
open P1OriginalFifthActualB13IntegralError (positiveKernel positiveKernel_integrableOn_of_subset
  positiveKernel_integral_motion_le)
open P1OriginalFifthLiteralKernelModulus (rowModulus rowModulus_continuous rowModulus_zero)
open P1FifthUnitBoxLiteralGainLower (literalRawKernel)
open P5FullArchiveOwnerIntegralAssembly (mesh_lower_mem selected_globalOwners_eq)
open P5OriginalFourthFifthSourceInputs (originalRows4 originalAdmission4 originalAdmission4_geometry)
open P1HistoricalFifthIndexedOwnerArchive
  (archiveRow sourceOwnerRow licensedOwner_decoded globalOwners globalOwner_selected_buffer)
open P5OriginalFifthArchiveActualMean (archiveFifthIntegral)

abbrev oldIntegral (e : ℚ) (q : ℕ) (a : ℝ) :=
  archiveFifthIntegral originalRows4 originalAdmission4 e q ((e : ℝ)/20) a

private theorem new_selected (e : ℚ) (q : ℕ) (a : ℝ) (j : RefinedCell q)
    (hj : j ∈ newLabels e q a) :
    j ∈ selectedFifthCells e ((e : ℝ)/20) (refinedMesh q) a (data e q a).J5 := by
  obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hj
  exact (rowAt_eligible i e q a j hi _ (mesh_lower_mem _ _)).1

private theorem old_selected (e : ℚ) (q : ℕ) (a : ℝ) (j : RefinedCell q)
    (hj : j ∈ (original e q a).J5) :
    j ∈ selectedFifthCells e ((e : ℝ)/20) (refinedMesh q) a (data e q a).J5 := by
  exact (mem_selectedFifthCells _ _ _ _ _ _).mpr ⟨Finset.mem_union_left _ hj,
    ((mem_selectedFifthCells _ _ _ _ _ _).mp (globalOwner_selected_buffer e q ((e : ℝ)/20) a j hj)).2⟩

private theorem selected_eq_union (e : ℚ) (q : ℕ) (a : ℝ) :
    selectedFifthCells e ((e : ℝ)/20) (refinedMesh q) a (data e q a).J5 =
      (original e q a).J5 ∪ newLabels e q a := by
  ext j
  constructor
  · exact fun h => ((mem_selectedFifthCells _ _ _ _ _ _).mp h).1
  · intro h
    exact (Finset.mem_union.mp h).elim (old_selected e q a j) (new_selected e q a j)

private theorem labels_disjoint (e : ℚ) (q : ℕ) (a : ℝ) :
    Disjoint (original e q a).J5 (newLabels e q a) := by
  apply Finset.disjoint_left.mpr
  intro j old newj
  obtain ⟨o,_,ho⟩ := Finset.mem_biUnion.mp old
  obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp newj
  let t := logPrimeMeshLo 0 (19/96) (refinedMesh q) j
  have ht := mesh_lower_mem (refinedMesh q) j
  have hn := (decodeFifthRows_source_geometry _ _ _ (rowAt_decodes i e q a j hi) t ht).2.2.2
  exact (new_box_excludes_old i t hn o)
    (decodeFifthRows_source_geometry _ _ _ (licensedOwner_decoded o e q ((e : ℝ)/20) a j ho) t ht).2.2.2

private theorem labels_pairwise (e : ℚ) (q : ℕ) (a : ℝ) :
    PairwiseDisjoint (Finset.univ : Finset Position) (fun i => owners i e q a) := by
  intro i _ k _ hne
  apply Finset.disjoint_left.mpr
  intro j hi hk
  let t := logPrimeMeshLo 0 (19/96) (refinedMesh q) j
  have ht := mesh_lower_mem (refinedMesh q) j
  exact (Set.disjoint_left.mp (boxes_pairwise_disjoint i k hne))
    (decodeFifthRows_source_geometry _ _ _ (rowAt_decodes i e q a j hi) t ht).2.2.2
    (decodeFifthRows_source_geometry _ _ _ (rowAt_decodes k e q a j hk) t ht).2.2.2

private theorem positive_cube (i : Position) :
    (rawRow i).originalBox ⊆ P1LiteralVariableFifthCompactSupplier.positiveCube (1/400 : ℝ) (19/96 : ℝ) := by
  intro t ht k _
  have h := (facts i).2.1 k
  exact ⟨(show (1/400 : ℝ) ≤ ((rawRow i).lower k : ℝ) by exact_mod_cast h.1).trans (ht k).1,
    (ht k).2.le.trans (by exact_mod_cast h.2)⟩

private theorem box_finite (i : Position) : volume (rawRow i).originalBox < ⊤ :=
  (measure_mono (positive_cube i)).trans_lt (isCompact_univ_pi (fun _ : Fin 5 => isCompact_Icc)).measure_lt_top

def moved (i : Position) (z : ℝ) : ℝ :=
  ∫ t in (rawRow i).originalBox, positiveKernel (rawRow i) z t

def motion (z : ℝ) : ℝ := ∑ i : Position, rowModulus (rawRow i) z * (volume (rawRow i).originalBox).toReal

private theorem old_cell_le (e : ℚ) (q : ℕ) (a : ℝ) (he : 0 ≤ e) (ha : 0 < a) (har : a < 19/96)
    (j : RefinedCell q) (hj : j ∈ (original e q a).J5) :
    fullCellIntegral e ((e : ℝ)/20) (refinedMesh q) a originalRows4 originalAdmission4 (original e q a).rows5 j ≤
    fullCellIntegral e ((e : ℝ)/20) (refinedMesh q) a originalRows4 originalAdmission4 (data e q a).rows5 j := by
  let m := refinedMesh q
  let chi := (e : ℝ)/20
  have hs := globalOwner_selected_buffer e q chi a j hj
  have hn := old_selected e q a j hj
  apply setIntegral_mono_on (integrableOn_actualKernel_fullCell e he chi m a ha har _ j hs _ _ _)
    (integrableOn_actualKernel_fullCell e he chi m a ha har _ j hn _ _ _)
    (fullCell_measurable e chi m a j)
  intro t ht
  have hcap : actualNext5 e chi m a j originalRows4 originalAdmission4 (original e q a).rows5 t ≤
      actualNext5 e chi m a j originalRows4 originalAdmission4 (data e q a).rows5 t := by
    apply finiteMax_le
    · exact finiteMax_seed_le _ _ _ _
    · exact fun r hr hel => finiteMax_row_le _ _ _ _ r (Finset.mem_union_left _ hr) hel
  exact mul_le_mul_of_nonneg_right (sub_le_sub_right (p1PrimeOwnCubeGatedProfile_mono t (ht.1 _) hcap) _)
    (Finset.prod_nonneg (fun k _ => (one_div_pos.mpr (ht.1 k)).le))

private theorem moved_le_owners (i : Position) (e : ℚ) (q : ℕ) (a : ℝ) (hs : Schedule e q a)
    (ha : 0 < a) (har : a < 19/96) :
    moved i (e : ℝ) ≤ ∑ j ∈ owners i e q a, fullCellIntegral e ((e : ℝ)/20) (refinedMesh q) a
      originalRows4 originalAdmission4 (data e q a).rows5 j := by
  let m := refinedMesh q
  let chi := (e : ℝ)/20
  let Cell := fun j : RefinedCell q => fullCell e chi m a j
  have hsub (j : RefinedCell q) (hj : j ∈ owners i e q a) : Cell j ⊆ (rawRow i).originalBox :=
    fun t ht => (decodeFifthRows_source_geometry _ _ _ (rowAt_decodes i e q a j hj) t ht.2.2.1).2.2.2
  have hpair : PairwiseDisjoint (owners i e q a : Finset (RefinedCell q)) Cell := by
    intro j _ k _ hne
    apply Set.disjoint_left.mpr
    intro t ht ht'
    exact hne (logPrimeMeshCell_unique (by norm_num : (0 : ℝ) ≤ 19/96) ht.2.2.1 ht'.2.2.1)
  have hint := positiveKernel_integrableOn_of_subset (rawRow i) (e : ℝ) _ (positive_cube i)
  unfold moved
  rw [source_box_eq_full_owner_union i e q a hs, integral_biUnion_finset (owners i e q a)
    (fun j _ => fullCell_measurable e chi m a j) hpair (fun j hj => hint.mono_set (hsub j hj))]
  apply Finset.sum_le_sum
  intro j hj
  have hsel := new_selected e q a j (Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hj⟩)
  apply setIntegral_mono_on (hint.mono_set (hsub j hj))
    (integrableOn_actualKernel_fullCell e hs.1 chi m a ha har _ j hsel _ _ _)
    (fullCell_measurable e chi m a j)
  intro t ht
  have hCl := ht.2.2.1
  have hJ := ht.2.2.2
  have hr : rowAt i q j ∈ (data e q a).rows5 := Finset.mem_union_right _
    (Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _, Finset.mem_image.mpr ⟨j,hj,rfl⟩⟩)
  have hnew : rawCandidate (e : ℝ) (rawRow i) t ≤
      actualNext5 e chi m a j originalRows4 originalAdmission4 (data e q a).rows5 t := by
    rw [rawCandidate_eq_candidate]
    exact finiteMax_row_le _ _ _ _ (rowAt i q j) hr ⟨rfl,(Finset.mem_filter.mp hj).2.2⟩
  have hold := P1OriginalOld15Majorant.actualOriginalFourth_le_old15 e (by exact_mod_cast hs.1) chi m a
    originalRows4 originalAdmission4 (fun r _ hr => originalAdmission4_geometry r hr) _ j hsel t hCl hJ
  apply max_le (actualKernel_domination e hs.1 chi m a _ j hsel _ _ _ t ht).1
  apply mul_le_mul_of_nonneg_right
  · exact sub_le_sub (p1PrimeOwnCubeGatedProfile_mono t (ht.1 _) hnew)
      (p1PrimeOwnCubeGatedProfile_mono t (ht.1 _) hold)
  · exact Finset.prod_nonneg (fun k _ => (one_div_pos.mpr (ht.1 k)).le)

/-- The entire old source is retained at its own value. Every added
position is purchased on its own physical-coordinate domain once. -/
theorem old_and_new_le_union (e : ℚ) (q : ℕ) (a : ℝ) (hs : Schedule e q a)
    (ha : 0 < a) (har : a < 19/96) :
    oldIntegral e q a + ∑ i : Position, moved i (e : ℝ) ≤ unionIntegral e q a := by
  let f := fun j : RefinedCell q => fullCellIntegral e ((e : ℝ)/20) (refinedMesh q) a
    originalRows4 originalAdmission4 (data e q a).rows5 j
  have hold : oldIntegral e q a ≤ ∑ j ∈ (original e q a).J5, f j := by
    unfold oldIntegral archiveFifthIntegral fullSelectedIntegral
    rw [selected_globalOwners_eq]
    exact Finset.sum_le_sum (fun j hj => old_cell_le e q a hs.1 ha har j hj)
  have hnew : (∑ i : Position, moved i (e : ℝ)) ≤ ∑ j ∈ newLabels e q a, f j := by
    rw [newLabels, Finset.sum_biUnion (labels_pairwise e q a)]
    exact Finset.sum_le_sum (fun i _ => moved_le_owners i e q a hs ha har)
  change _ ≤ ∑ j ∈ selectedFifthCells e ((e : ℝ)/20) (refinedMesh q) a (data e q a).J5, f j
  rw [selected_eq_union,Finset.sum_union (labels_disjoint e q a)]
  exact add_le_add hold hnew

theorem scalar_lower (e : ℚ) (q : ℕ) (a : ℝ) (hs : Schedule e q a)
    (ha : 0 < a) (har : a < 19/96) :
    (1648717268323516459667 : ℝ)/2^80 - motion (e : ℝ) ≤ unionIntegral e q a - oldIntegral e q a := by
  have hmotion : (∑ i : Position, literalIntegral i) - motion (e : ℝ) ≤ ∑ i : Position, moved i (e : ℝ) := by
    unfold motion
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro i _
    have hh := positiveKernel_integral_motion_le (rawRow i) (e : ℝ) _ (positive_cube i) (box_finite i)
    have hleft := (abs_le.mp hh).1
    dsimp [literalIntegral,moved]
    linarith
  linarith [original_floor_le_full_sum, old_and_new_le_union e q a hs ha har]

theorem exists_cofinal_scalar_lower (eta : ℝ) (heta : 0 < eta) :
    ∃ e0 : ℝ, 0 < e0 ∧ ∀ e : ℚ, 0 < (e : ℝ) → (e : ℝ) < e0 →
      ∃ q0 : ℕ, 0 < q0 ∧ ∀ q : ℕ, q0 ≤ q → ∀ a : ℝ, 0 < a → a ≤ 1/800 →
      (1648717268323516459667 : ℝ)/2^80 - eta < unionIntegral e q a - oldIntegral e q a := by
  have hc : Continuous motion := continuous_finsetSum _ (fun i _ => (rowModulus_continuous (rawRow i)).mul continuous_const)
  have hzero : motion 0 = 0 := by simp [motion,rowModulus_zero]
  obtain ⟨r,hr,hclose⟩ := Metric.continuousAt_iff.mp hc.continuousAt eta heta
  refine ⟨min r (1/64000), lt_min hr (by norm_num), ?_⟩
  intro e he her
  have hmotion : motion (e : ℝ) < eta := by
    have hd : dist (e : ℝ) 0 < r := by simpa [Real.dist_eq,abs_of_pos he] using her.trans_le (min_le_left _ _)
    have h := hclose hd
    rw [hzero,Real.dist_eq,sub_zero] at h
    exact (abs_lt.mp h).2
  obtain ⟨q0,hq0,hstep⟩ := exists_refinement_step_le_half ((e : ℝ)/10) (by positivity)
  refine ⟨q0,hq0,?_⟩
  intro q hq a ha hsmall
  have hqpos := hq0.trans_le hq
  have hle : logPrimeMeshStep 0 (19/96) (refinedMesh q) ≤ logPrimeMeshStep 0 (19/96) (refinedMesh q0) := by
    rw [refined_step q hqpos, refined_step q0 hq0]
    exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.mul_le_mul_left 2400 hq)
  have hs : Schedule e q a := ⟨by exact_mod_cast he.le,
    by exact_mod_cast (her.trans_le (min_le_right _ _)).le, hqpos, by linarith, hsmall⟩
  have har : a < 19/96 := hsmall.trans_lt (by norm_num)
  linarith [scalar_lower e q a hs ha har]

end
end ImbalancedChen.P4AOriginalNewFifthIntegral

