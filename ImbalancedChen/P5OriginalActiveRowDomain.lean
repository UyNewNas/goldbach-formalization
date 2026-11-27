import ImbalancedChen.P5OriginalABFoldGeometry
import ImbalancedChen.P5OriginalWireFloorInstantiation
import ImbalancedChen.P5OriginalWireChildDIdentity

/-! Active ratio/e-domain derived from the SAME original d and actual AB fold.
This removes finite d-domain, vertex and floor licences from the arbitrary-row
receiver. The separate b<=4 and parent upper gates remain explicit. -/
namespace ImbalancedChen.P5OriginalActiveRowDomain

open scoped BigOperators
open P1OriginalPrefixRowDecodeSoundness P1OriginalFifthRawBoxSelectorEquivalence
open P5OriginalChildIntegerWireBinding P5OriginalGenericWireFloorReceiver
open P5OriginalABFoldGeometry P5OriginalWireFloorInstantiation P5OriginalWireChildDIdentity
open P5ArbitraryMaskChildVertexRatio P5NamedFifthPayloadSemantics
open P5NamedFifthAllChildren P5OldFifthExact64ChildTiling
open P5OldFifthChildGapIntegral P5OldFifthOneCoordinateVertexChord
open P5OldFifthActualChildJensenIntegral P5ChildSelectedOwnerJensenReserve
open P5OldFifthPointwiseQ P5OldFifthFrozenUpperSurrogate
open P5OldFifthFiveCoordinateBarycentric (childVolume)
open ImbalancedChen.Certificates.P2DirectedLogRounding

/-- Positive ORIGINAL d forces b>2. The already proved saved-e theorem at
b=2 rules out b<=2, then gives the same actual e in [0,b-2]. -/
theorem original_active_ratio_e_ranges (raw : FifthWireRow) (hg : raw.grid = 400)
    (hpositive : ∀ i : Fin 5, 1 ≤ raw.lo i) (c : ChildIndex) (hd : 0 < rowD raw c) :
    2 < originalRatioQ raw c ∧ 0 ≤ rowEQ raw c ∧
      rowEQ raw c ≤ originalRatioQ raw c - 2 := by
  have hleft := positiveKey_childLeft_pos raw hpositive c
  have hd_eq : (rowD raw c : ℝ) = vertexD (sourcePicks raw) raw c :=
    originalD_cast_eq_actual_vertexD raw hg c
  have hdR : (0 : ℝ) < (rowD raw c : ℝ) := by exact_mod_cast hd
  have hH : (0 : ℝ) < 1024 * 1600 * childRight raw c 4 := by
    exact mul_pos (by norm_num) (childRight_pos raw c hleft 4)
  have hnew : ∀ t ∈ childClosed raw c,
      residual (rawCandidate 0 raw t) t ≤ (originalRatioQ raw c : ℝ) :=
    fun t ht => originalRatioQ_bound_on_child raw c hpositive t ht
  have hbR : (2 : ℝ) < (originalRatioQ raw c : ℝ) := by
    by_contra hn
    have hb : (originalRatioQ raw c : ℝ) ≤ 2 := le_of_not_gt hn
    have he2 := saved_e_mem_ratio_interval (sourcePicks raw) raw c hleft
      (le_rfl : (2 : ℝ) ≤ 2) (fun t ht => (hnew t ht).trans hb)
      (rowD raw c) hd.le hd_eq
    have hstrict : (0 : ℝ) < (rowD raw c : ℝ) /
        (1024 * 1600 * childRight raw c 4) := div_pos hdR hH
    have hnonpos : (rowD raw c : ℝ) / (1024 * 1600 * childRight raw c 4) ≤ 0 := by
      simpa only [sub_self] using he2.2
    exact (not_le_of_gt hstrict) hnonpos
  have he := saved_e_mem_ratio_interval (sourcePicks raw) raw c hleft hbR.le hnew
    (rowD raw c) hd.le hd_eq
  have he0R : (0 : ℝ) ≤ (rowEQ raw c : ℝ) := by
    rw [rowEQ_eq_actual_scale]
    exact he.1
  have heBR : (rowEQ raw c : ℝ) ≤ (originalRatioQ raw c : ℝ) - 2 := by
    rw [rowEQ_eq_actual_scale]
    exact he.2
  exact ⟨by exact_mod_cast hbR, by exact_mod_cast he0R, by exact_mod_cast heBR⟩

/-- All original positive grid400 rows: the exact quotient/floor identity
needs no per-child d-domain, stored floor or SourceChildFacts certificate. -/
theorem original_floor_eq_row_directed (raw : FifthWireRow) (hg : raw.grid = 400)
    (hpositive : ∀ i : Fin 5, 1 ≤ raw.lo i) (c : ChildIndex) :
    originalExactFloor (originalFields raw c) =
      if 0 < rowD raw c then
        Int.floor (rowPrefactorQ raw c * P5NamedFifthQ80FloorSoundness.directedQQ
          (originalRatioQ raw c) (rowEQ raw c) * dyadicScale 80) else 0 := by
  apply P5OriginalWireFloorInstantiation.original_floor_eq_row_directed raw c hpositive
  intro hd
  have hr := original_active_ratio_e_ranges raw hg hpositive c hd
  exact ⟨originalAB_den_pos raw c hpositive, hr.1, hr.2.2⟩

/-- The existing full receiver fact follows from the remaining parent upper
and active b<=4 gates. Both are plain original field/domain inequalities;
no vertex, d/e-domain, floor, Jensen or desired integral is an input. -/
theorem sourceChildFacts_of_upper_and_ratio4 (raw : FifthWireRow) (hg : raw.grid = 400)
    (hpositive : ∀ i : Fin 5, 1 ≤ raw.lo i)
    (hupper : ∀ i : Fin 5, 96 * (raw.lo i + 1) ≤ 19 * raw.grid)
    (c : ChildIndex) (hfour : 0 < rowD raw c → originalRatioQ raw c ≤ 4) :
    SourceChildFacts raw c := by
  have hleft := positiveKey_childLeft_pos raw hpositive c
  have hu : ∀ i : Fin 5, raw.upper i ≤ 19 / 96 := by
    intro i
    unfold FifthWireRow.upper
    have hgQ : (0 : ℚ) < (raw.grid : ℚ) := by rw [hg]; norm_num
    apply (div_le_iff₀ hgQ).mpr
    have hi : (96 : ℚ) * ((raw.lo i : ℚ) + 1) ≤ 19 * (raw.grid : ℚ) := by
      exact_mod_cast hupper i
    linarith
  refine ⟨hu, originalFields_d_cast_eq_childDQ raw hg c, ?_⟩
  intro hd
  have hr := original_active_ratio_e_ranges raw hg hpositive c hd
  have hpR : (0 : ℝ) ≤ (rowPrefactorQ raw c : ℝ) := by
    rw [rowPrefactorQ_cast raw c hleft]
    exact mul_nonneg (P5OldFifthChildQJensen.childVolume_pos raw c).le
      (childPrefactor_nonneg raw c hleft)
  have hpQ : (0 : ℚ) ≤ rowPrefactorQ raw c := by exact_mod_cast hpR
  refine ⟨hr.1, hfour hd, hr.2.1, hr.2.2, hpQ,
    original_chosen_vertex_upper raw c hpositive, ?_⟩
  rw [original_floor_eq_row_directed raw hg hpositive c, if_pos hd]

end ImbalancedChen.P5OriginalActiveRowDomain
