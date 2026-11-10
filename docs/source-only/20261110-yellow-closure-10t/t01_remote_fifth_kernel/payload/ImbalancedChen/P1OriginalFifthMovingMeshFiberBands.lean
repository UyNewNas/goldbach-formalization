import ImbalancedChen.P1OriginalThirdGammaMeshSectionBridge
import ImbalancedChen.P1OriginalFifthMovingMeshFubiniBridge
import ImbalancedChen.P1OriginalFifthActualOwnerGateCrossing
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.MetricSpace.Bounded

-- SOURCE ONLY / UNCOMPILED_ZERO_CREDIT / ready=false.
-- Uniform one-dimensional band measure from the exact moving-mesh Gamma
-- section spans. The source-specific owner-selector binding is recorded
-- below; no archived all-row selection or final 5D volume is asserted.
namespace ImbalancedChen.P1OriginalFifthMovingMeshFiberBands

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal
open ImbalancedChen.P1OriginalThirdGammaMeshSectionBridge
open ImbalancedChen.P1OriginalFifthMovingMeshFubiniBridge
open ImbalancedChen.P1OriginalFifthActualOwnerGateCrossing
open ImbalancedChen.HistoricalThirdCoarse

def levelBand (g : ℝ → ℝ) (a c d : ℝ) : Set ℝ :=
  {x | c ≤ a*x - g x ∧ a*x - g x ≤ c+d}

-- `Real.volume_le_diam` and `ediam_le_of_forall_dist_le` are actual
-- pinned mathlib lemmas. Pairwise section span is the preceding source's
-- section_span_of_one_sided_rise, not a new desired volume premise.
theorem levelBand_volume_le (g : ℝ → ℝ) (a c d h : ℝ)
    (ha : 1/2 < a)
    (hquasi : ∀ x y, x ≤ y → g y - g x ≤ (y-x+h)/2) :
    volume (levelBand g a c d) ≤
      ENNReal.ofReal ((d+h/2)/(a-1/2)) := by
  let S := levelBand g a c d
  have hspan : ∀ x ∈ S, ∀ y ∈ S,
      dist x y ≤ (d+h/2)/(a-1/2) := by
    intro x hx y hy
    rcases le_total x y with hxy | hyx
    · have hs := section_span_of_one_sided_rise a h d x y (g x) (g y) c
        ha hxy (hquasi x y hxy) hx.1 hx.2 hy.1 hy.2
      rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hxy)]
      exact hs
    · have hs := section_span_of_one_sided_rise a h d y x (g y) (g x) c
        ha hyx (hquasi y x hyx) hy.1 hy.2 hx.1 hx.2
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hyx)]
      exact hs
  exact (Real.volume_le_diam S).trans (ediam_le_of_forall_dist_le hspan)

theorem levelBand_one_volume_le (g : ℝ → ℝ) (c d h : ℝ)
    (hquasi : ∀ x y, x ≤ y → g y - g x ≤ (y-x+h)/2) :
    volume (levelBand g 1 c d) ≤ ENNReal.ofReal (2*d+h) := by
  have hb := levelBand_volume_le g 1 c d h (by norm_num) hquasi
  convert hb using 1
  congr 1
  ring

theorem levelBand_three_volume_le (g : ℝ → ℝ) (c d h : ℝ)
    (hquasi : ∀ x y, x ≤ y → g y - g x ≤ (y-x+h)/2) :
    volume (levelBand g 3 c d) ≤ ENNReal.ofReal ((2*d+h)/5) := by
  have hb := levelBand_volume_le g 3 c d h (by norm_num) hquasi
  convert hb using 1
  congr 1
  ring

def initialBand (e : ℝ) : Set ℝ :=
  Icc (initial e / 3) (initial 0 / 3)

theorem initialBand_volume (e : ℝ) :
    volume (initialBand e) = ENNReal.ofReal (2*e/3) := by
  rw [initialBand, Real.volume_Icc]
  congr 1
  dsimp [initial]
  ring

def threeMovingBands (g : ℝ → ℝ) (e h c : ℝ) : Set ℝ :=
  initialBand e ∪
    levelBand g 3 (-(41*e/20)) (41*e/20) ∪
      levelBand g 1 c (41*e/20)

-- The third cap is L0(j)=Gamma(0,b_j), while the initial cap remains
-- independent. Both third-gate crossings lie in the displayed bands
-- because 0<=L0(j)-Le(j)<=41e/20. For the true third form
-- x+t1+3t2, take c=-(t1+3t2)-41e/20. Equality faces stay included.
theorem threeMovingBands_volume_le (g : ℝ → ℝ) (e h c : ℝ)
    (he : 0 ≤ e) (hh0 : 0 ≤ h) (hh : h ≤ e/10)
    (hquasi : ∀ x y, x ≤ y → g y - g x ≤ (y-x+h)/2) :
    volume (threeMovingBands g e h c) ≤ ENNReal.ofReal ((428/75)*e) := by
  have hi := initialBand_volume e
  have h3 := levelBand_three_volume_le g (-(41*e/20)) (41*e/20) h hquasi
  have h1 := levelBand_one_volume_le g c (41*e/20) h hquasi
  have hn0 : 0 ≤ 2*e/3 := by positivity
  have hn3 : 0 ≤ (2*(41*e/20)+h)/5 := by linarith
  have hn1 : 0 ≤ 2*(41*e/20)+h := by linarith
  calc
    volume (threeMovingBands g e h c) ≤
        volume (initialBand e) +
          volume (levelBand g 3 (-(41*e/20)) (41*e/20)) +
            volume (levelBand g 1 c (41*e/20)) := by
      dsimp [threeMovingBands]
      exact (measure_union_le _ _).trans
        (add_le_add_right (measure_union_le _ _) _)
    _ ≤ ENNReal.ofReal (2*e/3) +
          ENNReal.ofReal ((2*(41*e/20)+h)/5) +
            ENNReal.ofReal (2*(41*e/20)+h) := by
      rw [hi]
      exact add_le_add (add_le_add le_rfl h3) h1
    _ = ENNReal.ofReal (2*e/3 + (2*(41*e/20)+h)/5 +
          (2*(41*e/20)+h)) := by
      rw [← ENNReal.ofReal_add hn0 hn3]
      rw [← ENNReal.ofReal_add (add_nonneg hn0 hn3) hn1]
    _ ≤ ENNReal.ofReal ((428/75)*e) :=
      ENNReal.ofReal_le_ofReal (by linarith)

-- Actual selected raw-owner set inclusion. No numerical volume premise,
-- branch-Boolean equality, or changing-mesh comparison is used here.
theorem actual_ownerSymmDiff_subset_crossingUnion
    (raw : FifthWireRow) (e : ℚ) (chi₀ chi : ℝ) (m : ℕ)
    (omega₀ omega : ℝ) (J : Finset (Fin 5 → Fin (m + 1)))
    (hselected₀ : ∀ j ∈ J,
      j ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells 0 chi₀ m omega₀ J)
    (hselected : ∀ j ∈ J,
      j ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells e chi m omega J)
    (hstop₀ : ∀ j ∈ J,
      P1OriginalHistoricalFifthOwnCubeAffineGates.firstStopCellCheck 0 m j = true)
    (hstop : ∀ j ∈ J,
      P1OriginalHistoricalFifthOwnCubeAffineGates.firstStopCellCheck
        (e : ℝ) m j = true) :
    ownerSymmDiff raw 0 e chi₀ chi m omega₀ omega J ⊆
      ⋃ j ∈ J, fixedOwnerBase raw m j ∩ movingGateCrossing 0 e m j := by
  intro t ht
  rcases ht with ht | ht
  · obtain ⟨j,hj,hj₀⟩ := mem_iUnion₂.mp ht.1
    have hnot : t ∉ P1FifthUnitBoxGainDecomposition.rawOwnerDomain
        raw e chi m omega j := by
      intro hjE
      exact ht.2 (mem_iUnion₂.mpr ⟨j,hj,hjE⟩)
    have hcross := selected_owner_difference_subset_gate_crossing
      raw 0 e chi₀ chi m omega₀ omega J J j
      (hselected₀ j hj) (hselected j hj) (hstop₀ j hj) (hstop j hj)
    exact mem_iUnion₂.mpr ⟨j,hj,hcross (Or.inl ⟨hj₀,hnot⟩)⟩
  · obtain ⟨j,hj,hjE⟩ := mem_iUnion₂.mp ht.1
    have hnot : t ∉ P1FifthUnitBoxGainDecomposition.rawOwnerDomain
        raw 0 chi₀ m omega₀ j := by
      intro hj₀
      exact ht.2 (mem_iUnion₂.mpr ⟨j,hj,hj₀⟩)
    have hcross := selected_owner_difference_subset_gate_crossing
      raw 0 e chi₀ chi m omega₀ omega J J j
      (hselected₀ j hj) (hselected j hj) (hstop₀ j hj) (hstop j hj)
    exact mem_iUnion₂.mpr ⟨j,hj,hcross (Or.inr ⟨hjE,hnot⟩)⟩

-- Exact next API binding, not asserted here: for fixed y in the four-
-- coordinate baseBox raw, define g_y(x) by the unique decoded Ico child
-- of t=piFinSuccAbove.symm (x,y), taking Gamma(0,box(thirdOwner child)).
-- On every selected/firstStop crossing point, the Phase4 seven-gate
-- inclusion and Phase8 VALUE rate put x in threeMovingBands g_y e h.
-- `gamma_mesh_first_rise` plus actual mesh index ordering gives hquasi
-- on the bounded raw x interval. Thus the theorem above yields the exact
-- fiber <=ofReal((428/75)e), and FubiniBridge gives the q-uniform volume.
-- Outside raw.originalBox this g_y can be extended by clamping x to its
-- original parent interval; this preserves hquasi and avoids assuming
-- any selected/firstStop verdict outside the genuine raw owner.

end
end ImbalancedChen.P1OriginalFifthMovingMeshFiberBands
