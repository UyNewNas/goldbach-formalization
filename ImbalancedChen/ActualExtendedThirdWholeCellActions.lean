import ImbalancedChen.ActualExtendedThirdActionParameters
import ImbalancedChen.ActualExtendedThirdGammaApproximation

/-!
# Fixing the actual winning action on the entire closed coarse cell

A coarse width at most e/32 fixes the parameter selected at one actual cell
representative for all points of that same closed ordered portion. The W
branch is its literal minimum, with global slope bound two; v has its proved
global slope bound 3/2. Positive gate and endpoint margins survive throughout
the actual cell, including its ordering walls. No fine-atom license, source
factorization, or alpha-perturbation conclusion is assumed or asserted.
-/

namespace ImbalancedChen

noncomputable section

open Set Filter Topology
open VariableEnvelope
open scoped Classical

private theorem wInner_abs_sub {a b c a' b' c' δ : ℝ}
    (hb : |b - b'| ≤ δ) (hc : |c - c'| ≤ δ) :
    |wInner a b c - wInner a' b' c'| ≤ 2 * δ := by
  have hδ : 0 ≤ δ := (abs_nonneg _).trans hb
  obtain ⟨hb₁, hb₂⟩ := abs_le.mp hb
  obtain ⟨hc₁, hc₂⟩ := abs_le.mp hc
  have hf : |(66 - 34 * c) / 107 - (66 - 34 * c') / 107| ≤ 2 * δ :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  have hB : |B c - B c'| ≤ 2 * δ := by
    apply abs_le.mpr
    dsimp [B]
    constructor <;> linarith
  have hg : |(1 - 2 * b) - (1 - 2 * b')| ≤ 2 * δ :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  have hm : |min (B c) (1 - 2 * b) - min (B c') (1 - 2 * b')| ≤ 2 * δ :=
    (abs_min_sub_min_le_max _ _ _ _).trans (max_le hB hg)
  exact (abs_min_sub_min_le_max _ _ _ _).trans (max_le hf hm)

/-- The actual rescued action chosen at t has one constant parameter on the
whole closed portion. Its branch case is decided once, at that representative. -/
theorem actualExtendedThirdSelectedRescue_wholeCell {e : ℝ} {m : ℕ}
    {j : ActualExtendedThirdDyadicLabel m} (he0 : 0 < e) (he : e ≤ 1 / 384)
    (hmesh : actualExtendedThirdDyadicStep m ≤ e / 32)
    (hfull : actualExtendedThirdDyadicHi m j 0 ≤ mu - 4 * e)
    {t : Fin 3 → ℝ} (ht : t ∈ actualExtendedThirdPhysicalCell m j) (swapped : Bool)
    (hk : actualExtendedThirdLeastWinningIndex e m j = if swapped then 5 else 4) :
    let W := if swapped then wInner (t 0) (t 2) (t 1) else wInner (t 0) (t 1) (t 2)
    (W - v (t 0) ≤ e / 4 ∧ 1 / 2 ≤ actualExtendedThirdBaseParameter e m j ∧
      actualExtendedThirdBaseParameter e m j < 5 / 8 ∧
      actualExtendedThirdPhysicalLevel e m j + e ≤ actualExtendedThirdBaseParameter e m j ∧
      ∀ s ∈ actualExtendedThirdPhysicalCell m j,
        actualExtendedThirdBaseParameter e m j + e / 2 ≤ v (s 0)) ∨
    (e / 4 < W - v (t 0) ∧ 1 / 2 ≤ actualExtendedThirdRescueParameter e m j t ∧
      actualExtendedThirdRescueParameter e m j t < 5 / 8 ∧
      actualExtendedThirdPhysicalLevel e m j + e ≤ actualExtendedThirdRescueParameter e m j t ∧
      ∀ s ∈ actualExtendedThirdPhysicalCell m j,
        v (s 0) + e / 16 ≤ actualExtendedThirdRescueParameter e m j t ∧
          actualExtendedThirdRescueParameter e m j t + e / 16 ≤
            (if swapped then wInner (s 0) (s 2) (s 1) else wInner (s 0) (s 1) (s 2))) := by
  have haction := actualExtendedThirdSelectedRescue_action he0 he hfull ht swapped hk
  rcases haction with ⟨hclose, hθlo, hθhi, hlevel, hp⟩ | ⟨hgap, hθlo, hθhi, hlevel, hgate, hp⟩
  · refine Or.inl ⟨hclose, hθlo, hθhi, hlevel, ?_⟩
    intro s hs
    have hv := (abs_le.mp (v_abs_sub_le_of_le
      ((actualExtendedThirdPhysicalCell_coordinate_error hs ht 0).trans hmesh))).1
    linarith
  · refine Or.inr ⟨hgap, hθlo, hθhi, hlevel, ?_⟩
    intro s hs
    have hcoords (i : Fin 3) : |s i - t i| ≤ e / 32 :=
      (actualExtendedThirdPhysicalCell_coordinate_error hs ht i).trans hmesh
    have hv := (abs_le.mp (v_abs_sub_le_of_le (hcoords 0))).2
    have hW : |(if swapped then wInner (s 0) (s 2) (s 1) else wInner (s 0) (s 1) (s 2)) -
        (if swapped then wInner (t 0) (t 2) (t 1) else wInner (t 0) (t 1) (t 2))| ≤ 2 * (e / 32) := by
      cases swapped
      · exact wInner_abs_sub (a := s 0) (a' := t 0) (hcoords 1) (hcoords 2)
      · exact wInner_abs_sub (a := s 0) (a' := t 0) (hcoords 2) (hcoords 1)
    exact ⟨by linarith, by linarith [(abs_le.mp hW).1]⟩

/-- The actual nonleading-pair parameter selected at t licenses the same
pair on every point of the entire closed cell, with uniform e/4 surplus. -/
theorem actualExtendedThirdSelectedPair_wholeCell {e : ℝ} {m : ℕ}
    {j : ActualExtendedThirdDyadicLabel m} (he0 : 0 < e) (he : e ≤ 1 / 384)
    (hmesh : actualExtendedThirdDyadicStep m ≤ e / 32)
    (hfull : actualExtendedThirdDyadicHi m j 0 ≤ mu - 4 * e)
    {t : Fin 3 → ℝ} (ht : t ∈ actualExtendedThirdPhysicalCell m j) (yz : Bool)
    (hk : actualExtendedThirdLeastWinningIndex e m j = if yz then 7 else 6) :
    1 / 2 ≤ actualExtendedThirdPairParameter e m j t yz ∧
      actualExtendedThirdPairParameter e m j t yz < 5 / 8 ∧
      actualExtendedThirdPhysicalLevel e m j + e ≤ actualExtendedThirdPairParameter e m j t yz ∧
      ∀ s ∈ actualExtendedThirdPhysicalCell m j,
        (if yz then 2 * s 0 + s 1 + s 2 else s 0 + 2 * s 1 + s 2) + e / 4 ≤
          actualExtendedThirdPairParameter e m j t yz ∧
        actualExtendedThirdPairParameter e m j t yz + e / 4 ≤
          v (if yz then s 1 + s 2 else s 0 + s 2) := by
  obtain ⟨hθlo, hθhi, hlevel, hgate, hp⟩ := actualExtendedThirdSelectedPair_action he0 he hfull ht yz hk
  refine ⟨hθlo, hθhi, hlevel, ?_⟩
  intro s hs
  have hcoords (i : Fin 3) : |s i - t i| ≤ e / 32 :=
    (actualExtendedThirdPhysicalCell_coordinate_error hs ht i).trans hmesh
  have hc0 := abs_le.mp (hcoords 0)
  have hc1 := abs_le.mp (hcoords 1)
  have hc2 := abs_le.mp (hcoords 2)
  have hsum : |(if yz then s 1 + s 2 else s 0 + s 2) -
      (if yz then t 1 + t 2 else t 0 + t 2)| ≤ 2 * (e / 32) := by
    cases yz <;> simp <;> apply abs_le.mpr <;> constructor <;>
      linarith [hc0.1, hc0.2, hc1.1, hc1.2, hc2.1, hc2.2]
  have hv := (abs_le.mp (v_abs_sub_le_of_le hsum)).1
  have hg : (if yz then 2 * s 0 + s 1 + s 2 else s 0 + 2 * s 1 + s 2) -
      (if yz then 2 * t 0 + t 1 + t 2 else t 0 + 2 * t 1 + t 2) ≤ 4 * (e / 32) := by
    cases yz <;> simp <;> linarith [hc0.1, hc0.2, hc1.1, hc1.2, hc2.1, hc2.2]
  exact ⟨by linarith, by linarith⟩

/-- The same grid threshold precedes every full cell, representative and
point in that cell. The parameter stays fixed under all later fine refinements. -/
theorem actualExtendedThirdWholeCellAction_mesh_threshold {e : ℝ} (he : 0 < e) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → actualExtendedThirdDyadicStep m ≤ e / 32 := by
  obtain ⟨m₀, hm₀⟩ := Filter.eventually_atTop.mp
    (tendsto_actualExtendedThirdDyadicStep.eventually (gt_mem_nhds (by linarith : 0 < e / 32)))
  exact ⟨m₀, fun m hm => (hm₀ m hm).le⟩

end

end ImbalancedChen
