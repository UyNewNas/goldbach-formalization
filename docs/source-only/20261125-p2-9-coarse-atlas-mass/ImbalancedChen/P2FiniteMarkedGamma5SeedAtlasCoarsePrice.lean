import ImbalancedChen.P2FiniteMarkedGamma5SeedAtlasFinitePP
import ImbalancedChen.P2FiniteMarkedGamma5CoarseAtlasMass

namespace ImbalancedChen.P2FiniteMarkedGamma5SeedAtlasCoarsePrice
noncomputable section
open Filter Finset Real
open Part5OriginalCausalSmoothAtlas (Plan Code)
open Part5OriginalH430FrozenRootRefinement (frozenLeafCutoffFloor frozenLeafCutoffFloor_pos)
open Part5OriginalH430SameQHistoryCells (cellQ)
open P2FiniteMarkedGamma5NativeSeedSum (fixedWeight)
open P2FiniteMarkedGamma5SeedAtlasFinitePP (Entry oldRank tailRank rank weight mark_nonneg)
open P2FiniteMarkedGamma5AllRankEulerBudget (scaleThreshold)
open P2FiniteMarkedGamma5AtlasFamily (atlasFamily_at_rank)
open P2FiniteMarkedGamma5RadialProfileCollar (radialWidth radialWidth_pos radialWidth_le_one)
open P2FiniteMarkedGamma5CoarseAtlasMass (mass finite_marked_bound)
open scoped Classical Topology BigOperators

/-- The finite receiver's literal ordinary term is uniformly bounded in
log N/N units. The root mesh is fixed first, and every code readout and
width follows the threshold. This is a coarse price, with no Theta conversion. -/
theorem ordinary_bounded (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      ∀ (P : Entry n → Plan)
        (A : (v : Entry n) → ℕ → (Fin (oldRank v) → Code (P v)) → Prop)
        (h : ℝ) (hp : 0 < h) (h8 : h ≤ 1/8),
      P2FiniteMarkedGamma5RadialRoughMass.norm N *
        (∑ v : Entry n, fixedWeight v.val.1 *
          p5z_labelledMass (Part3.labelledPrimeTuples (rank v) (2*N))
            (weight v (P v) (radialWidth h) frozenLeafCutoffFloor_pos
              (radialWidth_pos hp) (radialWidth_le_one hp h8) (A v) N)) ≤ C := by
  obtain ⟨C,hC,H⟩ := finite_marked_bound (univ : Finset (Entry n))
    (fun v => fixedWeight v.val.1) (fun v _ => mark_nonneg v.val.1)
  refine ⟨C,hC,?_⟩
  filter_upwards [H,tendsto_natCast_atTop_atTop.eventually_ge_atTop
    (scaleThreshold frozenLeafCutoffFloor)] with N HN hN
  intro P A h hp h8
  have hv (v : Entry n) :
      p5z_labelledMass (Part3.labelledPrimeTuples (rank v) (2*N))
        (weight v (P v) (radialWidth h) frozenLeafCutoffFloor_pos
          (radialWidth_pos hp) (radialWidth_le_one hp h8) (A v) N) =
      mass N (oldRank v) (tailRank v) (P v) (A v N)
        (log (cellQ N n v.val.2.1)) h := by
    unfold p5z_labelledMass mass
    apply sum_congr rfl
    intro u _
    unfold weight
    exact congrFun (atlasFamily_at_rank (P v) _ (oldRank v) (tailRank v)
      frozenLeafCutoffFloor (radialWidth h) (fun T => log (cellQ T n v.val.2.1))
      (A v) frozenLeafCutoffFloor_pos (radialWidth_pos hp) (radialWidth_le_one hp h8)
      v.property N hN) (fun j => ((u j).val : ℝ))
  simp_rw [hv]
  exact HN oldRank tailRank (fun v _ => v.property) P (fun v => A v N)
    (fun v => log (cellQ N n v.val.2.1)) (fun _ => h) (fun _ _ => ⟨hp,h8⟩)

end
end ImbalancedChen.P2FiniteMarkedGamma5SeedAtlasCoarsePrice
