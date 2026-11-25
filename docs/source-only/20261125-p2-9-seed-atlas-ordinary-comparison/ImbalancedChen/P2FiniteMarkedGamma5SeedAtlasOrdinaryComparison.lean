import ImbalancedChen.P2FiniteMarkedGamma5SeedAtlasOrdinaryExcess
import ImbalancedChen.P2FiniteMarkedGamma5SeedOrdinaryReindex

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The actual fixed atlas Family ordinary mass is paid by the original U4
seed ordinaryBad mass, with coefficient one and one absolute epsilon.
Both the physical width and every finite native mesh precede the target.
-/
namespace ImbalancedChen.P2FiniteMarkedGamma5SeedAtlasOrdinaryComparison
noncomputable section
open Filter Finset Real
open P2FiniteMarkedGamma5NativeSeedSum (Index fixedWeight)
open P2FiniteMarkedGamma5SeedAtlasFinitePP (Entry rank weight)
open P2FiniteMarkedGamma5SeedCellReadout (planAt acceptAt)
open P2FiniteMarkedGamma5SeedAtlasOrdinaryExcess (atlas_mass_le_exact_cell_plus_epsilon)
open P2FiniteMarkedGamma5SeedOrdinaryReindex (literalMass literalMass_eq_seedMass)
open P2FiniteMarkedGamma5SeedOrdinaryPrice (seedMass profile_le_ordinary)
open Part5OriginalH430FrozenRootRefinement (frozenLeafCutoffFloor_pos)
open Part5OriginalH430FrozenIntegerSupport (rootQ)
open P2EnhancedBadGamma5ArithmeticGeometry (ordinaryBad)
open P2FiniteMarkedGamma5RadialProfileCollar
  (radialWidth radialWidth_pos radialWidth_le_one)
open P2FiniteMarkedGamma5RadialRoughMass (norm)
open scoped Classical BigOperators Topology

/-- This is the same finite Family and original marked sharp price at
each target. The final bound has no coprimality or approximation premise.
The returned width and mesh are fixed before N and the allowed tau. -/
theorem atlas_mass_le_original_ordinary_plus_epsilon
    (n : ℕ) (hn : 1/((n:ℝ)+1) ≤ 11/384)
    {epsilon : ℝ} (he : 0 < epsilon) :
    ∃ (h : ℝ) (hh : 0 < h) (h8 : h ≤ 1/8) (m : Index 430 → ℕ),
      ∀ᶠ N : ℕ in atTop, ∀ tau : ℝ, 0 ≤ tau → tau ≤ 1/12 →
      norm N * (∑ v : Entry n, fixedWeight v.val.1 *
        ∑ u ∈ Part3.labelledPrimeTuples (rank v) (2*N),
          weight v (planAt m v) (radialWidth h) frozenLeafCutoffFloor_pos
            (radialWidth_pos hh) (radialWidth_le_one hh h8)
            (acceptAt .U4 tau m v) N u) ≤
      norm N * seedMass N n .U4 tau
        (fun p w => ordinaryBad N (rootQ N n .U4 tau p) w.prod) + epsilon := by
  have he2 : 0 < epsilon/2 := half_pos he
  obtain ⟨m,Houter⟩ := atlas_mass_le_exact_cell_plus_epsilon n .U4 hn he2
  obtain ⟨h,hh,h8,Hprofile⟩ := profile_le_ordinary n hn he2
  refine ⟨h,hh,h8,m,?_⟩
  filter_upwards [Houter,Hprofile,eventually_gt_atTop (0:ℕ)] with N hout hprofile hN
  intro tau ht ht'
  have H := hout tau ht ht' h hh h8
  change _ ≤ norm N * literalMass N n tau h + epsilon/2 at H
  rw [literalMass_eq_seedMass n tau h hN hh h8] at H
  have H' := hprofile tau ht ht'
  linarith only [H,H']

end
end ImbalancedChen.P2FiniteMarkedGamma5SeedAtlasOrdinaryComparison
