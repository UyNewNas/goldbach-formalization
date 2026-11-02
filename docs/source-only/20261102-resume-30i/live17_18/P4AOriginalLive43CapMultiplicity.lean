import ImbalancedChen.P4AOriginalLive1718ActualChronology
import ImbalancedChen.P4AOriginalLiveBankMultiplicity

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Exact original source LIST accounting after all LIVE17/18/19 cap rewrites.
An arbitrary functional reads the entire frontier state and the actual cap.
No nodup premise, unweighted-set replacement or complete87 cover is used.
-/
namespace ImbalancedChen.P4AOriginalLive43CapMultiplicity
noncomputable section
open scoped Classical BigOperators
open P4AOriginalLive171819Atlas P4AOriginalLive171819CommonParent
open P4AOriginalLive171819PrimeBank P4AOriginalLive1718ActualChronology
open P4AOriginalLiveBankMultiplicity

abbrev Data := P5OriginalCommonRefinedConstructor.OriginalData

/-- The physical source-index formula replaces the genuine final slot19
on each actual bank, including all LIVE17 and both winner50 branches. -/
theorem actual_live_cap_terms (c : LiveCell) (d : Data) (he : 0 ≤ d.e)
    (N cap : ℕ) (hN : 1 < N) (w z : ℝ)
    (F : FirstExitDepthState ℕ → ℝ → ℝ) :
    ((selected c d.e d.chi d.m d.omega N cap w z
      (P5OriginalCommonRefinedConstructor.policy8 d (N : ℝ))).map (fun s =>
        F s (P4AOriginalPrior58Chronology.slot19 (N : ℝ)
          (P5OriginalCommonRefinedConstructor.lambda6 d (N : ℝ)) s.selectedPrefix))).sum =
    ((selected c d.e d.chi d.m d.omega N cap w z
      (P5OriginalCommonRefinedConstructor.policy8 d (N : ℝ))).map (fun s =>
        F s (P5OriginalAdoptedEighthPhysicalMasks.newCap (sourceIndex c)
          (point8 (N : ℝ) s.selectedPrefix)))).sum := by
  apply congrArg List.sum
  apply List.map_congr_left
  intro s hs
  rw [actual_common_live_cap c d he N cap hN w z s hs]

/-- Exactly one original live source tag contributes at each covered
occurrence. The state and its cap are preserved together, so even repeated
identical prefixes with different incoming mass or remaining primes survive. -/
theorem actual_live_cap_partition (d : Data) (he : 0 ≤ d.e)
    (N cap : ℕ) (hN : 1 < N) (w z : ℝ)
    (F : FirstExitDepthState ℕ → ℝ → ℝ) :
    (∑ c : LiveCell, ((selected c d.e d.chi d.m d.omega N cap w z
      (P5OriginalCommonRefinedConstructor.policy8 d (N : ℝ))).map (fun s =>
        F s (P5OriginalAdoptedEighthPhysicalMasks.newCap (sourceIndex c)
          (point8 (N : ℝ) s.selectedPrefix)))).sum) =
    ((liveUnion d N cap w z).map (fun s =>
      F s (P4AOriginalPrior58Chronology.slot19 (N : ℝ)
        (P5OriginalCommonRefinedConstructor.lambda6 d (N : ℝ)) s.selectedPrefix))).sum := by
  calc
    _ = ∑ c : LiveCell, ((selected c d.e d.chi d.m d.omega N cap w z
        (P5OriginalCommonRefinedConstructor.policy8 d (N : ℝ))).map (fun s =>
          F s (P4AOriginalPrior58Chronology.slot19 (N : ℝ)
            (P5OriginalCommonRefinedConstructor.lambda6 d (N : ℝ)) s.selectedPrefix))).sum := by
      apply Finset.sum_congr rfl
      intro c _
      exact (actual_live_cap_terms c d he N cap hN w z F).symm
    _ = _ := actual_common_live_partition d he N cap hN w z
      (fun s => F s (P4AOriginalPrior58Chronology.slot19 (N : ℝ)
        (P5OriginalCommonRefinedConstructor.lambda6 d (N : ℝ)) s.selectedPrefix))

/-- The exact frontier identity retains all uncovered source occurrences.
It cannot be read as an exhaustion result for the original58/87 atlas. -/
theorem actual_live_cap_frontier_split (d : Data) (he : 0 ≤ d.e)
    (N cap : ℕ) (hN : 1 < N) (w z : ℝ)
    (F : FirstExitDepthState ℕ → ℝ → ℝ) :
    ((commonFrontier d N cap w z).map (fun s =>
      F s (P4AOriginalPrior58Chronology.slot19 (N : ℝ)
        (P5OriginalCommonRefinedConstructor.lambda6 d (N : ℝ)) s.selectedPrefix))).sum =
    (∑ c : LiveCell, ((selected c d.e d.chi d.m d.omega N cap w z
      (P5OriginalCommonRefinedConstructor.policy8 d (N : ℝ))).map (fun s =>
        F s (P5OriginalAdoptedEighthPhysicalMasks.newCap (sourceIndex c)
          (point8 (N : ℝ) s.selectedPrefix)))).sum) +
    ((uncovered d N cap w z).map (fun s =>
      F s (P4AOriginalPrior58Chronology.slot19 (N : ℝ)
        (P5OriginalCommonRefinedConstructor.lambda6 d (N : ℝ)) s.selectedPrefix))).sum := by
  rw [actual_common_frontier_split d he N cap hN w z]
  congr 1
  apply Finset.sum_congr rfl
  intro c _
  exact actual_live_cap_terms c d he N cap hN w z F

/-- Explicit joint state/cap multiplicities, derived without enumeration.
Each original occurrence has its actual slot19 cap and exactly one tag. -/
theorem actual_live_state_cap_occurrences (d : Data) (he : 0 ≤ d.e)
    (N cap : ℕ) (hN : 1 < N) (w z : ℝ)
    (a : FirstExitDepthState ℕ) (value : ℝ) :
    (∑ c : LiveCell, ((selected c d.e d.chi d.m d.omega N cap w z
      (P5OriginalCommonRefinedConstructor.policy8 d (N : ℝ))).map (fun s =>
        if s = a ∧ P5OriginalAdoptedEighthPhysicalMasks.newCap (sourceIndex c)
          (point8 (N : ℝ) s.selectedPrefix) = value then (1 : ℝ) else 0)).sum) =
    ((liveUnion d N cap w z).map (fun s =>
      if s = a ∧ P4AOriginalPrior58Chronology.slot19 (N : ℝ)
        (P5OriginalCommonRefinedConstructor.lambda6 d (N : ℝ)) s.selectedPrefix = value
        then (1 : ℝ) else 0)).sum :=
  actual_live_cap_partition d he N cap hN w z
    (fun s capValue => if s = a ∧ capValue = value then 1 else 0)

/-- The exact original candidate58 source LIST, with its repetitions,
is the same incoming list used by the independent common constructor. -/
theorem candidate58_live_cap_terms (c : LiveCell) (d : Data) (he : 0 ≤ d.e)
    (N cap : ℕ) (hN : 1 < N) (w z : ℝ)
    (F : FirstExitDepthState ℕ → ℝ → ℝ) :
    ((selected c d.e d.chi d.m d.omega N cap w z
      (P4AOriginalPrior58Chronology.candidate58Policy (N : ℝ)
        (P5OriginalCommonRefinedConstructor.lambda6 d (N : ℝ))
        (P5OriginalCommonRefinedConstructor.policy5 d (N : ℝ)))).map (fun s =>
          F s (P4AOriginalPrior58Chronology.slot19 (N : ℝ)
            (P5OriginalCommonRefinedConstructor.lambda6 d (N : ℝ)) s.selectedPrefix))).sum =
    ((selected c d.e d.chi d.m d.omega N cap w z
      (P5OriginalCommonRefinedConstructor.policy8 d (N : ℝ))).map (fun s =>
        F s (P5OriginalAdoptedEighthPhysicalMasks.newCap (sourceIndex c)
          (point8 (N : ℝ) s.selectedPrefix)))).sum := by
  rw [P4AOriginalLive19ActualChronology.candidate58_common_selected]
  exact actual_live_cap_terms c d he N cap hN w z F

/-- Real production density residual, with any signed incoming state
weight. At arbitrary w this is the displayed finite density-term identity;
no stopped-continuation/unpresieved-density identification is asserted. -/
theorem actual_live43_density_partition (d : Data) (he : 0 ≤ d.e)
    (N cap : ℕ) (hN : 1 < N) (w z : ℝ)
    (weight : FirstExitDepthState ℕ → ℝ) :
    (∑ c : LiveCell, ((selected c d.e d.chi d.m d.omega N cap w z
      (P5OriginalCommonRefinedConstructor.policy8 d (N : ℝ))).map (fun s =>
        weight s * (actualFrozenFrontierDensityTerm false N cap
          (fun pre => (N : ℝ) ^ P5OriginalCommonRefinedConstructor.lambda6 d (N : ℝ)
            (rosserAncestor 6 pre)) s.selectedPrefix -
        actualFrozenFrontierDensityTerm false N cap
          (fun pre => (N : ℝ) ^ P5OriginalAdoptedEighthPhysicalMasks.newCap (sourceIndex c)
            (point8 (N : ℝ) pre)) s.selectedPrefix))).sum) =
    ((liveUnion d N cap w z).map (fun s =>
      weight s * (actualFrozenFrontierDensityTerm false N cap
        (fun pre => (N : ℝ) ^ P5OriginalCommonRefinedConstructor.lambda6 d (N : ℝ)
          (rosserAncestor 6 pre)) s.selectedPrefix -
      actualFrozenFrontierDensityTerm false N cap
        (fun pre => (N : ℝ) ^ P4AOriginalPrior58Chronology.slot19 (N : ℝ)
          (P5OriginalCommonRefinedConstructor.lambda6 d (N : ℝ)) pre) s.selectedPrefix))).sum := by
  simpa only [actualFrozenFrontierDensityTerm] using
    actual_live_cap_partition d he N cap hN w z
      (fun s capValue => weight s * (actualFrozenFrontierDensityTerm false N cap
        (fun pre => (N : ℝ) ^ P5OriginalCommonRefinedConstructor.lambda6 d (N : ℝ)
          (rosserAncestor 6 pre)) s.selectedPrefix -
        actualFrozenFrontierDensityTerm false N cap (fun _ => (N : ℝ) ^ capValue)
          s.selectedPrefix))

end
end ImbalancedChen.P4AOriginalLive43CapMultiplicity
