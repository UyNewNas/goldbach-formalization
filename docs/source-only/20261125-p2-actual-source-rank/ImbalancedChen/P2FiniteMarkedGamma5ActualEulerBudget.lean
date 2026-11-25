import ImbalancedChen.P2FiniteMarkedGamma5ActualRank
import ImbalancedChen.P2FiniteMarkedGamma5EulerWordBudget

/-!
SOURCE ONLY / UNCOMPILED / ZERO NEW FORMAL CREDIT.

Short actual-source adapter to the accepted original-word Euler budget.
The source theorem supplies the complete rank and its own common cutoff;
no new rank ceiling or free replacement cutoff is assumed. The constant
is fixed before all arithmetic source parameters and before width.

The source-import qualification boundary remains that of ActualRank.
This is not a complete Family, source licence, collar or PP/VM theorem.
-/
namespace ImbalancedChen.P2FiniteMarkedGamma5ActualEulerBudget

noncomputable section
open Real Wu2008DoubleSieve LiLiuPrereqBuchstab
open P2EnhancedTwentyOneSameQWeighted (cutoff)
open P2EnhancedBadGamma5ArithmeticGeometry (badLabels)
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenRootRefinement
open Part5OriginalH430FrozenIntegerSupport Part5OriginalH430RequestedHistory
open Part5OriginalH430TaggedArithmeticReceivers (originalBand)
open Part5OriginalH430SeedHistoryMass
open P2FiniteMarkedGamma5ActualRank P2FiniteMarkedGamma5EulerWordBudget
open P5Z.AdmissibleAllRankIntegerGeometricFamily (eulerWord)

/-- Uniformity in the actual old and complete rough ranks is a derived
consequence of the original arithmetic source, at its original cutoff. -/
theorem enhanced_position_mixedEuler_budget (order : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {N n p dep m : ℕ} {t width : ℝ},
      2 ≤ N → 0 ≤ t → t ≤ 1 / 12 →
      1 / ((n : ℝ) + 1) ≤ 11 / 384 → p ∈ originalBand N .U4 → 0 < width →
      ∀ (l : LevelIndex N n .U4 t p dep) {qs : List ℕ},
      qs ∈ badLabels N (rootQ N n .U4 t p) (wordProduct l) →
      m ∈ roughNumbers ((N : ℝ) / (wordProduct l * qs.prod : ℕ))
        (cutoff (rootQ N n .U4 t p) (wordProduct l) (227 / 50)) →
      ∀ w : List (Fin ((levelOccurrence l).current.old.length +
          (2 + m.primeFactorsList.length))), w.length ≤ order →
      ∀ v : Fin ((levelOccurrence l).current.old.length +
          (2 + m.primeFactorsList.length)) → ℝ,
        |eulerWord w
          (finPhysicalProfile (log (rootQ N n .U4 t p)) (N : ℝ) width
            ((N : ℝ) ^ frozenLeafCutoffFloor)) v| ≤
          C * (1 + width⁻¹) ^ order := by
  obtain ⟨C, hC, hbound⟩ :=
    finPhysicalProfile_boundedRank_mixedEuler_budget frozenSourceRankBound order
  refine ⟨C, hC, ?_⟩
  intro N n p dep m t width hN ht ht' hn hp hw l qs hq hm w hwlen v
  have hrank := enhanced_position_source_rank hN ht ht' hn hp l hq hm
  have hb : 0 < (N : ℝ) ^ frozenLeafCutoffFloor :=
    rpow_pos_of_pos (by exact_mod_cast (show 0 < N by omega)) _
  exact hbound _ _ hrank _ _ _ _ hb hw w hwlen v

end
end ImbalancedChen.P2FiniteMarkedGamma5ActualEulerBudget
