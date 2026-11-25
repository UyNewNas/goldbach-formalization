import ImbalancedChen.P2FiniteMarkedGamma5LogExtension
import ImbalancedChen.Part5OriginalH430HistoryScaleCore
import ImbalancedChen.Part5OriginalH430HistoryRoughnessCore

/-!
SOURCE ONLY / UNCOMPILED / ZERO ENDPOINT CREDIT.

Apply the actual Gamma5 logarithmic plateau to the existing enhanced U4
marked positions. The original book supplies the positive residual scale,
every old-prime floor, and the literal Gamma5 cutoff. No replacement aStar,
rank cap, PP estimate, or family-admission hypothesis is introduced.
-/
namespace ImbalancedChen.P2FiniteMarkedGamma5SeedPlateau

noncomputable section
open Finset Real Wu2008DoubleSieve LiLiuPrereqBuchstab
open P2EnhancedTwentyOneSameQWeighted (cutoff)
open P2EnhancedBadGamma5ArithmeticGeometry (badLabels)
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenRootRefinement
open Part5OriginalH430FrozenIntegerSupport Part5OriginalH430RequestedHistory
open Part5OriginalH430RequestedMember
open Part5OriginalH430TaggedArithmeticReceivers Part5OriginalH430HistoryQuotientCounts
open Part5OriginalH430SeedHistoryMass P2FiniteMarkedGamma5LogExtension
open scoped Classical BigOperators

private theorem position_scale {N n p dep : ℕ} {t : ℝ}
    (hN : 2 ≤ N) (ht : 0 ≤ t) (ht' : t ≤ 1/12)
    (hn : 1 / ((n : ℝ) + 1) ≤ 11/384) (hp : p ∈ originalBand N .U4)
    (l : LevelIndex N n .U4 t p dep) :
    0 < wordProduct l ∧ 1 < rootQ N n .U4 t p / wordProduct l := by
  obtain ⟨hd, _hL, _hQ, hres, _ha⟩ := scale_and_alpha hN ht ht' hn hp l
  have hbase : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  exact ⟨hd, (one_lt_rpow hbase frozenResidualFloor_pos).trans_le hres⟩

/-- The cutoff and old-prime floor are those of the actual selected book.
All required positivity/scale inputs of actual_source_one are supplied. -/
theorem enhanced_position_source_one {N n p dep m : ℕ} {t width : ℝ}
    (hN : 2 ≤ N) (ht : 0 ≤ t) (ht' : t ≤ 1/12)
    (hn : 1 / ((n : ℝ) + 1) ≤ 11/384) (hp : p ∈ originalBand N .U4)
    (hw : 0 < width) (l : LevelIndex N n .U4 t p dep) {qs : List ℕ}
    (hq : qs ∈ badLabels N (rootQ N n .U4 t p) (wordProduct l))
    (hm : m ∈ roughNumbers ((N : ℝ) / (wordProduct l * qs.prod : ℕ))
      (cutoff (rootQ N n .U4 t p) (wordProduct l) (227/50))) :
    0 < frozenLeafCutoffFloor ∧
      (∀ q ∈ (wordProduct l).primeFactors, (N : ℝ)^frozenLeafCutoffFloor ≤ (q : ℝ)) ∧
      (N : ℝ)^frozenLeafCutoffFloor ≤ cutoff (rootQ N n .U4 t p) (wordProduct l) (227/50) ∧
      integerExtension N (rootQ N n .U4 t p) width (wordProduct l)
        (sourcePair qs) (canonicalTail m) = 1 := by
  have hs := position_scale hN ht ht' hn hp l
  have hc := (history_integer_roughness hN ht ht' hn hp (levelOccurrence_source l).1).2.2
  refine ⟨frozenLeafCutoffFloor_pos, hc.1, hc.2, ?_⟩
  exact actual_source_one (by omega) hs.1 hs.2 hw hq hm

/-- A fixed finite selection uses its actual LevelIndex occurrences and
levelMark weights throughout. Same-Q prime/congruence tests may be retained
literally in F. This is an equality before any distribution estimate. -/
theorem enhanced_marked_source_test_unchanged {N n p dep : ℕ} {t width : ℝ}
    (hN : 2 ≤ N) (ht : 0 ≤ t) (ht' : t ≤ 1/12)
    (hn : 1 / ((n : ℝ) + 1) ≤ 11/384) (hp : p ∈ originalBand N .U4)
    (hw : 0 < width) (B : Finset (LevelIndex N n .U4 t p dep))
    (F : LevelIndex N n .U4 t p dep → List ℕ → ℕ → ℝ) :
    let Q := rootQ N n .U4 t p
    (∑ l ∈ B, levelMark l * ∑ qs ∈ badLabels N Q (wordProduct l),
      ∑ m ∈ roughNumbers ((N : ℝ) / (wordProduct l * qs.prod : ℕ)) (cutoff Q (wordProduct l) (227/50)),
        F l qs m * integerExtension N Q width (wordProduct l) (sourcePair qs) (canonicalTail m)) =
      ∑ l ∈ B, levelMark l * ∑ qs ∈ badLabels N Q (wordProduct l),
        ∑ m ∈ roughNumbers ((N : ℝ) / (wordProduct l * qs.prod : ℕ)) (cutoff Q (wordProduct l) (227/50)),
          F l qs m := by
  exact marked_source_test_unchanged B wordProduct levelMark F (by omega) hw
    (fun l _ => (position_scale hN ht ht' hn hp l).1)
    (fun l _ => (position_scale hN ht ht' hn hp l).2)

end
end ImbalancedChen.P2FiniteMarkedGamma5SeedPlateau
