import ImbalancedChen.Part5OriginalH430DescendantLimits

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Literal active-child knot pullbacks on the SAME physical coordinates.
Their numerators are affine in the physical residual.  Lowering the root
therefore changes each numerator by its exact slope times the root loss.
This proves a physical strip localization; it does not assume that a
proper strip has small parent-Theta mass or delete inherited equalities.
-/

namespace ImbalancedChen.Part5OriginalH430ActiveKnotPullbacks

noncomputable section
open Set
open P2EnhancedLowerPhysicalNode P2EnhancedLowerPhysicalTransition
open P2EnhancedLowerFinitePhysicalGraph P5OriginalActionMassBound
open P5OriginalFeedbackDomains
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenRootRefinement
open Part5OriginalH430FrozenPerturbation Part5OriginalH430NativeQueryPaths

/-- All five feedback query constructors are active; zero-prime retain
and fixed comparison shapes are deliberately absent from this type. -/
def knotNumerator (p : PhysicalNode) (z : Point) (c : ℝ) : FeedbackQuery → ℝ
  | .w1 _ j => (W1Anchor j-c)*residual p-W1Anchor j*z 0
  | .w2Singleton j _ =>
      ((originalW2At j).s0-c)*residual p-(originalW2At j).s0*z 0
  | .w2Pair j piece =>
      if piece.val < 2 then
        ((originalW2At j).s0-c)*residual p-(originalW2At j).s0*(z 0+z 1)
      else residual p-(c+1)*z 0-z 1
  | .buchstabUpper _ => residual p-(c+1)*z 0
  | .buchstabLower _ => residual p-(c+1)*z 0

def knotDenominator (p : PhysicalNode) (z : Point) : FeedbackQuery → ℝ
  | .w1 _ _ | .w2Singleton _ _ => residual p
  | .w2Pair _ piece => if piece.val < 2 then residual p else z 0
  | .buchstabUpper _ | .buchstabLower _ => z 0

def knotSlope (c : ℝ) : FeedbackQuery → ℝ
  | .w1 _ j => W1Anchor j-c
  | .w2Singleton j _ => (originalW2At j).s0-c
  | .w2Pair j piece => if piece.val < 2 then (originalW2At j).s0-c else 1
  | .buchstabUpper _ | .buchstabLower _ => 1

theorem knotDenominator_pos {p : PhysicalNode} {z : Point}
    (hL : 0 < residual p) (hx : 0 < z 0) (q : FeedbackQuery) :
    0 < knotDenominator p z q := by
  cases q <;> simp only [knotDenominator]
  all_goals first | exact hL | exact hx | split_ifs <;> assumption

/-- The original unclamped W2 D7/D8 formula is retained.  No query is
reset to two, and no table monotonicity is used. -/
theorem query_sub_knot {p : PhysicalNode} {z : Point}
    (hL : 0 < residual p) (hx : 0 < z 0) (q : FeedbackQuery) (c : ℝ) :
    (perform p q.shape z).argument-c = knotNumerator p z c q/knotDenominator p z q := by
  cases q with
  | w1 i j =>
      dsimp [FeedbackQuery.shape, perform, appendOne, singletonProfile, normalized,
        knotNumerator, knotDenominator]
      field_simp [hL.ne']
      ring
  | w2Singleton j piece =>
      dsimp [FeedbackQuery.shape, perform, appendOne, singletonProfile, normalized,
        knotNumerator, knotDenominator]
      field_simp [hL.ne']
      ring
  | w2Pair j piece =>
      by_cases hp : piece.val < 2
      · simp only [FeedbackQuery.shape, perform, appendPair, pairProfile, hp, if_true,
          fixedPairProfile, normalized, knotNumerator, knotDenominator]
        field_simp [hL.ne']
        ring
      · simp only [FeedbackQuery.shape, perform, appendPair, pairProfile, hp, if_false,
          movingPairProfile, normalized, knotNumerator, knotDenominator]
        rw [moving_pair_query_physical hL.ne']
        field_simp [hx.ne']
        ring
  | buchstabUpper i =>
      dsimp [FeedbackQuery.shape, perform, appendOne, buchstabArgument,
        knotNumerator, knotDenominator]
      field_simp [hx.ne']
      ring
  | buchstabLower i =>
      dsimp [FeedbackQuery.shape, perform, appendOne, buchstabArgument,
        knotNumerator, knotDenominator]
      field_simp [hx.ne']
      ring

theorem query_knot_comparisons {p : PhysicalNode} {z : Point}
    (hL : 0 < residual p) (hx : 0 < z 0) (q : FeedbackQuery) (c : ℝ) :
    ((perform p q.shape z).argument ≤ c ↔ knotNumerator p z c q ≤ 0) ∧
    ((perform p q.shape z).argument < c ↔ knotNumerator p z c q < 0) ∧
    ((perform p q.shape z).argument = c ↔ knotNumerator p z c q = 0) := by
  have hd := knotDenominator_pos hL hx q
  have he := query_sub_knot hL hx q c
  constructor
  · rw [← sub_nonpos, he, div_le_iff₀ hd, zero_mul]
  constructor
  · rw [← sub_neg, he, div_lt_iff₀ hd, zero_mul]
  · rw [← sub_eq_zero, he, div_eq_zero_iff]
    exact or_iff_left hd.ne'

theorem knotNumerator_difference (p r : PhysicalNode) (z : Point)
    (q : FeedbackQuery) (c : ℝ) :
    knotNumerator p z c q-knotNumerator r z c q =
      knotSlope c q*(residual p-residual r) := by
  cases q <;> simp only [knotNumerator, knotSlope]
  all_goals first | ring | split_ifs <;> ring

/-- A change of a closed comparison can only occur in the full closed
strip.  In particular an equality point is retained inside the budget. -/
theorem closed_comparison_change_strip {a b e : ℝ}
    (he : |a-b| ≤ e) (hchange : ¬ (a ≤ 0 ↔ b ≤ 0)) : |a| ≤ e := by
  have hab := abs_le.mp he
  by_cases ha : a ≤ 0
  · have hb : 0 < b := lt_of_not_ge (fun hb => hchange ⟨fun _ => hb, fun _ => ha⟩)
    rw [abs_of_nonpos ha]
    linarith
  · have ha0 : 0 < a := lt_of_not_ge ha
    have hb : b ≤ 0 := by
      by_contra hb
      exact hchange ⟨fun h => False.elim (ha h), fun h => False.elim (hb h)⟩
    rw [abs_of_pos ha0]
    linarith

theorem actual_knotNumerator_error {n : ℕ} {k : Root} {tau t : ℝ}
    (htau : 0 ≤ tau) (htauhi : tau ≤ 1/12) (ht : t ∈ rootBand k)
    {mesh depth : ℕ} (code : Program mesh depth) (z : Coordinates depth)
    (next : Point) (q : FeedbackQuery) (c : ℝ) :
    |knotNumerator (realize depth (sourceRoot k 0 t) code z).physical next c q-
      knotNumerator (realize depth (frozenRoot n k tau t) code z).physical next c q| ≤
      |knotSlope c q|*levelError n tau := by
  rw [knotNumerator_difference, actual_descendant_residual_loss,
    abs_mul, abs_of_nonneg (rootLoss_bounds htau htauhi ht).1]
  exact mul_le_mul_of_nonneg_left (rootLoss_bounds htau htauhi ht).2 (abs_nonneg _)

/-- Actual physical-coordinate localization for every active child at
every finite Program prefix.  The two positive residuals are local
denominator conditions, not assumed admission or target error bounds. -/
theorem actual_active_knot_change_strip {n : ℕ} {k : Root} {tau t : ℝ}
    (htau : 0 ≤ tau) (htauhi : tau ≤ 1/12) (ht : t ∈ rootBand k)
    {mesh depth : ℕ} (code : Program mesh depth) (z : Coordinates depth)
    (next : Point) (q : FeedbackQuery) (c : ℝ)
    (hL : 0 < residual (realize depth (sourceRoot k 0 t) code z).physical)
    (hM : 0 < residual (realize depth (frozenRoot n k tau t) code z).physical)
    (hx : 0 < next 0)
    (hchange : ¬
      ((perform (realize depth (sourceRoot k 0 t) code z).physical q.shape next).argument ≤ c ↔
       (perform (realize depth (frozenRoot n k tau t) code z).physical q.shape next).argument ≤ c)) :
    |knotNumerator (realize depth (sourceRoot k 0 t) code z).physical next c q| ≤
      |knotSlope c q|*levelError n tau := by
  apply closed_comparison_change_strip (actual_knotNumerator_error htau htauhi ht code z next q c)
  rw [← (query_knot_comparisons hL hx q c).1,
    ← (query_knot_comparisons hM hx q c).1]
  exact hchange

end
end ImbalancedChen.Part5OriginalH430ActiveKnotPullbacks
