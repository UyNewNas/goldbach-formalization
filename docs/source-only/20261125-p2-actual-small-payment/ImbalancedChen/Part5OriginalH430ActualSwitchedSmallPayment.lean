import ImbalancedChen.Part5OriginalH430ClassicalSwitchedSmallPayment

/-!
Pay the actual Gamma9--21 small complete-product contribution on every
original U3/U4 generated history, using the existing scalar payment.

The old marked consumer was restricted to classicalBand at U3.  Its
scalar supplier only requires d > 0, Q <= N and the fixed residual floor;
the original history geometry supplies these at both original roots.
No classical cubic-residual or alpha > 3 assertion is used here.

Gamma5, the large complete-product discrepancy, all ordinary AP lanes,
and the earlier feedback term remain literal.  This is a source-only
candidate; it carries no compile, kernel, or P2-completion claim.
-/

namespace ImbalancedChen.Part5OriginalH430ActualSwitchedSmallPayment

noncomputable section
open Finset Real Wu2008DoubleSieve
open P2EnhancedSwitchedTrueNormalization (thetaConversion)
open P2EnhancedUnitSourceMass (thetaConversion_nonneg)
open P2OriginalChildPhysicalNormalization (thetaAtom)
open P2OriginalW2CentreThetaPayment (groupedSigma)
open P2SeedOmegaLiteralFibre (K)
open Part5OriginalH430PhysicalRoots
open Part5OriginalH430FrozenRootRefinement
open Part5OriginalH430FrozenIntegerSupport
open Part5OriginalH430RequestedHistory
open Part5OriginalH430TaggedArithmeticReceivers (originalBand)
open Part5OriginalH430SeedHistoryMass
open Part5OriginalH430OriginalRootQBound (original_root_Q_le_target)
open Part5OriginalH430SeedPurifiedPrimeFibres (badFibre switchedFibre)
open Part5OriginalH430SeedSameCarrierPP
open Part5OriginalH430ClassicalCausalSeedScale (smallProduct)
open Part5OriginalH430ClassicalSmallSwitchedIntegers
open Part5OriginalH430ClassicalSwitchedSmallPayment (small_both_atoms)
open Part5OriginalH430SeedMarkedPositiveAP (pairCredit)
open Part5OriginalH430SelectedOrdinaryPairCounts (trueAt)
open Part5OriginalH430SeedRosserCountCredit (credit)
open Part5OriginalH430SeedFourMarkedRounds (originalRound)
open Part5OriginalH430SeedSevenPhysicalWindows (physicalFeedback)
open Part5OriginalH430SeedSevenOrdinaryAP (ordinaryAP)
open scoped Classical BigOperators

/-- Both actual nonnegative small-product sums are paid with their own
original marked theta mass, uniformly over U3/U4 and every generated
history subfamily.  No division by that mass is used. -/
theorem all_marked_small_products {κ ε : ℝ} (hk : 0 < κ) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (n : ℕ) (r : Root) (t : ℝ) (p dep : ℕ),
      0 ≤ t → t ≤ 1/12 → 1/((n : ℝ)+1) ≤ 11/384 → p ∈ originalBand N r →
      ∀ B : Finset (LevelIndex N n r t p dep),
      let Q := rootQ N n r t p
      let X := smallProduct N κ
      (∑ l ∈ B, levelMark l * allSmall true N Q (wordProduct l) X) ≤ ε * markedTheta B ∧
      (∑ l ∈ B, levelMark l *
        ((K/4) * thetaConversion N (wordProduct l) * allSmall false N Q (wordProduct l) X))
        ≤ ε * markedTheta B := by
  obtain ⟨T, h4, ha⟩ := small_both_atoms hk he
  refine ⟨T, h4, ?_⟩
  intro N hN n r t p dep ht ht' hn hp B
  let Q := rootQ N n r t p
  let X := smallProduct N κ
  have h2 : 2 ≤ N := by omega
  have hQ := original_root_Q_le_target N n r t p h2 ht ht' hp
  have h (l : LevelIndex N n r t p dep) := by
    have hh := scale_and_alpha h2 ht ht' hn hp l
    exact ha N hN Q (wordProduct l) hh.1 hQ hh.2.2.2.1
  dsimp only
  unfold markedTheta
  simp only [mul_sum]
  constructor
  · apply sum_le_sum
    intro l _
    calc
      _ ≤ levelMark l * (ε * thetaAtom N Q (wordProduct l)) :=
        mul_le_mul_of_nonneg_left (h l).1 (mark_pos (levelOccurrence l)).le
      _ = _ := by ring
  · apply sum_le_sum
    intro l _
    calc
      _ ≤ levelMark l * (ε * thetaAtom N Q (wordProduct l)) :=
        mul_le_mul_of_nonneg_left (h l).2 (mark_pos (levelOccurrence l)).le
      _ = _ := by ring

/-- The retained signed discrepancy is the original Gamma5 term plus
the large Gamma9--21 complete products, with the original K/4 price.
Only the history root index is generalized from the classical consumer. -/
def remainingSwitchedBalance {N n p dep : ℕ} {r : Root} {t : ℝ} (κ : ℝ)
    (B : Finset (LevelIndex N n r t p dep)) : ℝ :=
  let Q := rootQ N n r t p
  let X := smallProduct N κ
  ∑ l ∈ B, levelMark l *
    ((badFibre true N Q (wordProduct l) + allLarge true N Q (wordProduct l) X) -
      (K/4) * thetaConversion N (wordProduct l) *
        (badFibre false N Q (wordProduct l) + allLarge false N Q (wordProduct l) X))

/-- Exact same-carrier partition: no label, repeated word occurrence,
unit tail, prime test, or converted coefficient is discarded. -/
theorem marked_split {N n p dep : ℕ} {r : Root} {t : ℝ} (κ : ℝ)
    (B : Finset (LevelIndex N n r t p dep)) :
    let Q := rootQ N n r t p
    let X := smallProduct N κ
    switchedPPBalance B - remainingSwitchedBalance κ B =
      (∑ l ∈ B, levelMark l * allSmall true N Q (wordProduct l) X) -
      ∑ l ∈ B, levelMark l *
        ((K/4) * thetaConversion N (wordProduct l) * allSmall false N Q (wordProduct l) X) := by
  unfold switchedPPBalance remainingSwitchedBalance
  dsimp only
  rw [← sum_sub_distrib, ← sum_sub_distrib]
  apply sum_congr rfl
  intro l _
  unfold switchedFibre
  rw [all_parts true _ _ _ (smallProduct N κ), all_parts false _ _ _ (smallProduct N κ)]
  ring

/-- The small complete-product part is an actual epsilon-theta error
for either original root, with no distribution or target-debt premise. -/
theorem actual_small_product_difference {κ ε : ℝ} (hk : 0 < κ) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (n : ℕ) (r : Root) (t : ℝ) (p dep : ℕ),
      0 ≤ t → t ≤ 1/12 → 1/((n : ℝ)+1) ≤ 11/384 → p ∈ originalBand N r →
      ∀ B : Finset (LevelIndex N n r t p dep),
        |switchedPPBalance B - remainingSwitchedBalance κ B| ≤ ε * markedTheta B := by
  obtain ⟨T, h4, hpay⟩ := all_marked_small_products hk he
  refine ⟨T, h4, ?_⟩
  intro N hN n r t p dep ht ht' hn hp B
  let Q := rootQ N n r t p
  let X := smallProduct N κ
  have hpays := hpay N hN n r t p dep ht ht' hn hp B
  have hpos (l : LevelIndex N n r t p dep) : 0 ≤ thetaConversion N (wordProduct l) := by
    have hh := scale_and_alpha (by omega : 2 ≤ N) ht ht' hn hp l
    have hR : 1 < Q / (wordProduct l : ℝ) :=
      (one_lt_rpow (by exact_mod_cast (show 1 < N by omega))
        frozenResidualFloor_pos).trans_le hh.2.2.2.1
    exact thetaConversion_nonneg (h4.trans hN) hh.1 hR
  have ha : 0 ≤ ∑ l ∈ B, levelMark l * allSmall true N Q (wordProduct l) X :=
    sum_nonneg (fun l _ => mul_nonneg (mark_pos (levelOccurrence l)).le
      (all_small_nonneg true N Q _ X))
  have hb : 0 ≤ ∑ l ∈ B, levelMark l *
      ((K/4) * thetaConversion N (wordProduct l) * allSmall false N Q (wordProduct l) X) :=
    sum_nonneg (fun l _ => mul_nonneg (mark_pos (levelOccurrence l)).le
      (mul_nonneg (mul_nonneg (by norm_num [K]) (hpos l))
        (all_small_nonneg false N Q _ X)))
  rw [marked_split, abs_le]
  dsimp only at hpays ⊢
  constructor <;> linarith only [hpays.1, hpays.2, ha, hb]

/-- Consume the payment in the actual original seed and each existing
feedback round, for both U3 and U4.  The remaining analytic debts keep
their original signs, masses and history carriers. -/
theorem actual_seed_and_four_rounds_after_small_payment
    {κ ε : ℝ} (hk : 0 < κ) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (n : ℕ) (r : Root) (t : ℝ) (p : ℕ),
      0 ≤ t → t ≤ 1/12 → 1/((n : ℝ)+1) ≤ 11/384 → p ∈ originalBand N r →
      let Q := rootQ N n r t p
      let S := seedPositions N n r t p
      let D := S.image wordProduct
      let σ := groupedSigma S wordProduct levelMark
      let C := ∑ l ∈ S, levelMark l * trueAt l
      0 ≤ credit N Q D σ ∧ 0 ≤ pairCredit S ∧
        (5 * (C - (1-1/50 : ℝ) * markedTheta S) + credit N Q D σ + pairCredit S ≤
          ordinaryAP S + remainingSwitchedBalance κ S + ε * markedTheta S) ∧
        ∀ j : Fin 4,
          5 * (C - (1-originalRound j.succ) * markedTheta S) + credit N Q D σ + pairCredit S ≤
            ordinaryAP S + remainingSwitchedBalance κ S +
              5 * originalRound j.castSucc *
                (∑ l ∈ S, levelMark l * physicalFeedback N Q (wordLevel l) (wordProduct l)) +
              ε * markedTheta S := by
  obtain ⟨Ta, h4, ha⟩ := actual_seed_and_four_rounds_at_common_prime_restriction (half_pos he)
  obtain ⟨Tb, _, hb⟩ := actual_small_product_difference hk (half_pos he)
  refine ⟨max Ta Tb, h4.trans (le_max_left _ _), ?_⟩
  intro N hN heven n r t p ht ht' hn hp
  have h := ha N ((le_max_left Ta Tb).trans hN) heven n r t p ht ht' hn hp
  have hpaid := hb N ((le_max_right Ta Tb).trans hN) n r t p 0 ht ht' hn hp
    (seedPositions N n r t p)
  have hupper := (abs_le.mp hpaid).2
  dsimp only at h ⊢
  refine ⟨h.1, h.2.1, ?_, ?_⟩
  · linarith only [h.2.2.1, hupper]
  · intro j
    linarith only [h.2.2.2 j, hupper]

end
end ImbalancedChen.Part5OriginalH430ActualSwitchedSmallPayment
