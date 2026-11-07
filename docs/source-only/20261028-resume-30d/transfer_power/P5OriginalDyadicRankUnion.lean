import ImbalancedChen.Part3AllKFamilyProperPowerSaving
import ImbalancedChen.P5OriginalJoinedLateRange

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The real chartBank is summed with all original ordered dyadic labels and
all ranks up to kStar. Its cardinal is computed from the actual word
constructor. The existing occurrence union already pays the bad-slot
factor k; no factorial or duplicate chart mass is invented. A common
strict scalar reserve is then chosen before every target/physical policy.
The signed noncollision-kernel clipping and its complete-scale asymptotic
application remain distinct, explicitly OPEN assembly obligations.
-/
namespace ImbalancedChen.P5Z.OriginalDyadicRankUnion
noncomputable section
open Classical
open scoped BigOperators
open ImbalancedChen.P5Z.ExactOriginalSmoothDyadicPartition
open ImbalancedChen.P5Z.ActualLabelledPrimeSmoothCharts
open ImbalancedChen.P5Z.AdmissibleAllRankIntegerGeometricFamily
open ImbalancedChen.Part3.AllKFamilyLambdaCorrectionBound
open ImbalancedChen.Part3.AllKLambdaChartCorrection
open ImbalancedChen.Part3.AllKFamilyProperPowerSaving

/-- The literal word constructor has no list duplicates, even when
coordinate VALUES repeat; label order is preserved by cons injectivity. -/
theorem words_card (A : Finset ℕ) (k : ℕ) : (words A k).card = A.card^k := by
  induction k with
  | zero => simp [words]
  | succ k ih =>
    have hinj : Set.InjOn (fun q : ℕ × List ℕ => q.1 :: q.2)
        (A.product (words A k) : Set (ℕ × List ℕ)) := by
      intro a ha b hb heq
      exact Prod.ext (List.cons.inj heq).1 (List.cons.inj heq).2
    rw [words, Finset.card_image_of_injOn hinj, Finset.card_product, ih, pow_succ]
    exact Nat.mul_comm _ _

theorem actual_chartBank_card (cap k : ℕ) :
    (chartBank cap k).card = (cutoffIndex cap+1)^k := by
  simp only [chartBank, words_card, Finset.card_range]

/-- All original ranks and all original dyadic labels. K is an independent
complete-product test kernel, exactly as in the existing chart identity. -/
def originalBankError {kStar : ℕ} (F : Family kStar) (T cap : ℕ)
    (chi eta : ℝ → ℝ) (kappa0 : ℝ) (K : ℕ → ℂ) : ℂ :=
  ∑ k : Fin (kStar+1), ∑ js ∈ chartBank cap k.val,
    ∑ us ∈ properChartWords cap k.val,
      lambdaWord us * chartTerm chi eta (bankWeight F T k) (T : ℝ) kappa0 js us * K us.prod

/-- Exact finite dyadic/rank union, using the actual per-chart occurrence
payment and the exact literal chart-bank cardinality. No count of
permutations, unordered product image, or unproved bank-size estimate is used. -/
theorem originalBankError_le_sum_powerBudgets {kStar : ℕ}
    (F : Family kStar) (T cap : ℕ) (hT : 0 < T) (chi eta : ℝ → ℝ)
    (hone : ∀ x, x ≤ 1 → chi x = 1) (hzero : ∀ x, 2 ≤ x → chi x = 0)
    (hchi : ∀ x, 0 ≤ chi x ∧ chi x ≤ 1) (heta : ∀ x, |eta x| ≤ 1)
    (kappa0 : ℝ) (K : ℕ → ℂ) (M H : ℝ) (hM : 0 ≤ M) (hH : 0 ≤ H)
    (hamp : ∀ (k : Fin (kStar+1)) us, us.length = k.val → ‖bankWeight F T k us‖ ≤ M)
    (hK : ∀ n, ‖K n‖ ≤ H) :
    ‖originalBankError F T cap chi eta kappa0 K‖ ≤
      ∑ k : Fin (kStar+1), ((cutoffIndex cap+1)^k.val : ℕ) *
        powerSavingBudget F T k cap M H := by
  unfold originalBankError
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro k hk
  calc
    _ ≤ ∑ js ∈ chartBank cap k.val,
        ‖∑ us ∈ properChartWords cap k.val,
          lambdaWord us * chartTerm chi eta (bankWeight F T k) (T : ℝ) kappa0 js us * K us.prod‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _js ∈ chartBank cap k.val, powerSavingBudget F T k cap M H := by
      apply Finset.sum_le_sum
      intro js hjs
      exact family_all_k_power_saving F T hT k chi eta hone hzero hchi heta cap kappa0 hjs
        K M H hM hH (hamp k) hK
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, actual_chartBank_card]

/-- The zeroth mixed-Euler bound supplies one M for every original rank
and every dyadic label before T, source cap, signed kernel or policy. -/
theorem uniform_originalBankError_bound {kStar : ℕ} (F : Family kStar) :
    ∃ C B : ℕ, 0 < C ∧ ∀ (T cap : ℕ), 0 < T →
      ∀ (chi eta : ℝ → ℝ), (∀ x, x ≤ 1 → chi x = 1) →
      (∀ x, 2 ≤ x → chi x = 0) → (∀ x, 0 ≤ chi x ∧ chi x ≤ 1) →
      (∀ x, |eta x| ≤ 1) → ∀ (kappa0 : ℝ) (K : ℕ → ℂ) (H : ℝ),
      0 ≤ H → (∀ n, ‖K n‖ ≤ H) →
      ‖originalBankError F T cap chi eta kappa0 K‖ ≤
        ∑ k : Fin (kStar+1), ((cutoffIndex cap+1)^k.val : ℕ) *
          powerSavingBudget F T k cap ((C : ℝ)*Real.log ((T : ℝ)+2)^B) H := by
  obtain ⟨C, B, hC, hamp⟩ := all_rank_bank_amplitude F
  refine ⟨C, B, hC, ?_⟩
  intro T cap hT chi eta hone hzero hchi heta kappa0 K H hH hK
  have hl : 0 ≤ Real.log ((T : ℝ)+2) := Real.log_nonneg (by positivity)
  exact originalBankError_le_sum_powerBudgets F T cap hT chi eta hone hzero hchi heta
    kappa0 K _ H (by positivity) hH (hamp T) hK

/-- A single actual reserve works for both original noncollision
proper-power saving and exact-product collision. It is selected from the
Family exponent and the physical support exponent, before N grows. -/
def commonMargin {kStar : ℕ} (F : Family kStar) (theta : ℝ) : ℝ :=
  min (F.aStar/8) ((1-theta)/8)

theorem commonMargin_pos {kStar : ℕ} (F : Family kStar) {theta : ℝ}
    (htheta : theta < 1) : 0 < commonMargin F theta := by
  exact lt_min (by have := F.aStar_pos; positivity) (by dsimp; linarith)

theorem commonMargin_noncollision_strict {kStar : ℕ} (F : Family kStar)
    (theta : ℝ) : 1-F.aStar/2+2*commonMargin F theta < 1 := by
  have hm : commonMargin F theta ≤ F.aStar/8 := min_le_left _ _
  have ha := F.aStar_pos
  linarith

theorem commonMargin_collision_strict {kStar : ℕ} (F : Family kStar) {theta : ℝ}
    (htheta : theta < 1) : theta+2*commonMargin F theta < 1 := by
  have hm : commonMargin F theta ≤ (1-theta)/8 := min_le_right _ _
  linarith

/-- The manuscript's inflated support exponent has the same strict
reserve, without an auxiliary support-cover exponent entering it. -/
theorem commonMargin_actual_theta {kStar : ℕ} (F : Family kStar) :
    0 < commonMargin F (599/1000) ∧
      1-F.aStar/2+2*commonMargin F (599/1000) < 1 ∧
      (599/1000 : ℝ)+2*commonMargin F (599/1000) < 1 := by
  exact ⟨commonMargin_pos F (by norm_num), commonMargin_noncollision_strict F _,
    commonMargin_collision_strict F (by norm_num)⟩

end
end ImbalancedChen.P5Z.OriginalDyadicRankUnion
