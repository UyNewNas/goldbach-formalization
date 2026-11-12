import ImbalancedChen.Part5OriginalH430ClassicalInclusiveLongMass

/-! The original seed and all four pre-existing feedback rounds on the
classical U3 causal positions. Only the Γ9--21 positive-product part
is trimmed. The Γ5 term at a general inherited word remains literal. -/
namespace ImbalancedChen.Part5OriginalH430ClassicalSeedLargeRemainder
noncomputable section
open Finset Real Wu2008DoubleSieve
open P2EnhancedSwitchedTrueNormalization (thetaConversion)
open P2EnhancedUnitSourceMass (thetaConversion_nonneg)
open P2SeedOmegaLiteralFibre (K)
open P2OriginalW2CentreThetaPayment (groupedSigma)
open Part5OriginalH430FrozenIntegerSupport (rootQ)
open Part5OriginalH430FrozenClassicalRootModuli
open Part5OriginalH430RequestedHistory Part5OriginalH430SeedHistoryMass
open Part5OriginalH430SeedPurifiedPrimeFibres (badFibre switchedFibre)
open Part5OriginalH430SeedSameCarrierPP
open Part5OriginalH430ClassicalCausalSeedScale
open Part5OriginalH430ClassicalSmallSwitchedIntegers
open Part5OriginalH430ClassicalSwitchedSmallPayment
open Part5OriginalH430SeedMarkedPositiveAP (pairCredit)
open Part5OriginalH430SelectedOrdinaryPairCounts (trueAt)
open Part5OriginalH430SeedRosserCountCredit (credit)
open Part5OriginalH430SeedFourMarkedRounds (originalRound)
open Part5OriginalH430SeedSevenPhysicalWindows (physicalFeedback)
open Part5OriginalH430SeedSevenOrdinaryAP (ordinaryAP)
open scoped Classical BigOperators

def largeSwitched (tested : Bool) (N : ℕ) (Q : ℝ) (d : ℕ) (κ : ℝ) : ℝ :=
  badFibre tested N Q d+allLarge tested N Q d (smallProduct N κ)

def largeBalance {N n p dep : ℕ} {τ : ℝ} (κ : ℝ)
    (B : Finset (LevelIndex N n .U3 τ p dep)) : ℝ :=
  let Q := rootQ N n .U3 τ p
  ∑ l∈B,levelMark l*(largeSwitched true N Q (wordProduct l) κ-
    (K/4)*thetaConversion N (wordProduct l)*largeSwitched false N Q (wordProduct l) κ)

theorem marked_split {N n p dep : ℕ} {τ : ℝ} (κ : ℝ)
    (B : Finset (LevelIndex N n .U3 τ p dep)) :
    let Q := rootQ N n .U3 τ p; let X := smallProduct N κ
    switchedPPBalance B-largeBalance κ B =
      (∑ l∈B,levelMark l*allSmall true N Q (wordProduct l) X)-
      ∑ l∈B,levelMark l*((K/4)*thetaConversion N (wordProduct l)*allSmall false N Q (wordProduct l) X) := by
  unfold switchedPPBalance largeBalance
  dsimp only
  rw [←sum_sub_distrib,←sum_sub_distrib]
  apply sum_congr rfl
  intro l _
  unfold switchedFibre largeSwitched
  rw [all_parts true _ _ _ (smallProduct N κ),all_parts false _ _ _ (smallProduct N κ)]
  ring

theorem actual_large_product_difference {κ ε : ℝ} (hk : 0<κ) (he : 0<ε) :
    ∃ T : ℕ,4≤T ∧ ∀ N : ℕ,T≤N → ∀ (n : ℕ) (τ : ℝ) (p dep : ℕ),
      0≤τ → τ≤1/12 → 1/((n:ℝ)+1)≤11/384 → p∈classicalBand N →
      ∀ B : Finset (LevelIndex N n .U3 τ p dep),
        |switchedPPBalance B-largeBalance κ B|≤ε*markedTheta B := by
  obtain ⟨T,h4,hpay⟩ := all_marked_small_products hk he
  refine ⟨T,h4,?_⟩
  intro N hN n τ p dep ht ht' hn hp B
  let Q := rootQ N n .U3 τ p
  let X := smallProduct N κ
  have hpays := hpay N hN n τ p dep ht ht' hn hp B
  have hpos (l : LevelIndex N n .U3 τ p dep) : 0≤thetaConversion N (wordProduct l) := by
    have hh := actual_cubic_residual (by omega : 2≤N) ht ht' hn hp l
    exact thetaConversion_nonneg (h4.trans hN) hh.1 hh.2.1
  have ha : 0≤∑ l∈B,levelMark l*allSmall true N Q (wordProduct l) X :=
    sum_nonneg (fun l _ => mul_nonneg (mark_pos _).le (all_small_nonneg true N Q _ X))
  have hb : 0≤∑ l∈B,levelMark l*((K/4)*thetaConversion N (wordProduct l)*allSmall false N Q (wordProduct l) X) :=
    sum_nonneg (fun l _ => mul_nonneg (mark_pos _).le (mul_nonneg
      (mul_nonneg (by norm_num [K]) (hpos l)) (all_small_nonneg false N Q _ X)))
  rw [marked_split,abs_le]
  dsimp only at hpays ⊢
  constructor <;> linarith only [hpays.1,hpays.2,ha,hb]

/-- The true counts and positive credits on the left are those of the
original seed, at S=seedPositions. The large-product discrepancy, the
seven ordinary AP lanes and the prior feedback mark retain their signs. -/
theorem classical_seed_and_four_rounds_large {κ ε : ℝ} (hk : 0<κ) (he : 0<ε) :
    ∃ T : ℕ,4≤T ∧ ∀ N : ℕ,T≤N → Even N → ∀ (n : ℕ) (τ : ℝ) (p : ℕ),
      0≤τ → τ≤1/12 → 1/((n:ℝ)+1)≤11/384 → p∈classicalBand N →
      let Q := rootQ N n .U3 τ p; let S := seedPositions N n .U3 τ p
      let D := S.image wordProduct; let σ := groupedSigma S wordProduct levelMark
      let C := ∑ l∈S,levelMark l*trueAt l
      0≤credit N Q D σ ∧ 0≤pairCredit S ∧
        (5*(C-(1-1/50:ℝ)*markedTheta S)+credit N Q D σ+pairCredit S ≤
          ordinaryAP S+largeBalance κ S+ε*markedTheta S) ∧
        ∀ j : Fin 4,5*(C-(1-originalRound j.succ)*markedTheta S)+credit N Q D σ+pairCredit S ≤
          ordinaryAP S+largeBalance κ S+5*originalRound j.castSucc*
            (∑ l∈S,levelMark l*physicalFeedback N Q (wordLevel l) (wordProduct l))+ε*markedTheta S := by
  obtain ⟨Ta,h4,ha⟩ := actual_seed_and_four_rounds_at_common_prime_restriction (half_pos he)
  obtain ⟨Tb,_,hb⟩ := actual_large_product_difference hk (half_pos he)
  refine ⟨max Ta Tb,h4.trans (le_max_left _ _),?_⟩
  intro N hN heven n τ p ht ht' hn hp
  have h := ha N ((le_max_left Ta Tb).trans hN) heven n .U3 τ p ht ht' hn (mem_filter.mp hp).1
  have hpaid := hb N ((le_max_right Ta Tb).trans hN) n τ p 0 ht ht' hn hp (seedPositions N n .U3 τ p)
  have hupper := (abs_le.mp hpaid).2
  dsimp only at h ⊢
  refine ⟨h.1,h.2.1,?_,?_⟩
  · linarith only [h.2.2.1,hupper]
  · intro j
    linarith only [h.2.2.2 j,hupper]

end
end ImbalancedChen.Part5OriginalH430ClassicalSeedLargeRemainder
