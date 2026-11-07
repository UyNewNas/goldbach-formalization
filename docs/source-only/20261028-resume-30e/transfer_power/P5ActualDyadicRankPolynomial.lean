import ImbalancedChen.P5OriginalDyadicRankUnion
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Actual source cap ceil(Family.upper*T), literal chartBank cardinal and the
complete rank sum are paid by one fixed logarithmic power. Constants and
threshold precede all chart labels, ranks, cutoffs and independent kernels.
No active-cap range or whole PP error is supplied as a hypothesis here.
-/
namespace ImbalancedChen.P5Z.ActualDyadicRankPolynomial
noncomputable section
open Classical Filter Topology
open scoped BigOperators
open ImbalancedChen.P5Z.ExactOriginalSmoothDyadicPartition
open ImbalancedChen.P5Z.ActualLabelledPrimeSmoothCharts
open ImbalancedChen.P5Z.AdmissibleAllRankIntegerGeometricFamily
open ImbalancedChen.Part3.OriginalProperPowerActualChart
open ImbalancedChen.Part3.AllKFamilyLambdaCorrectionBound
open ImbalancedChen.Part3.AllKLambdaChartCorrection
open ImbalancedChen.Part3.AllKFamilyProperPowerSaving
open ImbalancedChen.P5Z.OriginalDyadicRankUnion

/-- The canonical cap is forced by the actual Family product support.
Every positive coordinate divides that product, including composite proper
powers. Thus ceil(upper*T) contains every ACTIVE ordered integer word. -/
theorem active_word_mem_actual_source_cap {kStar : ℕ} (F : Family kStar)
    (T sourceCap : ℕ) (k : Fin (kStar+1)) {us : List ℕ}
    (hus : us ∈ integerWords sourceCap k.val) (hW : bankWeight F T k us ≠ 0) :
    us ∈ integerWords (Nat.ceil (F.upper*(T : ℝ))) k.val := by
  obtain ⟨hlen, hmem⟩ := words_spec (Finset.Icc 1 sourceCap) k.val us hus
  have hpos : 0 < us.prod := List.prod_pos (fun n hn => by
    have := (Finset.mem_Icc.mp (hmem n hn)).1
    omega)
  have hcap : us.prod ≤ Nat.ceil (F.upper*(T : ℝ)) := by
    exact_mod_cast (bankWeight_support F T k hlen hW).2.trans (Nat.le_ceil _)
  apply words_mem (Finset.Icc 1 (Nat.ceil (F.upper*(T : ℝ)))) k.val us hlen
  intro n hn
  exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp (hmem n hn)).1,
    (Nat.le_of_dvd hpos (List.dvd_prod hn)).trans hcap⟩

def bankLogConstant : ℝ := 3+2/Real.log 2

theorem bankLogConstant_pos : 0 < bankLogConstant := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  dsimp [bankLogConstant]
  positivity

/-- The source's ACTUAL cutoffIndex=log2(cap)+1, with cap=ceil(U*T).
The two endpoint paddings and the natural ceiling are both paid. -/
theorem actual_cutoffIndex_le_log (U : ℝ) (hU : 0 < U) (T : ℕ)
    (hT : 2 ≤ T) (hTU : U+1 ≤ (T : ℝ)) (hlogT : 1 ≤ Real.log (T : ℝ)) :
    ((cutoffIndex (Nat.ceil (U*(T : ℝ)))+2 : ℕ) : ℝ) ≤
      bankLogConstant*Real.log (T : ℝ) := by
  let cap := Nat.ceil (U*(T : ℝ))
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast (show 1 ≤ T by omega)
  have hTp : (0 : ℝ) < T := zero_lt_one.trans_le hT1
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hceil : (cap : ℝ) ≤ U*(T : ℝ)+1 :=
    (Nat.ceil_lt_add_one (mul_nonneg hU.le hTp.le)).le
  have hTUproduct := mul_le_mul_of_nonneg_right hTU hTp.le
  have hcapSq : (cap : ℝ) ≤ (T : ℝ)^2 := by nlinarith
  by_cases hcap0 : cap = 0
  · have hL : 3 ≤ bankLogConstant := by
      dsimp [bankLogConstant]
      linarith [div_nonneg (by norm_num : (0 : ℝ) ≤ 2) hlog2.le]
    have hmul := mul_le_mul_of_nonneg_left hlogT bankLogConstant_pos.le
    change ((cutoffIndex cap+2 : ℕ) : ℝ) ≤ _
    simp only [hcap0, cutoffIndex, Nat.log2_zero, Nat.zero_add, Nat.cast_ofNat]
    linarith
  · have hpow : (2 : ℕ)^(Nat.log2 cap) ≤ cap := (Nat.le_log2 hcap0).mp le_rfl
    have hpowR : (2 : ℝ)^(Nat.log2 cap) ≤ (T : ℝ)^2 :=
      (show (2 : ℝ)^(Nat.log2 cap) ≤ (cap : ℝ) by exact_mod_cast hpow).trans hcapSq
    have hl := Real.log_le_log (pow_pos (by norm_num : (0 : ℝ) < 2) _) hpowR
    simp only [Real.log_pow, Nat.cast_ofNat] at hl
    have hj : (Nat.log2 cap : ℝ) ≤ (2/Real.log 2)*Real.log (T : ℝ) := by
      calc
        _ ≤ (2*Real.log (T : ℝ))/Real.log 2 := (le_div_iff₀ hlog2).mpr hl
        _ = _ := by ring
    change ((cutoffIndex cap+2 : ℕ) : ℝ) ≤ _
    simp only [cutoffIndex, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
    dsimp [bankLogConstant]
    nlinarith

theorem eventually_actual_cutoffIndex_le_log (U : ℝ) (hU : 0 < U) :
    ∀ᶠ T : ℕ in atTop, 2 ≤ T ∧
      ((cutoffIndex (Nat.ceil (U*(T : ℝ)))+2 : ℕ) : ℝ) ≤
        bankLogConstant*Real.log (T : ℝ) := by
  have hTU : ∀ᶠ T : ℕ in atTop, U+1 ≤ (T : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (U+1))
  have hlogT : ∀ᶠ T : ℕ in atTop, 1 ≤ Real.log (T : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 1)
  filter_upwards [eventually_ge_atTop (2 : ℕ), hTU, hlogT] with T hT hU' hl
  exact ⟨hT, actual_cutoffIndex_le_log U hU T hT hU' hl⟩

def unionConstant {kStar : ℕ} (F : Family kStar) : ℝ :=
  2*((kStar+1 : ℕ) : ℝ)*(kStar : ℝ)*(5 : ℝ)^kStar*F.upper/Real.sqrt F.lower

theorem unionConstant_nonneg {kStar : ℕ} (F : Family kStar) : 0 ≤ unionConstant F := by
  have hu := F.upper_pos.le
  dsimp [unionConstant]
  positivity

/-- The literal finite all-rank/bank sum is controlled uniformly in its
rank by the largest original power. Rank zero is included without a
fictitious marked slot, and kStar=0 gives zero on both sides. -/
theorem sum_powerBudgets_le_rank_polynomial {kStar : ℕ}
    (F : Family kStar) (T cap : ℕ) (M H : ℝ) (hM : 0 ≤ M) (hH : 0 ≤ H) :
    (∑ k : Fin (kStar+1), ((cutoffIndex cap+1)^k.val : ℕ)*
      powerSavingBudget F T k cap M H) ≤
      unionConstant F*M*H*((cutoffIndex cap+2 : ℕ) : ℝ)^(kStar+1)*
        (T : ℝ)^(1-F.aStar/2) := by
  let J : ℝ := ((cutoffIndex cap+2 : ℕ) : ℝ)
  have hJ : 1 ≤ J := by
    exact_mod_cast (show 1 ≤ cutoffIndex cap+2 by omega)
  have hJ0 : 0 ≤ J := zero_le_one.trans hJ
  have hu := F.upper_pos.le
  have hsqrt := (Real.sqrt_pos.mpr F.lower_pos).le
  have hterm (k : Fin (kStar+1)) :
      ((cutoffIndex cap+1)^k.val : ℕ)*powerSavingBudget F T k cap M H ≤
      (2*(kStar : ℝ)*(M*H)*((5 : ℝ)^kStar*F.upper)/Real.sqrt F.lower)*
        J^(kStar+1)*(T : ℝ)^(1-F.aStar/2) := by
    have hk : k.val ≤ kStar := by have := k.isLt; omega
    have hkR : (k.val : ℝ) ≤ kStar := by exact_mod_cast hk
    have h5 : (5 : ℝ)^k.val ≤ (5 : ℝ)^kStar := pow_le_pow_right₀ (by norm_num) hk
    have hbase : ((cutoffIndex cap+1 : ℕ) : ℝ) ≤ J := by dsimp [J]; push_cast; linarith
    have hbank : (((cutoffIndex cap+1)^k.val : ℕ) : ℝ) ≤ J^kStar := by
      push_cast
      exact (pow_le_pow_left₀ (Nat.cast_nonneg _) hbase _).trans
        (pow_le_pow_right₀ hJ hk)
    unfold powerSavingBudget
    have hmain : (((cutoffIndex cap+1)^k.val : ℕ) : ℝ)*
        (2*(k.val : ℝ)*(M*H)*((5 : ℝ)^k.val*F.upper)*J/Real.sqrt F.lower) ≤
        (J^kStar)*(2*(kStar : ℝ)*(M*H)*((5 : ℝ)^kStar*F.upper)*J/Real.sqrt F.lower) := by
      gcongr <;> assumption
    calc
      _ = ((((cutoffIndex cap+1)^k.val : ℕ) : ℝ)*
          (2*(k.val : ℝ)*(M*H)*((5 : ℝ)^k.val*F.upper)*J/Real.sqrt F.lower))*
            (T : ℝ)^(1-F.aStar/2) := by dsimp [J]; ring
      _ ≤ ((J^kStar)*(2*(kStar : ℝ)*(M*H)*((5 : ℝ)^kStar*F.upper)*J/Real.sqrt F.lower))*
          (T : ℝ)^(1-F.aStar/2) :=
        mul_le_mul_of_nonneg_right hmain (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      _ = _ := by rw [pow_succ]; ring
  calc
    _ ≤ ∑ _k : Fin (kStar+1),
        (2*(kStar : ℝ)*(M*H)*((5 : ℝ)^kStar*F.upper)/Real.sqrt F.lower)*
          J^(kStar+1)*(T : ℝ)^(1-F.aStar/2) := Finset.sum_le_sum (fun k _ => hterm k)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      dsimp [unionConstant, J]
      ring

/-- A single fixed polynomial in log T pays the ACTUAL ceil(upper*T)
chart bank and EVERY original rank. Kernel bound H remains independent
of labels; a later physical-kernel invocation must use its same-rho bound. -/
theorem eventually_actual_rank_union_bound {kStar : ℕ} (F : Family kStar) :
    ∀ᶠ T : ℕ in atTop, 2 ≤ T ∧
      ∀ (chi eta : ℝ → ℝ), (∀ x, x ≤ 1 → chi x = 1) →
      (∀ x, 2 ≤ x → chi x = 0) → (∀ x, 0 ≤ chi x ∧ chi x ≤ 1) →
      (∀ x, |eta x| ≤ 1) → ∀ (kappa0 : ℝ) (K : ℕ → ℂ) (M H : ℝ),
      0 ≤ M → 0 ≤ H →
      (∀ (k : Fin (kStar+1)) us, us.length = k.val → ‖bankWeight F T k us‖ ≤ M) →
      (∀ n, ‖K n‖ ≤ H) →
      ‖originalBankError F T (Nat.ceil (F.upper*(T : ℝ))) chi eta kappa0 K‖ ≤
        (unionConstant F*bankLogConstant^(kStar+1))*M*H*
          Real.log (T : ℝ)^(kStar+1)*(T : ℝ)^(1-F.aStar/2) := by
  filter_upwards [eventually_actual_cutoffIndex_le_log F.upper F.upper_pos] with T hT
  refine ⟨hT.1, ?_⟩
  intro chi eta hone hzero hchi heta kappa0 K M H hM hH hamp hK
  have hbase := (originalBankError_le_sum_powerBudgets F T _ (by omega) chi eta
    hone hzero hchi heta kappa0 K M H hM hH hamp hK).trans
    (sum_powerBudgets_le_rank_polynomial F T _ M H hM hH)
  have hJ : 0 ≤ ((cutoffIndex (Nat.ceil (F.upper*(T : ℝ)))+2 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hp := pow_le_pow_left₀ hJ hT.2 (kStar+1)
  calc
    _ ≤ _ := hbase
    _ ≤ unionConstant F*M*H*(bankLogConstant*Real.log (T : ℝ))^(kStar+1)*
        (T : ℝ)^(1-F.aStar/2) := by
      gcongr <;> assumption
    _ = _ := by rw [mul_pow]; ring

end
end ImbalancedChen.P5Z.ActualDyadicRankPolynomial
