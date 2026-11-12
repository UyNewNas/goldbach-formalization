import ImbalancedChen.Part5OriginalH430ClassicalPowerProfile

/-! Splitting the true proper-power union by its complete integer product.
The independent pre-HB rough cutoff stays on its own dyadic chart. -/
namespace ImbalancedChen.Part5OriginalH430ClassicalProperChart
noncomputable section
open Finset Real
open P5Z.ActualEtaPsiOccurrenceBudget (chi eta)
open P5Z.AdmissibleAllRankIntegerGeometricFamily (Family licence)
open P5Z.ExactOriginalSmoothDyadicPartition
open P5Z.ActualLabelledPrimeSmoothCharts
open P5Z.ProperPowerSignedMeanHBTransport (signedRow)
open P5Z.ActualCommonRefinedPayments (fullCollisionWords fullCollisionWords_card_le)
open P5Z.OriginalPrimeAllGroupHBDiscrepancy
open Part3 (roughOneSlot roughOneSlot_norm_le)
open Part3.OriginalProperPowerActualChart
open Part3.AllKFamilyLambdaCorrectionBound
open Part3.AllKLambdaChartCorrection
open Part3.AllKFamilyProperPowerSaving (powerSavingBudget family_all_k_power_saving)
open Part5OriginalH430ClassicalPowerProfile
open Part5OriginalH430ClassicalSmoothNativeFamily (family)
open scoped Classical BigOperators

def part (F : Family 200) (N : ℕ) (k : Fin 201) (κ₀ : ℝ) (js : List ℕ) (G : ℕ→ℂ) : ℂ :=
  ∑ ps∈properChartWords (2*N) k.val,
    lambdaWord ps*originalChart (licence F N k) N κ₀ js ps*
      (roughWord (beforeHBCutoff 200 js) ps*G ps.prod)

theorem split_row (F : Family 200) (N : ℕ) (k : Fin 201) (κ₀ : ℝ) (js : List ℕ)
    (D : Finset ℕ) (R : ℕ→ℂ) :
    properPowerReserve (licence F N k) 200 (2*N) N κ₀ D R js =
      part F N k κ₀ js (fun b => if b=N then 0 else signedRow D R N b)+
      part F N k κ₀ js (fun b => if b=N then signedRow D R N N else 0) := by
  unfold properPowerReserve part
  rw [←sum_add_distrib]
  apply sum_congr rfl
  intro ps _
  rw [P4BActualUpperTrimPayment.wordKernel_eq_signedRow]
  by_cases h : ps.prod=N <;> simp [h]

variable (μ : ℝ) {δ h c : ℝ} (hd : 0<δ) (hh : 0<h) (hh' : h≤1/8) (hc : 0<c) (hc' : c≤1/8)
local notation "F₀" => family μ hd hh hh' hc hc'

/-- Clip only outside the physical support of an actual nonzero chart.
The complete signed row is retained on both sides of the target. -/
theorem off_chart {N : ℕ} (hN : 0<N) (k : Fin 201) (κ₀ : ℝ) {js : List ℕ}
    (hj : js∈chartBank (2*N) k.val) (G : ℕ→ℂ) {H : ℝ} (hH : 0≤H)
    (hG : ∀ b : ℕ,1≤b → (b:ℝ)≤2*(N:ℝ) → b≠N → ‖G b‖≤H) :
    ‖part F₀ N k κ₀ js (fun b => if b=N then 0 else G b)‖≤
      powerSavingBudget F₀ N k (2*N) markBound H := by
  let z := beforeHBCutoff 200 js
  let K := fun b : ℕ => if 1≤b ∧ (b:ℝ)≤2*(N:ℝ) ∧ b≠N then
    roughOneSlot z b*G b else 0
  have hK (b : ℕ) : ‖K b‖≤H := by
    classical
    dsimp only [K]
    split_ifs with hb
    · rw [norm_mul]
      exact (mul_le_mul (roughOneSlot_norm_le _ _) (hG b hb.1 hb.2.1 hb.2.2)
        (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
    · simpa only [norm_zero] using hH
  have eq : part F₀ N k κ₀ js (fun b => if b=N then 0 else G b)=
      ∑ ps∈properChartWords (2*N) k.val,lambdaWord ps*
        chartTerm chi eta (bankWeight F₀ N k) (N:ℝ) κ₀ js ps*K ps.prod := by
    apply sum_congr rfl
    intro ps hp
    change lambdaWord ps*originalChart (licence F₀ N k) N κ₀ js ps*_=lambdaWord ps*
      originalChart (licence F₀ N k) N κ₀ js ps*_
    by_cases hz : originalChart (licence F₀ N k) N κ₀ js ps=0
    · simp [hz]
    obtain ⟨hl,hm⟩ := words_spec (Icc 1 (2*N)) k.val ps (properChartWords_spec hp).1
    have hs := bankWeight_support F₀ N k hl (chart_live μ hd hh hh' hc hc' hz)
    have hp1 : 1≤ps.prod := List.prod_pos (fun p hp => (mem_Icc.mp (hm p hp)).1)
    have hcap : (ps.prod:ℝ)≤2*(N:ℝ) := hs.2
    by_cases he : ps.prod=N
    · simp [K,he]
    · simp only [K,if_pos ⟨hp1,hcap,he⟩,if_neg he]
      rw [roughWord_eq_product (original_cutoff_nonneg 200 js)]
  rw [eq]
  exact family_all_k_power_saving F₀ N hN k chi eta (fun _ ht => actual_chi_one ht)
    (fun _ ht => actual_chi_zero ht) chi_bounds abs_eta (2*N) κ₀ hj K markBound H
    markBound_nonneg hH (word_amplitude μ hd hh hh' hc hc' N k) hK

/-- The collision evaluates the real count and exact coprime centre on
the target itself. The multiplicity counts ordered integer factor words. -/
theorem diag_chart {N : ℕ} (hN : N≠0) (k : Fin 201) (κ₀ : ℝ) (js : List ℕ) (Z : ℂ) :
    ‖part F₀ N k κ₀ js (fun b => if b=N then Z else 0)‖≤
      (N.divisors.card^k.val:ℕ)*(markBound*‖Z‖) := by
  let C := fullCollisionWords (2*N) k.val N
  let V := fun ps : List ℕ => lambdaWord ps*originalChart (licence F₀ N k) N κ₀ js ps*
    (roughWord (beforeHBCutoff 200 js) ps*Z)
  have eq : part F₀ N k κ₀ js (fun b => if b=N then Z else 0)=∑ ps∈C,V ps := by
    unfold part
    simp only [C,fullCollisionWords,sum_filter]
    apply sum_congr rfl
    intro ps _
    by_cases he : ps.prod=N <;> simp [V,he]
  have hpoint (ps : List ℕ) (hp : ps∈C) : ‖V ps‖≤markBound*‖Z‖ := by
    have hl := (words_spec (Icc 1 (2*N)) k.val ps (properChartWords_spec (mem_filter.mp hp).1).1).1
    have hch := bank_chart_amplitude F₀ N k chi eta chi_bounds abs_eta markBound
      markBound_nonneg (word_amplitude μ hd hh hh' hc hc' N k) κ₀ js ps hl
    have hw : ‖lambdaWord ps‖*‖originalChart (licence F₀ N k) N κ₀ js ps‖≤markBound :=
      (mul_le_mul (lambdaWord_norm_le_one _) hch (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
    have hr := mul_le_mul_of_nonneg_right (roughWord_norm_le_one (beforeHBCutoff 200 js) ps) (norm_nonneg Z)
    simp only [one_mul] at hr
    simpa only [V,norm_mul] using mul_le_mul hw hr (mul_nonneg (norm_nonneg _) (norm_nonneg _)) markBound_nonneg
  rw [eq]
  exact (norm_sum_le _ _).trans ((sum_le_sum hpoint).trans (by
    simp only [sum_const,nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast fullCollisionWords_card_le (2*N) k.val N hN)
      (mul_nonneg markBound_nonneg (norm_nonneg Z))))

end
end ImbalancedChen.Part5OriginalH430ClassicalProperChart

