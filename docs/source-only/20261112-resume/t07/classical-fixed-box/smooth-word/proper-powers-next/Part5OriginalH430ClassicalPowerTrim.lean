import ImbalancedChen.Part5OriginalH430ClassicalPowerProfile

/-! Removing the original eta trim in the true-prime functional. All
active omitted products lie strictly below N. The cap of the independent
ordered primes is 2N throughout. -/
namespace ImbalancedChen.Part5OriginalH430ClassicalPowerTrim
noncomputable section
open Finset Real Filter
open P5Z.OriginalPrimeAllGroupHBDiscrepancy (trimReserve)
open P5Z.ActualEtaPsiOccurrenceBudget (eta eta_bounds)
open P5Z.ActualLabelledPrimeSmoothCharts (primeTuples primeTuples_spec)
open P5Z.AdmissibleAllRankIntegerGeometricFamily (licence)
open P5Z.LicensedOriginalIntegerProfile (listExtension)
open P5Z.IndependentPrimeSourceWordDictionary (wordKernel)
open Part3.AllKFamilyLambdaCorrectionBound (bankWeight)
open P4BActualUpperTrimPayment (lowPrimeWords exists_lowPrimeWords_card_budget prime_word_product_pos wordKernel_eq_signedRow)
open P4BOriginalFiniteProperArithmetic (exists_row_costs modulusExponent)
open P5OriginalSharpPrime (originalLowerCut)
open Part5OriginalH430ClassicalPowerProfile (markBound markBound_nonneg word_amplitude too_short)
open Part5OriginalH430ClassicalSmoothNativeFamily (family)
open scoped Classical BigOperators

variable (μ : ℝ) {δ h c : ℝ} (hd : 0<δ) (hh : 0<h) (hh' : h≤1/8) (hc : 0<c) (hc' : c≤1/8)
local notation "F₀" => family μ hd hh hh' hc hc'
private theorem rank_trim (k : Fin 201) {κ₀ ε : ℝ} (hk : 0<κ₀) (hk' : κ₀<1) (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop,∀ (Q : Finset ℕ) (ρ : ℕ→ℝ),(∀ d∈Q,0<d) → (∀ d,|ρ d|≤1) →
      (∀ d,ρ d≠0 → (d:ℝ)<(N:ℝ)^modulusExponent) →
      ‖trimReserve (licence F₀ N k) (2*N) N κ₀ Q (fun d => (ρ d:ℂ))‖≤ε*singularNormalization N := by
  by_cases hk1 : 1≤k.val
  · let s := κ₀/4
    have hs : 0<s := by dsimp [s]; positivity
    obtain ⟨C,hC,count⟩ := exists_lowPrimeWords_card_budget k.val hk1 hs
    obtain ⟨D,_,hD,_,rows⟩ := exists_row_costs s hs
    have cost := eventually_powerLog_le_singularNormalization (3*C*(markBound*D))
      (1-κ₀+s+s) 0 (by dsimp [s]; linarith only [hk]) ε hε
    filter_upwards [cost,P5OriginalSingletonLowerTrimPaid.eventually_originalLowerCut_lt κ₀ hk hk',
      eventually_ge_atTop (1:ℕ)] with N hcost hcut hn
    intro Q ρ hQ hρ hr
    let Y := originalLowerCut κ₀ N
    let Z := markBound*(D*(N:ℝ)^s)
    have h0 : (0:ℝ)<N := Nat.cast_pos.mpr (by omega)
    have hZ : 0≤Z := by dsimp [Z]; have := markBound_nonneg; positivity
    have hrow := (rows N hn Q ρ hQ hρ hr).1
    have h2 : 2*(N:ℝ)^(1-κ₀)≤(Y:ℝ) := Nat.le_ceil _
    have he : (1:ℝ)≤exp 1 := by linarith only [Real.add_one_le_exp (1:ℝ)]
    let V := fun ps : List ℕ => (1-(eta ((ps.prod:ℝ)/(N:ℝ)^(1-κ₀)):ℂ))*
      bankWeight F₀ N k ps*wordKernel Q (fun d => (ρ d:ℂ)) N ps
    have H (ps : List ℕ) (hp : ps∈primeTuples (2*N) k.val) :
        ‖V ps‖≤if ps.prod≤Y then Z else 0 := by
      by_cases hY : ps.prod≤Y
      · have hlt := lt_of_le_of_lt hY hcut.1
        have hab := eta_bounds ((ps.prod:ℝ)/(N:ℝ)^(1-κ₀))
        have hEta : ‖1-(eta ((ps.prod:ℝ)/(N:ℝ)^(1-κ₀)):ℂ)‖≤1 := by
          rw [←Complex.ofReal_one,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,
            abs_of_nonneg (sub_nonneg.mpr hab.2)]
          linarith only [hab.1]
        have hW := word_amplitude μ hd hh hh' hc hc' N k ps (primeTuples_spec _ _ hp).1
        have hm : ‖wordKernel Q (fun d => (ρ d:ℂ)) N ps‖≤D*(N:ℝ)^s := by
          rw [wordKernel_eq_signedRow]
          exact hrow _ (prime_word_product_pos hp)
            ((Nat.cast_le.mpr hlt.le).trans (le_mul_of_one_le_left h0.le he)) hlt.ne
        simp only [V,if_pos hY,norm_mul]
        exact mul_le_mul ((mul_le_mul hEta hW (norm_nonneg _) zero_le_one).trans_eq (one_mul _))
          hm (norm_nonneg _) markBound_nonneg
      · have hi : 2≤(ps.prod:ℝ)/(N:ℝ)^(1-κ₀) := (le_div_iff₀ (rpow_pos_of_pos h0 _)).mpr
          (h2.trans (by exact_mod_cast (le_of_not_ge hY)))
        simp only [V,P5Z.ActualEtaPsiOccurrenceBudget.eta_one hi,Complex.ofReal_one,sub_self,
          zero_mul,norm_zero,if_neg hY,le_refl]
    have hCard := count N (2*N) Y hcut.1.le
    change ‖∑ ps∈primeTuples (2*N) k.val,V ps‖≤_
    calc
      _ ≤ ∑ ps∈primeTuples (2*N) k.val,if ps.prod≤Y then Z else 0 :=
        (norm_sum_le _ _).trans (sum_le_sum H)
      _ = ((lowPrimeWords (2*N) k.val Y).card:ℝ)*Z := by
        rw [←sum_filter]; simp only [lowPrimeWords,sum_const,nsmul_eq_mul]
      _ ≤ ((3*(N:ℝ)^(1-κ₀))*(C*(N:ℝ)^s))*Z :=
        mul_le_mul_of_nonneg_right (hCard.trans (mul_le_mul_of_nonneg_right hcut.2 (by positivity))) hZ
      _ = (3*C*(markBound*D))*(N:ℝ)^(1-κ₀+s+s) := by
        rw [rpow_add h0,rpow_add h0]; dsimp [Z]; ring
      _ ≤ _ := by simpa only [pow_zero,mul_one] using hcost
  · filter_upwards [eventually_singularNormalization_pos] with N hn
    intro Q ρ _ _ _
    have hz : trimReserve (licence F₀ N k) (2*N) N κ₀ Q (fun d => (ρ d:ℂ))=0 := by
      apply sum_eq_zero
      intro ps hp
      have hw := too_short μ hd hh hh' hc hc' (k:=k) (N:=N) (by omega) (primeTuples_spec _ _ hp).1
      change _*bankWeight F₀ N k ps*_=0
      simp only [hw,mul_zero,zero_mul]
    simpa only [hz,norm_zero] using mul_nonneg hε.le hn.le

theorem trim_paid {κ₀ ε : ℝ} (hk : 0<κ₀) (hk' : κ₀<1) (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop,∀ (Q : Finset ℕ) (ρ : ℕ→ℝ),(∀ d∈Q,0<d) → (∀ d,|ρ d|≤1) →
    (∀ d,ρ d≠0 → (d:ℝ)<(N:ℝ)^modulusExponent) →
    (∑ k : Fin 201,‖trimReserve (licence F₀ N k) (2*N) N κ₀ Q (fun d => (ρ d:ℂ))‖)≤
      ε*singularNormalization N := by
  have e : 0<ε/201 := by positivity
  filter_upwards [eventually_all.2 (fun k : Fin 201 => rank_trim μ hd hh hh' hc hc' k hk hk' e)] with N H
  intro Q ρ hQ hρ hr
  apply (sum_le_sum (s:=univ) (fun k _ => H k Q ρ hQ hρ hr)).trans_eq
  simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat]
  ring

end
end ImbalancedChen.Part5OriginalH430ClassicalPowerTrim

