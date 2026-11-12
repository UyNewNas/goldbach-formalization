import ImbalancedChen.Part5OriginalH430ClassicalProperChart

/-! Simultaneous same-Fine proper-power payment over every original rank
and dyadic label. Count and coprime mean stay together through the modulus
sum, on and off the complete-product diagonal. -/
namespace ImbalancedChen.Part5OriginalH430ClassicalProperPayment
noncomputable section
open Finset Filter Real
open P5Z.AdmissibleAllRankIntegerGeometricFamily (licence)
open P5Z.ExactOriginalSmoothDyadicPartition (chartBank cutoffIndex)
open P5Z.OriginalDyadicRankUnion (actual_chartBank_card)
open P5Z.ActualDyadicRankPolynomial
open P5Z.ProperPowerPhysicalPolynomialPayment (tau_word_rank_subpower)
open P5Z.ProperPowerSignedMeanHBTransport (signedRow)
open P5Z.OriginalPrimeAllGroupHBDiscrepancy (properPowerReserve)
open Part3.AllKFamilyProperPowerSaving (powerSavingBudget)
open P4BOriginalFiniteProperArithmetic (exists_row_costs modulusExponent)
open Part5OriginalH430ClassicalPowerProfile (markBound markBound_nonneg)
open Part5OriginalH430ClassicalProperChart (off_chart diag_chart split_row part)
open Part5OriginalH430ClassicalSmoothNativeFamily (family)
open scoped Classical BigOperators

private theorem count_charts (P : ℕ) (b : ℝ) (hb : 0≤b) :
    (∑ k : Fin 201, (∑ _js∈chartBank P k.val,b))≤
      201*((cutoffIndex P+2:ℕ):ℝ)^200*b := by
  let J : ℝ := (cutoffIndex P+2:ℕ)
  have hj : 1≤J := by exact_mod_cast (show 1≤cutoffIndex P+2 by omega)
  have H (k : Fin 201) : ((chartBank P k.val).card:ℝ)≤J^200 := by
    rw [actual_chartBank_card,Nat.cast_pow]
    have hbase : ((cutoffIndex P+1:ℕ):ℝ)≤J := by exact_mod_cast (Nat.le_succ (cutoffIndex P+1))
    exact (pow_le_pow_left₀ (Nat.cast_nonneg _) hbase k.val).trans
      (pow_le_pow_right₀ hj (by have := k.isLt; omega))
  apply (sum_le_sum (s:=univ) (fun (k : Fin 201) _ => show (∑ _js∈chartBank P k.val,b)≤J^200*b by
    simpa only [sum_const,nsmul_eq_mul] using mul_le_mul_of_nonneg_right (H k) hb)).trans_eq
  simp [J,mul_assoc]

variable (μ : ℝ) {δ h c : ℝ} (hd : 0<δ) (hh : 0<h) (hh' : h≤1/8) (hc : 0<c) (hc' : c≤1/8)
local notation "F₀" => family μ hd hh hh' hc hc'

/-- The displayed Q can contain arbitrarily large zero-coefficient moduli.
Only its nonzero coefficients enter the active polynomial range. -/
theorem proper_paid {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop,∀ (κ₀ : ℝ) (Q : Finset ℕ) (ρ : ℕ→ℝ),
    (∀ d∈Q,0<d) → (∀ d,|ρ d|≤1) → (∀ d,ρ d≠0 → (d:ℝ)<(N:ℝ)^modulusExponent) →
    (∑ k : Fin 201,∑ js∈chartBank (2*N) k.val,
      ‖properPowerReserve (licence F₀ N k) 200 (2*N) N κ₀ Q (fun d => (ρ d:ℂ)) js‖)≤
        ε*singularNormalization N := by
  let s : ℝ := 1/720
  have hs : 0<s := by norm_num [s]
  obtain ⟨C,D,hC,hD,rows⟩ := exists_row_costs s hs
  obtain ⟨T,hT,tau⟩ := tau_word_rank_subpower 200 hs
  let a := unionConstant F₀*markBound*C*bankLogConstant^201
  let b := 201*bankLogConstant^200*(T*(markBound*D))
  have offpay := eventually_powerLog_le_singularNormalization a (1-(1/90:ℝ)/2+s) 201
    (by norm_num [s]) (ε/2) (half_pos hε)
  have dipay := eventually_powerLog_le_singularNormalization b (s+(modulusExponent+s)) 200
    (by norm_num [s,modulusExponent]) (ε/2) (half_pos hε)
  filter_upwards [offpay,dipay,eventually_actual_cutoffIndex_le_log 2 (by norm_num)]
    with N hoff hdi hJ
  intro κ₀ Q ρ hQ hρ hr
  have hN2 := hJ.1
  have hN : 1≤N := by omega
  have h0 : (0:ℝ)<N := Nat.cast_pos.mpr (by omega)
  have hNN : N≠0 := by omega
  have hreal : (0:ℝ)≤log (N:ℝ) := log_nonneg (by exact_mod_cast hN)
  let J : ℝ := (cutoffIndex (2*N)+2:ℕ)
  have hscale : Nat.ceil (2*(N:ℝ))=2*N := by
    rw [show 2*(N:ℝ)=((2*N:ℕ):ℝ) by norm_cast,Nat.ceil_natCast]
  have hlog : J≤bankLogConstant*log (N:ℝ) := by simpa only [J,hscale] using hJ.2
  have hJ0 : 0≤J := Nat.cast_nonneg _
  have hlogB := bankLogConstant_pos.le
  let G := signedRow Q (fun d => (ρ d:ℂ)) N
  let H := C*(N:ℝ)^s
  let Y := (T*(N:ℝ)^s)*(markBound*(D*(N:ℝ)^(modulusExponent+s)))
  have hH : 0≤H := by dsimp only [H]; positivity
  have hY : 0≤Y := by dsimp only [Y]; have := markBound_nonneg; positivity
  obtain ⟨hrow,hdiag⟩ := rows N hN Q ρ hQ hρ hr
  have he : (2:ℝ)≤exp 1 := by linarith only [Real.add_one_le_exp (1:ℝ)]
  have hG (m : ℕ) (hm : 1≤m) (hx : (m:ℝ)≤2*(N:ℝ)) (hn : m≠N) : ‖G m‖≤H :=
    hrow m hm (hx.trans (mul_le_mul_of_nonneg_right he h0.le)) hn
  let B := fun k : Fin 201 => powerSavingBudget F₀ N k (2*N) markBound H
  have per (k : Fin 201) (js : List ℕ) (hj : js∈chartBank (2*N) k.val) :
      ‖properPowerReserve (licence F₀ N k) 200 (2*N) N κ₀ Q (fun d => (ρ d:ℂ)) js‖≤B k+Y := by
    rw [split_row]
    apply (norm_add_le _ _).trans (add_le_add
      (off_chart μ hd hh hh' hc hc' (by omega) k κ₀ hj G hH hG) ?_)
    exact (diag_chart μ hd hh hh' hc hc' hNN k κ₀ js (G N)).trans
      (mul_le_mul (tau N k.val hN (by have := k.isLt; omega))
        (mul_le_mul_of_nonneg_left hdiag markBound_nonneg)
        (mul_nonneg markBound_nonneg (norm_nonneg _)) (by positivity))
  have Hoff : (∑ k : Fin 201,∑ _js∈chartBank (2*N) k.val,B k)≤(ε/2)*singularNormalization N := by
    simp only [sum_const,nsmul_eq_mul,actual_chartBank_card,B]
    apply (sum_powerBudgets_le_rank_polynomial F₀ N (2*N) markBound H markBound_nonneg hH).trans
    have hpow := pow_le_pow_left₀ hJ0 hlog 201
    have hbase := unionConstant_nonneg F₀
    have hM := markBound_nonneg
    calc
      _ ≤ unionConstant F₀*markBound*H*(bankLogConstant*log (N:ℝ))^201*
          (N:ℝ)^(1-(1/90:ℝ)/2) := by
        change _*J^201*(N:ℝ)^(1-(1/90:ℝ)/2)≤_
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpow (mul_nonneg (mul_nonneg hbase hM) hH))
          (rpow_nonneg h0.le _)
      _ = a*(N:ℝ)^(1-(1/90:ℝ)/2+s)*log (N:ℝ)^201 := by
        rw [rpow_add h0,mul_pow]; dsimp only [a,H]; ring
      _ ≤ _ := hoff
  have Hdiag : (∑ k : Fin 201,∑ _js∈chartBank (2*N) k.val,Y)≤(ε/2)*singularNormalization N := by
    apply (count_charts (2*N) Y hY).trans
    have hpow := pow_le_pow_left₀ hJ0 hlog 200
    calc
      _ ≤ 201*(bankLogConstant*log (N:ℝ))^200*Y := by
        change 201*J^200*Y≤_
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (by norm_num)) hY
      _ = b*(N:ℝ)^(s+(modulusExponent+s))*log (N:ℝ)^200 := by
        rw [rpow_add h0,mul_pow]; dsimp only [Y,b]; ring
      _ ≤ _ := hdi
  apply (sum_le_sum (s:=univ) (fun (k : Fin 201) _ => sum_le_sum (per k))).trans
  simp only [sum_add_distrib]
  linarith only [Hoff,Hdiag]

end
end ImbalancedChen.Part5OriginalH430ClassicalProperPayment

