import ImbalancedChen.P4AOriginalFull87SharpMeanPaymentLedger
import ImbalancedChen.P4BPrimorialDivisorEnvelope
import ImbalancedChen.P5OriginalPrimeEndpointLogPayment
import ImbalancedChen.P5PrimeDivisorMeanCorrection
import ImbalancedChen.Part3PolynomialResidueDivisorBound
import ImbalancedChen.ChenQuotientCentreBudget

/-! Pay the five non-PP terms in the literal singleton ledger, keeping the
complete signed coefficient in the remaining primitive discrepancy. This
count estimate uses no compiler or density allowance. -/
namespace ImbalancedChen.P4AFull87SharpMeanAsymptoticPayment
noncomputable section
open scoped Classical BigOperators Topology
open Filter P4AOriginalFull87SharpMeanPaymentLedger
open P4AOriginalFull87SameRhoEndpointDivisor P4AOriginalFull87ActualRhoDivisorTau
open P4AOriginalFull87ExceptionDivisorFibres P4AOriginalFull87WeightedPrimitiveRecentering
open P4AOriginalFull87SharpCentreCarrier P5OriginalPrimeEndpoint
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

private theorem end_mass (N D : ℕ) (W : ℕ → ℝ) (hNP : ¬N.Prime)
    (hi : ∀ p, p < N → D < N-p → W p = 1) (hw : ∀ p, 0 ≤ W p ∧ W p ≤ 1) :
    |upperWeightTail N D W - lowerWeightDefect N W| ≤ (D : ℝ) := by
  let low := (chenPrimePrefix N).filter (fun p => N-p ≤ D)
  let high := (chenPrimePrefix (N+D)).filter (fun p => N < p)
  have hl : low ⊆ Finset.Ico (N-D) N := by
    intro p hp
    obtain ⟨hprefix,hwindow⟩ := Finset.mem_filter.mp hp
    obtain ⟨hpN,hprime⟩ := mem_chenPrimePrefix.mp hprefix
    have hne : p ≠ N := fun he => hNP (he ▸ hprime)
    exact Finset.mem_Ico.mpr ⟨by omega,by omega⟩
  have hh : high ⊆ Finset.Ioc N (N+D) := by
    intro p hp
    obtain ⟨hp,hpN⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_Ioc.mpr ⟨hpN,(mem_chenPrimePrefix.mp hp).1⟩
  have hlc : low.card ≤ D := by
    have hs := Finset.card_le_card hl
    rw [Nat.card_Ico] at hs
    omega
  have hhc : high.card ≤ D := by
    have hs := Finset.card_le_card hh
    rw [Nat.card_Ioc] at hs
    omega
  have heq : lowerWeightDefect N W = ∑ p ∈ low, (1-W p) := by
    unfold lowerWeightDefect
    dsimp only [low]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p hp
    obtain ⟨hpn,hprime⟩ := mem_chenPrimePrefix.mp hp
    by_cases h : N-p ≤ D
    · simp only [if_pos h]
    · have hne : p ≠ N := fun he => hNP (he ▸ hprime)
      simp only [if_neg h,hi p (by omega) (by omega),sub_self]
  have hlo : lowerWeightDefect N W ≤ (D : ℝ) := by
    rw [heq]
    calc
      _ ≤ ∑ _p ∈ low, (1 : ℝ) := Finset.sum_le_sum fun p _ => sub_le_self _ (hw p).1
      _ = (low.card : ℝ) := by simp
      _ ≤ _ := by exact_mod_cast hlc
  have hup : upperWeightTail N D W ≤ (D : ℝ) := by
    calc
      _ ≤ ∑ _p ∈ high, (1 : ℝ) := Finset.sum_le_sum fun p _ => (hw p).2
      _ = (high.card : ℝ) := by simp
      _ ≤ _ := by exact_mod_cast hhc
  have hl0 : 0 ≤ lowerWeightDefect N W := Finset.sum_nonneg fun p _ => sub_nonneg.mpr (hw p).2
  have hh0 : 0 ≤ upperWeightTail N D W := Finset.sum_nonneg fun p _ => (hw p).1
  exact abs_le.mpr ⟨by linarith,by linarith⟩

private theorem exists_centre :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 4 ≤ N → Even N →
      ∀ (P : Bool → List ℕ → Bool) (cap : ℕ) (w z L : ℝ),
      centreDivisorInvoice P N cap w z L ≤
        (C / Real.log 2) * (N : ℝ) ^ (1/2 : ℝ) * Real.log (N : ℝ) := by
  obtain ⟨C,hC,ht⟩ := Part3.PolynomialResidueDivisorBound.fouvryTau_le_const_rpow
    (k := 2) (by norm_num) (show (0 : ℝ) < 1/2 by norm_num)
  refine ⟨C,hC,?_⟩
  intro N hN hEven P cap w z L
  have hNP := chen_not_prime_of_even_four_le hEven hN
  have hdiv (p : ℕ) (hp : p ∈ centrePrimeFactors N) :
      ((N-p).divisors.card : ℝ) ≤ C*(N : ℝ)^(1/2 : ℝ) := by
    have hg := ht (N-p) (chenCentrePrimeCarrier_sub_pos hNP hp)
    rw [fouvryTau_two] at hg
    exact hg.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg (N-p))
        (by exact_mod_cast Nat.sub_le N p) (by norm_num : (0 : ℝ) ≤ 1/2)) hC.le)
  calc
    _ ≤ ∑ p ∈ centrePrimeFactors N, ((N-p).divisors.card : ℝ) :=
      centre_invoice_le_actual_divisor_count P N cap w z L hNP
    _ ≤ ∑ _p ∈ centrePrimeFactors N, C*(N : ℝ)^(1/2 : ℝ) := Finset.sum_le_sum hdiv
    _ = chenPrimeDivisorCount N N * (C*(N : ℝ)^(1/2 : ℝ)) := by
      rw [Finset.sum_const,nsmul_eq_mul]
      rfl
    _ ≤ (Real.log (N : ℝ)/Real.log 2)*(C*(N : ℝ)^(1/2 : ℝ)) :=
      mul_le_mul_of_nonneg_right (chenPrimeDivisorCount_le_log N (by omega)) (by positivity)
    _ = _ := by ring

/-- The integer bound is on each prime of the modulus. Even a very large
product, including a displayed zero, lies in the same primorial. -/
private theorem primorial_mass (P : Bool → List ℕ → Bool) (N cap : ℕ)
    (w z : ℝ) (hwz : w ≤ z) :
    actualSmallRoughModuli (P false) N cap w z ⊆ (sieveProduct N ⌈z⌉₊).divisors := by
  intro d hd
  exact Nat.mem_divisors.mpr ⟨actualSmallRoughModuli_dvd_sieveProduct_ceil _ _ _ _ _ hwz hd,
    (sieveProduct_squarefree _ _).ne_zero⟩

private theorem exists_mean_cost :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 2 ≤ N → Even N → ∀ (P : Bool → List ℕ → Bool)
      (D cap : ℕ) (w z L : ℝ), w ≤ z → 1 < z → z ≤ N →
      ∀ W : ℕ → ℝ, (∀ p, |W p| ≤ 1) →
      let Q := actualSmallRoughModuli (P false) N cap w z
      let rho := actualSmallRoughRho (P false) N cap w z L
      (∑ d ∈ Q, |rho d/(Nat.totient d : ℝ)|) ≤ C*Real.log (N : ℝ) ∧
      (∑ d ∈ Q, |rho d*(weightedModulusPrimeMass N D d W/(Nat.totient d : ℝ))|) ≤
        (⌈z⌉₊ : ℝ)*C*Real.log (N : ℝ) := by
  obtain ⟨C,hC,hprim⟩ := P4BPrimorialDivisorEnvelope.exists_sievePrimorial_divisor_mass_le_log
  refine ⟨C,hC,?_⟩
  intro N hN hEven P D cap w z L hwz hz hZN W hW
  let Q := actualSmallRoughModuli (P false) N cap w z
  let rho := actualSmallRoughRho (P false) N cap w z L
  let Z := ⌈z⌉₊
  have hZ : 2 ≤ Z := Nat.add_one_le_ceil_iff.mpr hz
  have hlogZ := Real.log_le_log (show (0:ℝ) < Z by exact_mod_cast (show 0 < Z by omega))
    (show (Z:ℝ) ≤ N by exact_mod_cast (Nat.ceil_le.mpr hZN : Z ≤ N))
  have hmass : (∑ d ∈ Q, 1/(Nat.totient d : ℝ)) ≤ C*Real.log (N : ℝ) :=
    (Finset.sum_le_sum_of_subset_of_nonneg (primorial_mass P N cap w z hwz)
      (fun _ _ _ => by positivity)).trans
      ((hprim N Z hEven (by exact_mod_cast hZ)).trans (mul_le_mul_of_nonneg_left hlogZ hC.le))
  have hnorm : (∑ d ∈ Q, |rho d/(Nat.totient d : ℝ)|) ≤ C*Real.log (N : ℝ) := by
    refine le_trans (Finset.sum_le_sum ?_) hmass
    intro d _
    rw [abs_div,abs_of_nonneg (Nat.cast_nonneg _)]
    exact div_le_div_of_nonneg_right (actualSmallRoughRho_abs_le_one _ _ _ _ _ _ d)
      (Nat.cast_nonneg _)
  refine ⟨hnorm,?_⟩
  have hp (d : ℕ) (hd : d ∈ Q) : |weightedModulusPrimeMass N D d W| ≤ (Z:ℝ) := by
    have hprime : (chenPrimePrefix (N+D)).filter (fun p => p ∣ d) ⊆ Finset.range Z := by
      intro p hp
      obtain ⟨hpre,hpd⟩ := Finset.mem_filter.mp hp
      have hdM := actualSmallRoughModuli_dvd_sieveProduct_ceil _ _ _ _ _ hwz hd
      exact Finset.mem_range.mpr ((mem_sievePrimes.mp (prime_mem_sievePrimes_of_dvd
        (mem_chenPrimePrefix.mp hpre).2 (hpd.trans hdM))).1)
    have hcost := P5PrimeDivisorMean.abs_modulusPrimeMass_le_count (N+D) W (fun p _ => hW p) d
    have hs : chenPrimeDivisorCount (N+D) d ≤ (Z:ℝ) := by
      unfold chenPrimeDivisorCount
      exact_mod_cast (show ((chenPrimePrefix (N+D)).filter (fun p => p ∣ d)).card ≤ Z by
        simpa only [Finset.card_range] using Finset.card_le_card hprime)
    simpa only [weightedModulusPrimeMass,P5PrimeDivisorMean.modulusPrimeMass,Finset.sum_filter]
      using hcost.trans hs
  calc
    _ ≤ ∑ d ∈ Q, (Z:ℝ)*|rho d/(Nat.totient d : ℝ)| := by
      apply Finset.sum_le_sum
      intro d hd
      calc
        _ = |weightedModulusPrimeMass N D d W| * |rho d/(Nat.totient d : ℝ)| := by
          rw [← abs_mul]
          congr 1
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (hp d hd) (abs_nonneg _)
    _ ≤ (Z:ℝ)*(C*Real.log (N:ℝ)) := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left hnorm (Nat.cast_nonneg _)
    _ = _ := by ring

/-- The original full physical singleton, after paying every term except
the single primitive discrepancy for *that same complete coefficient*.
Specializes to both the licensed sixth and full87 eighth policies.
No AP bound for a restriction or transfer to a tagged coefficient is used. -/
theorem eventually_sharp_minus_primitive_paid (v eta : ℝ) (hv : 0 < v)
    (hv1 : v < 1) (heta : 0 < eta) :
    ∀ᶠ N : ℕ in atTop, Even N → ∀ (P : Bool → List ℕ → Bool) (cap D : ℕ)
      (w L : ℝ), w ≤ (N : ℝ)^v → D ≤ ⌈(N : ℝ)/Real.log (N : ℝ)^6⌉₊ →
      ∀ W : ℕ → ℝ, (∀ p, p < N → D < N-p → W p = 1) →
      (∀ p, 0 ≤ W p ∧ W p ≤ 1) →
      let z := (N : ℝ)^v
      let Q := actualSmallRoughModuli (P false) N cap w z
      let rho := actualSmallRoughRho (P false) N cap w z L
      |actualSharpCarrierLiteral P N cap w z L -
         ((chenPrimePrefix N).card : ℝ)*(∑ d ∈ Q, rho d/(Nat.totient d : ℝ))| ≤
        |∑ d ∈ Q, rho d*finitePrimitiveDiscrepancy (chenPrimePrefix (N+D)) W N d| +
        eta*singularNormalization N := by
  obtain ⟨C,hC,hmean⟩ := exists_mean_cost
  obtain ⟨B,hB,hcentre⟩ := exists_centre
  filter_upwards [eventually_ge_atTop (4 : ℕ), eventually_one_le_nat_log,
    eventually_log_window_cost_le 3,
    p5z_eventually_logCube_le_singularNormalization (40*(2+C)) (eta/3) (by positivity),
    eventually_powerLog_le_singularNormalization (2*C) v 1 hv1 (eta/3) (by positivity),
    eventually_powerLog_le_singularNormalization (B/Real.log 2) (1/2) 1
      (by norm_num) (eta/3) (by positivity)] with N hN hlog hwin hend hmod hcen
  intro hEven P cap D w L hwz hD W hi hW
  have hn : (1:ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hz : 1 < (N:ℝ)^v := Real.one_lt_rpow hn hv
  have hzn : (N:ℝ)^v ≤ N := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hn.le hv1.le
  have hceil : (⌈(N:ℝ)^v⌉₊ : ℝ) ≤ 2*(N:ℝ)^v := by
    have hc := Nat.ceil_lt_add_one (Real.rpow_nonneg (Nat.cast_nonneg N) v)
    linarith
  have hwindow := hwin D hD
  have hlogD : Real.log (D : ℝ) ≤ Real.log (N : ℝ) := by
    by_cases h0 : D = 0
    · simp only [h0,Nat.cast_zero,Real.log_zero]
      exact Real.log_nonneg hn.le
    · exact Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero h0)
        (by exact_mod_cast hwindow.1)
  have habs (p : ℕ) : |W p| ≤ 1 := by rw [abs_of_nonneg (hW p).1]; exact (hW p).2
  obtain ⟨htot,hmodulus⟩ := hmean N (by omega) hEven P D cap w _ L hwz hz hzn W habs
  have hp := chen_not_prime_of_even_four_le hEven hN
  have hgap := mul_le_mul (end_mass N D W hp hi hW) htot
    (Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (Nat.cast_nonneg D)
  have hlow := (lower_endpoint_invoice_le_divisor_sum P N D cap w ((N:ℝ)^v) L).trans
    (sum_divisors_card_le_log D)
  have hupp := (upper_endpoint_invoice_le_divisor_sum P N D cap w ((N:ℝ)^v) L).trans
    (sum_divisors_card_le_log D)
  have hDG := mul_le_mul_of_nonneg_left (add_le_add_left hlogD 1) (Nat.cast_nonneg D)
  have hD0 : (0:ℝ) ≤ D := Nat.cast_nonneg _
  have hlog0 := Real.log_nonneg hn.le
  have hshort : (D:ℝ)*(1+Real.log (N:ℝ)) ≤ 40*(N:ℝ)/Real.log (N:ℝ)^3 := by
    linarith only [hwindow.2,mul_nonneg hD0 (add_nonneg zero_le_one hlog0)]
  have hcost := mul_le_mul_of_nonneg_left hshort (show 0 ≤ 2+C by linarith)
  have htime : (2+C)*((D:ℝ)*(1+Real.log (N:ℝ))) ≤ eta/3*singularNormalization N := by
    refine hcost.trans ?_
    convert hend using 1 <;> ring
  have hcm := (hcentre N hN hEven P cap w ((N:ℝ)^v) L).trans
    (by simpa only [pow_one] using hcen)
  have hmul := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hceil hC.le) hlog0
  have hmp := hmodulus.trans (hmul.trans (by
    simpa only [pow_one,mul_assoc,mul_left_comm,mul_comm] using hmod))
  have h0 := actual_carrier_sharp_density_invoice P N D cap w ((N:ℝ)^v) L W hp hi hW
  dsimp only
  linarith only [h0,hlow,hupp,hDG,hgap,hcm,hmp,htime,mul_nonneg hD0 hC.le]

end
end ImbalancedChen.P4AFull87SharpMeanAsymptoticPayment
