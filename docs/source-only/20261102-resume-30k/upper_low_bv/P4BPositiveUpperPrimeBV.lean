import ImbalancedChen.P4BPositiveUpperLowRankClass
import ImbalancedChen.Part3PrimeAPDistribution
import ImbalancedChen.P5PrimeDivisorMeanCorrection

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Maximal classical PRIME BV, with its actual logarithmic-integral centre,
is converted here to the exact coprime prime mean.  Endpoint selectors may
move with the modulus.  A common source profile is a finite superposition
of prefixes; its l1 coefficient mass, not its number of pieces, is charged.
This is not a convolution BV assertion for the whole Gamma source.
-/
namespace ImbalancedChen.P4BPositiveUpperPrimeBV
noncomputable section
open scoped Classical BigOperators
open Filter Topology
open MathlibNt.SieveTheory.BombieriVinogradov
open MathlibNt.SieveTheory.LiuWeight
open P4BPositiveUpperLowRankClass

def primeError (Y a q : ℕ) : ℝ :=
  finitePrimitiveDiscrepancy (chenPrimePrefix Y) (fun _ => 1) a q

def bvPool (X Q : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 Q, standardPrimeAPPrefixMaxError X q

def logBudget (Q : ℕ) : ℝ := 1 + Real.log (max 1 (Q : ℝ))

theorem logBudget_nonneg (Q : ℕ) : 0 ≤ logBudget Q := by
  have h := Real.log_nonneg (le_max_left (1 : ℝ) (Q : ℝ))
  unfold logBudget
  linarith

theorem primeError_eq_trueLi_errors (Y a q : ℕ) :
    primeError Y a q = part3PrimeAPError Y a q -
      part3PrimeAPError Y 1 1 / (Nat.totient q : ℝ) +
      chenPrimeDivisorCount Y q / (Nat.totient q : ℝ) := by
  have hAP : finiteCongruenceMass (chenPrimePrefix Y) (fun _ => 1) a q =
      chenPrimeAPCount Y a q := by
    simp [finiteCongruenceMass,chenPrimeAPCount]
  have hunit : part3PrimeAPError Y 1 1 =
      ((chenPrimePrefix Y).card : ℝ) - trueLogarithmicIntegral Y := by
    simp [part3PrimeAPError,chenPrimeAPCount,Nat.ModEq]
  rw [primeError,finitePrimitiveDiscrepancy,hAP,chenPrimePrefix_coprime_mass,hunit]
  unfold part3PrimeAPError
  ring

theorem primeDivisorCount_mono {Y X : ℕ} (hYX : Y ≤ X) (q : ℕ) :
    chenPrimeDivisorCount Y q ≤ chenPrimeDivisorCount X q := by
  unfold chenPrimeDivisorCount
  exact_mod_cast Finset.card_le_card (show
    (chenPrimePrefix Y).filter (fun p => p ∣ q) ⊆
      (chenPrimePrefix X).filter (fun p => p ∣ q) from by
        intro p hp
        obtain ⟨hpY,hpq⟩ := Finset.mem_filter.mp hp
        obtain ⟨hpY,hprime⟩ := mem_chenPrimePrefix.mp hpY
        exact Finset.mem_filter.mpr ⟨mem_chenPrimePrefix.mpr ⟨hpY.trans hYX,hprime⟩,hpq⟩)

/-- Both the primitive residue and the endpoint are selected after X. -/
theorem primeError_le_prefix {X Y a q : ℕ}
    (hYX : Y ≤ X) (hq : 0 < q) (ha : a.Coprime q) :
    |primeError Y a q| ≤ standardPrimeAPPrefixMaxError X q +
      standardPrimeAPPrefixMaxError X 1 / (Nat.totient q : ℝ) +
      chenPrimeDivisorCount X q / (Nat.totient q : ℝ) := by
  rw [primeError_eq_trueLi_errors]
  have hphi : 0 ≤ (Nat.totient q : ℝ) := Nat.cast_nonneg _
  have hD : 0 ≤ chenPrimeDivisorCount Y q := Nat.cast_nonneg _
  calc
    _ ≤ |part3PrimeAPError Y a q| +
        |part3PrimeAPError Y 1 1 / (Nat.totient q : ℝ)| +
        |chenPrimeDivisorCount Y q / (Nat.totient q : ℝ)| :=
      (abs_add _ _).trans (add_le_add_right (abs_sub _ _) _)
    _ ≤ _ := by
      rw [abs_div,abs_div,abs_of_nonneg hphi,abs_of_nonneg hD]
      exact add_le_add
        (add_le_add (part3_abs_primeAPError_le_prefix hYX hq ha)
          (div_le_div_of_nonneg_right
            (part3_abs_primeAPError_le_prefix hYX (by omega : 0 < 1) (by simp)) hphi))
        (div_le_div_of_nonneg_right (primeDivisorCount_mono hYX q) hphi)

/-- The extra mean costs only one reciprocal-totient logarithm and the
full modulus-prime correction costs log squared.  No pi/li error is
silently omitted.  Squarefreeness is used only in the last correction. -/
theorem sum_primeError_le_pool (X Q : ℕ) (hQ : 1 ≤ Q)
    (S : Finset ℕ) (hS : S ⊆ Finset.Icc 1 Q)
    (hsq : ∀ q ∈ S, Squarefree q) (Y a : ℕ → ℕ)
    (hY : ∀ q ∈ S, Y q ≤ X) (ha : ∀ q ∈ S, (a q).Coprime q) :
    (∑ q ∈ S, |primeError (Y q) (a q) q|) ≤
      (1 + 4*logBudget Q)*bvPool X Q + 4*(logBudget Q)^2 := by
  have hE0 : 0 ≤ standardPrimeAPPrefixMaxError X 1 :=
    standardPrimeAPPrefixMaxError_nonneg X 1
  have hE : standardPrimeAPPrefixMaxError X 1 ≤ bvPool X Q := by
    exact Finset.single_le_sum (fun q _ => standardPrimeAPPrefixMaxError_nonneg X q)
      (Finset.mem_Icc.mpr ⟨le_rfl,hQ⟩)
  have hsum : (∑ q ∈ S, standardPrimeAPPrefixMaxError X q) ≤ bvPool X Q :=
    Finset.sum_le_sum_of_subset_of_nonneg hS
      (fun q _ _ => standardPrimeAPPrefixMaxError_nonneg X q)
  have hrec := sum_reciprocal_totient_subset_le_log S Q hS
  have hdiv := P5PrimeDivisorMean.sum_prime_divisor_count_div_totient_le_log_square
    X Q S hS hsq
  calc
    _ ≤ ∑ q ∈ S, (standardPrimeAPPrefixMaxError X q +
        standardPrimeAPPrefixMaxError X 1 / (Nat.totient q : ℝ) +
        chenPrimeDivisorCount X q / (Nat.totient q : ℝ)) := by
      apply Finset.sum_le_sum
      intro q hq
      exact primeError_le_prefix (hY q hq) (Finset.mem_Icc.mp (hS hq)).1 (ha q hq)
    _ = (∑ q ∈ S, standardPrimeAPPrefixMaxError X q) +
        standardPrimeAPPrefixMaxError X 1 * (∑ q ∈ S, 1/(Nat.totient q : ℝ)) +
        (∑ q ∈ S, chenPrimeDivisorCount X q / (Nat.totient q : ℝ)) := by
      simp only [Finset.sum_add_distrib,Finset.mul_sum,div_eq_mul_inv,one_mul]
    _ ≤ bvPool X Q + bvPool X Q*(4*logBudget Q) + 4*(logBudget Q)^2 := by
      exact add_le_add (add_le_add hsum
        ((mul_le_mul_of_nonneg_left hrec hE0).trans
          (mul_le_mul_of_nonneg_right hE (mul_nonneg (by norm_num) (logBudget_nonneg Q))))) hdiv
    _ = _ := by ring

theorem belowHalfCap_le_target {X : ℕ} (hX : 1 ≤ X) :
    1 ≤ Nat.floor ((X : ℝ)^(9/20 : ℝ)) ∧
      Nat.floor ((X : ℝ)^(9/20 : ℝ)) ≤ X := by
  have hXr : (1 : ℝ) ≤ X := by exact_mod_cast hX
  constructor
  · exact Nat.le_floor (by simpa using Real.one_le_rpow hXr (by norm_num : (0 : ℝ) ≤ 9/20))
  · apply Nat.floor_le_of_le
    calc
      (X : ℝ)^(9/20 : ℝ) ≤ (X : ℝ)^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hXr (by norm_num)
      _ = X := Real.rpow_one _

/-- Unconditional, exact-coprime, maximal PRIME BV at the genuine fixed
gap 1/20.  Constants precede S, all endpoints, and every primitive residue.
The only BV input is the pinned upstream standard theorem; there is no
user-supplied class distribution hypothesis. -/
theorem eventually_primeError_log_saving (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℕ in atTop,
      ∀ S : Finset ℕ, S ⊆ Finset.Icc 1 (Nat.floor ((X : ℝ)^(9/20 : ℝ))) →
        (∀ q ∈ S, Squarefree q) → ∀ Y a : ℕ → ℕ,
          (∀ q ∈ S, Y q ≤ X) → (∀ q ∈ S, (a q).Coprime q) →
          (∑ q ∈ S, |primeError (Y q) (a q) q|) ≤
            C*(X : ℝ)/Real.log (X : ℝ)^A := by
  obtain ⟨B,hB,C,hC,hBV⟩ :=
    AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418.standardBombieriVinogradov
      ((A+2 : ℕ) : ℝ) (by positivity)
  have hcap : ∀ᶠ X : ℕ in atTop,
      Nat.floor ((X : ℝ)^(9/20 : ℝ)) ≤ panModulusCutoff X B := by
    have h := eventually_liuSourceDEpsilon_le_panModulusCutoff
      (1/20 : ℝ) B (by norm_num) hB
    simpa only [liuSourceDEpsilon,show (1/2-1/20 : ℝ)=9/20 by norm_num] using h
  have hsmall : ∀ᶠ X : ℕ in atTop,
      Real.log (X : ℝ)^(A+2) ≤ (X : ℝ) := by
    have h := (tendsto_nat_log_pow_div_rpow (A+2)
      (by norm_num : (0 : ℝ)<1)).eventually (gt_mem_nhds (by norm_num : (0 : ℝ)<1))
    filter_upwards [h,eventually_ge_atTop (1 : ℕ)] with X hx hX
    have hp : (0 : ℝ)<X := by exact_mod_cast (show 0<X by omega)
    simp only [Real.rpow_one] at hx
    have hh := ((div_lt_iff₀ hp).mp hx).le
    simpa only [one_mul] using hh
  refine ⟨9*C+16,by linarith,?_⟩
  filter_upwards [hBV,hcap,hsmall,eventually_one_le_nat_log,eventually_ge_atTop (2 : ℕ)]
    with X hBVX hcapX hsmallX hlog hX
  intro S hS hsq Y a hY ha
  let Q := Nat.floor ((X : ℝ)^(9/20 : ℝ))
  have hQ := belowHalfCap_le_target (by omega : 1 ≤ X)
  have hQr : (Q : ℝ) ≤ X := by exact_mod_cast hQ.2
  have hXr : (1 : ℝ) ≤ X := by exact_mod_cast (show 1≤X by omega)
  have hlogQ : logBudget Q ≤ 2*Real.log (X : ℝ) := by
    have hh := Real.log_le_log (lt_of_lt_of_le zero_lt_one (le_max_left (1 : ℝ) (Q : ℝ)))
      (max_le hXr hQr)
    unfold logBudget
    linarith
  have hpool : bvPool X Q ≤ C*(X : ℝ)/Real.log (X : ℝ)^(A+2) := by
    refine (Finset.sum_le_sum_of_subset_of_nonneg ?_
      (fun q _ _ => standardPrimeAPPrefixMaxError_nonneg X q)).trans ?_
    · intro q hq
      obtain ⟨hq1,hqQ⟩ := Finset.mem_Icc.mp hq
      exact Finset.mem_Icc.mpr ⟨hq1,hqQ.trans hcapX⟩
    · simpa only [Real.rpow_natCast] using hBVX hX
  have hp : 0 < Real.log (X : ℝ) := zero_lt_one.trans_le hlog
  have hmain : (1+4*logBudget Q)*bvPool X Q ≤
      9*C*(X : ℝ)/Real.log (X : ℝ)^A := by
    have hfac : 1+4*logBudget Q ≤ 9*Real.log (X : ℝ)^2 := by
      have hs := mul_le_mul_of_nonneg_left hlog hp.le
      nlinarith
    calc
      _ ≤ (9*Real.log (X : ℝ)^2)*(C*(X : ℝ)/Real.log (X : ℝ)^(A+2)) :=
        mul_le_mul hfac hpool
          (Finset.sum_nonneg (fun q _ => standardPrimeAPPrefixMaxError_nonneg X q))
          (by positivity)
      _ = _ := by rw [pow_add]; field_simp [hp.ne']; ring
  have hmean : 4*(logBudget Q)^2 ≤ 16*(X : ℝ)/Real.log (X : ℝ)^A := by
    have hs := (sq_le_sq₀ (logBudget_nonneg Q) (by positivity : 0≤2*Real.log (X : ℝ))).mpr hlogQ
    have hp2 : Real.log (X : ℝ)^2 ≤ (X : ℝ)/Real.log (X : ℝ)^A := by
      apply (le_div_iff₀ (pow_pos hp A)).mpr
      simpa only [pow_add,mul_comm] using hsmallX
    nlinarith
  exact (sum_primeError_le_pool X Q hQ.1 S hS hsq Y a hY ha).trans
    (by nlinarith [add_le_add hmain hmean])

/-- A finite signed profile on one unchanged prime carrier.  Intervals
are the two-prefix case, with exact left-open/right-closed ownership. -/
def prefixProfile {ι : Type*} (I : Finset ι) (c : ι → ℝ)
    (Y : ι → ℕ) (p : ℕ) : ℝ :=
  ∑ i ∈ I, c i * (if p ≤ Y i then 1 else 0)

theorem prefixProfile_discrepancy {ι : Type*} (I : Finset ι)
    (c : ι → ℝ) (Y : ι → ℕ) (X a q : ℕ) (hY : ∀ i ∈ I, Y i ≤ X) :
    finitePrimitiveDiscrepancy (chenPrimePrefix X) (prefixProfile I c Y) a q =
      ∑ i ∈ I, c i * primeError (Y i) a q := by
  rw [prefixProfile,finitePrimitiveDiscrepancy_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hmul (w : ℕ → ℝ) :
      finitePrimitiveDiscrepancy (chenPrimePrefix X) (fun p => c i*w p) a q =
        c i*finitePrimitiveDiscrepancy (chenPrimePrefix X) w a q := by
    simp only [finitePrimitiveDiscrepancy,finiteCongruenceMass,finiteCoprimeMass,
      ← Finset.mul_sum]
    ring
  rw [hmul,P5S1SingletonPP.prefix_truncation_discrepancy_eq X (Y i) a q (hY i hi)]
  rfl

/-- The complete signed physical sum pays the variation/scalar mass of
the common profile.  The number of endpoints never enters the bound. -/
theorem eventually_profile_log_saving (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℕ in atTop,
      ∀ (S : Finset ℕ) (rho : ℕ → ℝ),
        S ⊆ Finset.Icc 1 (Nat.floor ((X : ℝ)^(9/20 : ℝ))) →
        (∀ q ∈ S, Squarefree q) → (∀ q ∈ S, |rho q| ≤ 1) →
        ∀ a : ℕ → ℕ, (∀ q ∈ S, (a q).Coprime q) →
        ∀ (k : ℕ) (I : Finset (Fin k)) (c : Fin k → ℝ) (Y : Fin k → ℕ),
        (∀ i ∈ I, Y i ≤ X) →
        |∑ q ∈ S, rho q * finitePrimitiveDiscrepancy (chenPrimePrefix X)
          (prefixProfile I c Y) (a q) q| ≤
          (∑ i ∈ I, |c i|)*(C*(X : ℝ)/Real.log (X : ℝ)^A) := by
  obtain ⟨C,hC,h⟩ := eventually_primeError_log_saving A
  refine ⟨C,hC,?_⟩
  filter_upwards [h] with X hX
  intro S rho hS hsq hrho a ha k I c Y hY
  simp_rw [prefixProfile_discrepancy I c Y X _ _ hY,Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ i ∈ I, |∑ q ∈ S, rho q * (c i * primeError (Y i) (a q) q)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ I, |c i|*(C*(X : ℝ)/Real.log (X : ℝ)^A) := by
      apply Finset.sum_le_sum
      intro i hi
      calc
        _ ≤ ∑ q ∈ S, |rho q * (c i * primeError (Y i) (a q) q)| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ q ∈ S, |c i|*|primeError (Y i) (a q) q| := by
          apply Finset.sum_le_sum
          intro q hq
          rw [abs_mul,abs_mul]
          exact (mul_le_mul_of_nonneg_right (hrho q hq) (by positivity)).trans_eq (one_mul _)
        _ = |c i|*(∑ q ∈ S, |primeError (Y i) (a q) q|) := (Finset.mul_sum _ _ _).symm
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (hX S hS hsq (fun _ => Y i) a (fun _ _ => hY i hi) ha) (abs_nonneg _)
    _ = _ := (Finset.sum_mul _ _ _).symm

end
end ImbalancedChen.P4BPositiveUpperPrimeBV
