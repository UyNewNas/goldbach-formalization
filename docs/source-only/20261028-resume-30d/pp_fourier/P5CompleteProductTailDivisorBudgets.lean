import ImbalancedChen.P5ActualCompleteModulusFourierTail

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The elementary mixed moment used here is DERIVED from the original native
divisor-power bound, its unshifted finite mean, and the previously written
real-endpoint E1 shifted interval theorem. For Fourier tail payment one may
use a global complete-product scale X >= T with b <= 6X; retained arithmetic
mode estimates keep their own smaller local scale. No E3 or final Fourier
tail estimate is inserted as a new primitive premise.
-/
namespace ImbalancedChen.P5Z.CompleteProductTailDivisorBudgets
noncomputable section
open Classical MeasureTheory Set
open scoped BigOperators
open ActualCompleteModulusFourierTail P5OriginalPrimeEndpoint
open ImbalancedChen.Part3.ElementaryShiftedTau
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- One global logarithm is fixed before every Fourier accuracy exponent. -/
def logScale (X : ℝ) : ℝ := 1 + Real.log (7 * X)

theorem logScale_one_le {X : ℝ} (hX : 1 ≤ X) : 1 ≤ logScale X := by
  unfold logScale
  linarith [Real.log_nonneg (by linarith : (1 : ℝ) ≤ 7 * X)]

def completeNonzero (X : ℝ) (T : ℕ) : Finset ℕ :=
  (Finset.Icc 1 ⌊6 * X⌋₊).filter (fun b => b ≠ T)

theorem distance_eq_natAbs (T b : ℕ) : distance T b = ((b : ℤ) - T).natAbs := by
  unfold distance
  split_ifs with h
  · have heq : (b : ℤ) - T = -((T - b : ℕ) : ℤ) := by omega
    rw [heq]
    simp
  · have heq : (b : ℤ) - T = ((b - T : ℕ) : ℤ) := by omega
    rw [heq]
    simp

theorem tau_pow_le_native (r : ℕ) {n : ℕ} (hn : n ≠ 0) :
    tau n ^ r ≤ (fouvryTau (2 ^ r) n : ℝ) := by
  have h := fouvryTau_pow_le 2 r hn
  rw [fouvryTau_two] at h
  exact_mod_cast h

/-- The true unshifted mean, including exponent zero, reused from the
formalized native divisor-power mean rather than assumed as a tail port. -/
theorem sum_tau_pow_Icc_le (r : ℕ) {X : ℝ} (hX : 1 ≤ X) :
    (∑ b ∈ Finset.Icc 1 ⌊6 * X⌋₊, tau b ^ r) ≤
      6 * X * logScale X ^ (2 ^ r - 1) := by
  have hI : Finset.Icc 1 ⌊6 * X⌋₊ = Finset.Ioc 0 ⌊6 * X⌋₊ := by
    ext b
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [hI]
  have hn := sum_fouvryTau_pow_le_real (k := 2) (r := r) (by norm_num)
    (show (1 : ℝ) ≤ 6 * X by linarith)
  rw [fouvryTau_two] at hn
  have hlog : 1 + Real.log (6 * X) ≤ logScale X := by
    unfold logScale
    exact add_le_add_left (Real.log_le_log (by linarith) (by linarith)) 1
  exact hn.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by linarith [Real.log_nonneg (by linarith : (1 : ℝ) ≤ 6 * X)])
      hlog _) (by linarith : 0 ≤ 6 * X))

/-- The original shifted E1 is used at kappa=0 on the complete global
scale X>=T. It gives a near-linear budget without any tau(0) term. -/
theorem sum_shifted_native_le {K : ℕ} (hK : 2 ≤ K) {X : ℝ} (hX : 1 ≤ X)
    (T : ℕ) (hT : (T : ℝ) ≤ X) :
    (∑ b ∈ completeNonzero X T, (fouvryTau K (distance T b) : ℝ)) ≤
      26 * (K : ℝ) * X * logScale X ^ (K - 1) := by
  have hsource : completeNonzero X T =
      (Finset.Icc 1 ⌊6 * X⌋₊).filter (fun b : ℕ => (b : ℤ) ≠ (T : ℤ)) := by
    ext b
    simp only [completeNonzero, Finset.mem_filter, Int.natCast_inj]
  have hraw := shifted_tau_Icc_sum_le hK hX (κ := 0) (by norm_num) (T : ℤ)
    (by simpa using hT)
  simp only [add_zero, Real.rpow_one] at hraw
  have hZ : (1 : ℝ) ≤ 7 * X := by linarith
  have hKpos : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  have hzpow : (7 * X) ^ (1 - 1 / (K : ℝ)) ≤ 7 * X := by
    have h := Real.rpow_le_rpow_of_exponent_le hZ
      (show 1 - 1 / (K : ℝ) ≤ 1 by positivity)
    simpa only [Real.rpow_one] using h
  have hL : 1 ≤ logScale X := logScale_one_le hX
  have hpower : logScale X ^ (K - 2) ≤ logScale X ^ (K - 1) :=
    pow_le_pow_right₀ hL (by omega)
  have hsecond : (7 * X) ^ (1 - 1 / (K : ℝ)) * logScale X ^ (K - 2) ≤
      (7 * X) * logScale X ^ (K - 1) :=
    mul_le_mul hzpow hpower (pow_nonneg (by linarith) _) (by linarith)
  rw [hsource]
  simp_rw [distance_eq_natAbs]
  calc
    (∑ b ∈ (Finset.Icc 1 ⌊6 * X⌋₊).filter (fun b : ℕ => (b : ℤ) ≠ (T : ℤ)),
      (fouvryTau K ((b : ℤ) - T).natAbs : ℝ)) ≤
        2 * (K : ℝ) * (6 * X * logScale X ^ (K - 1) +
          (7 * X) ^ (1 - 1 / (K : ℝ)) * logScale X ^ (K - 2)) := hraw
    _ ≤ 2 * (K : ℝ) * (6 * X * logScale X ^ (K - 1) +
        7 * X * logScale X ^ (K - 1)) :=
      mul_le_mul_of_nonneg_left (add_le_add_left hsecond _) (by positivity)
    _ = 26 * (K : ℝ) * X * logScale X ^ (K - 1) := by ring

/-- Derived complete-product mixed moment. R,S are fixed divisor orders
and the constant/exponent are independent of the requested accuracy.
Only the shifted order needs S>=1; unshifted R=0 is included. -/
theorem complete_mixed_moment_le (R S : ℕ) (hS : 1 ≤ S)
    {X : ℝ} (hX : 1 ≤ X) (T : ℕ) (hT : (T : ℝ) ≤ X) :
    (∑ b ∈ completeNonzero X T, tau b ^ R * tau (distance T b) ^ S) ≤
      (3 + 13 * (2 ^ (2 * S) : ℕ) : ℝ) * X *
        logScale X ^ (2 ^ (2 * R) + 2 ^ (2 * S)) := by
  let KS := 2 ^ (2 * S)
  let E := 2 ^ (2 * R) + KS
  have hKS : 2 ≤ KS := by
    have h := Nat.pow_le_pow_right (by norm_num : 0 < 2) (show 1 ≤ 2 * S by omega)
    simpa only [pow_one, KS] using h
  have hpoint (b : ℕ) (hb : b ∈ completeNonzero X T) :
      tau b ^ R * tau (distance T b) ^ S ≤
        (tau b ^ (2 * R) + (fouvryTau KS (distance T b) : ℝ)) / 2 := by
    have hne : distance T b ≠ 0 := (distance_pos (Finset.mem_filter.mp hb).2).ne'
    have hp := tau_pow_le_native (2 * S) hne
    have hsquare : (tau (distance T b) ^ S) ^ 2 ≤
        (fouvryTau KS (distance T b) : ℝ) := by
      simpa only [KS, ← pow_mul, Nat.mul_comm] using hp
    have hs := sq_nonneg (tau b ^ R - tau (distance T b) ^ S)
    have hr : (tau b ^ R) ^ 2 = tau b ^ (2 * R) := by rw [← pow_mul]; ring_nf
    rw [hr] at hs
    nlinarith
  have hu : (∑ b ∈ completeNonzero X T, tau b ^ (2 * R)) ≤
      6 * X * logScale X ^ (2 ^ (2 * R) - 1) := by
    apply le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun b hb hnot => by positivity))
    exact sum_tau_pow_Icc_le (2 * R) hX
  have hv := sum_shifted_native_le hKS hX T hT
  have hL := logScale_one_le hX
  have hpu : logScale X ^ (2 ^ (2 * R) - 1) ≤ logScale X ^ E :=
    pow_le_pow_right₀ hL (by dsimp [E]; omega)
  have hpv : logScale X ^ (KS - 1) ≤ logScale X ^ E :=
    pow_le_pow_right₀ hL (by dsimp [E]; omega)
  calc
    (∑ b ∈ completeNonzero X T, tau b ^ R * tau (distance T b) ^ S) ≤
        ∑ b ∈ completeNonzero X T,
          (tau b ^ (2 * R) + (fouvryTau KS (distance T b) : ℝ)) / 2 :=
      Finset.sum_le_sum hpoint
    _ = ((∑ b ∈ completeNonzero X T, tau b ^ (2 * R)) +
        (∑ b ∈ completeNonzero X T, (fouvryTau KS (distance T b) : ℝ))) / 2 := by
      rw [Finset.sum_div, Finset.sum_add_distrib]
    _ ≤ (6 * X * logScale X ^ (2 ^ (2 * R) - 1) +
        26 * (KS : ℝ) * X * logScale X ^ (KS - 1)) / 2 := by
      gcongr
    _ ≤ (6 * X * logScale X ^ E + 26 * (KS : ℝ) * X * logScale X ^ E) / 2 := by
      gcongr
    _ = (3 + 13 * (2 ^ (2 * S) : ℕ) : ℝ) * X *
        logScale X ^ (2 ^ (2 * R) + 2 ^ (2 * S)) := by
      dsimp [KS, E]
      push_cast
      ring

/-- General squarefree reciprocal-totient moment: this extends the
already formalized exponent-4/16 identity to its actual fixed J. -/
theorem squarefree_halfProduct_power (J : ℕ) {q : ℕ} (hq : Squarefree q) :
    (halfProductDensity ^ (2 ^ J)) q = tau q ^ J / (q.totient : ℝ) := by
  have htau : tau q ^ J = ∏ p ∈ q.primeFactors, ((2 ^ J : ℕ) : ℝ) := by
    rw [tau, squarefree_divisors_card_eq_prod_two hq, ← Finset.prod_pow]
    simp only [Nat.cast_pow, Nat.cast_ofNat]
  rw [← halfProductDensity_isMultiplicative.pow.prod_primeFactors hq]
  calc
    _ = ∏ p ∈ q.primeFactors, ((2 ^ J : ℕ) : ℝ) * halfProductDensity p := by
      apply Finset.prod_congr rfl
      intro p hp
      exact halfProductDensity_pow_apply_prime (2 ^ J) (Nat.prime_of_mem_primeFactors hp)
    _ = (∏ p ∈ q.primeFactors, ((2 ^ J : ℕ) : ℝ)) * halfProductDensity q := by
      rw [Finset.prod_mul_distrib, halfProductDensity_isMultiplicative.prod_primeFactors hq]
    _ = tau q ^ J / (q.totient : ℝ) := by rw [← htau, halfProductDensity_apply]; ring

theorem squarefree_tau_totient_sum_le (Q : Finset ℕ) (D J : ℕ)
    (hQ : Q ⊆ Finset.Icc 1 D) (hsq : ∀ q ∈ Q, Squarefree q) :
    (∑ q ∈ Q, tau q ^ J / (q.totient : ℝ)) ≤
      (4 * (1 + Real.log (max 1 (D : ℝ)))) ^ (2 ^ J) := by
  have hnonneg (n : ℕ) : 0 ≤ halfProductDensity n := by
    rw [halfProductDensity_apply]
    positivity
  have hexp : (2 ^ J - 1) + 1 = 2 ^ J := by
    have hp : 0 < (2 : ℕ) ^ J := pow_pos (by decide) _
    omega
  have hconv : (∑ q ∈ Q, tau q ^ J / (q.totient : ℝ)) =
      ∑ q ∈ Q, (halfProductDensity ^ (2 ^ J)) q := by
    apply Finset.sum_congr rfl
    intro q hq
    exact (squarefree_halfProduct_power J (hsq q hq)).symm
  rw [hconv]
  calc
    (∑ q ∈ Q, (halfProductDensity ^ (2 ^ J)) q) ≤
      ∑ q ∈ Finset.Icc 1 D, (halfProductDensity ^ (2 ^ J)) q :=
      Finset.sum_le_sum_of_subset_of_nonneg hQ (fun q hq hnot =>
        arithmeticFunction_pow_nonneg halfProductDensity hnonneg (2 ^ J) q)
    _ ≤ (∑ q ∈ Finset.Icc 1 D, 1 / (q.totient : ℝ)) ^ (2 ^ J) := by
      simpa only [hexp, halfProductDensity_apply] using
        sum_arithmeticFunction_pow_succ_le halfProductDensity hnonneg (2 ^ J - 1) D
    _ ≤ (4 * (1 + Real.log (max 1 (D : ℝ)))) ^ (2 ^ J) :=
      pow_le_pow_left₀ (Finset.sum_nonneg (fun q hq => by positivity))
        (sum_reciprocal_totient_le_log D) _

theorem actual_rho_mean_budget (Q : Finset ℕ) (rho : ℕ → ℂ) (D J : ℕ)
    (hQ : effectiveModuli Q ⊆ Finset.Icc 1 D)
    (hsq : ∀ q ∈ effectiveModuli Q, Squarefree q)
    (Cρ : ℝ) (hCρ : 0 ≤ Cρ)
    (hrho : ∀ q ∈ effectiveModuli Q, ‖rho q‖ ≤ Cρ * tau q ^ J) :
    rhoMeanMass Q rho ≤ Cρ *
      (4 * (1 + Real.log (max 1 (D : ℝ)))) ^ (2 ^ J) := by
  unfold rhoMeanMass
  calc
    (∑ q ∈ effectiveModuli Q, ‖rho q‖ / (q.totient : ℝ)) ≤
      ∑ q ∈ effectiveModuli Q, Cρ * (tau q ^ J / (q.totient : ℝ)) := by
      apply Finset.sum_le_sum
      intro q hq
      simpa only [mul_div_assoc] using div_le_div_of_nonneg_right (hrho q hq) (Nat.cast_nonneg _)
    _ = Cρ * ∑ q ∈ effectiveModuli Q, tau q ^ J / (q.totient : ℝ) := by rw [Finset.mul_sum]
    _ ≤ Cρ * (4 * (1 + Real.log (max 1 (D : ℝ)))) ^ (2 ^ J) :=
      mul_le_mul_of_nonneg_left (squarefree_tau_totient_sum_le _ D J hQ hsq) hCρ

/-- The exceptional b=T row retains the actual modulus support cap D. -/
theorem actual_rho_total_budget (Q : Finset ℕ) (rho : ℕ → ℂ) (D J : ℕ)
    (hD : 1 ≤ D) (hQ : effectiveModuli Q ⊆ Finset.Icc 1 D)
    (Cρ : ℝ) (hCρ : 0 ≤ Cρ)
    (hrho : ∀ q ∈ effectiveModuli Q, ‖rho q‖ ≤ Cρ * tau q ^ J) :
    rhoMass Q rho ≤ Cρ * (D : ℝ) * (1 + Real.log (D : ℝ)) ^ (2 ^ J - 1) := by
  have hsub : effectiveModuli Q ⊆ Finset.Ioc 0 D := by
    intro q hq
    have h := Finset.mem_Icc.mp (hQ hq)
    exact Finset.mem_Ioc.mpr ⟨by omega, h.2⟩
  have hDreal : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hn := sum_fouvryTau_pow_le_real (k := 2) (r := J) (by norm_num) hDreal
  simp only [Nat.floor_natCast, fouvryTau_two] at hn
  calc
    rhoMass Q rho ≤ Cρ * ∑ q ∈ effectiveModuli Q, tau q ^ J := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum hrho
    _ ≤ Cρ * ∑ q ∈ Finset.Ioc 0 D, tau q ^ J :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun q hq hnot => by positivity)) hCρ
    _ ≤ Cρ * ((D : ℝ) * (1 + Real.log (D : ℝ)) ^ (2 ^ J - 1)) :=
      mul_le_mul_of_nonneg_left hn hCρ
    _ = _ := by ring

end
end ImbalancedChen.P5Z.CompleteProductTailDivisorBudgets
