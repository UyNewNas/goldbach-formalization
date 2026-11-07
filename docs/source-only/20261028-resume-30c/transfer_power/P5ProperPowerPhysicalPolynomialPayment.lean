import ImbalancedChen.P5ProperPowerActualReciprocalTail
import ImbalancedChen.Part3PolynomialResidueDivisorBound
import ImbalancedChen.P4BActualSmoothHyperbolaCorrection
import ImbalancedChen.PowerErrorBudget

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The named existing divisor-subpower theorem and finite reciprocal-totient
logarithmic theorem are applied to the LITERAL attached upper rho.
Its active primitive support is used after exact q=1/zero-row erasure.
The genuine active-cap polynomial range remains explicit; no such range
is claimed for arbitrary causal policies. Complete-product=N collision
is paid separately from noncollision distances, with integer-word tau(N)^k.
-/

namespace ImbalancedChen.P5Z.ProperPowerPhysicalPolynomialPayment

noncomputable section
open Classical Filter Topology
open scoped BigOperators
open ImbalancedChen.Part3
open ImbalancedChen.P5Z.AdmissibleAllRankIntegerGeometricFamily
open ImbalancedChen.Part3.AllKFamilyLambdaCorrectionBound
open ImbalancedChen.Part3.AllKLambdaChartCorrection
open ImbalancedChen.P5Z.ActualLabelledPrimeSmoothCharts
open ImbalancedChen.Part3.PolynomialResidueDivisorBound
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
open ImbalancedChen.P4BPrimitiveModulusEndpoints
open ImbalancedChen.P4BActualSmoothHyperbolaCorrection
open ImbalancedChen.P5Z.ProperPowerSignedMeanHBTransport
open ImbalancedChen.P5Z.ProperPowerSignedModulusPayment
open ImbalancedChen.P5Z.ProperPowerActualReciprocalTail
open ImbalancedChen.P5Z.RoughSquareWeightedBudget

/-- Complex version of the SAME real physical coefficient, with no
absolute-value or positivity substitution in the signed functional. -/
def physicalRho (nu r epsilon : ℝ) (retain : ℕ → List ℕ → Bool)
    (cap : ℕ → ℕ) (N q : ℕ) : ℂ :=
  (attachedUpperCoefficient nu r epsilon retain cap N q : ℂ)

abbrev physicalQ (nu r epsilon : ℝ) (retain : ℕ → List ℕ → Bool)
    (cap : ℕ → ℕ) (N : ℕ) : Finset ℕ :=
  attachedPrimitiveModuli nu r epsilon retain cap N

/-- Exact complex signed-row restriction: q=1 cancels in count minus mean,
while zero coefficients disappear without enlarging their counting cost. -/
theorem physical_signedRow_eq_active (nu r epsilon : ℝ)
    (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ) (N b : ℕ) :
    signedRow (attachedUpperModuli nu r epsilon retain cap N)
      (physicalRho nu r epsilon retain cap N) N b =
    signedRow (physicalQ nu r epsilon retain cap N)
      (physicalRho nu r epsilon retain cap N) N b := by
  unfold signedRow
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro q hq hnot
  by_cases hrho : attachedUpperCoefficient nu r epsilon retain cap N q = 0
  · simp only [physicalRho, hrho, Complex.ofReal_zero, zero_mul]
  · by_cases hq1 : q = 1
    · subst q
      simp [signedKernel, Nat.ModEq]
    · have hpos := attachedUpperModuli_pos nu r epsilon retain cap N hq
      exact False.elim (hnot ((mem_attachedPrimitiveModuli nu r epsilon retain cap N q).mpr
        ⟨hq, by omega, hrho⟩))

theorem physicalRho_norm_le_one (nu r epsilon : ℝ)
    (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ) (N q : ℕ) :
    ‖physicalRho nu r epsilon retain cap N q‖ ≤ 1 := by
  simpa only [physicalRho, attachedUpperCoefficient, Complex.norm_real, Real.norm_eq_abs] using
    actualSmallRoughRho_abs_le_one (retain N) N (cap N)
      ((N : ℝ)^(nu*epsilon^2)) ((N : ℝ)^(nu*r)) ((N : ℝ)^(nu*epsilon)) q

theorem physicalQ_subset_activeCap (nu r epsilon : ℝ)
    (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ) (N : ℕ) :
    physicalQ nu r epsilon retain cap N ⊆
      Finset.Icc 1 (actualActiveUpperCap nu r epsilon retain cap N) := by
  intro q hq
  obtain ⟨hmem, hgt, hactive⟩ := (mem_attachedPrimitiveModuli nu r epsilon retain cap N q).mp hq
  exact actual_active_modulus_mem_Icc nu r epsilon retain cap N q hmem hactive

theorem physicalQ_card_le_activeCap (nu r epsilon : ℝ)
    (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ) (N : ℕ) :
    (physicalQ nu r epsilon retain cap N).card ≤ actualActiveUpperCap nu r epsilon retain cap N := by
  simpa only [Nat.card_Icc, Nat.add_sub_cancel] using
    Finset.card_le_card (physicalQ_subset_activeCap nu r epsilon retain cap N)

/-- The existing finite Euler/totient theorem, with its absolute constant
four, pays the exact SAME physical rho mean on the true active carrier. -/
theorem physical_meanBudget_le_log (nu r epsilon : ℝ)
    (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ) (N : ℕ) :
    meanBudget (physicalQ nu r epsilon retain cap N)
      (physicalRho nu r epsilon retain cap N) ≤
      4 * logBudget (actualActiveUpperCap nu r epsilon retain cap N) := by
  calc
    _ ≤ ∑ q ∈ physicalQ nu r epsilon retain cap N, 1 / (Nat.totient q : ℝ) := by
      apply Finset.sum_le_sum
      intro q hq
      exact div_le_div_of_nonneg_right
        (physicalRho_norm_le_one nu r epsilon retain cap N q) (Nat.cast_nonneg _)
    _ ≤ _ := sum_reciprocal_totient_subset_le_log _ _
      (physicalQ_subset_activeCap nu r epsilon retain cap N)

/-- At complete-product range n<=ceil(U*N), every nonzero distance from
N is <=(U+2)N. The NAMED already-proved divisor subpower supplies the
uniform bound for the literal finite supremum, including the zero distance. -/
theorem distanceEnvelope_linear_subpower {eta : ℝ} (heta : 0 < eta) :
    ∃ C : ℝ, 0 < C ∧ ∀ (U : ℝ), 0 < U → ∀ N : ℕ, 1 ≤ N →
      (distanceDivisorEnvelope N (Nat.ceil (U*(N : ℝ))) : ℝ) ≤
        (C * (U+2)^eta) * (N : ℝ)^eta := by
  obtain ⟨C, hC, htau⟩ := fouvryTau_le_const_rpow (k := 2) (by norm_num) heta
  refine ⟨C, hC, ?_⟩
  intro U hU N hN
  let K := Nat.ceil (U*(N : ℝ))
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := zero_lt_one.trans_le hN1
  have hK : (K : ℝ) ≤ U*(N : ℝ)+1 :=
    (Nat.ceil_lt_add_one (mul_nonneg hU.le hN0.le)).le
  have hpoint (n : ℕ) (hn : n ∈ Finset.Icc 1 K) :
      ((ImbalancedChen.P5OriginalPrimeEndpoint.distance N n).divisors.card : ℝ) ≤
        (C*(U+2)^eta)*(N : ℝ)^eta := by
    let d := ImbalancedChen.P5OriginalPrimeEndpoint.distance N n
    have hdistNat : d ≤ N+n := by
      dsimp [d, ImbalancedChen.P5OriginalPrimeEndpoint.distance]
      split_ifs <;> omega
    have hnK : (n : ℝ) ≤ K := by exact_mod_cast (Finset.mem_Icc.mp hn).2
    have hd : (d : ℝ) ≤ (U+2)*(N : ℝ) := by
      have hsum : (d : ℝ) ≤ (N : ℝ)+(n : ℝ) := by exact_mod_cast hdistNat
      nlinarith
    change (d.divisors.card : ℝ) ≤ _
    by_cases hd0 : d = 0
    · simp only [hd0, Nat.divisors_zero, Finset.card_empty, Nat.cast_zero]
      positivity
    · have hsmall : (d.divisors.card : ℝ) ≤ C*(d : ℝ)^eta := by
        simpa only [fouvryTau_two] using htau d (Nat.pos_of_ne_zero hd0)
      calc
        _ ≤ C*(d : ℝ)^eta := hsmall
        _ ≤ C*((U+2)*(N : ℝ))^eta := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (Nat.cast_nonneg _) hd heta.le) hC.le
        _ = _ := by rw [Real.mul_rpow (by linarith : 0 ≤ U+2) hN0.le]; ring
  by_cases hs : (Finset.Icc 1 K).Nonempty
  · obtain ⟨n, hn, heq⟩ := Finset.exists_mem_eq_sup _ hs
      (fun n => (ImbalancedChen.P5OriginalPrimeEndpoint.distance N n).divisors.card)
    change (((Finset.Icc 1 K).sup (fun n =>
      (ImbalancedChen.P5OriginalPrimeEndpoint.distance N n).divisors.card) : ℕ) : ℝ) ≤ _
    rw [heq]
    exact hpoint n hn
  · have he := Finset.not_nonempty_iff_eq_empty.mp hs
    simp only [distanceDivisorEnvelope, he, Finset.sup_empty, Nat.bot_eq_zero, Nat.cast_zero]
    positivity

/-- All fixed word ranks j<=kStar are paid by one named divisor bound.
Constants are chosen before the target N and the retained rank. -/
theorem tau_word_rank_subpower (kStar : ℕ) {eta : ℝ} (heta : 0 < eta) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N j : ℕ), 1 ≤ N → j ≤ kStar →
      (N.divisors.card ^ j : ℕ) ≤ C*(N : ℝ)^eta := by
  let delta := eta / (kStar+1 : ℕ)
  have hdelta : 0 < delta := by dsimp [delta]; positivity
  obtain ⟨D, hD, htau⟩ := fouvryTau_le_const_rpow (k := 2) (by norm_num) hdelta
  let E := max 1 D
  have hE : 1 ≤ E := le_max_left _ _
  have hE0 : 0 < E := zero_lt_one.trans_le hE
  refine ⟨E^kStar, pow_pos hE0 _, ?_⟩
  intro N j hN hj
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := zero_lt_one.trans_le hN1
  have ht : (N.divisors.card : ℝ) ≤ E*(N : ℝ)^delta := by
    have h := htau N (by omega)
    rw [fouvryTau_two] at h
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_right 1 D)
      (Real.rpow_nonneg hN0.le _))
  have hexp : delta*(kStar : ℝ) ≤ eta := by
    have hd : delta*((kStar+1 : ℕ) : ℝ) = eta := by
      dsimp [delta]
      exact div_mul_cancel₀ _ (by positivity)
    have hcast : ((kStar+1 : ℕ) : ℝ) = (kStar : ℝ)+1 := by norm_num
    rw [hcast] at hd
    nlinarith
  calc
    _ = (N.divisors.card : ℝ)^j := by push_cast; rfl
    _ ≤ (E*(N : ℝ)^delta)^j := pow_le_pow_left₀ (Nat.cast_nonneg _) ht _
    _ ≤ (E*(N : ℝ)^delta)^kStar := pow_le_pow_right₀
      (by nlinarith [Real.one_le_rpow hN1 hdelta.le]) hj
    _ = E^kStar * (N : ℝ)^(delta*(kStar : ℝ)) := by
      rw [mul_pow, ← Real.rpow_mul_natCast hN0.le]
    _ ≤ E^kStar * (N : ℝ)^eta := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hN1 hexp) (pow_nonneg hE0.le _)

/-- A direct polynomial-range logarithmic bound for the same active cap.
The range premise is a concrete proof obligation for the literal rho. -/
theorem logBudget_le_of_polynomial_cap {N D : ℕ} {theta : ℝ}
    (hN : 1 ≤ N) (htheta : 0 ≤ theta) (hD : (D : ℝ) ≤ (N : ℝ)^theta) :
    logBudget D ≤ 1+theta*Real.log (N : ℝ) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := zero_lt_one.trans_le hN1
  have hmax : max 1 (D : ℝ) ≤ (N : ℝ)^theta :=
    max_le (Real.one_le_rpow hN1 htheta) hD
  have hl := Real.log_le_log (zero_lt_one.trans_le (le_max_left (1 : ℝ) (D : ℝ))) hmax
  rw [Real.log_rpow hN0] at hl
  exact add_le_add_left hl 1

/-- The reciprocal-totient logarithm is absorbed with an arbitrary small
positive exponent. No asymptotic desired error or modulus l1 mass is assumed. -/
theorem logBudget_polynomial_free_epsilon {theta eta : ℝ}
    (htheta : 0 ≤ theta) (heta : 0 < eta) {N D : ℕ}
    (hN : 1 ≤ N) (hD : (D : ℝ) ≤ (N : ℝ)^theta) :
    logBudget D ≤ (1+theta/eta)*(N : ℝ)^eta := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog := Real.log_le_rpow_div (zero_le_one.trans hN1) heta
  have hone := Real.one_le_rpow hN1 heta.le
  calc
    _ ≤ 1+theta*Real.log (N : ℝ) := logBudget_le_of_polynomial_cap hN htheta hD
    _ ≤ 1+theta*((N : ℝ)^eta/eta) := add_le_add_left
      (mul_le_mul_of_nonneg_left hlog htheta) 1
    _ ≤ _ := by nlinarith

/-- The actual physical signed noncollision kernel has divisor subpower
and logarithmic mean costs. This instantiates the earlier row budget for
Q=the same active primitive rho, rather than an unrelated abstract support. -/
theorem physical_noncollision_budget_polynomial {eta : ℝ} (heta : 0 < eta) :
    ∃ C : ℝ, 0 < C ∧ ∀ (U : ℝ), 0 < U →
      ∀ (theta nu r epsilon : ℝ), 0 ≤ theta →
      ∀ (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ) (N : ℕ), 1 ≤ N →
        (actualActiveUpperCap nu r epsilon retain cap N : ℝ) ≤ (N : ℝ)^theta →
        noncollisionModulusBudget (physicalQ nu r epsilon retain cap N)
          (physicalRho nu r epsilon retain cap N) 1 N (Nat.ceil (U*(N : ℝ))) ≤
          (C*(U+2)^eta)*(N : ℝ)^eta + 4*(1+theta*Real.log (N : ℝ)) := by
  obtain ⟨C, hC, hdiv⟩ := distanceEnvelope_linear_subpower heta
  refine ⟨C, hC, ?_⟩
  intro U hU theta nu r epsilon htheta retain cap N hN hcap
  unfold noncollisionModulusBudget
  rw [one_mul]
  exact add_le_add (hdiv U hU N hN)
    ((physical_meanBudget_le_log nu r epsilon retain cap N).trans
      (mul_le_mul_of_nonneg_left (logBudget_le_of_polynomial_cap hN htheta hcap)
        (by norm_num)))

/-- Direct application to the ORIGINAL displayed same-rho signed row.
The primitive active support is an exact restriction of that row, not a
replacement coefficient. The caller supplies only the actual polynomial
cap and its concrete complete-product range, rather than a desired error. -/
theorem physical_noncollision_signedRow_subpower {eta : ℝ} (heta : 0 < eta) :
    ∃ C : ℝ, 0 < C ∧ ∀ (U : ℝ), 0 < U →
      ∀ (theta nu r epsilon : ℝ), 0 ≤ theta →
      ∀ (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ) (N : ℕ), 1 ≤ N →
        (actualActiveUpperCap nu r epsilon retain cap N : ℝ) ≤ (N : ℝ)^theta →
        ∀ b : ℕ, 1 ≤ b → b ≤ Nat.ceil (U*(N : ℝ)) → b ≠ N →
        ‖signedRow (attachedUpperModuli nu r epsilon retain cap N)
          (physicalRho nu r epsilon retain cap N) N b‖ ≤
          (C*(U+2)^eta)*(N : ℝ)^eta + 4*(1+theta*Real.log (N : ℝ)) := by
  obtain ⟨C, hC, hbudget⟩ := physical_noncollision_budget_polynomial heta
  refine ⟨C, hC, ?_⟩
  intro U hU theta nu r epsilon htheta retain cap N hN hcap b hb hbU hne
  rw [physical_signedRow_eq_active]
  have hrow := norm_signedRow_le (physicalQ nu r epsilon retain cap N)
    (physicalRho nu r epsilon retain cap N) 1 (by norm_num)
    (fun q _ => physicalRho_norm_le_one nu r epsilon retain cap N q) N b
  have hd : ((ImbalancedChen.P5OriginalPrimeEndpoint.distance N b).divisors.card : ℝ) ≤
      (distanceDivisorEnvelope N (Nat.ceil (U*(N : ℝ))) : ℝ) := by
    exact_mod_cast Finset.le_sup (f := fun n =>
      (ImbalancedChen.P5OriginalPrimeEndpoint.distance N n).divisors.card)
      (Finset.mem_Icc.mpr ⟨hb, hbU⟩)
  have hto : rowBudget (physicalQ nu r epsilon retain cap N)
      (physicalRho nu r epsilon retain cap N) 1 N b ≤
      noncollisionModulusBudget (physicalQ nu r epsilon retain cap N)
        (physicalRho nu r epsilon retain cap N) 1 N (Nat.ceil (U*(N : ℝ))) := by
    simp only [rowBudget, if_neg hne, noncollisionModulusBudget, one_mul]
    exact add_le_add_right hd _
  exact (hrow.trans hto).trans (hbudget U hU theta nu r epsilon htheta retain cap N hN hcap)

/-- Product=N collision is bounded by N^(theta+eta), with tau(N)^rank
and the physical active-cardinality cost paid SEPARATELY from distances.
All constants precede the actual policy, cap, target and retained rank. -/
theorem physical_collision_factor_polynomial (kStar : ℕ) {theta eta : ℝ}
    (htheta : 0 ≤ theta) (heta : 0 < eta) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (nu r epsilon : ℝ) (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ)
        (N j : ℕ), 1 ≤ N → j ≤ kStar →
        (actualActiveUpperCap nu r epsilon retain cap N : ℝ) ≤ (N : ℝ)^theta →
        (N.divisors.card ^ j : ℕ) *
          (((physicalQ nu r epsilon retain cap N).card : ℝ) +
            meanBudget (physicalQ nu r epsilon retain cap N)
              (physicalRho nu r epsilon retain cap N)) ≤
          C*(N : ℝ)^(theta+eta) := by
  obtain ⟨D, hD, htau⟩ := tau_word_rank_subpower kStar (show 0 < eta/2 by positivity)
  let B := 1+4*(1+theta/(eta/2))
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨D*B, mul_pos hD hB, ?_⟩
  intro nu r epsilon retain cap N j hN hj hcap
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := zero_lt_one.trans_le hN1
  have hcard : ((physicalQ nu r epsilon retain cap N).card : ℝ) ≤ (N : ℝ)^theta :=
    (Nat.cast_le.mpr (physicalQ_card_le_activeCap nu r epsilon retain cap N)).trans hcap
  have hmean : meanBudget (physicalQ nu r epsilon retain cap N)
      (physicalRho nu r epsilon retain cap N) ≤
        4*(1+theta/(eta/2))*(N : ℝ)^(eta/2) := by
    apply (physical_meanBudget_le_log nu r epsilon retain cap N).trans
    have h := mul_le_mul_of_nonneg_left
      (logBudget_polynomial_free_epsilon htheta (show 0 < eta/2 by positivity) hN hcap)
      (by norm_num : (0 : ℝ) ≤ 4)
    simpa only [mul_assoc] using h
  have hcost : ((physicalQ nu r epsilon retain cap N).card : ℝ) +
      meanBudget (physicalQ nu r epsilon retain cap N)
        (physicalRho nu r epsilon retain cap N) ≤ B*(N : ℝ)^(theta+eta/2) := by
    have hc := Real.rpow_le_rpow_of_exponent_le hN1
      (show theta ≤ theta+eta/2 by linarith)
    have hm := Real.rpow_le_rpow_of_exponent_le hN1
      (show eta/2 ≤ theta+eta/2 by linarith)
    have hfactor : 0 ≤ 4*(1+theta/(eta/2)) := by positivity
    have hp := mul_le_mul_of_nonneg_left hm hfactor
    dsimp [B]
    nlinarith
  calc
    _ ≤ (D*(N : ℝ)^(eta/2)) * (B*(N : ℝ)^(theta+eta/2)) :=
      mul_le_mul (htau N j hN hj) hcost (by dsimp [meanBudget]; positivity) (by positivity)
    _ = (D*B)*(N : ℝ)^(theta+eta) := by
      rw [mul_mul_mul_comm, ← Real.rpow_add hN0]
      congr 1
      congr 1
      ring

/-- Uniform power-small payment for the TRUE product=N collision factor
with any fixed allowed polylog amplitude. N is chosen before the later
physical policy, cap and retained rank; the polynomial active-cap gate
is imposed on that same rho at the chosen N. -/
theorem eventually_physical_polylog_collision_small (kStar : ℕ)
    {theta : ℝ} (htheta : 0 ≤ theta) (hthetaOne : theta < 1)
    (a : ℝ) (ha : 0 ≤ a) (B : ℕ) (tolerance : ℝ) (htolerance : 0 < tolerance) :
    ∀ᶠ N : ℕ in atTop, 2 ≤ N ∧
      ∀ (nu r epsilon : ℝ) (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ)
        (j : ℕ), j ≤ kStar →
        (actualActiveUpperCap nu r epsilon retain cap N : ℝ) ≤ (N : ℝ)^theta →
        (a * Real.log ((N : ℝ)+2)^B) * (N.divisors.card ^ j : ℕ) *
          (((physicalQ nu r epsilon retain cap N).card : ℝ) +
            meanBudget (physicalQ nu r epsilon retain cap N)
              (physicalRho nu r epsilon retain cap N)) ≤
          tolerance * singularNormalization N := by
  let eta := (1-theta)/2
  have heta : 0 < eta := by dsimp [eta]; linarith
  have hgamma : theta+eta < 1 := by dsimp [eta]; linarith
  obtain ⟨C, hC, hcollision⟩ := physical_collision_factor_polynomial kStar htheta heta
  have hbudget := eventually_powerLog_le_singularNormalization
    (a*(2 : ℝ)^B*C) (theta+eta) B hgamma tolerance htolerance
  filter_upwards [hbudget, eventually_ge_atTop (2 : ℕ)] with N hpay hN
  refine ⟨hN, ?_⟩
  intro nu r epsilon retain cap j hj hcap
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hN1
  have hlogPlus : 0 ≤ Real.log ((N : ℝ)+2) := Real.log_nonneg (by linarith)
  have hlogCompare : Real.log ((N : ℝ)+2) ≤ 2*Real.log (N : ℝ) := by
    have hsq : (N : ℝ)+2 ≤ (N : ℝ)^2 := by nlinarith
    have hl := Real.log_le_log (by positivity : (0 : ℝ) < (N : ℝ)+2) hsq
    simpa only [Real.log_pow, Nat.cast_ofNat] using hl
  have hlogPower : Real.log ((N : ℝ)+2)^B ≤ (2 : ℝ)^B * Real.log (N : ℝ)^B := by
    simpa only [mul_pow] using pow_le_pow_left₀ hlogPlus hlogCompare B
  have hfactor := hcollision nu r epsilon retain cap N j (by omega) hj hcap
  have hfactor0 : 0 ≤ (N.divisors.card ^ j : ℕ) *
      (((physicalQ nu r epsilon retain cap N).card : ℝ) +
        meanBudget (physicalQ nu r epsilon retain cap N)
          (physicalRho nu r epsilon retain cap N)) := by
    dsimp [meanBudget]
    positivity
  calc
    _ = (a * Real.log ((N : ℝ)+2)^B) *
        ((N.divisors.card ^ j : ℕ) *
          (((physicalQ nu r epsilon retain cap N).card : ℝ) +
            meanBudget (physicalQ nu r epsilon retain cap N)
              (physicalRho nu r epsilon retain cap N))) := by ring
    _ ≤ (a * ((2 : ℝ)^B * Real.log (N : ℝ)^B)) *
        (C*(N : ℝ)^(theta+eta)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hlogPower ha) hfactor hfactor0
        (by positivity)
    _ = (a*(2 : ℝ)^B*C)*(N : ℝ)^(theta+eta)*Real.log (N : ℝ)^B := by ring
    _ ≤ _ := hpay

/-- Actual Family marked-chart collision, with its normalized Lambda word
and ORIGINAL displayed physical rho, is uniformly negligible once that
same rho has its genuine sublinear polynomial active range. The chosen N
precedes every chart, retained rank, physical policy, source cap and cutoffs. -/
theorem eventually_family_actual_collision_small {kStar : ℕ}
    (F : Family kStar) {theta : ℝ} (htheta : 0 ≤ theta) (hthetaOne : theta < 1)
    (tolerance : ℝ) (htolerance : 0 < tolerance) :
    ∀ᶠ N : ℕ in atTop, 2 ≤ N ∧
      ∀ (nu r epsilon : ℝ) (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ)
        (k : Fin (kStar+1)) (chi eta : ℝ → ℝ),
        (∀ x, 0 ≤ chi x ∧ chi x ≤ 1) → (∀ x, |eta x| ≤ 1) →
        ∀ (sourceCap : ℕ) (kappa0 : ℝ) (js : List ℕ) (bad : Fin k.val),
        (actualActiveUpperCap nu r epsilon retain cap N : ℝ) ≤ (N : ℝ)^theta →
        ‖∑ us ∈ collisionWords (licence F N k) chi eta (N : ℝ) kappa0 sourceCap js bad N,
          lambdaWord us * chartTerm chi eta (bankWeight F N k) (N : ℝ) kappa0 js us *
            signedRow (attachedUpperModuli nu r epsilon retain cap N)
              (physicalRho nu r epsilon retain cap N) N us.prod‖ ≤
          tolerance * singularNormalization N := by
  obtain ⟨C, B, hC, hamp⟩ := all_rank_bank_amplitude F
  have hsmall := eventually_physical_polylog_collision_small kStar htheta hthetaOne
    (C : ℝ) (by positivity) B tolerance htolerance
  filter_upwards [hsmall] with N hN
  refine ⟨hN.1, ?_⟩
  intro nu r epsilon retain cap k chi eta hchi heta sourceCap kappa0 js bad hcap
  simp_rw [physical_signedRow_eq_active]
  let M : ℝ := (C : ℝ)*Real.log ((N : ℝ)+2)^B
  have hM : 0 ≤ M := by
    have hl : 0 ≤ Real.log ((N : ℝ)+2) := Real.log_nonneg (by positivity)
    dsimp [M]
    positivity
  have hsource := family_collision_chart_signed_le F N k chi eta hchi heta sourceCap kappa0
    js bad (physicalQ nu r epsilon retain cap N) (physicalRho nu r epsilon retain cap N)
    1 M (by norm_num) hM (fun q _ => physicalRho_norm_le_one nu r epsilon retain cap N q)
    (hamp N k) N (by omega)
  have hfactor := hN.2 nu r epsilon retain cap k.val (rank_le F k) hcap
  exact hsource.trans (by simpa only [one_mul, M] using hfactor)

end
end ImbalancedChen.P5Z.ProperPowerPhysicalPolynomialPayment
