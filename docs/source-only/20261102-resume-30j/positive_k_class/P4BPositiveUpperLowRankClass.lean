import ImbalancedChen.ActualUpperCountingInputs
import ImbalancedChen.P4ASpliceDifferenceLocalization

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The rank here is the number of ROUGH MODULUS primes in the literal positive
upper coefficient. It is not the rank of an outer switched Gamma word.
The policy, both small Rosser weights and their sign rule stay unchanged.
In particular the full small factor is paid before the below-half support
claim. No ALL16 lower W licence, PP estimate, density or J bound is used.
-/
namespace ImbalancedChen.P4BPositiveUpperLowRankClass
noncomputable section
open scoped Classical BigOperators

/-- The actual rough support cut by its squarefree prime-factor rank. -/
def roughRankSupport (retain : List ℕ → Bool) (N cap : ℕ) (w z : ℝ) (k : ℕ) :
    Finset ℕ :=
  (fixedRoughSupport retain N cap w z).filter (fun b => b.primeFactors.card ≤ k)

/-- This is only a displayed carrier: small coefficients above their level
may vanish. The strict complete support theorem below concerns ACTIVE terms. -/
def rankModuli (retain : List ℕ → Bool) (N cap : ℕ) (w z : ℝ) (k : ℕ) :
    Finset ℕ :=
  smallRoughModuli (actualSmallRosserSupport N cap w)
    (roughRankSupport retain N cap w z k)

def rankRho (retain : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ) (k q : ℕ) : ℝ :=
  if q ∈ rankModuli retain N cap w z k then
    actualSmallRoughRho retain N cap w z L q else 0

def remainingRho (retain : List ℕ → Bool) (N cap : ℕ)
    (w z L : ℝ) (k q : ℕ) : ℝ :=
  if q ∈ rankModuli retain N cap w z k then 0 else
    actualSmallRoughRho retain N cap w z L q

theorem rankModuli_subset (retain : List ℕ → Bool) (N cap : ℕ) (w z : ℝ) (k : ℕ) :
    rankModuli retain N cap w z k ⊆ actualSmallRoughModuli retain N cap w z := by
  intro q hq
  obtain ⟨⟨a,b⟩,hab,hprod⟩ := Finset.mem_image.mp hq
  have hp := Finset.mem_product.mp hab
  exact Finset.mem_image.mpr ⟨(a,b),
    Finset.mem_product.mpr ⟨hp.1,(Finset.mem_filter.mp hp.2).1⟩,hprod⟩

/-- The restriction is EXACTLY the old attachment on the filtered rough
carrier. It does not choose a new beta sign or multiply a lower polynomial. -/
theorem rankRho_eq_filtered_attachment
    (retain : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ) (k q : ℕ) :
    rankRho retain N cap w z L k q =
      smallRoughRho (actualSmallRosserSupport N cap w)
        (roughRankSupport retain N cap w z k)
        (fixedRoughCoefficient retain N cap w z)
        (actualSmallRosserMinus N cap w L) (actualSmallRosserPlus N cap w L) q := by
  by_cases hq : q ∈ rankModuli retain N cap w z k
  · obtain ⟨⟨a,b⟩,hab,hprod⟩ := Finset.mem_image.mp hq
    have hp := Finset.mem_product.mp hab
    have hb := (Finset.mem_filter.mp hp.2).1
    rw [rankRho,if_pos hq,← hprod]
    change smallRoughRho _ _ _ _ _ (a*b) = smallRoughRho _ _ _ _ _ (a*b)
    rw [smallRoughRho_mul
      (fun _ ha => actualSmallRosserSupport_smallPrimeSupportedAt N cap w ha)
      (fun _ hb => fixedRoughSupport_roughPrimeSupportedAt retain N cap w z hb)
      _ _ _ hp.1 hb]
    rw [smallRoughRho_mul
      (fun _ ha => actualSmallRosserSupport_smallPrimeSupportedAt N cap w ha)
      (fun _ hb => fixedRoughSupport_roughPrimeSupportedAt retain N cap w z
        (Finset.mem_filter.mp hb).1) _ _ _ hp.1 hp.2]
  · rw [rankRho,if_neg hq]
    exact (smallRoughRho_eq_zero_of_not_mem _ _ _ _ _ hq).symm

/-- A later causal splice cannot change this branch, even after the
sign-sensitive beta attachment. Agreement is needed only through rank k. -/
theorem rankRho_eq_of_shallow_policy_eq (k : ℕ)
    (retain₁ retain₂ : List ℕ → Bool)
    (hagree : ∀ history,history.length ≤ k → retain₁ history = retain₂ history)
    (N cap : ℕ) (w z L : ℝ) (q : ℕ) :
    rankRho retain₁ N cap w z L k q = rankRho retain₂ N cap w z L k q := by
  have hs : roughRankSupport retain₁ N cap w z k =
      roughRankSupport retain₂ N cap w z k := by
    ext b
    by_cases hk : b.primeFactors.card ≤ k
    · simp only [roughRankSupport,Finset.mem_filter,hk,and_true]
      exact P4ASpliceDifferenceLocalization.shallow_support_mem_iff
        k retain₁ retain₂ hagree N cap w z b hk
    · simp [roughRankSupport,hk]
  rw [rankRho_eq_filtered_attachment,rankRho_eq_filtered_attachment,← hs]
  unfold smallRoughRho
  apply Finset.sum_congr rfl
  intro ab hab
  have hb := (Finset.mem_product.mp (Finset.mem_filter.mp hab).1).2
  have hk := (Finset.mem_filter.mp hb).2
  unfold smallRoughPairCoefficient
  rw [P4ASpliceDifferenceLocalization.shallow_coefficient_eq
    k retain₁ retain₂ hagree N cap w z ab.2 hk]

/-- Concrete original upper source: the actual compact extended-third
coefficient has precisely the initial policy's low-rank attached branch.
The third owner, its W/tent alternative and its later history are NOT
replaced in the complementary high-rank coefficient. -/
theorem actualCompact_rank_two_eq_initial
    (e h : ℝ) (m N cap : ℕ) (w z L : ℝ) (q : ℕ) :
    rankRho (actualExtendedThirdCompactUpperPolicy e h m N false) N cap w z L 2 q =
      rankRho (actualExtendedThirdCompactInitialPolicy e m N false) N cap w z L 2 q := by
  apply rankRho_eq_of_shallow_policy_eq
  intro history hlen
  exact actualExtendedThirdCompactUpperPolicy_through_two e h m N false history hlen

/-- Both pieces sum to the original rho at EVERY modulus. No remainder is
estimated or omitted, and this identity precedes the choice of a test. -/
theorem rho_eq_rank_add_remaining
    (retain : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ) (k q : ℕ) :
    actualSmallRoughRho retain N cap w z L q =
      rankRho retain N cap w z L k q + remainingRho retain N cap w z L k q := by
  by_cases hq : q ∈ rankModuli retain N cap w z k <;>
    simp [rankRho,remainingRho,hq]

theorem rankRho_abs_le_one
    (retain : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ) (k q : ℕ) :
    |rankRho retain N cap w z L k q| ≤ 1 := by
  unfold rankRho
  split
  · exact actualSmallRoughRho_abs_le_one retain N cap w z L q
  · norm_num

/-- Recover the full beta factor and the SAME rough factor from an active
rank part. Uniqueness at the strict small/rough wall proves that the beta
level bound and the rank bound concern a single factorization. -/
theorem rankRho_active_factors
    (retain : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ) (k : ℕ) {q : ℕ}
    (hq : rankRho retain N cap w z L k q ≠ 0) :
    ∃ a ∈ actualSmallRosserSupport N cap w,
      ∃ b ∈ fixedRoughSupport retain N cap w z,
        q = a*b ∧ (a : ℝ) < L ∧ b.primeFactors.card ≤ k := by
  have hmem : q ∈ rankModuli retain N cap w z k := by
    by_contra hnot
    exact hq (by simp [rankRho,hnot])
  have hactive : actualSmallRoughRho retain N cap w z L q ≠ 0 := by
    simpa only [rankRho,if_pos hmem] using hq
  obtain ⟨a,ha,b,hb,hprod,haL,_hc⟩ :=
    actualSmallRoughRho_ne_zero_factors retain N cap w z L hactive
  obtain ⟨⟨a',b'⟩,hab',hprod'⟩ := Finset.mem_image.mp hmem
  have hp' := Finset.mem_product.mp hab'
  have hb' := Finset.mem_filter.mp hp'.2
  have heq : (a,b) = (a',b') := smallRough_factorization_unique
    (actualSmallRosserSupport_smallPrimeSupportedAt N cap w ha)
    (fixedRoughSupport_roughPrimeSupportedAt retain N cap w z hb)
    (actualSmallRosserSupport_smallPrimeSupportedAt N cap w hp'.1)
    (fixedRoughSupport_roughPrimeSupportedAt retain N cap w z hb'.1)
    (hprod.symm.trans hprod'.symm)
  refine ⟨a,ha,b,hb,hprod,haL,?_⟩
  simpa only [congrArg Prod.snd heq] using hb'.2

/-- Every rough factor is paid, including the unit. Squarefreeness is a
theorem of the literal tree, not a premise about an arbitrary modulus. -/
theorem rough_rank_product_le
    (retain : List ℕ → Bool) (N cap : ℕ) (w z : ℝ) (k : ℕ)
    (hz : 1 ≤ z) {b : ℕ} (hb : b ∈ fixedRoughSupport retain N cap w z)
    (hrank : b.primeFactors.card ≤ k) : (b : ℝ) ≤ z^k := by
  have hsq := fixedRoughSupport_squarefree retain N cap w z hb
  calc
    (b : ℝ) = ∏ p ∈ b.primeFactors, (p : ℝ) := by
      rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hsq]
    _ ≤ ∏ _p ∈ b.primeFactors, z := by
      apply Finset.prod_le_prod
      · intro p hp
        exact Nat.cast_nonneg p
      · intro p hp
        exact (mem_roughPrimeUniverse_upper
          (fixedRoughSupport_primeFactors_mem retain N cap w z hb hp)).le
    _ = z^b.primeFactors.card := by rw [Finset.prod_const]
    _ ≤ z^k := pow_le_pow_right₀ hz hrank

/-- Complete active support includes the FULL sign-selected beta level. -/
theorem rankRho_complete_support
    (retain : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ) (k : ℕ)
    (hz : 1 ≤ z) {q : ℕ} (hq : rankRho retain N cap w z L k q ≠ 0) :
    0 < q ∧ Squarefree q ∧ q.Coprime N ∧ (q : ℝ) < L*z^k := by
  obtain ⟨a,ha,b,hb,hprod,haL,hrank⟩ :=
    rankRho_active_factors retain N cap w z L k hq
  have ha0 := Nat.pos_of_ne_zero
    (actualSmallRosserSupport_smallPrimeSupportedAt N cap w ha).1
  have hb0 := Nat.pos_of_ne_zero (fixedRoughSupport_squarefree retain N cap w z hb).ne_zero
  have hqmem : q ∈ actualSmallRoughModuli retain N cap w z := by
    exact Finset.mem_image.mpr ⟨(a,b),Finset.mem_product.mpr ⟨ha,hb⟩,hprod.symm⟩
  refine ⟨by rw [hprod]; exact Nat.mul_pos ha0 hb0,
    actualSmallRoughModuli_squarefree retain N cap w z hqmem,
    actualSmallRoughModuli_coprime_target retain N cap w z hqmem,?_⟩
  have hL : 0 ≤ L := (Nat.cast_nonneg a).trans haL.le
  rw [hprod,Nat.cast_mul]
  exact (mul_lt_mul_of_pos_right haL (by exact_mod_cast hb0)).trans_le
    (mul_le_mul_of_nonneg_left (rough_rank_product_le retain N cap w z k hz hb hrank) hL)

theorem attachment_rank_power {N : ℕ} (hN : 0 < N) (nu r epsilon : ℝ) (k : ℕ) :
    (N : ℝ)^(nu*epsilon)*((N : ℝ)^(nu*r))^k =
      (N : ℝ)^(nu*((k : ℝ)*r+epsilon)) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  rw [← Real.rpow_natCast ((N : ℝ)^(nu*r)) k,← Real.rpow_mul hNp.le,
    ← Real.rpow_add hNp]
  congr 1
  ring

/-- The actual upper normalization has z=N^(nu*r), L=N^(nu*epsilon).
At rough ranks at most two the entire support exponent is nu*(2*r+epsilon).
Neither the outer Gamma rank nor a residual Q/B occurs in this expression. -/
theorem attached_rank_two_support
    (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ)
    {nu r epsilon : ℝ} (hnur : 0 ≤ nu*r) {N : ℕ} (hN : 1 ≤ N)
    {q : ℕ}
    (hq : rankRho (retain N) N (cap N)
      ((N : ℝ)^(nu*epsilon^2)) ((N : ℝ)^(nu*r)) ((N : ℝ)^(nu*epsilon)) 2 q ≠ 0) :
    0 < q ∧ Squarefree q ∧ q.Coprime N ∧ (q : ℝ) < (N : ℝ)^(nu*(2*r+epsilon)) := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := lt_of_lt_of_le zero_lt_one hNr
  obtain ⟨hpos,hsq,hcop,hbound⟩ := rankRho_complete_support (retain N) N (cap N)
    ((N : ℝ)^(nu*epsilon^2)) ((N : ℝ)^(nu*r)) ((N : ℝ)^(nu*epsilon)) 2
    (Real.one_le_rpow hNr hnur) hq
  refine ⟨hpos,hsq,hcop,?_⟩
  have hpower : (N : ℝ)^(nu*epsilon)*((N : ℝ)^(nu*r))^2 =
      (N : ℝ)^(nu*(2*r+epsilon)) := by
    simpa only [Nat.cast_ofNat] using attachment_rank_power (by omega : 0 < N) nu r epsilon 2
  simpa only [hpower] using hbound

/-- The ORIGINAL upper rho=19/96 gives 19/48 before the small attachment.
The full beta margin epsilon<5/48 is retained, uniformly in every policy. -/
theorem original_upper_rank_two_below_half
    (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ)
    {nu epsilon : ℝ} (hnu : 0 ≤ nu) (hnu1 : nu ≤ 1)
    (heps : 0 ≤ epsilon) (hepsGap : epsilon < 5/48)
    {N : ℕ} (hN : 1 < N) {q : ℕ}
    (hq : rankRho (retain N) N (cap N)
      ((N : ℝ)^(nu*epsilon^2)) ((N : ℝ)^(nu*(19/96 : ℝ)))
      ((N : ℝ)^(nu*epsilon)) 2 q ≠ 0) :
    (q : ℝ) < (N : ℝ)^(19/48+epsilon) ∧
      (19/48+epsilon : ℝ) < 1/2 := by
  have h := (attached_rank_two_support retain cap
    (mul_nonneg hnu (by norm_num : (0 : ℝ) ≤ 19/96)) hN.le hq).2.2.2
  refine ⟨h.trans_le (Real.rpow_le_rpow_of_exponent_le
    (by exact_mod_cast hN.le) ?_),by linarith⟩
  have hbase : (0 : ℝ) ≤ 2*(19/96)+epsilon := by linarith
  nlinarith [mul_le_mul_of_nonneg_right hnu1 hbase]

/-- Absolute BV can consume this entire low-rank branch with scalar norm
ONE. This finite estimate has no multiplicity, chart or logarithmic factor;
it assumes no BV, PP or K estimate for the independent test F. -/
theorem rankRho_absolute_test_bound
    (retain : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ) (k : ℕ)
    (hz : 1 ≤ z) (F : ℕ → ℝ) :
    |∑ q ∈ actualSmallRoughModuli retain N cap w z,
      rankRho retain N cap w z L k q * F q| ≤
      ∑ q ∈ (Finset.range (Nat.ceil (L*z^k))).filter
        (fun q => 0 < q ∧ q.Coprime N), |F q| := by
  let S := (actualSmallRoughModuli retain N cap w z).filter
    (fun q => rankRho retain N cap w z L k q ≠ 0)
  have heq : (∑ q ∈ actualSmallRoughModuli retain N cap w z,
      rankRho retain N cap w z L k q * F q) =
      ∑ q ∈ S,rankRho retain N cap w z L k q * F q := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro q hq hnq
    have hzq : rankRho retain N cap w z L k q = 0 := by
      by_contra hne
      exact hnq (Finset.mem_filter.mpr ⟨hq,hne⟩)
    rw [hzq,zero_mul]
  rw [heq]
  calc
    |∑ q ∈ S,rankRho retain N cap w z L k q * F q| ≤
        ∑ q ∈ S,|rankRho retain N cap w z L k q * F q| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ q ∈ S,|F q| := by
      apply Finset.sum_le_sum
      intro q hq
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_right
        (rankRho_abs_le_one retain N cap w z L k q) (abs_nonneg (F q))).trans_eq (one_mul _)
    _ ≤ ∑ q ∈ (Finset.range (Nat.ceil (L*z^k))).filter
        (fun q => 0 < q ∧ q.Coprime N),|F q| := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro q hq
        have h := rankRho_complete_support retain N cap w z L k hz
          (Finset.mem_filter.mp hq).2
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr (Nat.lt_ceil.mpr h.2.2.2),h.1,h.2.2.1⟩
      · intro q hq hnq
        exact abs_nonneg _

/-- The complete signed functional retains the other ranks exactly. -/
theorem signed_test_rank_split
    (retain : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ) (k : ℕ) (F : ℕ → ℝ) :
    (∑ q ∈ actualSmallRoughModuli retain N cap w z,
      actualSmallRoughRho retain N cap w z L q * F q) =
    (∑ q ∈ actualSmallRoughModuli retain N cap w z,rankRho retain N cap w z L k q * F q) +
    (∑ q ∈ actualSmallRoughModuli retain N cap w z,remainingRho retain N cap w z L k q * F q) := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  rw [rho_eq_rank_add_remaining retain N cap w z L k q,add_mul]

end
end ImbalancedChen.P4BPositiveUpperLowRankClass
