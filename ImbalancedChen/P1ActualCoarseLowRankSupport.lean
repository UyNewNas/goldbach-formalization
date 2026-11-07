import ImbalancedChen.P1ActualCoarseFixedCoefficient

/-!
# Exact low-rank atoms of the original coarse coefficient

The support is the actual fixed support of `HistoricalThirdCoarse.policy`.
Prime-product uniqueness and the actual decreasing carrier recover the
selected singleton or ordered pair from any retained representation.
Conversely, their actual valid selections construct retained leaves.
Only the original firstStop and initial first cube occur at ranks 1/2.
-/

namespace ImbalancedChen.P1ActualCoarseLowRankSupport

noncomputable section

open scoped Classical
open HistoricalThirdCoarse
open P1ActualCoarseFixedCoefficient
open MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser

private theorem ordered_sublist_of_mem (N cap : ℕ) (w z : ℝ)
    (chosen : List ℕ) (hsort : chosen.Pairwise (· > ·))
    (hmem : ∀ r ∈ chosen, r ∈ roughPrimeUniverse N cap w z) :
    chosen <+ roughPrimeUniverse N cap w z := by
  exact List.sublist_of_subperm_of_pairwise
    (List.subperm_of_subset hsort.nodup hmem) hsort
    (roughPrimeUniverse_pairwise_gt N cap w z)

/-- Product equality recovers a literal ordered prime list inside the
actual carrier, with no extra low-rank or history assumption. -/
private theorem chosen_eq_ordered_prime_list
    (N cap : ℕ) (w z : ℝ) (chosen target : List ℕ)
    (hsub : chosen <+ roughPrimeUniverse N cap w z)
    (htarget : target.Pairwise (· > ·))
    (hprime : ∀ r ∈ target, r.Prime) (hprod : chosen.prod = target.prod) :
    chosen = target := by
  have hcprime : ∀ r ∈ chosen, r.Prime :=
    fun _ hr => mem_roughPrimeUniverse_prime (hsub.subset hr)
  have hperm := (Nat.primeFactorsList_unique hprod hcprime).trans
    (Nat.primeFactorsList_unique (rfl : target.prod = target.prod) hprime).symm
  exact List.Perm.eq_of_pairwise
    (fun _ _ _ _ hab hba => Nat.le_antisymm hba hab)
    (((roughPrimeUniverse_pairwise_gt N cap w z).sublist hsub).imp fun h => h.le)
    (htarget.imp fun h => h.le) hperm

theorem singleton_policy_iff_original_first_tests
    (e chi : ℝ) (m : ℕ) (omega : ℝ) (N p : ℕ) (hp : p.Prime) :
    policy e chi m omega (N : ℝ) false [p] = true ↔
      firstStop e m (N : ℝ) [p] ∧ (p : ℝ) ^ 3 < (N : ℝ) ^ initial e := by
  constructor
  · intro hpass
    exact (P1OriginalFirstStopInheritance.singleton_original_tests
      e chi m omega (N : ℝ) p hpass).2
  · rintro ⟨hstop, hcube⟩
    have hsq : (1 : ℝ) ≤ (p : ℝ) ^ 2 := by
      have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
      nlinarith
    have hple : (p : ℝ) ≤ (p : ℝ) ^ 3 := by
      have hm := mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg (α := ℝ) p)
      simpa only [mul_one, pow_succ, mul_comm] using hm
    have hadm : ordinaryRosserPrefixAdmissible false ((N : ℝ) ^ initial e) [p] := by
      refine ⟨?_, ?_⟩
      · simpa using hple.trans_lt hcube
      · change UpperAdmissibleSet ((N : ℝ) ^ initial e) [p].toFinset
        simpa [UpperAdmissibleSet, Finset.filter_singleton, pow_succ, mul_comm] using hcube
    rw [policy_through_two e chi m omega (N : ℝ) false [p] (by simp)]
    simpa [initialPolicy, oddFirstExitPolicy] using And.intro hadm hstop

theorem valid_singleton_iff_original_first_tests
    (e chi : ℝ) (m : ℕ) (omega : ℝ) (N p : ℕ) (hp : p.Prime) :
    FirstExitValidSelection (policy e chi m omega (N : ℝ)) [] true [p] ↔
      firstStop e m (N : ℝ) [p] ∧ (p : ℝ) ^ 3 < (N : ℝ) ^ initial e := by
  simpa only [FirstExitValidSelection, Bool.not_true, and_true] using
    singleton_policy_iff_original_first_tests e chi m omega N p hp

/-- The rank-two test is the actual inactive even policy. -/
theorem valid_pair_iff_original_first_tests
    (e chi : ℝ) (m : ℕ) (omega : ℝ) (N p q : ℕ) (hp : p.Prime) :
    FirstExitValidSelection (policy e chi m omega (N : ℝ)) [] true [p, q] ↔
      firstStop e m (N : ℝ) [p] ∧ (p : ℝ) ^ 3 < (N : ℝ) ^ initial e := by
  simpa [FirstExitValidSelection, policy_even] using
    singleton_policy_iff_original_first_tests e chi m omega N p hp

theorem unit_mem_support (e chi : ℝ) (m : ℕ) (omega : ℝ)
    (N cap : ℕ) (w z : ℝ) : 1 ∈ roughSupport e chi m omega N cap w z := by
  exact one_mem_oddFirstExitRetainedModuli
    (policy e chi m omega (N : ℝ) false) (fun _ => 1) (roughPrimeUniverse N cap w z)

theorem unit_coefficient (e chi : ℝ) (m : ℕ) (omega : ℝ)
    (N cap : ℕ) (w z : ℝ) : roughCoefficient e chi m omega N cap w z 1 = 1 := by
  exact coefficient_one e chi m omega N cap w z

/-- Both directions use the actual retained selections of the same tree. -/
theorem prime_mem_support_iff
    (e chi : ℝ) (m : ℕ) (omega : ℝ) (N cap : ℕ) (w z : ℝ)
    (p : ℕ) (hp : p.Prime) :
    p ∈ roughSupport e chi m omega N cap w z ↔
      p ∈ roughPrimeUniverse N cap w z ∧
      firstStop e m (N : ℝ) [p] ∧ (p : ℝ) ^ 3 < (N : ℝ) ^ initial e := by
  rw [support_eq_original_retainedModuli, mem_firstExitRetainedModuli_iff_validSelection]
  constructor
  · rintro ⟨chosen, hsub, hvalid, hprod⟩
    have heq : chosen = [p] := chosen_eq_ordered_prime_list
      N cap w z chosen [p] hsub (by simp) (by simpa using hp) (by simpa using hprod)
    subst chosen
    exact ⟨hsub.subset (by simp),
      (valid_singleton_iff_original_first_tests e chi m omega N p hp).1 hvalid⟩
  · rintro ⟨hpcarrier, hstop, hcube⟩
    refine ⟨[p], ordered_sublist_of_mem N cap w z [p] (by simp) ?_,
      (valid_singleton_iff_original_first_tests e chi m omega N p hp).2
        ⟨hstop, hcube⟩, by simp⟩
    simpa using hpcarrier

theorem prime_mem_support_iff_arithmetic
    (e chi : ℝ) (m : ℕ) (omega : ℝ) (N cap : ℕ) (w z : ℝ)
    (p : ℕ) (hp : p.Prime) :
    p ∈ roughSupport e chi m omega N cap w z ↔
      p < cap ∧ ¬p ∣ N ∧ w ≤ (p : ℝ) ∧ (p : ℝ) < z ∧
      firstStop e m (N : ℝ) [p] ∧ (p : ℝ) ^ 3 < (N : ℝ) ^ initial e := by
  rw [prime_mem_support_iff e chi m omega N cap w z p hp]
  simp only [mem_roughPrimeUniverse, hp, true_and, and_assoc]

/-- `p` is the larger, first processed prime. No selected-third condition
or new-level test occurs in this exact rank-two support formula. -/
theorem ordered_pair_mem_support_iff
    (e chi : ℝ) (m : ℕ) (omega : ℝ) (N cap : ℕ) (w z : ℝ)
    (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hqp : q < p) :
    p * q ∈ roughSupport e chi m omega N cap w z ↔
      p ∈ roughPrimeUniverse N cap w z ∧ q ∈ roughPrimeUniverse N cap w z ∧
      firstStop e m (N : ℝ) [p] ∧ (p : ℝ) ^ 3 < (N : ℝ) ^ initial e := by
  have hsort : [p, q].Pairwise (· > ·) := List.pairwise_pair.mpr hqp
  have hprime : ∀ r ∈ [p, q], r.Prime := by
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact hp
    · have hrq : r = q := List.mem_singleton.mp hr
      simpa only [hrq] using hq
  rw [support_eq_original_retainedModuli, mem_firstExitRetainedModuli_iff_validSelection]
  constructor
  · rintro ⟨chosen, hsub, hvalid, hprod⟩
    have heq : chosen = [p, q] := chosen_eq_ordered_prime_list
      N cap w z chosen [p, q] hsub hsort hprime (by simpa using hprod)
    subst chosen
    exact ⟨hsub.subset (by simp), hsub.subset (by simp),
      (valid_pair_iff_original_first_tests e chi m omega N p q hp).1 hvalid⟩
  · rintro ⟨hpcarrier, hqcarrier, hstop, hcube⟩
    have hmem : ∀ r ∈ [p, q], r ∈ roughPrimeUniverse N cap w z := by
      intro r hr
      rcases List.mem_cons.mp hr with rfl | hr
      · exact hpcarrier
      · have hrq : r = q := List.mem_singleton.mp hr
        simpa only [hrq] using hqcarrier
    exact ⟨[p, q], ordered_sublist_of_mem N cap w z [p, q] hsort hmem,
      (valid_pair_iff_original_first_tests e chi m omega N p q hp).2 ⟨hstop, hcube⟩,
      by simp⟩

private theorem coefficient_eq_mu_on_support
    (e chi : ℝ) (m : ℕ) (omega : ℝ) (N cap : ℕ) (w z : ℝ) (d : ℕ)
    (hd : d ∈ roughSupport e chi m omega N cap w z) :
    roughCoefficient e chi m omega N cap w z d = (ArithmeticFunction.moebius d : ℝ) := by
  change ((if d ∈ roughSupport e chi m omega N cap w z then
    ArithmeticFunction.moebius d else 0 : ℤ) : ℝ) = _
  rw [if_pos hd]

private theorem coefficient_eq_zero_off_support
    (e chi : ℝ) (m : ℕ) (omega : ℝ) (N cap : ℕ) (w z : ℝ) (d : ℕ)
    (hd : d ∉ roughSupport e chi m omega N cap w z) :
    roughCoefficient e chi m omega N cap w z d = 0 := by
  change ((if d ∈ roughSupport e chi m omega N cap w z then
    ArithmeticFunction.moebius d else 0 : ℤ) : ℝ) = 0
  rw [if_neg hd]
  norm_num

theorem prime_coefficient_formula
    (e chi : ℝ) (m : ℕ) (omega : ℝ) (N cap : ℕ) (w z : ℝ)
    (p : ℕ) (hp : p.Prime) :
    roughCoefficient e chi m omega N cap w z p =
      if p ∈ roughPrimeUniverse N cap w z ∧ firstStop e m (N : ℝ) [p] ∧
        (p : ℝ) ^ 3 < (N : ℝ) ^ initial e then -1 else 0 := by
  have hmu : ArithmeticFunction.moebius p = (-1 : ℤ) := by
    have h := moebius_list_prod_eq_negOnePow_length [p] (by simp) (by simpa using hp)
    simpa using h
  by_cases hcond : p ∈ roughPrimeUniverse N cap w z ∧ firstStop e m (N : ℝ) [p] ∧
      (p : ℝ) ^ 3 < (N : ℝ) ^ initial e
  · rw [if_pos hcond, coefficient_eq_mu_on_support e chi m omega N cap w z p
      ((prime_mem_support_iff e chi m omega N cap w z p hp).2 hcond), hmu]
    norm_num
  · rw [if_neg hcond]
    apply coefficient_eq_zero_off_support
    exact fun hd => hcond ((prime_mem_support_iff e chi m omega N cap w z p hp).1 hd)

theorem ordered_pair_coefficient_formula
    (e chi : ℝ) (m : ℕ) (omega : ℝ) (N cap : ℕ) (w z : ℝ)
    (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hqp : q < p) :
    roughCoefficient e chi m omega N cap w z (p * q) =
      if p ∈ roughPrimeUniverse N cap w z ∧ q ∈ roughPrimeUniverse N cap w z ∧
        firstStop e m (N : ℝ) [p] ∧ (p : ℝ) ^ 3 < (N : ℝ) ^ initial e then 1 else 0 := by
  have hprime : ∀ r ∈ [p, q], r.Prime := by
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact hp
    · have hrq : r = q := List.mem_singleton.mp hr
      simpa only [hrq] using hq
  have hmu : ArithmeticFunction.moebius (p * q) = (1 : ℤ) := by
    have h := moebius_list_prod_eq_negOnePow_length [p, q] (by simp [hqp.ne']) hprime
    simpa using h
  by_cases hcond : p ∈ roughPrimeUniverse N cap w z ∧ q ∈ roughPrimeUniverse N cap w z ∧
      firstStop e m (N : ℝ) [p] ∧ (p : ℝ) ^ 3 < (N : ℝ) ^ initial e
  · rw [if_pos hcond, coefficient_eq_mu_on_support e chi m omega N cap w z (p * q)
      ((ordered_pair_mem_support_iff e chi m omega N cap w z p q hp hq hqp).2 hcond), hmu]
    norm_num
  · rw [if_neg hcond]
    apply coefficient_eq_zero_off_support
    exact fun hd => hcond
      ((ordered_pair_mem_support_iff e chi m omega N cap w z p q hp hq hqp).1 hd)

/-- The parameters controlling the selected third rule have no effect on
these concrete atoms, once all original first-test inputs are fixed. -/
theorem prime_coefficient_independent_third_parameters
    (e chi₁ chi₂ : ℝ) (m : ℕ) (omega₁ omega₂ : ℝ)
    (N cap : ℕ) (w z : ℝ) (p : ℕ) (hp : p.Prime) :
    roughCoefficient e chi₁ m omega₁ N cap w z p =
      roughCoefficient e chi₂ m omega₂ N cap w z p := by
  rw [prime_coefficient_formula e chi₁ m omega₁ N cap w z p hp,
    prime_coefficient_formula e chi₂ m omega₂ N cap w z p hp]

theorem ordered_pair_coefficient_independent_third_parameters
    (e chi₁ chi₂ : ℝ) (m : ℕ) (omega₁ omega₂ : ℝ)
    (N cap : ℕ) (w z : ℝ) (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hqp : q < p) :
    roughCoefficient e chi₁ m omega₁ N cap w z (p * q) =
      roughCoefficient e chi₂ m omega₂ N cap w z (p * q) := by
  rw [ordered_pair_coefficient_formula e chi₁ m omega₁ N cap w z p q hp hq hqp,
    ordered_pair_coefficient_formula e chi₂ m omega₂ N cap w z p q hp hq hqp]

end

end ImbalancedChen.P1ActualCoarseLowRankSupport
