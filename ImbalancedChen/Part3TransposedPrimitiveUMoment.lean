import ImbalancedChen.Part3TransposedPrimitiveU

/-!
# Divisor moment payment for the actual transposed U error

The paired coefficient is original alpha and is one-bounded on its actual
interval. Its two coprime masses cost at most 4 U squared. The three-factor
gamma fiber costs tau_3; the coprime counting error adds tau_2 on each side.
The existing tau_6/totient mean therefore pays log exponent 24. The original
beta L2 factor is then paid by its owned fixed-order divisor square moment.

All envelopes below are conclusions derived from the actual data. No error
budget, integral normalization, extra coefficient premise or stronger medium
geometry is supplied by the caller.
-/

namespace ImbalancedChen.Part3

noncomputable section

open Classical Finset
open scoped BigOperators Pointwise
open TransposedZeroCovariance TransposedPrimitiveU
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

namespace TransposedPrimitiveUMoment

theorem card_divisors_mul_le (q r : ℕ) :
    (q * r).divisors.card ≤ q.divisors.card * r.divisors.card := by
  have he : (q * r).divisors = q.divisors * r.divisors := by
    ext k
    simp_rw [Finset.mem_mul, Nat.mem_divisors, Nat.dvd_mul, mul_ne_zero_iff,
      ← exists_and_left, ← exists_and_right]
    simp only [and_assoc, and_comm, and_left_comm]
  rw [he]
  exact Finset.card_mul_le

/-- The three original gamma fibers and the ordinary divisor gate are paid
by an already reachable fixed-order totient moment. -/
theorem sum_gamma_tau_div_totient_le
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) :
    (∑ q ∈ d.physicalFactorModuli,
      ‖d.groupedFactorGamma q‖ * (q.divisors.card : ℝ) / (q.totient : ℝ)) ≤
        (1 + Real.log d.physicalFactorCap) ^ 12 := by
  calc
    _ ≤ ∑ q ∈ d.physicalFactorModuli, (fouvryTau 6 q : ℝ) / q.totient := by
      apply Finset.sum_le_sum
      intro q _
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      calc
        _ ≤ (fouvryTau 3 q : ℝ) * (q.divisors.card : ℝ) :=
          mul_le_mul_of_nonneg_right (d.groupedFactorGamma_norm_le_tauThree hd q)
            (Nat.cast_nonneg _)
        _ ≤ _ := by
          rw [← fouvryTau_two]
          exact_mod_cast fouvryTau_mul_le 3 2 q
    _ ≤ ∑ q ∈ Finset.Ioc 0 (Nat.floor d.physicalFactorCap),
        (fouvryTau 6 q : ℝ) / q.totient :=
      Finset.sum_le_sum_of_subset_of_nonneg (d.physicalFactorModuli_subset_cap hd)
        (fun _ _ _ ↦ by positivity)
    _ ≤ _ := sum_fouvryTau_div_totient_le_real 6 (d.one_le_physicalFactorCap hd)

theorem sum_gamma_norm_le
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) :
    (∑ q ∈ d.physicalFactorModuli, ‖d.groupedFactorGamma q‖) ≤
      d.physicalFactorCap * (1 + Real.log d.physicalFactorCap) ^ 2 := by
  calc
    _ ≤ ∑ q ∈ d.physicalFactorModuli, (fouvryTau 3 q : ℝ) :=
      Finset.sum_le_sum (fun q _ ↦ d.groupedFactorGamma_norm_le_tauThree hd q)
    _ ≤ ∑ q ∈ Finset.Ioc 0 (Nat.floor d.physicalFactorCap), (fouvryTau 3 q : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg (d.physicalFactorModuli_subset_cap hd)
        (fun _ _ _ ↦ Nat.cast_nonneg _)
    _ ≤ _ := sum_fouvryTau_le_real (by norm_num : 1 ≤ (3 : ℕ))
      (d.one_le_physicalFactorCap hd)

theorem actualU_finite_envelope_le
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) :
    (∑ q ∈ d.physicalFactorModuli, ∑ r ∈ d.physicalFactorModuli,
      ‖primitivePairCoefficient d q r‖ * ((q * r).divisors.card : ℝ)) ≤
        4 * d.U ^ 2 * (1 + Real.log d.physicalFactorCap) ^ 24 := by
  have hU : 0 ≤ d.U := by linarith [hd.1]
  let w : ℕ → ℝ := fun q ↦
    ‖d.groupedFactorGamma q‖ * (q.divisors.card : ℝ) / (q.totient : ℝ)
  have hw (q : ℕ) : 0 ≤ w q := by dsimp [w]; positivity
  have hpoint (q r : ℕ) :
      ‖primitivePairCoefficient d q r‖ * ((q * r).divisors.card : ℝ) ≤
        4 * d.U ^ 2 * (w q * w r) := by
    have hc : ‖primitivePairCoefficient d q r‖ ≤
        ‖d.groupedFactorGamma q‖ * ‖d.groupedFactorGamma r‖ *
          (2 * d.U) * (2 * d.U) / ((q.totient : ℝ) * (r.totient : ℝ)) := by
      simp only [primitivePairCoefficient, norm_div, norm_mul, norm_star,
        Complex.norm_natCast]
      apply div_le_div_of_nonneg_right _ (by positivity)
      gcongr
      · exact coprimeMass_norm_le_twice_U hd q
      · exact coprimeMass_norm_le_twice_U hd r
    have hdiv : ((q * r).divisors.card : ℝ) ≤
        (q.divisors.card : ℝ) * (r.divisors.card : ℝ) := by
      exact_mod_cast card_divisors_mul_le q r
    calc
      _ ≤ (‖d.groupedFactorGamma q‖ * ‖d.groupedFactorGamma r‖ *
          (2 * d.U) * (2 * d.U) / ((q.totient : ℝ) * (r.totient : ℝ))) *
            ((q.divisors.card : ℝ) * (r.divisors.card : ℝ)) :=
        mul_le_mul hc hdiv (Nat.cast_nonneg _) (by positivity)
      _ = _ := by
        dsimp [w]
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
  calc
    _ ≤ ∑ q ∈ d.physicalFactorModuli, ∑ r ∈ d.physicalFactorModuli,
        4 * d.U ^ 2 * (w q * w r) :=
      Finset.sum_le_sum (fun q _ ↦ Finset.sum_le_sum (fun r _ ↦ hpoint q r))
    _ = 4 * d.U ^ 2 * (∑ q ∈ d.physicalFactorModuli, w q) ^ 2 := by
      simp only [pow_two, Finset.sum_mul_sum, Finset.mul_sum]
    _ ≤ 4 * d.U ^ 2 * ((1 + Real.log d.physicalFactorCap) ^ 12) ^ 2 :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (Finset.sum_nonneg (fun q _ ↦ hw q))
          (sum_gamma_tau_div_totient_le hd) 2) (by positivity)
    _ = _ := by rw [← pow_mul]; norm_num

/-- U minus P0 has a proved global logarithmic envelope on the full domain. -/
theorem actualU_sub_primitive_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : ℕ) (sigma kappa c0 : ℝ) (d : MediumAtom),
      MediumAdmissible B sigma kappa c0 d →
      ‖(d.transposedAtom.complexDispersionU d.transposedAtom.commonSmoothCarrier
        d.transposedAtom.commonSmoothWeight : ℂ) - primitiveZeroMain d‖ ≤
          C * d.U ^ 2 * (1 + Real.log d.physicalFactorCap) ^ 24 := by
  obtain ⟨C, hC, hbound⟩ := actualU_sub_primitive_finite_bound
  refine ⟨4 * C, by positivity, fun B sigma kappa c0 d hd ↦ ?_⟩
  calc
    _ ≤ C * ∑ q ∈ d.physicalFactorModuli, ∑ r ∈ d.physicalFactorModuli,
        ‖primitivePairCoefficient d q r‖ * ((q * r).divisors.card : ℝ) :=
      hbound B sigma kappa c0 d hd
    _ ≤ C * (4 * d.U ^ 2 * (1 + Real.log d.physicalFactorCap) ^ 24) :=
      mul_le_mul_of_nonneg_left (actualU_finite_envelope_le hd) hC.le
    _ = _ := by ring

/-- The original beta L2 factor is actually paid, with its full log cost. -/
theorem actual_betaL2_mul_U_error_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : ℕ) (sigma kappa c0 : ℝ) (d : MediumAtom),
      MediumAdmissible B sigma kappa c0 d →
      (∑ n ∈ d.betaCarrier, ‖d.beta n‖ ^ 2) *
        ‖(d.transposedAtom.complexDispersionU d.transposedAtom.commonSmoothCarrier
          d.transposedAtom.commonSmoothWeight : ℂ) - primitiveZeroMain d‖ ≤
            C * d.V * d.U ^ 2 *
              (1 + Real.log (2 * d.V)) ^ ((2 ^ B) ^ 2 - 1) *
                (1 + Real.log d.physicalFactorCap) ^ 24 := by
  obtain ⟨C, hC, hbound⟩ := actualU_sub_primitive_bound
  refine ⟨2 * C, by positivity, fun B sigma kappa c0 d hd ↦ ?_⟩
  have hlogV : 0 ≤ 1 + Real.log (2 * d.V) := by
    have := Real.log_nonneg (show 1 ≤ 2 * d.V by linarith [hd.2.1])
    linarith
  calc
    _ ≤ (2 * d.V * (1 + Real.log (2 * d.V)) ^ ((2 ^ B) ^ 2 - 1)) *
        (C * d.U ^ 2 * (1 + Real.log d.physicalFactorCap) ^ 24) :=
      mul_le_mul (mediumAdmissible_beta_norm_sq_sum_le hd)
        (hbound B sigma kappa c0 d hd) (norm_nonneg _)
          (by have := hd.2.1; positivity)
    _ = _ := by ring

/-- The existing medium monomial, with Q2,Q3 at least one, already bounds
the original U squared. This is derived, not a stronger caller gate. -/
theorem U_sq_lt_scale_rpow
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) :
    d.U ^ 2 < d.scale ^ (1 - 8 * sigma) := by
  obtain ⟨hU, _, _, hQ2, hQ3, _, _, _, _, hgeom, _⟩ := hd
  have hQ3sq : 1 ≤ d.Q3 ^ 2 := by nlinarith
  calc
    _ = d.U ^ 2 * 1 * 1 := by ring
    _ ≤ d.U ^ 2 * d.Q2 * d.Q3 ^ 2 := by gcongr
    _ < _ := hgeom

end TransposedPrimitiveUMoment

end

end ImbalancedChen.Part3
