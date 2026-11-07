import ImbalancedChen.Part3SharedFirstFactorDispersion
import ImbalancedChen.Part3TransposedPrimitiveVPayment

/-!
# Primitive U/V payment for the actual common first factor

Both primitive centers are taken in the literal point-mass slice. The
finite coefficient bridge removes its inactive labels before taking the
physical divisor moments. U retains its reciprocal-square first-factor
weight. V has one totient denominator and is paid by the original medium
geometry after the exact beta and gamma1 outside moments.
-/

namespace ImbalancedChen.Part3

noncomputable section

open Classical Finset Filter Topology
open scoped BigOperators Pointwise
open TransposedZeroCovariance TransposedPrimitiveU TransposedPrimitiveV
open TransposedPrimitiveUMoment TransposedPrimitiveVMoment
open TransposedPrimitiveUPayment
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- The actual primitive-center remainder in the shared-first-factor identity. -/
def MediumAtom.sharedPrimitiveUVError (d : MediumAtom) : ℂ :=
  ∑ p ∈ d.primitiveFirstFactorCarrier,
    ((((d.q1SliceAtom p).transposedAtom.complexDispersionU
        d.transposedAtom.commonSmoothCarrier d.transposedAtom.commonSmoothWeight : ℂ) -
      primitiveZeroMain (d.q1SliceAtom p)) -
      2 * (((d.q1SliceAtom p).transposedAtom.complexDispersionV
        d.transposedAtom.commonSmoothCarrier d.transposedAtom.commonSmoothWeight : ℂ) -
          primitiveZeroMain (d.q1SliceAtom p)))

namespace SharedFirstFactorPrimitiveUVPayment

private def uError (d : MediumAtom) (p : ℕ) : ℂ :=
  ((d.q1SliceAtom p).transposedAtom.complexDispersionU
    d.transposedAtom.commonSmoothCarrier d.transposedAtom.commonSmoothWeight : ℂ) -
      primitiveZeroMain (d.q1SliceAtom p)

private def vError (d : MediumAtom) (p : ℕ) : ℂ :=
  ((d.q1SliceAtom p).transposedAtom.complexDispersionV
    d.transposedAtom.commonSmoothCarrier d.transposedAtom.commonSmoothWeight : ℂ) -
      primitiveZeroMain (d.q1SliceAtom p)

private def divisorTau (n : ℕ) : ℝ := (n.divisors.card : ℝ)

private theorem divisorTau_nonneg (n : ℕ) : 0 ≤ divisorTau n := by
  exact Nat.cast_nonneg _

private theorem divisorTau_mul_le (a b : ℕ) :
    divisorTau (a * b) ≤ divisorTau a * divisorTau b := by
  unfold divisorTau
  exact_mod_cast card_divisors_mul_le a b

private theorem divisorTau_pow_le (r : ℕ) {n : ℕ} (hn : n ≠ 0) :
    divisorTau n ^ r ≤ (fouvryTau (2 ^ r) n : ℝ) := by
  unfold divisorTau
  have h := fouvryTau_pow_le 2 r hn
  rw [fouvryTau_two] at h
  exact_mod_cast h

private theorem factor_bounds {Q : ℝ} (hQ : 1 ≤ Q) {n : ℕ}
    (hn : n ∈ factorCarrier Q) :
    0 < n ∧ Q ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * Q := by
  obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hn
  have hlower : Q ≤ (n : ℝ) :=
    (Nat.le_ceil Q).trans (by exact_mod_cast hlo)
  have hpos : (0 : ℝ) < n := (zero_lt_one.trans_le hQ).trans_le hlower
  refine ⟨by exact_mod_cast hpos, hlower, ?_⟩
  exact (show (n : ℝ) ≤ (Nat.floor (2 * Q) : ℝ) by exact_mod_cast hhi).trans
    (Nat.floor_le (by linarith : 0 ≤ 2 * Q))

private theorem factor_subset_Ioc {Q : ℝ} (hQ : 1 ≤ Q) :
    factorCarrier Q ⊆ Finset.Ioc 0 (Nat.floor (2 * Q)) := by
  intro n hn
  exact Finset.mem_Ioc.mpr ⟨(factor_bounds hQ hn).1, (Finset.mem_Icc.mp hn).2⟩

private theorem dyadic_divisor_harmonic {Q : ℝ} (hQ : 1 ≤ Q) (r : ℕ) :
    (∑ n ∈ factorCarrier Q, divisorTau n ^ r / (n : ℝ)) ≤
      (1 + Real.log (2 * Q)) ^ (2 ^ r) := by
  calc
    _ ≤ ∑ n ∈ factorCarrier Q, (fouvryTau (2 ^ r) n : ℝ) / (n : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      exact div_le_div_of_nonneg_right
        (divisorTau_pow_le r (factor_bounds hQ hn).1.ne') (Nat.cast_nonneg _)
    _ ≤ ∑ n ∈ Finset.Ioc 0 (Nat.floor (2 * Q)),
        (fouvryTau (2 ^ r) n : ℝ) / (n : ℝ) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (factor_subset_Ioc hQ)
        (fun n _ _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    _ ≤ _ := sum_fouvryTau_div_le_real _ (by linarith : 1 ≤ 2 * Q)

private theorem primitive_p_reciprocal_square (d : MediumAtom)
    (hQ : 1 ≤ d.Q1) (r : ℕ) :
    (∑ p ∈ d.primitiveFirstFactorCarrier, divisorTau p ^ r / (p : ℝ) ^ 2) ≤
      (1 + Real.log (2 * d.Q1)) ^ (2 ^ r) / d.Q1 := by
  have hQpos : 0 < d.Q1 := zero_lt_one.trans_le hQ
  calc
    _ ≤ ∑ p ∈ d.primitiveFirstFactorCarrier, (divisorTau p ^ r / (p : ℝ)) / d.Q1 := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨hp0, hQp, _⟩ := factor_bounds hQ (Finset.mem_filter.mp hp).1
      have hpR : (0 : ℝ) < p := by exact_mod_cast hp0
      have hi : 1 / (p : ℝ) ≤ 1 / d.Q1 := one_div_le_one_div_of_le hQpos hQp
      calc
        _ = (divisorTau p ^ r / (p : ℝ)) * (1 / (p : ℝ)) := by ring
        _ ≤ (divisorTau p ^ r / (p : ℝ)) * (1 / d.Q1) :=
          mul_le_mul_of_nonneg_left hi (div_nonneg
            (pow_nonneg (divisorTau_nonneg _) _) hpR.le)
        _ = _ := by ring
    _ = (∑ p ∈ d.primitiveFirstFactorCarrier, divisorTau p ^ r / (p : ℝ)) / d.Q1 := by
      rw [Finset.sum_div]
    _ ≤ (∑ p ∈ factorCarrier d.Q1, divisorTau p ^ r / (p : ℝ)) / d.Q1 := by
      apply div_le_div_of_nonneg_right _ hQpos.le
      have hsubset : d.primitiveFirstFactorCarrier ⊆ factorCarrier d.Q1 := by
        intro p hp
        exact (Finset.mem_filter.mp hp).1
      exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun p _ _ => div_nonneg (pow_nonneg (divisorTau_nonneg _) _) (Nat.cast_nonneg _))
    _ ≤ _ := div_le_div_of_nonneg_right (dyadic_divisor_harmonic hQ r) hQpos.le

private theorem card_factorCarrier_le {Q : ℝ} (hQ : 1 ≤ Q) :
    ((factorCarrier Q).card : ℝ) ≤ 2 * Q := by
  have hcard := Finset.card_le_card (factor_subset_Ioc hQ)
  simp only [Nat.card_Ioc, Nat.sub_zero] at hcard
  exact (show ((factorCarrier Q).card : ℝ) ≤ (Nat.floor (2 * Q) : ℝ) by
    exact_mod_cast hcard).trans (Nat.floor_le (by linarith))

private theorem cap_log_bounds
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) :
    1 ≤ 1 + Real.log d.physicalFactorCap ∧
      1 + Real.log (2 * d.Q1) ≤ 1 + Real.log d.physicalFactorCap ∧
      1 + Real.log (2 * d.Q2) ≤ 1 + Real.log d.physicalFactorCap ∧
      1 + Real.log (2 * d.Q3) ≤ 1 + Real.log d.physicalFactorCap := by
  have hcap := d.one_le_physicalFactorCap hd
  obtain ⟨_, _, hQ1, hQ2, hQ3, _⟩ := hd
  have h1 : 2 * d.Q1 ≤ d.physicalFactorCap := by
    unfold MediumAtom.physicalFactorCap
    calc
      _ ≤ 8 * d.Q1 := by linarith
      _ = 8 * d.Q1 * 1 * 1 := by ring
      _ ≤ _ := by gcongr
  have h2 : 2 * d.Q2 ≤ d.physicalFactorCap := by
    unfold MediumAtom.physicalFactorCap
    calc
      _ ≤ 8 * d.Q2 := by linarith
      _ = 8 * 1 * d.Q2 * 1 := by ring
      _ ≤ _ := by gcongr
  have h3 : 2 * d.Q3 ≤ d.physicalFactorCap := by
    unfold MediumAtom.physicalFactorCap
    calc
      _ ≤ 8 * d.Q3 := by linarith
      _ = 8 * 1 * 1 * d.Q3 := by ring
      _ ≤ _ := by gcongr
  exact ⟨by linarith [Real.log_nonneg hcap],
    add_le_add (le_refl 1) (Real.log_le_log (by linarith) h1),
    add_le_add (le_refl 1) (Real.log_le_log (by linarith) h2),
    add_le_add (le_refl 1) (Real.log_le_log (by linarith) h3)⟩

/-- The full physical image is unchanged; zero slice coefficients are removed
by a finite fiber inequality, not by redefining that image. -/
private theorem weighted_slice_gamma_le (d : MediumAtom) {p : ℕ}
    (hp : p ∈ factorCarrier d.Q1) (f : ℕ → ℝ) (hf : ∀ q, 0 ≤ f q) :
    (∑ q ∈ (d.q1SliceAtom p).physicalFactorModuli,
      ‖(d.q1SliceAtom p).groupedFactorGamma q‖ * f q) ≤
        ∑ a ∈ factorCarrier d.Q2, ∑ b ∈ factorCarrier d.Q3,
          ‖d.gamma2 a * d.gamma3 b‖ * f (p * a * b) := by
  let e := d.q1SliceAtom p
  have hreindex := Finset.sum_fiberwise_of_maps_to
    (s := e.complexFactorLabels) (t := e.physicalFactorModuli)
    (g := complexFactorModulus) (fun r hr ↦ Finset.mem_image_of_mem _ hr)
    (fun r ↦ ‖e.complexFactorGamma r‖ * f (complexFactorModulus r))
  calc
    _ ≤ ∑ q ∈ e.physicalFactorModuli, ∑ r ∈ e.physicalFactorFiber q,
        ‖e.complexFactorGamma r‖ * f q := by
      apply Finset.sum_le_sum
      intro q _
      calc
        _ ≤ (∑ r ∈ e.physicalFactorFiber q, ‖e.complexFactorGamma r‖) * f q :=
          mul_le_mul_of_nonneg_right (norm_sum_le _ _) (hf q)
        _ = _ := Finset.sum_mul _ _ _
    _ = ∑ r ∈ e.complexFactorLabels,
        ‖e.complexFactorGamma r‖ * f (complexFactorModulus r) := by
      rw [← hreindex]
      apply Finset.sum_congr rfl
      intro q _
      apply Finset.sum_congr rfl
      intro r hr
      rw [(Finset.mem_filter.mp hr).2]
    _ = _ := by
      simp only [e, MediumAtom.q1SliceAtom, MediumAtom.complexFactorLabels,
        Finset.sum_product]
      change (∑ q ∈ factorCarrier d.Q1, ∑ a ∈ factorCarrier d.Q2,
        ∑ b ∈ factorCarrier d.Q3,
          ‖(if q = p then (1 : ℂ) else 0) * d.gamma2 a * d.gamma3 b‖ *
            f (q * a * b)) = _
      rw [Finset.sum_eq_single p]
      · simp only [ite_true, one_mul]
      · intro q _ hqp
        simp only [if_neg hqp, zero_mul, norm_zero, Finset.sum_const_zero]
      · intro hnot
        exact (hnot hp).elim

private theorem tail_gamma_norm_le_one
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) {a b : ℕ}
    (ha : a ∈ factorCarrier d.Q2) (hb : b ∈ factorCarrier d.Q3) :
    ‖d.gamma2 a * d.gamma3 b‖ ≤ 1 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h2, h3⟩ := hd
  rw [norm_mul]
  simpa only [one_mul] using
    mul_le_mul (h2 a ha).1 (h3 b hb).1 (norm_nonneg _) zero_le_one

private theorem tau_div_totient_le {n : ℕ} (hn : 0 < n) :
    divisorTau n / (n.totient : ℝ) ≤ divisorTau n ^ 2 / (n : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hphi : (0 : ℝ) < n.totient := by exact_mod_cast Nat.totient_pos.mpr hn
  have ht : (n : ℝ) ≤ (n.totient : ℝ) * divisorTau n := by
    have h := le_totient_mul_fouvryTau_two n
    rw [fouvryTau_two] at h
    unfold divisorTau
    exact_mod_cast h
  apply (div_le_div_iff₀ hphi hnR).mpr
  have h := mul_le_mul_of_nonneg_left ht (divisorTau_nonneg n)
  simpa only [pow_two, mul_assoc, mul_comm, mul_left_comm] using h

private theorem tau_totient_three_factor {p a b : ℕ}
    (hp : 0 < p) (ha : 0 < a) (hb : 0 < b) :
    divisorTau (p * a * b) / ((p * a * b).totient : ℝ) ≤
      (divisorTau p ^ 2 / (p : ℝ)) *
        (divisorTau a ^ 2 / (a : ℝ)) * (divisorTau b ^ 2 / (b : ℝ)) := by
  have hmul : divisorTau (p * a * b) ≤ divisorTau p * divisorTau a * divisorTau b :=
    (divisorTau_mul_le (p * a) b).trans
      (mul_le_mul_of_nonneg_right (divisorTau_mul_le p a) (divisorTau_nonneg b))
  calc
    _ ≤ divisorTau (p * a * b) ^ 2 / ((p * a * b : ℕ) : ℝ) :=
      tau_div_totient_le (Nat.mul_pos (Nat.mul_pos hp ha) hb)
    _ ≤ (divisorTau p * divisorTau a * divisorTau b) ^ 2 /
        ((p * a * b : ℕ) : ℝ) :=
      div_le_div_of_nonneg_right
        (pow_le_pow_left₀ (divisorTau_nonneg _) hmul 2) (Nat.cast_nonneg _)
    _ = _ := by
      simp only [Nat.cast_mul, mul_pow, div_eq_mul_inv, mul_inv_rev]
      ring

private theorem slice_gamma_norm_sum_le
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) {p : ℕ}
    (hp : p ∈ d.primitiveFirstFactorCarrier) :
    (∑ q ∈ (d.q1SliceAtom p).physicalFactorModuli,
      ‖(d.q1SliceAtom p).groupedFactorGamma q‖) ≤ 4 * d.Q2 * d.Q3 := by
  calc
    _ ≤ ∑ a ∈ factorCarrier d.Q2, ∑ b ∈ factorCarrier d.Q3,
        ‖d.gamma2 a * d.gamma3 b‖ := by
      simpa only [mul_one] using
        weighted_slice_gamma_le d (Finset.mem_filter.mp hp).1 (fun _ ↦ 1)
          (fun _ ↦ zero_le_one)
    _ ≤ ∑ _a ∈ factorCarrier d.Q2, ∑ _b ∈ factorCarrier d.Q3, (1 : ℝ) :=
      Finset.sum_le_sum (fun a ha ↦ Finset.sum_le_sum
        (fun b hb ↦ tail_gamma_norm_le_one hd ha hb))
    _ = ((factorCarrier d.Q2).card : ℝ) * ((factorCarrier d.Q3).card : ℝ) := by simp
    _ ≤ (2 * d.Q2) * (2 * d.Q3) :=
      mul_le_mul (card_factorCarrier_le hd.2.2.2.1) (card_factorCarrier_le hd.2.2.2.2.1)
        (Nat.cast_nonneg _) (by linarith [hd.2.2.2.1])
    _ = _ := by ring

private theorem slice_gamma_tau_sum_le
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) {p : ℕ}
    (hp : p ∈ d.primitiveFirstFactorCarrier) :
    (∑ q ∈ (d.q1SliceAtom p).physicalFactorModuli,
      ‖(d.q1SliceAtom p).groupedFactorGamma q‖ * divisorTau q / (q.totient : ℝ)) ≤
      (divisorTau p ^ 2 / (p : ℝ)) * (1 + Real.log d.physicalFactorCap) ^ 8 := by
  have hp0 := (factor_bounds hd.2.2.1 (Finset.mem_filter.mp hp).1).1
  have hQ2 := hd.2.2.2.1
  have hQ3 := hd.2.2.2.2.1
  obtain ⟨hH, _, hH2, hH3⟩ := cap_log_bounds hd
  have h2nonneg : 0 ≤ 1 + Real.log (2 * d.Q2) := by
    linarith [Real.log_nonneg (show 1 ≤ 2 * d.Q2 by linarith)]
  have h3nonneg : 0 ≤ 1 + Real.log (2 * d.Q3) := by
    linarith [Real.log_nonneg (show 1 ≤ 2 * d.Q3 by linarith)]
  calc
    _ ≤ ∑ a ∈ factorCarrier d.Q2, ∑ b ∈ factorCarrier d.Q3,
        ‖d.gamma2 a * d.gamma3 b‖ *
          (divisorTau (p * a * b) / ((p * a * b).totient : ℝ)) := by
      simpa only [mul_div_assoc] using
        weighted_slice_gamma_le d (Finset.mem_filter.mp hp).1
          (fun q ↦ divisorTau q / (q.totient : ℝ))
          (fun q ↦ div_nonneg (divisorTau_nonneg q) (Nat.cast_nonneg _))
    _ ≤ ∑ a ∈ factorCarrier d.Q2, ∑ b ∈ factorCarrier d.Q3,
        (divisorTau p ^ 2 / (p : ℝ)) *
          (divisorTau a ^ 2 / (a : ℝ)) * (divisorTau b ^ 2 / (b : ℝ)) := by
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro b hb
      calc
        _ ≤ 1 * ((divisorTau p ^ 2 / (p : ℝ)) *
            (divisorTau a ^ 2 / (a : ℝ)) * (divisorTau b ^ 2 / (b : ℝ))) :=
          mul_le_mul (tail_gamma_norm_le_one hd ha hb)
            (tau_totient_three_factor hp0 (factor_bounds hQ2 ha).1 (factor_bounds hQ3 hb).1)
            (div_nonneg (divisorTau_nonneg _) (Nat.cast_nonneg _)) zero_le_one
        _ = _ := one_mul _
    _ = (divisorTau p ^ 2 / (p : ℝ)) *
        (∑ a ∈ factorCarrier d.Q2, divisorTau a ^ 2 / (a : ℝ)) *
        (∑ b ∈ factorCarrier d.Q3, divisorTau b ^ 2 / (b : ℝ)) := by
      calc
        _ = (divisorTau p ^ 2 / (p : ℝ)) *
            (∑ a ∈ factorCarrier d.Q2, ∑ b ∈ factorCarrier d.Q3,
              (divisorTau a ^ 2 / (a : ℝ)) * (divisorTau b ^ 2 / (b : ℝ))) := by
          simp only [Finset.mul_sum, mul_assoc]
        _ = (divisorTau p ^ 2 / (p : ℝ)) *
            ((∑ a ∈ factorCarrier d.Q2, divisorTau a ^ 2 / (a : ℝ)) *
              (∑ b ∈ factorCarrier d.Q3, divisorTau b ^ 2 / (b : ℝ))) := by
          rw [Finset.sum_mul_sum]
        _ = _ := by ring
    _ ≤ (divisorTau p ^ 2 / (p : ℝ)) *
        (1 + Real.log (2 * d.Q2)) ^ 4 * (1 + Real.log (2 * d.Q3)) ^ 4 := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (dyadic_divisor_harmonic hQ2 2) (by
          exact div_nonneg (pow_nonneg (divisorTau_nonneg _) _) (Nat.cast_nonneg _)))
        (dyadic_divisor_harmonic hQ3 2)
        (Finset.sum_nonneg (fun b _ ↦ div_nonneg
          (pow_nonneg (divisorTau_nonneg _) _) (Nat.cast_nonneg _)))
        (mul_nonneg (div_nonneg (pow_nonneg (divisorTau_nonneg _) _) (Nat.cast_nonneg _))
          (pow_nonneg h2nonneg _))
    _ ≤ (divisorTau p ^ 2 / (p : ℝ)) *
        (1 + Real.log d.physicalFactorCap) ^ 4 *
          (1 + Real.log d.physicalFactorCap) ^ 4 := by
      gcongr
    _ = _ := by ring

private theorem U_finite_envelope_le_weight_sq
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) :
    (∑ q ∈ d.physicalFactorModuli, ∑ r ∈ d.physicalFactorModuli,
      ‖primitivePairCoefficient d q r‖ * ((q * r).divisors.card : ℝ)) ≤
        4 * d.U ^ 2 * (∑ q ∈ d.physicalFactorModuli,
          ‖d.groupedFactorGamma q‖ * divisorTau q / (q.totient : ℝ)) ^ 2 := by
  have hU : 0 ≤ d.U := by linarith [hd.1]
  let w : ℕ → ℝ := fun q ↦
    ‖d.groupedFactorGamma q‖ * (q.divisors.card : ℝ) / (q.totient : ℝ)
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
        dsimp [w, divisorTau]
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
  calc
    _ ≤ ∑ q ∈ d.physicalFactorModuli, ∑ r ∈ d.physicalFactorModuli,
        4 * d.U ^ 2 * (w q * w r) :=
      Finset.sum_le_sum (fun q _ ↦ Finset.sum_le_sum (fun r _ ↦ hpoint q r))
    _ = 4 * d.U ^ 2 * (∑ q ∈ d.physicalFactorModuli, w q) ^ 2 := by
      have hsum : (∑ q ∈ d.physicalFactorModuli, w q) ^ 2 =
          ∑ q ∈ d.physicalFactorModuli, ∑ r ∈ d.physicalFactorModuli, w q * w r := by
        rw [pow_two, Finset.sum_mul_sum]
      rw [hsum]
      simp only [Finset.mul_sum]
    _ = _ := rfl

private theorem V_finite_envelope_le_weights
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) :
    (∑ q ∈ d.physicalFactorModuli, ∑ r ∈ d.physicalFactorModuli,
      ‖mixedPairCoefficient d q r‖ *
        coprimeMass d.alphaCarrier (fun n ↦ ‖d.alpha n‖) q *
          (r.divisors.card : ℝ)) ≤
      4 * d.U ^ 2 *
        ((∑ q ∈ d.physicalFactorModuli, ‖d.groupedFactorGamma q‖) *
          ∑ r ∈ d.physicalFactorModuli,
            ‖d.groupedFactorGamma r‖ * divisorTau r / (r.totient : ℝ)) := by
  have hU : 0 ≤ d.U := by linarith [hd.1]
  have hmass (q : ℕ) :
      0 ≤ coprimeMass d.alphaCarrier (fun n ↦ ‖d.alpha n‖) q := by
    unfold coprimeMass
    apply Finset.sum_nonneg
    intro n _
    by_cases hn : n.Coprime q
    · rw [if_pos hn]
      exact norm_nonneg _
    · rw [if_neg hn]
  let w : ℕ → ℝ := fun r ↦
    ‖d.groupedFactorGamma r‖ * (r.divisors.card : ℝ) / (r.totient : ℝ)
  have hpoint (q r : ℕ) :
      ‖mixedPairCoefficient d q r‖ *
          coprimeMass d.alphaCarrier (fun n ↦ ‖d.alpha n‖) q *
            (r.divisors.card : ℝ) ≤
        4 * d.U ^ 2 * (‖d.groupedFactorGamma q‖ * w r) := by
    have hc : ‖mixedPairCoefficient d q r‖ ≤
        ‖d.groupedFactorGamma q‖ * ‖d.groupedFactorGamma r‖ *
          (2 * d.U) / (r.totient : ℝ) := by
      simp only [mixedPairCoefficient, norm_div, norm_mul, norm_star,
        Complex.norm_natCast]
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      exact mul_le_mul_of_nonneg_left (coprimeMass_norm_le_twice_U hd r) (by positivity)
    calc
      _ ≤ (‖d.groupedFactorGamma q‖ * ‖d.groupedFactorGamma r‖ *
            (2 * d.U) / (r.totient : ℝ)) * (2 * d.U) *
              (r.divisors.card : ℝ) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul hc (coprimeNormMass_le_twice_U hd q) (hmass q) (by positivity))
          (Nat.cast_nonneg _)
      _ = _ := by dsimp [w]; ring
  calc
    _ ≤ ∑ q ∈ d.physicalFactorModuli, ∑ r ∈ d.physicalFactorModuli,
        4 * d.U ^ 2 * (‖d.groupedFactorGamma q‖ * w r) :=
      Finset.sum_le_sum (fun q _ ↦ Finset.sum_le_sum (fun r _ ↦ hpoint q r))
    _ = 4 * d.U ^ 2 *
        ((∑ q ∈ d.physicalFactorModuli, ‖d.groupedFactorGamma q‖) *
          ∑ r ∈ d.physicalFactorModuli, w r) := by
      rw [Finset.sum_mul_sum]
      simp only [Finset.mul_sum]
    _ = _ := rfl

private theorem shared_U_error_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : ℕ) (sigma kappa c0 : ℝ) (d : MediumAtom),
      MediumAdmissible B sigma kappa c0 d →
      (∑ p ∈ d.primitiveFirstFactorCarrier, ‖uError d p‖) ≤
        C * d.U ^ 2 / d.Q1 * (1 + Real.log d.physicalFactorCap) ^ 32 := by
  obtain ⟨C, hC, hbound⟩ := actualU_sub_primitive_finite_bound
  refine ⟨4 * C, by positivity, fun B sigma kappa c0 d hd ↦ ?_⟩
  let H := 1 + Real.log d.physicalFactorCap
  have hH : 0 ≤ H := (zero_le_one.trans (cap_log_bounds hd).1)
  have hQ1 : 0 < d.Q1 := zero_lt_one.trans_le hd.2.2.1
  have hpoint (p : ℕ) (hp : p ∈ d.primitiveFirstFactorCarrier) :
      ‖uError d p‖ ≤ 4 * C * d.U ^ 2 * H ^ 16 *
        (divisorTau p ^ 4 / (p : ℝ) ^ 2) := by
    have hs := mediumAdmissible_q1SliceAtom hd hp
    have hw0 : 0 ≤ ∑ q ∈ (d.q1SliceAtom p).physicalFactorModuli,
        ‖(d.q1SliceAtom p).groupedFactorGamma q‖ * divisorTau q / (q.totient : ℝ) :=
      Finset.sum_nonneg (fun q _ ↦ div_nonneg
        (mul_nonneg (norm_nonneg _) (divisorTau_nonneg _)) (Nat.cast_nonneg _))
    calc
      _ ≤ C * ∑ q ∈ (d.q1SliceAtom p).physicalFactorModuli,
          ∑ r ∈ (d.q1SliceAtom p).physicalFactorModuli,
            ‖primitivePairCoefficient (d.q1SliceAtom p) q r‖ *
              ((q * r).divisors.card : ℝ) := by
        exact hbound B sigma kappa c0 (d.q1SliceAtom p) hs
      _ ≤ C * (4 * d.U ^ 2 *
          (∑ q ∈ (d.q1SliceAtom p).physicalFactorModuli,
            ‖(d.q1SliceAtom p).groupedFactorGamma q‖ * divisorTau q / (q.totient : ℝ)) ^ 2) :=
        mul_le_mul_of_nonneg_left (U_finite_envelope_le_weight_sq hs) hC.le
      _ ≤ C * (4 * d.U ^ 2 *
          ((divisorTau p ^ 2 / (p : ℝ)) * H ^ 8) ^ 2) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ hw0 (slice_gamma_tau_sum_le hd hp) 2) (by positivity)) hC.le
      _ = _ := by
        rw [mul_pow, div_pow]
        ring
  calc
    _ ≤ ∑ p ∈ d.primitiveFirstFactorCarrier,
        4 * C * d.U ^ 2 * H ^ 16 * (divisorTau p ^ 4 / (p : ℝ) ^ 2) :=
      Finset.sum_le_sum (fun p hp ↦ hpoint p hp)
    _ = 4 * C * d.U ^ 2 * H ^ 16 *
        (∑ p ∈ d.primitiveFirstFactorCarrier, divisorTau p ^ 4 / (p : ℝ) ^ 2) := by
      rw [Finset.mul_sum]
    _ ≤ 4 * C * d.U ^ 2 * H ^ 16 *
        ((1 + Real.log (2 * d.Q1)) ^ 16 / d.Q1) :=
      mul_le_mul_of_nonneg_left (primitive_p_reciprocal_square d hd.2.2.1 4) (by positivity)
    _ ≤ 4 * C * d.U ^ 2 * H ^ 16 * (H ^ 16 / d.Q1) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact div_le_div_of_nonneg_right
        (pow_le_pow_left₀ (by linarith [(Real.log_nonneg
          (show 1 ≤ 2 * d.Q1 by linarith [hd.2.2.1]))])
          (cap_log_bounds hd).2.1 16) hQ1.le
    _ = _ := by dsimp [H]; ring

private theorem primitive_p_harmonic (d : MediumAtom)
    (hQ : 1 ≤ d.Q1) (r : ℕ) :
    (∑ p ∈ d.primitiveFirstFactorCarrier, divisorTau p ^ r / (p : ℝ)) ≤
      (1 + Real.log (2 * d.Q1)) ^ (2 ^ r) := by
  have hsubset : d.primitiveFirstFactorCarrier ⊆ factorCarrier d.Q1 := by
    intro p hp
    exact (Finset.mem_filter.mp hp).1
  calc
    _ ≤ ∑ p ∈ factorCarrier d.Q1, divisorTau p ^ r / (p : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun p _ _ ↦ div_nonneg (pow_nonneg (divisorTau_nonneg _) _) (Nat.cast_nonneg _))
    _ ≤ _ := dyadic_divisor_harmonic hQ r

private theorem shared_V_error_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : ℕ) (sigma kappa c0 : ℝ) (d : MediumAtom),
      MediumAdmissible B sigma kappa c0 d →
      (∑ p ∈ d.primitiveFirstFactorCarrier, ‖vError d p‖) ≤
        C * d.U ^ 2 * (4 * d.Q2 * d.Q3) *
          (1 + Real.log d.physicalFactorCap) ^ 12 := by
  obtain ⟨C, hC, hbound⟩ := actualV_sub_primitive_finite_bound
  refine ⟨4 * C, by positivity, fun B sigma kappa c0 d hd ↦ ?_⟩
  let H := 1 + Real.log d.physicalFactorCap
  let T := 4 * d.Q2 * d.Q3
  have hH : 0 ≤ H := zero_le_one.trans (cap_log_bounds hd).1
  have hT : 0 ≤ T := by
    dsimp [T]
    exact mul_nonneg
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4)
        (by linarith [hd.2.2.2.1])) (by linarith [hd.2.2.2.2.1])
  have hpoint (p : ℕ) (hp : p ∈ d.primitiveFirstFactorCarrier) :
      ‖vError d p‖ ≤ 4 * C * d.U ^ 2 * T * H ^ 8 *
        (divisorTau p ^ 2 / (p : ℝ)) := by
    have hs := mediumAdmissible_q1SliceAtom hd hp
    have hw0 : 0 ≤ ∑ q ∈ (d.q1SliceAtom p).physicalFactorModuli,
        ‖(d.q1SliceAtom p).groupedFactorGamma q‖ * divisorTau q / (q.totient : ℝ) :=
      Finset.sum_nonneg (fun q _ ↦ div_nonneg
        (mul_nonneg (norm_nonneg _) (divisorTau_nonneg _)) (Nat.cast_nonneg _))
    calc
      _ ≤ C * ∑ q ∈ (d.q1SliceAtom p).physicalFactorModuli,
          ∑ r ∈ (d.q1SliceAtom p).physicalFactorModuli,
            ‖mixedPairCoefficient (d.q1SliceAtom p) q r‖ *
              coprimeMass (d.q1SliceAtom p).alphaCarrier
                (fun n ↦ ‖(d.q1SliceAtom p).alpha n‖) q * (r.divisors.card : ℝ) := by
        exact hbound B sigma kappa c0 (d.q1SliceAtom p) hs
      _ ≤ C * (4 * d.U ^ 2 *
          ((∑ q ∈ (d.q1SliceAtom p).physicalFactorModuli,
              ‖(d.q1SliceAtom p).groupedFactorGamma q‖) *
            ∑ r ∈ (d.q1SliceAtom p).physicalFactorModuli,
              ‖(d.q1SliceAtom p).groupedFactorGamma r‖ * divisorTau r / (r.totient : ℝ))) :=
        mul_le_mul_of_nonneg_left (V_finite_envelope_le_weights hs) hC.le
      _ ≤ C * (4 * d.U ^ 2 *
          (T * ((divisorTau p ^ 2 / (p : ℝ)) * H ^ 8))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (mul_le_mul (slice_gamma_norm_sum_le hd hp) (slice_gamma_tau_sum_le hd hp) hw0 hT)
            (by positivity)) hC.le
      _ = _ := by ring
  calc
    _ ≤ ∑ p ∈ d.primitiveFirstFactorCarrier,
        4 * C * d.U ^ 2 * T * H ^ 8 * (divisorTau p ^ 2 / (p : ℝ)) :=
      Finset.sum_le_sum (fun p hp ↦ hpoint p hp)
    _ = 4 * C * d.U ^ 2 * T * H ^ 8 *
        (∑ p ∈ d.primitiveFirstFactorCarrier, divisorTau p ^ 2 / (p : ℝ)) := by
      rw [Finset.mul_sum]
    _ ≤ 4 * C * d.U ^ 2 * T * H ^ 8 * (1 + Real.log (2 * d.Q1)) ^ 4 :=
      mul_le_mul_of_nonneg_left (primitive_p_harmonic d hd.2.2.1 2) (by positivity)
    _ ≤ 4 * C * d.U ^ 2 * T * H ^ 8 * H ^ 4 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact pow_le_pow_left₀ (by linarith [(Real.log_nonneg
        (show 1 ≤ 2 * d.Q1 by linarith [hd.2.2.1]))]) (cap_log_bounds hd).2.1 4
    _ = _ := by dsimp [H, T]; ring

private theorem outside_U_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : ℕ) (sigma kappa c0 : ℝ) (d : MediumAtom),
      MediumAdmissible B sigma kappa c0 d →
      (∑ n ∈ d.betaCarrier, ‖d.beta n‖ ^ 2) *
        (∑ p ∈ d.primitiveFirstFactorCarrier, ‖d.gamma1 p‖ ^ 2) *
          (∑ p ∈ d.primitiveFirstFactorCarrier, ‖uError d p‖) ≤
        C * d.V * d.U ^ 2 *
          (1 + Real.log (2 * d.V)) ^ ((2 ^ B) ^ 2 - 1) *
            (1 + Real.log d.physicalFactorCap) ^ 32 := by
  obtain ⟨C, hC, hbound⟩ := shared_U_error_bound
  refine ⟨4 * C, by positivity, fun B sigma kappa c0 d hd ↦ ?_⟩
  have hV : 0 ≤ d.V := by linarith [hd.2.1]
  have hQ1 : 0 < d.Q1 := zero_lt_one.trans_le hd.2.2.1
  have hH : 0 ≤ 1 + Real.log d.physicalFactorCap :=
    zero_le_one.trans (cap_log_bounds hd).1
  have hbeta : 0 ≤ 1 + Real.log (2 * d.V) := by
    linarith [Real.log_nonneg (show 1 ≤ 2 * d.V by linarith [hd.2.1])]
  calc
    _ ≤ (4 * d.V * d.Q1 *
          (1 + Real.log (2 * d.V)) ^ ((2 ^ B) ^ 2 - 1)) *
        (C * d.U ^ 2 / d.Q1 * (1 + Real.log d.physicalFactorCap) ^ 32) :=
      mul_le_mul (d.sharedFirstFactor_outside_le hd) (hbound B sigma kappa c0 d hd)
        (Finset.sum_nonneg (fun p _ ↦ norm_nonneg _)) (by positivity)
    _ = ((C * d.U ^ 2 * (1 + Real.log d.physicalFactorCap) ^ 32) / d.Q1) *
        d.Q1 * (4 * d.V * (1 + Real.log (2 * d.V)) ^ ((2 ^ B) ^ 2 - 1)) := by ring
    _ = (C * d.U ^ 2 * (1 + Real.log d.physicalFactorCap) ^ 32) *
        (4 * d.V * (1 + Real.log (2 * d.V)) ^ ((2 ^ B) ^ 2 - 1)) := by
      rw [div_mul_cancel₀ _ hQ1.ne']
    _ = _ := by ring

private theorem outside_V_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : ℕ) (sigma kappa c0 : ℝ) (d : MediumAtom),
      MediumAdmissible B sigma kappa c0 d →
      (∑ n ∈ d.betaCarrier, ‖d.beta n‖ ^ 2) *
        (∑ p ∈ d.primitiveFirstFactorCarrier, ‖d.gamma1 p‖ ^ 2) *
          (∑ p ∈ d.primitiveFirstFactorCarrier, ‖vError d p‖) ≤
        C * d.V * d.U ^ 2 * d.physicalFactorCap *
          (1 + Real.log (2 * d.V)) ^ ((2 ^ B) ^ 2 - 1) *
            (1 + Real.log d.physicalFactorCap) ^ 12 := by
  obtain ⟨C, hC, hbound⟩ := shared_V_error_bound
  refine ⟨2 * C, by positivity, fun B sigma kappa c0 d hd ↦ ?_⟩
  have hV : 0 ≤ d.V := by linarith [hd.2.1]
  have hQ1 : 0 ≤ d.Q1 := by linarith [hd.2.2.1]
  have hH : 0 ≤ 1 + Real.log d.physicalFactorCap :=
    zero_le_one.trans (cap_log_bounds hd).1
  have hbeta : 0 ≤ 1 + Real.log (2 * d.V) := by
    linarith [Real.log_nonneg (show 1 ≤ 2 * d.V by linarith [hd.2.1])]
  calc
    _ ≤ (4 * d.V * d.Q1 *
          (1 + Real.log (2 * d.V)) ^ ((2 ^ B) ^ 2 - 1)) *
        (C * d.U ^ 2 * (4 * d.Q2 * d.Q3) *
          (1 + Real.log d.physicalFactorCap) ^ 12) :=
      mul_le_mul (d.sharedFirstFactor_outside_le hd) (hbound B sigma kappa c0 d hd)
        (Finset.sum_nonneg (fun p _ ↦ norm_nonneg _)) (by positivity)
    _ = _ := by unfold MediumAtom.physicalFactorCap; ring

private theorem outside_U_power_bound (B : ℕ) (sigma kappa c0 : ℝ)
    (hsigma : 0 < sigma) :
    ∃ C : ℝ, 0 < C ∧ ∃ x0 : ℝ, 1 < x0 ∧ ∀ d : MediumAtom,
      MediumAdmissible B sigma kappa c0 d → x0 ≤ d.scale →
      (∑ n ∈ d.betaCarrier, ‖d.beta n‖ ^ 2) *
        (∑ p ∈ d.primitiveFirstFactorCarrier, ‖d.gamma1 p‖ ^ 2) *
          (∑ p ∈ d.primitiveFirstFactorCarrier, ‖uError d p‖) ≤
            C * d.scale ^ (7 / 4 : ℝ) := by
  obtain ⟨C, hC, hbound⟩ := outside_U_bound
  obtain ⟨x0, hx0, hcost⟩ := eventually_actual_log_cost_le_rpow
    ((2 ^ B) ^ 2 - 1) 32 sigma hsigma (by norm_num : (0 : ℝ) < 1 / 4)
  refine ⟨C, hC, x0, hx0, fun d hd hx ↦ ?_⟩
  have hxpos : 0 < d.scale := zero_lt_one.trans_le (one_le_scale hd)
  have hlogV0 : 0 ≤ 1 + Real.log (2 * d.V) := by
    linarith [Real.log_nonneg (show 1 ≤ 2 * d.V by linarith [hd.2.1])]
  have hlogCap0 : 0 ≤ 1 + Real.log d.physicalFactorCap := by
    linarith [Real.log_nonneg (d.one_le_physicalFactorCap hd)]
  calc
    _ ≤ C * d.V * d.U ^ 2 *
        (1 + Real.log (2 * d.V)) ^ ((2 ^ B) ^ 2 - 1) *
          (1 + Real.log d.physicalFactorCap) ^ 32 := hbound B sigma kappa c0 d hd
    _ = C * d.scale * d.U *
        ((1 + Real.log (2 * d.V)) ^ ((2 ^ B) ^ 2 - 1) *
          (1 + Real.log d.physicalFactorCap) ^ 32) := by
      unfold MediumAtom.scale
      ring
    _ ≤ C * d.scale * (d.scale ^ (1 / 2 : ℝ)) * d.scale ^ (1 / 4 : ℝ) :=
      mul_le_mul
        (mul_le_mul_of_nonneg_left (U_le_scale_half hsigma hd) (by positivity))
        (hcost B kappa c0 d hd hx) (by positivity) (by positivity)
    _ = C * (d.scale ^ (1 : ℝ) * d.scale ^ (1 / 2 : ℝ) *
        d.scale ^ (1 / 4 : ℝ)) := by rw [Real.rpow_one]; ring
    _ = _ := by rw [← Real.rpow_add hxpos, ← Real.rpow_add hxpos]; norm_num

private theorem outside_V_power_bound (B : ℕ) (sigma kappa c0 : ℝ)
    (hsigma : 0 < sigma) :
    ∃ C : ℝ, 0 < C ∧ ∃ x0 : ℝ, 1 < x0 ∧ ∀ d : MediumAtom,
      MediumAdmissible B sigma kappa c0 d → x0 ≤ d.scale →
      (∑ n ∈ d.betaCarrier, ‖d.beta n‖ ^ 2) *
        (∑ p ∈ d.primitiveFirstFactorCarrier, ‖d.gamma1 p‖ ^ 2) *
          (∑ p ∈ d.primitiveFirstFactorCarrier, ‖vError d p‖) ≤
            C * d.scale ^ (2 - 8 * sigma) := by
  obtain ⟨C, hC, hbound⟩ := outside_V_bound
  obtain ⟨x0, hx0, hcost⟩ := eventually_actual_log_cost_le_rpow
    ((2 ^ B) ^ 2 - 1) 12 sigma hsigma hsigma
  refine ⟨8 * C, by positivity, x0, hx0, fun d hd hx ↦ ?_⟩
  have hxpos : 0 < d.scale := zero_lt_one.trans_le (one_le_scale hd)
  have hlogV0 : 0 ≤ 1 + Real.log (2 * d.V) := by
    linarith [Real.log_nonneg (show 1 ≤ 2 * d.V by linarith [hd.2.1])]
  have hlogCap0 : 0 ≤ 1 + Real.log d.physicalFactorCap := by
    linarith [Real.log_nonneg (d.one_le_physicalFactorCap hd)]
  calc
    _ ≤ C * d.V * d.U ^ 2 * d.physicalFactorCap *
        (1 + Real.log (2 * d.V)) ^ ((2 ^ B) ^ 2 - 1) *
          (1 + Real.log d.physicalFactorCap) ^ 12 := hbound B sigma kappa c0 d hd
    _ = C * d.scale * (d.U * d.physicalFactorCap) *
        ((1 + Real.log (2 * d.V)) ^ ((2 ^ B) ^ 2 - 1) *
          (1 + Real.log d.physicalFactorCap) ^ 12) := by
      unfold MediumAtom.scale
      ring
    _ ≤ (C * d.scale * (8 * d.scale ^ (1 - 9 * sigma))) * d.scale ^ sigma :=
      mul_le_mul
        (mul_le_mul_of_nonneg_left (d.U_mul_physicalFactorCap_le hd) (by positivity))
        (hcost B kappa c0 d hd hx) (by positivity) (by positivity)
    _ = (8 * C) * (d.scale ^ (1 : ℝ) * d.scale ^ (1 - 9 * sigma) *
        d.scale ^ sigma) := by rw [Real.rpow_one]; ring
    _ = _ := by
      rw [← Real.rpow_add hxpos, ← Real.rpow_add hxpos]
      congr 2
      ring

private theorem outside_U_log_payment (B : ℕ) (sigma kappa c0 A : ℝ)
    (hsigma : 0 < sigma) :
    ∃ x0 : ℝ, 1 < x0 ∧ ∀ d : MediumAtom,
      MediumAdmissible B sigma kappa c0 d → x0 ≤ d.scale →
      (∑ n ∈ d.betaCarrier, ‖d.beta n‖ ^ 2) *
        (∑ p ∈ d.primitiveFirstFactorCarrier, ‖d.gamma1 p‖ ^ 2) *
          (∑ p ∈ d.primitiveFirstFactorCarrier, ‖uError d p‖) ≤
            d.scale ^ 2 / (Real.log d.scale) ^ A := by
  obtain ⟨C, hC, x1, hx1, hbound⟩ := outside_U_power_bound B sigma kappa c0 hsigma
  obtain ⟨x2, hx2⟩ := eventually_atTop.mp
    (eventually_const_rpow_two_le_logBudget C A hC.le
      (by norm_num : (0 : ℝ) < 1 / 4))
  refine ⟨max x1 x2, lt_of_lt_of_le hx1 (le_max_left _ _), fun d hd hx ↦ ?_⟩
  apply (hbound d hd ((le_max_left _ _).trans hx)).trans
  simpa only [show (2 : ℝ) - 1 / 4 = 7 / 4 by norm_num] using
    hx2 d.scale ((le_max_right _ _).trans hx)

private theorem outside_V_log_payment (B : ℕ) (sigma kappa c0 A : ℝ)
    (hsigma : 0 < sigma) :
    ∃ x0 : ℝ, 1 < x0 ∧ ∀ d : MediumAtom,
      MediumAdmissible B sigma kappa c0 d → x0 ≤ d.scale →
      (∑ n ∈ d.betaCarrier, ‖d.beta n‖ ^ 2) *
        (∑ p ∈ d.primitiveFirstFactorCarrier, ‖d.gamma1 p‖ ^ 2) *
          (∑ p ∈ d.primitiveFirstFactorCarrier, ‖vError d p‖) ≤
            d.scale ^ 2 / (Real.log d.scale) ^ A := by
  obtain ⟨C, hC, x1, hx1, hbound⟩ := outside_V_power_bound B sigma kappa c0 hsigma
  obtain ⟨x2, hx2⟩ := eventually_atTop.mp
    (eventually_const_rpow_two_le_logBudget C A hC.le (by linarith : 0 < 8 * sigma))
  refine ⟨max x1 x2, lt_of_lt_of_le hx1 (le_max_left _ _), fun d hd hx ↦ ?_⟩
  exact (hbound d hd ((le_max_left _ _).trans hx)).trans
    (hx2 d.scale ((le_max_right _ _).trans hx))

private theorem shared_UV_norm_le (d : MediumAtom) :
    ‖d.sharedPrimitiveUVError‖ ≤
      (∑ p ∈ d.primitiveFirstFactorCarrier, ‖uError d p‖) +
        2 * (∑ p ∈ d.primitiveFirstFactorCarrier, ‖vError d p‖) := by
  calc
    _ ≤ ∑ p ∈ d.primitiveFirstFactorCarrier, ‖uError d p - 2 * vError d p‖ :=
      norm_sum_le _ _
    _ ≤ ∑ p ∈ d.primitiveFirstFactorCarrier, (‖uError d p‖ + 2 * ‖vError d p‖) := by
      apply Finset.sum_le_sum
      intro p _
      calc
        _ ≤ ‖uError d p‖ + ‖(2 : ℂ) * vError d p‖ := norm_sub_le _ _
        _ = _ := by rw [norm_mul]; norm_num
    _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum]

end SharedFirstFactorPrimitiveUVPayment

open SharedFirstFactorPrimitiveUVPayment

/-- The original beta and primitive gamma1 moments pay the literal same-p
U/V remainder. Its threshold is chosen before every actual medium atom. -/
theorem actual_betaL2_gamma1L2_sharedPrimitiveUV_log_payment
    (B : ℕ) (sigma kappa c0 A : ℝ) (hsigma : 0 < sigma) :
    ∃ x0 : ℝ, 1 < x0 ∧ ∀ d : MediumAtom,
      MediumAdmissible B sigma kappa c0 d → x0 ≤ d.scale →
      (∑ n ∈ d.betaCarrier, ‖d.beta n‖ ^ 2) *
        (∑ p ∈ d.primitiveFirstFactorCarrier, ‖d.gamma1 p‖ ^ 2) *
          ‖d.sharedPrimitiveUVError‖ ≤
            3 * (d.scale ^ 2 / (Real.log d.scale) ^ A) := by
  obtain ⟨xU, hxU, hU⟩ := outside_U_log_payment B sigma kappa c0 A hsigma
  obtain ⟨xV, _hxV, hV⟩ := outside_V_log_payment B sigma kappa c0 A hsigma
  refine ⟨max xU xV, lt_of_lt_of_le hxU (le_max_left _ _), fun d hd hx ↦ ?_⟩
  have hu := hU d hd ((le_max_left _ _).trans hx)
  have hv := hV d hd ((le_max_right _ _).trans hx)
  calc
    _ ≤ ((∑ n ∈ d.betaCarrier, ‖d.beta n‖ ^ 2) *
          (∑ p ∈ d.primitiveFirstFactorCarrier, ‖d.gamma1 p‖ ^ 2)) *
        ((∑ p ∈ d.primitiveFirstFactorCarrier, ‖uError d p‖) +
          2 * (∑ p ∈ d.primitiveFirstFactorCarrier, ‖vError d p‖)) :=
      mul_le_mul_of_nonneg_left (shared_UV_norm_le d) (by positivity)
    _ = ((∑ n ∈ d.betaCarrier, ‖d.beta n‖ ^ 2) *
          (∑ p ∈ d.primitiveFirstFactorCarrier, ‖d.gamma1 p‖ ^ 2) *
            (∑ p ∈ d.primitiveFirstFactorCarrier, ‖uError d p‖)) +
        2 * ((∑ n ∈ d.betaCarrier, ‖d.beta n‖ ^ 2) *
          (∑ p ∈ d.primitiveFirstFactorCarrier, ‖d.gamma1 p‖ ^ 2) *
            (∑ p ∈ d.primitiveFirstFactorCarrier, ‖vError d p‖)) := by ring
    _ ≤ d.scale ^ 2 / (Real.log d.scale) ^ A +
        2 * (d.scale ^ 2 / (Real.log d.scale) ^ A) :=
      add_le_add hu (mul_le_mul_of_nonneg_left hv (by norm_num))
    _ = _ := by ring

end

end ImbalancedChen.Part3
