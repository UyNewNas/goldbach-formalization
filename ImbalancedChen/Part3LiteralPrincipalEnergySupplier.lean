import ImbalancedChen.Part3SharedFirstFactorPrimitiveUVPayment
import ImbalancedChen.Part3TransposedModulusProgression
import ImbalancedChen.Part3CommonPM2FiniteFold

/-! SOURCE ONLY / UNCOMPILED / HOLD.
Finite literal principal energy, retaining the sliced reciprocal-square first factor.
The local private helpers below are exact source copies from the accepted parent;
no private mangled name is referenced and no upstream visibility is changed.
-/
namespace ImbalancedChen.Part3.PrincipalEnergySupplier
noncomputable section
open Classical Finset Filter Topology
open scoped BigOperators Pointwise
open ImbalancedChen.Part3
open TransposedZeroCovariance TransposedPrimitiveU TransposedPrimitiveV
open TransposedPrimitiveUMoment TransposedPrimitiveVMoment TransposedPrimitiveUPayment
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

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

private theorem principal_row_norm_le
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) {p : ℕ}
    (hp : p ∈ d.primitiveFirstFactorCarrier) (m : ℕ) :
    ‖(d.q1SliceAtom p).transposedAtom.complexPrincipalRow m‖ ≤
      2 * d.U * ((divisorTau p ^ 2 / (p : ℝ)) *
        (1 + Real.log d.physicalFactorCap) ^ 8) := by
  have hU : 0 ≤ d.U := zero_le_one.trans hd.1
  let e := d.q1SliceAtom p
  have he := mediumAdmissible_q1SliceAtom hd hp
  have hpoint (q : ℕ) (hq : q ∈ e.physicalFactorModuli) :
      ‖e.groupedFactorGamma q *
        (if m.Coprime q then coprimeMass e.alphaCarrier e.alpha q else 0) /
          (q.totient : ℂ)‖ ≤
        (2 * d.U) * (‖e.groupedFactorGamma q‖ * divisorTau q / (q.totient : ℝ)) := by
    have hmass : ‖(if m.Coprime q then coprimeMass e.alphaCarrier e.alpha q else 0)‖ ≤
        2 * d.U := by
      split_ifs
      · exact coprimeMass_norm_le_twice_U he q
      · simpa only [norm_zero] using (by linarith [hd.1] : (0 : ℝ) ≤ 2 * d.U)
    have hq0 : 0 < q := (Finset.mem_Ioc.mp (e.physicalFactorModuli_subset_cap he hq)).1
    have ht : 1 ≤ divisorTau q := by
      have hc : 1 ≤ q.divisors.card := Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hq0.ne'⟩
      exact_mod_cast hc
    calc
      _ = ‖e.groupedFactorGamma q‖ *
          ‖(if m.Coprime q then coprimeMass e.alphaCarrier e.alpha q else 0)‖ /
            (q.totient : ℝ) := by rw [norm_div, norm_mul, Complex.norm_natCast]
      _ ≤ ‖e.groupedFactorGamma q‖ * (2 * d.U) / (q.totient : ℝ) :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hmass (norm_nonneg _)) (Nat.cast_nonneg _)
      _ ≤ (‖e.groupedFactorGamma q‖ * (2 * d.U) * divisorTau q) /
          (q.totient : ℝ) := by
        apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
        simpa only [mul_one] using
          mul_le_mul_of_nonneg_left ht
            (mul_nonneg (norm_nonneg _) (mul_nonneg (by norm_num) hU))
      _ = _ := by ring
  calc
    _ ≤ ∑ q ∈ e.physicalFactorModuli,
        ‖e.groupedFactorGamma q *
          (if m.Coprime q then coprimeMass e.alphaCarrier e.alpha q else 0) /
            (q.totient : ℂ)‖ := by
      rw [actual_principalRow_eq_grouped]
      exact norm_sum_le _ _
    _ ≤ ∑ q ∈ e.physicalFactorModuli,
        (2 * d.U) * (‖e.groupedFactorGamma q‖ * divisorTau q / (q.totient : ℝ)) :=
      Finset.sum_le_sum hpoint
    _ = (2 * d.U) * (∑ q ∈ e.physicalFactorModuli,
        ‖e.groupedFactorGamma q‖ * divisorTau q / (q.totient : ℝ)) := by
      rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (slice_gamma_tau_sum_le hd hp) (by linarith [hd.1])

private theorem sum_p_principal_norm_sq_le
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (m : ℕ) :
    (∑ p ∈ d.primitiveFirstFactorCarrier,
      ‖(d.q1SliceAtom p).transposedAtom.complexPrincipalRow m‖ ^ 2) ≤
        4 * d.U ^ 2 / d.Q1 * (1 + Real.log d.physicalFactorCap) ^ 32 := by
  let H := 1 + Real.log d.physicalFactorCap
  have hH : 0 ≤ H := zero_le_one.trans (cap_log_bounds hd).1
  have hQ1 : 0 < d.Q1 := zero_lt_one.trans_le hd.2.2.1
  have hpoint (p : ℕ) (hp : p ∈ d.primitiveFirstFactorCarrier) :
      ‖(d.q1SliceAtom p).transposedAtom.complexPrincipalRow m‖ ^ 2 ≤
        4 * d.U ^ 2 * H ^ 16 * (divisorTau p ^ 4 / (p : ℝ) ^ 2) := by
    calc
      _ ≤ (2 * d.U * ((divisorTau p ^ 2 / (p : ℝ)) * H ^ 8)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (principal_row_norm_le hd hp m) 2
      _ = _ := by simp only [mul_pow, div_pow]; ring
  calc
    _ ≤ ∑ p ∈ d.primitiveFirstFactorCarrier,
        4 * d.U ^ 2 * H ^ 16 * (divisorTau p ^ 4 / (p : ℝ) ^ 2) :=
      Finset.sum_le_sum hpoint
    _ = 4 * d.U ^ 2 * H ^ 16 *
        (∑ p ∈ d.primitiveFirstFactorCarrier, divisorTau p ^ 4 / (p : ℝ) ^ 2) := by
      rw [Finset.mul_sum]
    _ ≤ 4 * d.U ^ 2 * H ^ 16 * ((1 + Real.log (2 * d.Q1)) ^ 16 / d.Q1) :=
      mul_le_mul_of_nonneg_left (primitive_p_reciprocal_square d hd.2.2.1 4) (by positivity)
    _ ≤ 4 * d.U ^ 2 * H ^ 16 * (H ^ 16 / d.Q1) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact div_le_div_of_nonneg_right
        (pow_le_pow_left₀ (by linarith [Real.log_nonneg
          (show 1 ≤ 2 * d.Q1 by linarith [hd.2.2.1])]) (cap_log_bounds hd).2.1 16) hQ1.le
    _ = _ := by dsimp [H]; ring

private theorem transposed_smoothWeight_sum_le
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) :
    (∑ m ∈ d.transposedAtom.commonSmoothCarrier, d.transposedAtom.commonSmoothWeight m) ≤
      5 * d.V := by
  calc
    _ ≤ ∑ _m ∈ d.transposedAtom.commonSmoothCarrier, (1 : ℝ) :=
      Finset.sum_le_sum (fun _ _ ↦ CommonSmoothCutoff.scaledDyadicCutoff_le_one _ _)
    _ = (Nat.ceil (3 * d.V) : ℝ) + 1 := by
      simp [MediumAtom.commonSmoothCarrier, MediumAtom.transposedAtom]
    _ ≤ _ := by
      have := Nat.ceil_lt_add_one (by linarith [hd.2.1] : 0 ≤ 3 * d.V)
      linarith [hd.2.1]

private theorem raw_principal_energy_le
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) :
    (∑ p ∈ d.primitiveFirstFactorCarrier,
      ∑ m ∈ d.transposedAtom.commonSmoothCarrier,
        d.transposedAtom.commonSmoothWeight m *
          ‖(d.q1SliceAtom p).transposedAtom.complexPrincipalRow m‖ ^ 2) ≤
      20 * d.V * d.U ^ 2 / d.Q1 * (1 + Real.log d.physicalFactorCap) ^ 32 := by
  let C := 4 * d.U ^ 2 / d.Q1 * (1 + Real.log d.physicalFactorCap) ^ 32
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (div_nonneg (by positivity) (by linarith [hd.2.2.1]))
      (pow_nonneg (zero_le_one.trans (cap_log_bounds hd).1) _)
  calc
    _ = ∑ m ∈ d.transposedAtom.commonSmoothCarrier,
        d.transposedAtom.commonSmoothWeight m *
          (∑ p ∈ d.primitiveFirstFactorCarrier,
            ‖(d.q1SliceAtom p).transposedAtom.complexPrincipalRow m‖ ^ 2) := by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ ≤ ∑ m ∈ d.transposedAtom.commonSmoothCarrier,
        d.transposedAtom.commonSmoothWeight m * C := by
      apply Finset.sum_le_sum
      intro m _
      exact mul_le_mul_of_nonneg_left (sum_p_principal_norm_sq_le hd m)
        (d.transposedAtom.commonSmoothWeight_nonneg m)
    _ = (∑ m ∈ d.transposedAtom.commonSmoothCarrier,
        d.transposedAtom.commonSmoothWeight m) * C := by rw [Finset.sum_mul]
    _ ≤ (5 * d.V) * C := mul_le_mul_of_nonneg_right (transposed_smoothWeight_sum_le hd) hC
    _ = _ := by dsimp [C]; ring

/-- The exact original smoothed principal energy, with only alpha cleaned. -/
def principalEnergy (d : MediumAtom) : ℝ :=
  ∑ p ∈ d.primitiveFirstFactorCarrier,
    ∑ m ∈ d.cleanedAlphaAtom.transposedAtom.commonSmoothCarrier,
      d.cleanedAlphaAtom.transposedAtom.commonSmoothWeight m *
        ‖(d.cleanedAlphaAtom.q1SliceAtom p).transposedAtom.complexPrincipalRow m‖ ^ 2

theorem principalEnergy_nonneg (d : MediumAtom) : 0 ≤ principalEnergy d := by
  exact Finset.sum_nonneg (fun p _ ↦ Finset.sum_nonneg (fun m _ ↦
    mul_nonneg (d.cleanedAlphaAtom.transposedAtom.commonSmoothWeight_nonneg m) (sq_nonneg _)))

/-- Finite U0 supplier; no sigma or kappa sign restriction is added. -/
theorem principalEnergy_le
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) :
    principalEnergy d ≤ 20 * d.V * d.U ^ 2 / d.Q1 *
      (1 + Real.log d.physicalFactorCap) ^ 32 := by
  exact raw_principal_energy_le (mediumAdmissible_cleanedAlphaAtom hd)

/-- Original outside beta and gamma1 energies occur once; E=0 is allowed. -/
theorem outsideEnergy_mul_principalEnergy_le
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) :
    CommonPM2FiniteFold.outsideEnergy d * principalEnergy d ≤
      80 * d.scale ^ 2 * (1 + Real.log (2 * d.V)) ^ ((2 ^ B) ^ 2 - 1) *
        (1 + Real.log d.physicalFactorCap) ^ 32 := by
  have hQ1 : 0 < d.Q1 := zero_lt_one.trans_le hd.2.2.1
  have hV : 0 ≤ d.V := zero_le_one.trans hd.2.1
  have hL : 0 ≤ 1 + Real.log (2 * d.V) := by
    linarith [Real.log_nonneg (show 1 ≤ 2 * d.V by linarith [hd.2.1])]
  calc
    _ ≤ (4 * d.V * d.Q1 * (1 + Real.log (2 * d.V)) ^ ((2 ^ B) ^ 2 - 1)) *
        (20 * d.V * d.U ^ 2 / d.Q1 * (1 + Real.log d.physicalFactorCap) ^ 32) :=
      mul_le_mul (d.sharedFirstFactor_outside_le hd) (principalEnergy_le hd)
        (principalEnergy_nonneg d) (by positivity)
    _ = ((20 * d.V * d.U ^ 2 * (1 + Real.log d.physicalFactorCap) ^ 32) / d.Q1) *
        d.Q1 * (4 * d.V * (1 + Real.log (2 * d.V)) ^ ((2 ^ B) ^ 2 - 1)) := by ring
    _ = (20 * d.V * d.U ^ 2 * (1 + Real.log d.physicalFactorCap) ^ 32) *
        (4 * d.V * (1 + Real.log (2 * d.V)) ^ ((2 ^ B) ^ 2 - 1)) := by
      rw [div_mul_cancel₀ _ hQ1.ne']
    _ = _ := by unfold MediumAtom.scale; ring

end
end ImbalancedChen.Part3.PrincipalEnergySupplier
