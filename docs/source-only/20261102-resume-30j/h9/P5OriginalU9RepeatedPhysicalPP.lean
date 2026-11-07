import ImbalancedChen.CurrentChenP5U9OrderedPhysicalPP
import ImbalancedChen.CurrentChenP5U9RepeatedLabels
import ImbalancedChen.P5OriginalPrimeEndpointDivisors
import ImbalancedChen.TotientReciprocalBudget
import ImbalancedChen.Part3PolynomialResidueDivisorBound
import Mathlib.Tactic

/-!
# The actual repeated-coordinate U9 PP source is paid

SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The existing repeated-label count is not a bound for a signed modulus
sum. Here each congruence is charged to a divisor of the NONZERO actual
receiver N-product; the exact coprime mean pays only reciprocal totients.
The original three branch labels are retained throughout. In particular
the repeated physical tuple is never counted as an unlabelled product.

No PP, density, integral endpoint or U9 mean estimate is assumed.
-/

namespace ImbalancedChen.P5OriginalU9RepeatedPP

noncomputable section
open Classical Filter Topology
open scoped BigOperators
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

def strict {N : ℕ} (u : Fin 3 → Fin (N + 1)) : Prop :=
  (u 0).val < (u 1).val ∧ (u 1).val < (u 2).val

def strictWeight (j : Fin 3) (N : ℕ) (u : Fin 3 → Fin (N + 1)) : ℝ :=
  if strict u then p5z_u9_orderedPhysicalWeight j N u else 0

def repeatedWeight (j : Fin 3) (N : ℕ) (u : Fin 3 → Fin (N + 1)) : ℝ :=
  if strict u then 0 else p5z_u9_orderedPhysicalWeight j N u

def repeatedTuples (j : Fin 3) (N : ℕ) : Finset (Fin 3 → Fin (N + 1)) :=
  (Part3.labelledPrimeTuples 3 N).filter fun u =>
    p5z_u9_orderedPhysicalWeight j N u ≠ 0 ∧ ¬ strict u

theorem weight_split (j : Fin 3) (N : ℕ) (u : Fin 3 → Fin (N + 1)) :
    p5z_u9_orderedPhysicalWeight j N u = strictWeight j N u + repeatedWeight j N u := by
  by_cases h : strict u <;> simp [strictWeight, repeatedWeight, h]

theorem repeatedTuples_inverse_mem {j : Fin 3} {N : ℕ}
    {u : Fin 3 → Fin (N + 1)} (hu : u ∈ repeatedTuples j N) :
    p5z_u9_physicalInverse j u ∈ p5z_u9_repeatedLabels N := by
  obtain ⟨_, huweight, hunot⟩ := Finset.mem_filter.mp hu
  have hbranch := p5z_u9_orderedPhysicalWeight_support huweight
  by_contra hn
  have hs := (p5z_u9_orderBranch_strict_iff_not_repeated hbranch).mpr hn
  apply hunot
  simpa only [strict, p5z_u9_orderedNat_physicalInverse] using hs

/-- Inject into ORIGINAL marked labels, not the product image. The fixed
inverse is injective within a branch, including equal prime coordinates. -/
theorem repeatedTuples_card_le_original (j : Fin 3) (N : ℕ) :
    (repeatedTuples j N).card ≤ (p5z_u9_repeatedLabels N).card := by
  apply Finset.card_le_card_of_injOn (p5z_u9_physicalInverse j)
  · intro u hu
    exact repeatedTuples_inverse_mem hu
  · intro u hu v hv huv
    funext i
    apply Fin.ext
    have h := congrArg (fun t => p5z_u9_orderedNat j t i) huv
    simpa only [p5z_u9_orderedNat_physicalInverse] using h

theorem repeatedTuples_product_lt {j : Fin 3} {N : ℕ}
    {u : Fin 3 → Fin (N + 1)} (hu : u ∈ repeatedTuples j N) :
    Part3.labelledProduct u < N := by
  have hs := p5z_u9_orderedPhysicalWeight_support (Finset.mem_filter.mp hu).2.1
  rw [← p5z_u9_physicalInverse_product j u]
  exact p5z_u9_switchedLabels_product_lt (Finset.mem_filter.mp hs).1

theorem repeatedTuples_card_le_power (j : Fin 3) {N : ℕ} (hN : (1 : ℝ) ≤ N) :
    ((repeatedTuples j N).card : ℝ) ≤ 8 * (N : ℝ) ^ (92 / 125 : ℝ) := by
  have hc : ((repeatedTuples j N).card : ℝ) ≤
      ((p5z_u9_repeatedLabels N).card : ℝ) := by
    exact_mod_cast repeatedTuples_card_le_original j N
  exact hc.trans (p5z_u9_repeatedLabels_card_le_power hN)

/-- Exact support restriction of the physical repeated weight. -/
theorem repeatedWeight_sum (j : Fin 3) (N : ℕ)
    (G : (Fin 3 → Fin (N + 1)) → ℝ) :
    (∑ u ∈ Part3.labelledPrimeTuples 3 N, repeatedWeight j N u * G u) =
      ∑ u ∈ repeatedTuples j N, G u := by
  rw [repeatedTuples, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro u hu
  by_cases hs : strict u
  · simp [repeatedWeight, hs]
  · by_cases hb : p5z_u9_physicalInverse j u ∈ p5z_u9_orderBranch j N
    · simp [repeatedWeight, hs, p5z_u9_orderedPhysicalWeight, hb]
    · simp [repeatedWeight, hs, p5z_u9_orderedPhysicalWeight, hb]

theorem repeatedPP_eq_labelled (j : Fin 3) (N : ℕ) (D : Finset ℕ) (rho : ℕ → ℝ) :
    Part3.primeProductSignedError 3 N N D rho (repeatedWeight j N) =
      p5z_labelledDistributionError (repeatedTuples j N) Part3.labelledProduct
        (fun _ => 1) N D rho := by
  unfold Part3.primeProductSignedError p5z_labelledDistributionError
  apply Finset.sum_congr rfl
  intro d hd
  rw [repeatedWeight_sum]
  simp only [p5z_labelledCongruenceMass, p5z_labelledCoprimeMass,
    Finset.sum_sub_distrib, Finset.sum_div]

theorem physicalPP_split (j : Fin 3) (N : ℕ) (D : Finset ℕ) (rho : ℕ → ℝ) :
    Part3.primeProductSignedError 3 N N D rho (p5z_u9_orderedPhysicalWeight j N) =
      Part3.primeProductSignedError 3 N N D rho (strictWeight j N) +
      Part3.primeProductSignedError 3 N N D rho (repeatedWeight j N) := by
  unfold Part3.primeProductSignedError
  simp only [weight_split j N, add_mul, Finset.sum_add_distrib, mul_add]

/-- Finite Fubini before absolute values. Each original label retains
its own receiver; a zero receiver is excluded by the true product<N gate. -/
theorem abs_labelled_error_le_divisors {α : Type*} (S : Finset α) (f : α → ℕ)
    (N : ℕ) (D : Finset ℕ) (rho : ℕ → ℝ)
    (hS : ∀ t ∈ S, f t < N) (hrho : ∀ d ∈ D, |rho d| ≤ 1) :
    |p5z_labelledDistributionError S f (fun _ => 1) N D rho| ≤
      (∑ t ∈ S, ((N - f t).divisors.card : ℝ)) +
        (S.card : ℝ) * ∑ d ∈ D, 1 / (Nat.totient d : ℝ) := by
  have hcong : (∑ d ∈ D, rho d * p5z_labelledCongruenceMass S f (fun _ => 1) N d) =
      ∑ t ∈ S, ∑ d ∈ D with Nat.ModEq d (f t) N, rho d := by
    simp only [p5z_labelledCongruenceMass, Finset.mul_sum, Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro t ht
    apply Finset.sum_congr rfl
    intro d hd
    by_cases hm : Nat.ModEq d (f t) N <;> simp [hm]
  have hcount : |∑ d ∈ D, rho d * p5z_labelledCongruenceMass S f (fun _ => 1) N d| ≤
      ∑ t ∈ S, ((N - f t).divisors.card : ℝ) := by
    rw [hcong]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro t ht
    have hb := P5OriginalPrimeEndpoint.sum_abs_rho_congruence_le_divisors
      D rho N (f t) (ne_of_lt (hS t ht)) hrho
    have hdistance : P5OriginalPrimeEndpoint.distance N (f t) = N - f t := by
      simp only [P5OriginalPrimeEndpoint.distance, if_pos (hS t ht).le]
    rw [hdistance] at hb
    exact (Finset.abs_sum_le_sum_abs _ _).trans hb
  have hmean : |∑ d ∈ D, rho d *
      (p5z_labelledCoprimeMass S f (fun _ => 1) d / (Nat.totient d : ℝ))| ≤
      (S.card : ℝ) * ∑ d ∈ D, 1 / (Nat.totient d : ℝ) := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro d hd
    have hc0 : 0 ≤ p5z_labelledCoprimeMass S f (fun _ => 1) d := by
      unfold p5z_labelledCoprimeMass
      positivity
    have hc : p5z_labelledCoprimeMass S f (fun _ => 1) d ≤ (S.card : ℝ) := by
      calc
        _ ≤ ∑ _t ∈ S, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro t ht
          split_ifs <;> norm_num
        _ = _ := by simp
    rw [abs_mul, abs_div, abs_of_nonneg hc0,
      abs_of_nonneg (Nat.cast_nonneg (Nat.totient d))]
    calc
      _ ≤ 1 * ((S.card : ℝ) / (Nat.totient d : ℝ)) :=
        mul_le_mul (hrho d hd)
          (div_le_div_of_nonneg_right hc (Nat.cast_nonneg _))
          (div_nonneg hc0 (Nat.cast_nonneg _)) zero_le_one
      _ = _ := by ring
  have hid : p5z_labelledDistributionError S f (fun _ => 1) N D rho =
      (∑ d ∈ D, rho d * p5z_labelledCongruenceMass S f (fun _ => 1) N d) -
        ∑ d ∈ D, rho d *
          (p5z_labelledCoprimeMass S f (fun _ => 1) d / (Nat.totient d : ℝ)) := by
    simp only [p5z_labelledDistributionError, mul_sub, Finset.sum_sub_distrib]
  rw [hid]
  exact (abs_sub _ _).trans (add_le_add hcount hmean)

/-- Uniform finite power saving for the actual repeated PP source.
The constant precedes N, all three branches, D, and the signed rho.
The source exponent is 92/125; the divisor/log fee is only 1/10. -/
theorem exists_repeatedPP_power_bound (nu : ℝ) (hnu : 0 ≤ nu) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, (1 : ℝ) ≤ N → ∀ j : Fin 3,
      ∀ D : Finset ℕ, ∀ Q : ℕ, ∀ rho : ℕ → ℝ,
        D ⊆ Finset.Icc 1 Q → (Q : ℝ) ≤ (N : ℝ) ^ nu →
        (∀ d ∈ D, |rho d| ≤ 1) →
        |Part3.primeProductSignedError 3 N N D rho (repeatedWeight j N)| ≤
          C * (N : ℝ) ^ (209 / 250 : ℝ) := by
  obtain ⟨K, hK, hTau⟩ := Part3.PolynomialResidueDivisorBound.fouvryTau_le_const_rpow
    (k := 2) (by norm_num) (show (0 : ℝ) < 1 / 10 by norm_num)
  let L : ℝ := 4 * (1 + 10 * nu)
  have hL : 0 < L := by dsimp [L]; positivity
  refine ⟨8 * (K + L), by positivity, ?_⟩
  intro N hN j D Q rho hD hQ hrho
  have hNp : (0 : ℝ) < N := zero_lt_one.trans_le hN
  have hpow : 0 ≤ (N : ℝ) ^ (1 / 10 : ℝ) := Real.rpow_nonneg hNp.le _
  have htau (u : Fin 3 → Fin (N + 1)) (hu : u ∈ repeatedTuples j N) :
      ((N - Part3.labelledProduct u).divisors.card : ℝ) ≤
        K * (N : ℝ) ^ (1 / 10 : ℝ) := by
    have hp := repeatedTuples_product_lt hu
    have hn : 0 < N - Part3.labelledProduct u := Nat.sub_pos_of_lt hp
    have ht : ((N - Part3.labelledProduct u).divisors.card : ℝ) ≤
        K * ((N - Part3.labelledProduct u : ℕ) : ℝ) ^ (1 / 10 : ℝ) := by
      simpa only [fouvryTau_two] using hTau _ hn
    exact ht.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _)
        (by exact_mod_cast Nat.sub_le N (Part3.labelledProduct u)) (by norm_num)) hK.le)
  have hsumTau : (∑ u ∈ repeatedTuples j N, ((N - Part3.labelledProduct u).divisors.card : ℝ)) ≤
      ((repeatedTuples j N).card : ℝ) * (K * (N : ℝ) ^ (1 / 10 : ℝ)) := by
    simpa only [Finset.sum_const, nsmul_eq_mul] using Finset.sum_le_sum htau
  have hmax : max (1 : ℝ) (Q : ℝ) ≤ (N : ℝ) ^ nu :=
    max_le (Real.one_le_rpow hN hnu) hQ
  have hlogQ : Real.log (max 1 (Q : ℝ)) ≤ nu * Real.log (N : ℝ) := by
    have h := Real.log_le_log (zero_lt_one.trans_le (le_max_left _ _)) hmax
    rwa [Real.log_rpow hNp] at h
  have hlog : Real.log (N : ℝ) ≤ 10 * (N : ℝ) ^ (1 / 10 : ℝ) := by
    have h := Real.log_le_rpow_div hNp.le (show (0 : ℝ) < 1 / 10 by norm_num)
    convert h using 1 <;> ring
  have hone : 1 ≤ (N : ℝ) ^ (1 / 10 : ℝ) := Real.one_le_rpow hN (by norm_num)
  have hlogpay : 4 * (1 + Real.log (max 1 (Q : ℝ))) ≤
      L * (N : ℝ) ^ (1 / 10 : ℝ) := by
    have hnulog := mul_le_mul_of_nonneg_left hlog hnu
    dsimp [L]
    nlinarith only [hlogQ, hnulog, hone]
  have hphi := (sum_reciprocal_totient_subset_le_log D Q hD).trans hlogpay
  rw [repeatedPP_eq_labelled]
  calc
    _ ≤ (∑ u ∈ repeatedTuples j N, ((N - Part3.labelledProduct u).divisors.card : ℝ)) +
        ((repeatedTuples j N).card : ℝ) * ∑ d ∈ D, 1 / (Nat.totient d : ℝ) :=
      abs_labelled_error_le_divisors _ _ _ _ _ (fun _ hu => repeatedTuples_product_lt hu) hrho
    _ ≤ ((repeatedTuples j N).card : ℝ) * (K * (N : ℝ) ^ (1 / 10 : ℝ)) +
        ((repeatedTuples j N).card : ℝ) * (L * (N : ℝ) ^ (1 / 10 : ℝ)) :=
      add_le_add hsumTau (mul_le_mul_of_nonneg_left hphi (Nat.cast_nonneg _))
    _ = ((repeatedTuples j N).card : ℝ) * ((K + L) * (N : ℝ) ^ (1 / 10 : ℝ)) := by ring
    _ ≤ (8 * (N : ℝ) ^ (92 / 125 : ℝ)) * ((K + L) * (N : ℝ) ^ (1 / 10 : ℝ)) :=
      mul_le_mul_of_nonneg_right (repeatedTuples_card_le_power j hN)
        (mul_nonneg (add_nonneg hK.le hL.le) hpow)
    _ = (8 * (K + L)) * (N : ℝ) ^ (209 / 250 : ℝ) := by
      rw [show (209 / 250 : ℝ) = 92 / 125 + 1 / 10 by norm_num, Real.rpow_add hNp]
      ring

/-- Every fixed natural logarithmic accuracy is paid. This is stronger
than the A=3 estimate required by the original h9 branch port. -/
theorem eventually_repeatedPP_log_bound (nu : ℝ) (hnu : 0 ≤ nu) (A : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ j : Fin 3, ∀ D : Finset ℕ, ∀ Q : ℕ,
      ∀ rho : ℕ → ℝ, D ⊆ Finset.Icc 1 Q → (Q : ℝ) ≤ (N : ℝ) ^ nu →
        (∀ d ∈ D, |rho d| ≤ 1) →
        |Part3.primeProductSignedError 3 N N D rho (repeatedWeight j N)| ≤
          (N : ℝ) / Real.log (N : ℝ) ^ A := by
  obtain ⟨C, hC, hfinite⟩ := exists_repeatedPP_power_bound nu hnu
  have hlim : Tendsto (fun N : ℕ =>
      C * (Real.log (N : ℝ) ^ A / (N : ℝ) ^ (41 / 250 : ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_nat_log_pow_div_rpow A (show (0 : ℝ) < 41 / 250 by norm_num)).const_mul C
  have hsmall := hlim.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  filter_upwards [hsmall, eventually_ge_atTop (2 : ℕ)] with N hsmallN hN
  intro j D Q rho hD hQ hrho
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hNp : (0 : ℝ) < N := zero_lt_one.trans hNr
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos hNr
  have hexp : (N : ℝ) ^ (41 / 250 : ℝ) * (N : ℝ) ^ (209 / 250 : ℝ) = N := by
    rw [← Real.rpow_add hNp, show (41 / 250 : ℝ) + 209 / 250 = 1 by norm_num,
      Real.rpow_one]
  have hsmall' : C * Real.log (N : ℝ) ^ A ≤ (N : ℝ) ^ (41 / 250 : ℝ) := by
    apply (div_le_one (Real.rpow_pos_of_pos hNp _)).mp
    simpa only [mul_div_assoc] using hsmallN.le
  have hpay : C * (N : ℝ) ^ (209 / 250 : ℝ) ≤
      (N : ℝ) / Real.log (N : ℝ) ^ A := by
    apply (le_div_iff₀ (pow_pos hlog A)).mpr
    calc
      _ = (C * Real.log (N : ℝ) ^ A) * (N : ℝ) ^ (209 / 250 : ℝ) := by ring
      _ ≤ (N : ℝ) ^ (41 / 250 : ℝ) * (N : ℝ) ^ (209 / 250 : ℝ) :=
        mul_le_mul_of_nonneg_right hsmall' (Real.rpow_nonneg hNp.le _)
      _ = N := hexp
  exact (hfinite N hNr.le j D Q rho hD hQ hrho).trans hpay

end
end ImbalancedChen.P5OriginalU9RepeatedPP
