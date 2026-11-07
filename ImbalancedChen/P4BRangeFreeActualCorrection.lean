import ImbalancedChen.P4BPrimorialDivisorEnvelope
import ImbalancedChen.P4BWeightedHyperbolaSlotDecay
import ImbalancedChen.P4BActualSmoothPowerTail

/-!
# The actual same-rho arithmetic correction without a q-size premise

SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

The new primorial prime-divisor envelope replaces the logarithm of the
largest active modulus. The weighted complete-product hyperbola estimate
then pays the correction without assuming a source mass, a polynomial
modulus range, rough coprime-zero, a density bound, or a PP estimate.
The final result is uniform in the actual compact real-b family.
The original full22 range and wholebox licensing remain OPEN P3 obligations.
-/

namespace ImbalancedChen.P4BRangeFreeActualCorrection

noncomputable section
open Filter Topology
open scoped Classical BigOperators
open Part3 P4B P4BLabelledOuterPushforward P4BNoncoprimeSlotTail
open P4BPrimorialDivisorEnvelope P4BWeightedHyperbolaSlotDecay
open P4BActualCompactSmoothFamily P4BActualSmoothPowerTail

theorem noncoprime_absolute_mass_le_prime_slots {N : ℕ}
    (t : Fin 2 → Fin (N + 1)) (ht : t ∈ labelledPrimeTuples 2 N)
    (D : Finset ℕ) (rho : ℕ → ℝ) :
    (∑ d ∈ D, if Nat.Coprime (labelledProduct t) d then 0
      else |rho d| / (Nat.totient d : ℝ)) ≤
      ∑ i : Fin 2, ∑ d ∈ D,
        if (t i).val ∣ d then |rho d| / (Nat.totient d : ℝ) else 0 := by
  have hp : ∀ i, Nat.Prime (t i).val := (Finset.mem_filter.mp ht).2
  have hpoint (d : ℕ) :
      (if Nat.Coprime (labelledProduct t) d then 0
        else |rho d| / (Nat.totient d : ℝ)) ≤
      ∑ i : Fin 2, if (t i).val ∣ d then |rho d| / (Nat.totient d : ℝ) else 0 := by
    by_cases hc : Nat.Coprime (labelledProduct t) d
    · rw [if_pos hc]
      exact Finset.sum_nonneg (fun _ _ => by positivity)
    · have hex : ∃ i : Fin 2, ¬Nat.Coprime (t i).val d := by
        by_contra hn
        apply hc
        apply Nat.coprime_prod_left_iff.mpr
        intro i _hi
        by_contra hbad
        exact hn ⟨i, hbad⟩
      obtain ⟨i, hi⟩ := hex
      have hdiv : (t i).val ∣ d := by
        by_contra hnot
        exact hi ((hp i).coprime_iff_not_dvd.mpr hnot)
      have hsingle := Finset.single_le_sum
        (fun j (_hj : j ∈ (Finset.univ : Finset (Fin 2))) =>
          show 0 ≤ (if (t j).val ∣ d then |rho d| / (Nat.totient d : ℝ) else 0) by positivity)
        (Finset.mem_univ i)
      simpa only [if_neg hc, if_pos hdiv] using hsingle
  exact (Finset.sum_le_sum (fun d _hd => hpoint d)).trans_eq Finset.sum_comm

/-- A genuine complete-product finite bound with the original actual rho.
The constant precedes all policies and parameters. There is no bound on q. -/
theorem exists_actual_upper_outer_hyperbola_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ nu r epsilon : ℝ, 0 < nu → 0 < r → epsilon ^ 2 ≤ r →
      ∀ (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ) (N : ℕ), Even N → 2 ≤ N →
      ∀ K L : ℕ, 2 ≤ L → ∀ V : (Fin 2 → Fin (N + 1)) → ℝ,
      ∀ B : ℝ, 0 ≤ B →
      (∀ t ∈ labelledPrimeTuples 2 N, |V t| ≤ B) →
      (∀ t ∈ labelledPrimeTuples 2 N, V t ≠ 0 → ∀ i, L ≤ (t i).val) →
      (∀ t ∈ labelledPrimeTuples 2 N, V t ≠ 0 → labelledProduct t ≤ K) →
      |∑ d ∈ attachedUpperModuli nu r epsilon retain cap N,
        attachedUpperCoefficient nu r epsilon retain cap N d *
          ((finiteCoprimeMass (productCarrier N) (productWeight N V) d -
            finiteSourceMass (productCarrier N) (productWeight N V)) / (Nat.totient d : ℝ))| ≤
        (4 * C * (nu * r + 1) * Real.log (N : ℝ)) *
          (B * (K : ℝ) / ((L : ℝ) - 1)) := by
  obtain ⟨C, hC, henvelope⟩ := exists_actual_upper_prime_divisor_envelope
  refine ⟨C, hC, ?_⟩
  intro nu r epsilon hnu hr hepsilon retain cap N hEven hN K L hL V B hB hV hrough hproduct
  let D := attachedUpperModuli nu r epsilon retain cap N
  let rho := attachedUpperCoefficient nu r epsilon retain cap N
  let A : ℝ := C * (nu * r + 1) * Real.log (N : ℝ)
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hA : 0 ≤ A := by
    dsimp only [A]
    exact mul_nonneg (mul_nonneg hC.le (by positivity)) (Real.log_pos hN1).le
  have hslot (t : Fin 2 → Fin (N + 1)) (ht : t ∈ labelledPrimeTuples 2 N) :
      (∑ d ∈ D, if Nat.Coprime (labelledProduct t) d then 0
        else |rho d| / (Nat.totient d : ℝ)) ≤
      A * ∑ i : Fin 2, 1 / (((t i).val : ℝ) - 1) := by
    apply (noncoprime_absolute_mass_le_prime_slots t ht D rho).trans
    calc
      _ ≤ ∑ i : Fin 2, A / (((t i).val : ℝ) - 1) := by
        apply Finset.sum_le_sum
        intro i _hi
        exact henvelope nu r epsilon hnu hr hepsilon retain cap N hEven hN
          (t i).val ((Finset.mem_filter.mp ht).2 i)
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _hi
        ring
  have hfour (t : Fin 2 → Fin (N + 1)) :
      (∑ i : Fin 2, 4 / (((t i).val : ℝ) - 1)) =
        4 * ∑ i : Fin 2, 1 / (((t i).val : ℝ) - 1) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    ring
  rw [outer_correction_eq_labelled, p5z_markedCoprimeCorrection_eq_neg_sum, abs_neg]
  calc
    _ ≤ ∑ t ∈ labelledPrimeTuples 2 N, ∑ d ∈ D,
        |V t * (rho d *
          (if Nat.Coprime (labelledProduct t) d then 0 else 1 / (Nat.totient d : ℝ)))| := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      exact Finset.sum_le_sum (fun _ _ => Finset.abs_sum_le_sum_abs _ _)
    _ = ∑ t ∈ labelledPrimeTuples 2 N, |V t| *
        (∑ d ∈ D, if Nat.Coprime (labelledProduct t) d then 0
          else |rho d| / (Nat.totient d : ℝ)) := by
      apply Finset.sum_congr rfl
      intro t _ht
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _hd
      by_cases hc : Nat.Coprime (labelledProduct t) d
      · simp only [if_pos hc, mul_zero, abs_zero]
      · simp only [if_neg hc, abs_mul, abs_div, abs_one,
          abs_of_nonneg (Nat.cast_nonneg (Nat.totient d))]
        ring
    _ ≤ ∑ t ∈ labelledPrimeTuples 2 N,
        |V t| * (A * ∑ i : Fin 2, 1 / (((t i).val : ℝ) - 1)) :=
      Finset.sum_le_sum (fun t ht => mul_le_mul_of_nonneg_left (hslot t ht) (abs_nonneg _))
    _ = (A / 4) * ∑ t ∈ labelledPrimeTuples 2 N,
        |V t| * (∑ i : Fin 2, 4 / (((t i).val : ℝ) - 1)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _ht
      rw [hfour]
      ring
    _ ≤ (A / 4) * (16 * B * (K : ℝ) / ((L : ℝ) - 1)) :=
      mul_le_mul_of_nonneg_left
        (full_weighted_slot_cost_le hL V B hB hV hrough hproduct) (div_nonneg hA (by norm_num))
    _ = _ := by dsimp only [A]; ring

/-- Floor and ceiling losses in the genuine physical complete-product cap. -/
private theorem physical_hyperbola_rounded_ratio_le
    {N : ℕ} (hN : 2 ≤ N) (width theta : ℝ) (hH : (4 : ℝ) ≤ (N : ℝ) ^ theta) :
    (Nat.ceil (Real.exp width * (N : ℝ)) : ℝ) /
        ((Nat.floor ((N : ℝ) ^ theta) : ℝ) - 1) ≤
      2 * (Real.exp width + 1) * (N : ℝ) ^ (1 - theta) := by
  let H := (N : ℝ) ^ theta
  have hHpos : 0 < H := by dsimp only [H]; linarith only [hH]
  have hf : H < (Nat.floor H : ℝ) + 1 := Nat.lt_floor_add_one H
  have hd : H / 2 ≤ (Nat.floor H : ℝ) - 1 := by
    have hfour : (4 : ℝ) ≤ H := hH
    linarith only [hf, hfour]
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hceil : (Nat.ceil (Real.exp width * (N : ℝ)) : ℝ) ≤
      (Real.exp width + 1) * (N : ℝ) := by
    have hc := (Nat.ceil_lt_add_one
      (mul_nonneg (Real.exp_pos width).le (Nat.cast_nonneg N))).le
    nlinarith only [hc, hNreal]
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  calc
    _ ≤ (Nat.ceil (Real.exp width * (N : ℝ)) : ℝ) / (H / 2) :=
      div_le_div_of_nonneg_left (Nat.cast_nonneg _) (half_pos hHpos) hd
    _ ≤ ((Real.exp width + 1) * (N : ℝ)) / (H / 2) :=
      div_le_div_of_nonneg_right hceil (half_pos hHpos).le
    _ = 2 * (Real.exp width + 1) * ((N : ℝ) / (N : ℝ) ^ theta) := by
      dsimp only [H]
      ring
    _ = _ := by rw [Real.rpow_sub hNpos, Real.rpow_one]

/-- The full arithmetic correction is now unconditionally negligible for
the literal attached coefficient and actual smooth family. No polynomial
range, source mean, coprime-zero, density or signed PP input occurs. -/
theorem eventually_actual_compact_smooth_correction_le
    {b0 b1 kappa kappaZero theta precision widthMax : ℝ}
    (F : ActualCompactSmoothFamily b0 b1 kappa kappaZero theta precision widthMax)
    (htheta : 0 < theta) (nu r epsilon : ℝ) (hnu : 0 < nu) (hr : 0 < r)
    (hepsilon : epsilon ^ 2 ≤ r)
    (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ)
    (tolerance : ℝ) (htolerance : 0 < tolerance) :
    ∀ᶠ N : ℕ in atTop, Even N → ∀ b : ℝ, b0 ≤ b → b ≤ b1 →
      |actualSmoothOuterCorrection b kappa F.width nu r epsilon retain cap N| ≤
        tolerance * singularNormalization N := by
  obtain ⟨C, hC, hfinite⟩ := exists_actual_upper_outer_hyperbola_bound
  let c : ℝ := 8 * C * (nu * r + 1) * (Real.exp F.width + 1)
  have hlarge : ∀ᶠ N : ℕ in atTop, (4 : ℝ) ≤ (N : ℝ) ^ theta :=
    ((tendsto_rpow_atTop htheta).comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop 4)
  filter_upwards [hlarge, eventually_ge_atTop (2 : ℕ),
    eventually_powerLog_le_singularNormalization c (1 - theta) 1
      (by linarith only [htheta]) tolerance htolerance] with N hH hN hbudget
  intro hEven b hb0 hb1
  let L : ℕ := Nat.floor ((N : ℝ) ^ theta)
  let K : ℕ := Nat.ceil (Real.exp F.width * (N : ℝ))
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hNpos : (0 : ℝ) < N := zero_lt_one.trans hN1
  have hL : 2 ≤ L :=
    (Nat.le_floor_iff (Real.rpow_nonneg hNpos.le theta)).mpr (by linarith only [hH])
  have hLpow : (L : ℝ) ≤ (N : ℝ) ^ theta := Nat.floor_le (Real.rpow_nonneg hNpos.le theta)
  have hK : Real.exp F.width * (N : ℝ) ≤ (K : ℝ) := Nat.le_ceil _
  have hV : ∀ t ∈ labelledPrimeTuples 2 N,
      |smoothPhysicalPairOuterRamp b N (manuscriptHalfProductCutoff kappa N) F.width t| ≤ 1 := by
    intro t _ht
    have hbnd := smoothPhysicalPairOuterRamp_bounds b N
      (manuscriptHalfProductCutoff kappa N) F.width t
    simpa only [abs_of_nonneg hbnd.1] using hbnd.2
  have hrough : ∀ t ∈ labelledPrimeTuples 2 N,
      smoothPhysicalPairOuterRamp b N (manuscriptHalfProductCutoff kappa N) F.width t ≠ 0 →
        ∀ i, L ≤ (t i).val := by
    intro t ht hn i
    have hp := primeTuplePoint_mem_positivePrimeOrthant ht
    have hn' : smoothPrimeVariableProfile b N (manuscriptHalfProductCutoff kappa N)
        F.width (primeTuplePoint N t) ≠ 0 := by
      simpa only [smoothPhysicalPairOuterRamp_eq_primeVariableProfile] using hn
    have hprime := F.prime_lower_support b hb0 hb1 N hN (primeTuplePoint N t) hp hn' i
    have hreal := hLpow.trans_lt hprime
    change (L : ℝ) < ((t i).val : ℝ) at hreal
    exact_mod_cast hreal.le
  have hproduct : ∀ t ∈ labelledPrimeTuples 2 N,
      smoothPhysicalPairOuterRamp b N (manuscriptHalfProductCutoff kappa N) F.width t ≠ 0 →
        labelledProduct t ≤ K := by
    intro t ht hn
    have hp := primeTuplePoint_mem_positivePrimeOrthant ht
    have hn' : smoothPrimeVariableProfile b N (manuscriptHalfProductCutoff kappa N)
        F.width (primeTuplePoint N t) ≠ 0 := by
      simpa only [smoothPhysicalPairOuterRamp_eq_primeVariableProfile] using hn
    have hprod := (F.product_window b hb0 hb1 N hN (primeTuplePoint N t) hp hn').2
    have hreal : (labelledProduct t : ℝ) ≤ (K : ℝ) := by
      simpa only [labelledProduct, Fin.prod_univ_two, Nat.cast_mul, primeTuplePoint] using
        (hprod.trans_le hK).le
    exact_mod_cast hreal
  have hbound := hfinite nu r epsilon hnu hr hepsilon retain cap N hEven hN
    K L hL (smoothPhysicalPairOuterRamp b N (manuscriptHalfProductCutoff kappa N) F.width)
    1 (by norm_num) hV hrough hproduct
  have hbound' : |actualSmoothOuterCorrection b kappa F.width nu r epsilon retain cap N| ≤
      (4 * C * (nu * r + 1) * Real.log (N : ℝ)) * ((K : ℝ) / ((L : ℝ) - 1)) := by
    simpa only [actualSmoothOuterCorrection, one_mul] using hbound
  have hratio : (K : ℝ) / ((L : ℝ) - 1) ≤
      2 * (Real.exp F.width + 1) * (N : ℝ) ^ (1 - theta) :=
    physical_hyperbola_rounded_ratio_le hN F.width theta hH
  calc
    _ ≤ (4 * C * (nu * r + 1) * Real.log (N : ℝ)) *
        ((K : ℝ) / ((L : ℝ) - 1)) := hbound'
    _ ≤ (4 * C * (nu * r + 1) * Real.log (N : ℝ)) *
        (2 * (Real.exp F.width + 1) * (N : ℝ) ^ (1 - theta)) :=
      mul_le_mul_of_nonneg_left hratio
        (mul_nonneg (by positivity) (Real.log_pos hN1).le)
    _ = c * (N : ℝ) ^ (1 - theta) * (Real.log (N : ℝ)) ^ (1 : ℕ) := by
      dsimp only [c]
      rw [pow_one]
      ring
    _ ≤ _ := hbudget

end
end ImbalancedChen.P4BRangeFreeActualCorrection
