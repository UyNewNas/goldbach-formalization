import ImbalancedChen.ChenQuotientPrimeSource
import ImbalancedChen.ChenInitialCorrectionBudget
import ImbalancedChen.RoughSquareException

/-!
# Paid finite corrections for the actual single-prime harmonic windows

The manuscript window is [A,U), excludes prime divisors of N, and uses
1/(p-1). The standard continuous-test Mertens window is (A,U] with 1/p.
The three changes below are bounded explicitly. No limiting prime-sum
estimate is a premise. Held source candidate; not compiled.
-/

namespace ImbalancedChen

noncomputable section
open scoped BigOperators
open Classical

/-- Inclusive-lower, strict-upper prime window before the centre mask. -/
def chenPrimeHarmonicWindow (N : ℕ) (A U : ℝ) : Finset ℕ :=
  (chenPrimePrefix N).filter (fun p => A ≤ (p : ℝ) ∧ (p : ℝ) < U)

/-- Opposite half-open convention used by the approved Mertens supplier. -/
def chenPrimeHarmonicSupplierWindow (N : ℕ) (A U : ℝ) : Finset ℕ :=
  (chenPrimePrefix N).filter (fun p => A < (p : ℝ) ∧ (p : ℝ) ≤ U)

/-- The actual selector has exactly the original centre-divisor mask. -/
theorem chenSinglePrimeSelector_eq_harmonic_filter (N : ℕ) (A U : ℝ) :
    chenSinglePrimeSelector N A U =
      (chenPrimeHarmonicWindow N A U).filter (fun p => ¬p ∣ N) := by
  unfold chenSinglePrimeSelector
  rw [chenAdditivePrimeCarrier_eq_prefix_filter]
  ext p
  simp only [chenPrimeHarmonicWindow, Finset.mem_filter]
  tauto

/-- At most two endpoint atoms change when switching half-open conventions. -/
theorem chen_prime_window_endpoint_bound (P : Finset ℕ) (g : ℕ → ℝ)
    {A U E : ℝ} (hAU : A < U) (hE : 0 ≤ E)
    (hg : ∀ p ∈ P, (p : ℝ) = A ∨ (p : ℝ) = U → |g p| ≤ E) :
    |(∑ p ∈ P.filter (fun p : ℕ => A ≤ (p : ℝ) ∧ (p : ℝ) < U), g p) -
      ∑ p ∈ P.filter (fun p : ℕ => A < (p : ℝ) ∧ (p : ℝ) ≤ U), g p| ≤ 2 * E := by
  let B := P.filter (fun p : ℕ => (p : ℝ) = A ∨ (p : ℝ) = U)
  have hsingle (x : ℝ) : ((P.filter (fun p : ℕ => (p : ℝ) = x)).card : ℝ) ≤ 1 := by
    have hn : (P.filter (fun p : ℕ => (p : ℝ) = x)).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro p hp q hq
      have heq : (p : ℝ) = (q : ℝ) :=
        (Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hq).2.symm
      exact_mod_cast heq
    exact_mod_cast hn
  have hB : (B.card : ℝ) ≤ 2 := by
    have heq : B = (P.filter (fun p : ℕ => (p : ℝ) = A)) ∪
        (P.filter (fun p : ℕ => (p : ℝ) = U)) := by
      ext p
      simp only [B, Finset.mem_filter, Finset.mem_union]
      tauto
    rw [heq]
    have hc : (((P.filter (fun p : ℕ => (p : ℝ) = A)) ∪
        (P.filter (fun p : ℕ => (p : ℝ) = U))).card : ℝ) ≤
        ((P.filter (fun p : ℕ => (p : ℝ) = A)).card : ℝ) +
          ((P.filter (fun p : ℕ => (p : ℝ) = U)).card : ℝ) := by
      exact_mod_cast Finset.card_union_le
        (P.filter (fun p : ℕ => (p : ℝ) = A)) (P.filter (fun p : ℕ => (p : ℝ) = U))
    linarith [hsingle A, hsingle U]
  have hterm : ∀ p ∈ P,
      |(if A ≤ (p : ℝ) ∧ (p : ℝ) < U then g p else 0) -
        (if A < (p : ℝ) ∧ (p : ℝ) ≤ U then g p else 0)| ≤
        if (p : ℝ) = A ∨ (p : ℝ) = U then E else 0 := by
    intro p hp
    by_cases hpA : (p : ℝ) = A
    · have hl : A ≤ (p : ℝ) ∧ (p : ℝ) < U := by rw [hpA]; exact ⟨le_rfl, hAU⟩
      have hr : ¬(A < (p : ℝ) ∧ (p : ℝ) ≤ U) := by rw [hpA]; simp
      rw [if_pos hl, if_neg hr, sub_zero, if_pos (Or.inl hpA)]
      exact hg p hp (Or.inl hpA)
    · by_cases hpU : (p : ℝ) = U
      · have hl : ¬(A ≤ (p : ℝ) ∧ (p : ℝ) < U) := by rw [hpU]; simp
        have hr : A < (p : ℝ) ∧ (p : ℝ) ≤ U := by rw [hpU]; exact ⟨hAU, le_rfl⟩
        rw [if_neg hl, if_pos hr, zero_sub, abs_neg, if_pos (Or.inr hpU)]
        exact hg p hp (Or.inr hpU)
      · have hnone : ¬((p : ℝ) = A ∨ (p : ℝ) = U) := by tauto
        have heq : (A ≤ (p : ℝ) ∧ (p : ℝ) < U) ↔
            (A < (p : ℝ) ∧ (p : ℝ) ≤ U) := by
          constructor
          · intro h
            exact ⟨lt_of_le_of_ne h.1 (Ne.symm hpA), h.2.le⟩
          · intro h
            exact ⟨h.1.le, lt_of_le_of_ne h.2 hpU⟩
        rw [if_neg hnone]
        simp only [heq, sub_self, abs_zero, le_refl]
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ p ∈ P,
        |(if A ≤ (p : ℝ) ∧ (p : ℝ) < U then g p else 0) -
          (if A < (p : ℝ) ∧ (p : ℝ) ≤ U then g p else 0)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ P, if (p : ℝ) = A ∨ (p : ℝ) = U then E else 0 :=
      Finset.sum_le_sum hterm
    _ = (B.card : ℝ) * E := by
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul]
      rfl
    _ ≤ 2 * E := mul_le_mul_of_nonneg_right hB hE

/-- Varying-centre removal is paid by the actual distinct-prime count. -/
theorem chen_prime_centre_removal_bound {N : ℕ} (hN : 0 < N)
    (T : Finset ℕ) (g : ℕ → ℝ) {E : ℝ} (hE : 0 ≤ E)
    (hp : ∀ p ∈ T, Nat.Prime p)
    (hg : ∀ p ∈ T, p ∣ N → |g p| ≤ E) :
    |(∑ p ∈ T.filter (fun p => ¬p ∣ N), g p) - ∑ p ∈ T, g p| ≤
      E * (Real.log (N : ℝ) / Real.log 2) := by
  have hpart := Finset.sum_filter_add_sum_filter_not T (fun p => p ∣ N) g
  have heq : (∑ p ∈ T.filter (fun p => ¬p ∣ N), g p) - ∑ p ∈ T, g p =
      -(∑ p ∈ T.filter (fun p => p ∣ N), g p) := by linarith
  have hsub : T.filter (fun p => p ∣ N) ⊆ N.primeFactors := by
    intro p h
    obtain ⟨ht, hdiv⟩ := Finset.mem_filter.mp h
    exact Nat.mem_primeFactors.mpr ⟨hp p ht, hdiv, hN.ne'⟩
  have hcard : ((T.filter (fun p => p ∣ N)).card : ℝ) ≤
      Real.log (N : ℝ) / Real.log 2 := by
    have hc : ((T.filter (fun p => p ∣ N)).card : ℝ) ≤
        (N.primeFactors.card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
    exact hc.trans (chen_primeFactors_card_le_log hN)
  rw [heq, abs_neg]
  calc
    _ ≤ ∑ p ∈ T.filter (fun p => p ∣ N), |g p| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _p ∈ T.filter (fun p => p ∣ N), E := by
      apply Finset.sum_le_sum
      intro p h
      exact hg p (Finset.mem_filter.mp h).1 (Finset.mem_filter.mp h).2
    _ = ((T.filter (fun p => p ∣ N)).card : ℝ) * E := by simp
    _ ≤ (Real.log (N : ℝ) / Real.log 2) * E :=
      mul_le_mul_of_nonneg_right hcard hE
    _ = _ := mul_comm _ _

private theorem chen_harmonic_term_bound {A x M v : ℝ}
    (hA : 2 ≤ A) (hx : A ≤ x) (hM : 0 ≤ M) (hv : |v| ≤ M) :
    |v / (x - 1)| ≤ 2 * M / A := by
  have hx1 : 0 < x - 1 := by linarith
  have hApos : 0 < A := by linarith
  have hrec : 1 / (x - 1) ≤ 2 / A := by
    apply (div_le_div_iff₀ hx1 hApos).mpr
    linarith
  rw [abs_div, abs_of_pos hx1]
  calc
    _ ≤ M / (x - 1) := div_le_div_of_nonneg_right hv hx1.le
    _ = M * (1 / (x - 1)) := by ring
    _ ≤ M * (2 / A) := mul_le_mul_of_nonneg_left hrec hM
    _ = _ := by ring

private theorem chen_harmonic_reciprocal_difference {p : ℕ} (hp : Nat.Prime p)
    {M v : ℝ} (hM : 0 ≤ M) (hv : |v| ≤ M) :
    |v / ((p : ℝ) - 1) - v / (p : ℝ)| ≤ 2 * M / (p : ℝ) ^ 2 := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hp1 : 0 < (p : ℝ) - 1 := by linarith
  have heq : v / ((p : ℝ) - 1) - v / (p : ℝ) =
      v / ((p : ℝ) * ((p : ℝ) - 1)) := by
    field_simp [hp0.ne', hp1.ne']
    ring
  have hrec : 1 / ((p : ℝ) * ((p : ℝ) - 1)) ≤ 2 / (p : ℝ) ^ 2 := by
    apply (div_le_div_iff₀ (mul_pos hp0 hp1) (pow_pos hp0 2)).mpr
    nlinarith
  rw [heq, abs_div, abs_of_pos (mul_pos hp0 hp1)]
  calc
    _ ≤ M / ((p : ℝ) * ((p : ℝ) - 1)) :=
      div_le_div_of_nonneg_right hv (mul_pos hp0 hp1).le
    _ = M * (1 / ((p : ℝ) * ((p : ℝ) - 1))) := by ring
    _ ≤ M * (2 / (p : ℝ) ^ 2) := mul_le_mul_of_nonneg_left hrec hM
    _ = _ := by ring

/-- The denominator correction is controlled by the already proved,
telescoping reciprocal-square tail, not by the number of selected primes. -/
theorem chen_prime_reciprocal_shift_bound (N : ℕ) (T : Finset ℕ) (f : ℕ → ℝ)
    {A M : ℝ} (hA : 2 ≤ A) (hM : 0 ≤ M)
    (hT : T ⊆ chenPrimeHarmonicWindow N A (N + 1))
    (hf : ∀ p ∈ T, |f p| ≤ M) :
    |(∑ p ∈ T, f p / ((p : ℝ) - 1)) - ∑ p ∈ T, f p / (p : ℝ)| ≤
      4 * M / A := by
  have hceil : 2 ≤ Nat.ceil A :=
    Nat.add_one_le_ceil_iff.mpr (by simpa using (show 1 < A by linarith))
  have hsub : T ⊆ Finset.Icc (Nat.ceil A) N := by
    intro p hp
    obtain ⟨hpN, hpA, _⟩ := Finset.mem_filter.mp (hT hp)
    exact Finset.mem_Icc.mpr ⟨Nat.ceil_le.mpr hpA, (mem_chenPrimePrefix.mp hpN).1⟩
  have htail : (∑ p ∈ T, 1 / (p : ℝ) ^ 2) ≤ 2 / A := by
    have hs : (∑ p ∈ T, 1 / (p : ℝ) ^ 2) ≤
        ∑ p ∈ Finset.Icc (Nat.ceil A) N, 1 / (p : ℝ) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    have hrec : 1 / (A - 1) ≤ 2 / A := by
      apply (div_le_div_iff₀ (by linarith : 0 < A - 1) (by linarith : 0 < A)).mpr
      linarith
    exact hs.trans ((reciprocalSquare_Icc_tail_le N hceil).trans
      ((div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1)
        (by linarith : 0 < A - 1) (sub_le_sub_right (Nat.le_ceil A) 1)).trans hrec))
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ p ∈ T, |f p / ((p : ℝ) - 1) - f p / (p : ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ T, 2 * M / (p : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro p hp
      exact chen_harmonic_reciprocal_difference
        (mem_chenPrimePrefix.mp (Finset.mem_filter.mp (hT hp)).1).2 hM (hf p hp)
    _ = (2 * M) * ∑ p ∈ T, 1 / (p : ℝ) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      ring
    _ ≤ (2 * M) * (2 / A) := mul_le_mul_of_nonneg_left htail (by positivity)
    _ = _ := by ring

/-- All three literal changes are paid. The test may depend arbitrarily on
N; only its displayed finite-window bound is used here. -/
theorem chenSinglePrimeHarmonic_difference_le (N : ℕ) (f : ℕ → ℝ)
    {A U M : ℝ} (hN : 0 < N) (hA : 2 ≤ A) (hAU : A < U) (hM : 0 ≤ M)
    (hf : ∀ p ∈ chenPrimePrefix N, A ≤ (p : ℝ) → (p : ℝ) ≤ U → |f p| ≤ M) :
    |(∑ p ∈ chenSinglePrimeSelector N A U, f p / ((p : ℝ) - 1)) -
      ∑ p ∈ chenPrimeHarmonicSupplierWindow N A U, f p / (p : ℝ)| ≤
      (2 * M) * (Real.log (N : ℝ) / Real.log 2) / A + 6 * M / A := by
  let T := chenPrimeHarmonicWindow N A U
  let X := ∑ p ∈ chenSinglePrimeSelector N A U, f p / ((p : ℝ) - 1)
  let Y := ∑ p ∈ T, f p / ((p : ℝ) - 1)
  let Z := ∑ p ∈ T, f p / (p : ℝ)
  let W := ∑ p ∈ chenPrimeHarmonicSupplierWindow N A U, f p / (p : ℝ)
  have hcentre : |X - Y| ≤ (2 * M / A) * (Real.log (N : ℝ) / Real.log 2) := by
    dsimp [X, Y]
    rw [chenSinglePrimeSelector_eq_harmonic_filter]
    apply chen_prime_centre_removal_bound hN T _ (by positivity)
    · intro p hp
      exact (mem_chenPrimePrefix.mp (Finset.mem_filter.mp hp).1).2
    · intro p hp _
      obtain ⟨hpN, hpA, hpU⟩ := Finset.mem_filter.mp hp
      exact chen_harmonic_term_bound hA hpA hM (hf p hpN hpA hpU.le)
  have hshift : |Y - Z| ≤ 4 * M / A := by
    apply chen_prime_reciprocal_shift_bound N T f hA hM
    · intro p hp
      obtain ⟨hpN, hpA, _⟩ := Finset.mem_filter.mp hp
      have hle : (p : ℝ) ≤ N := by exact_mod_cast (mem_chenPrimePrefix.mp hpN).1
      exact Finset.mem_filter.mpr ⟨hpN, hpA, by linarith⟩
    · intro p hp
      obtain ⟨hpN, hpA, hpU⟩ := Finset.mem_filter.mp hp
      exact hf p hpN hpA hpU.le
  have hend : |Z - W| ≤ 2 * (M / A) := by
    apply chen_prime_window_endpoint_bound (chenPrimePrefix N) (fun p => f p / (p : ℝ))
      hAU (by positivity)
    intro p hp hboundary
    have hpA : A ≤ (p : ℝ) := by rcases hboundary with h | h <;> rw [h] <;> linarith
    have hpU : (p : ℝ) ≤ U := by rcases hboundary with h | h <;> rw [h] <;> linarith
    have hp0 : (0 : ℝ) < p := by linarith
    rw [abs_div, abs_of_pos hp0]
    exact (div_le_div_of_nonneg_right (hf p hp hpA hpU) hp0.le).trans
      (div_le_div_of_nonneg_left hM (by linarith : 0 < A) hpA)
  change |X - W| ≤ _
  calc
    _ ≤ |X - Y| + |Y - W| := abs_sub_le _ _ _
    _ ≤ |X - Y| + (|Y - Z| + |Z - W|) :=
      add_le_add le_rfl (abs_sub_le _ _ _)
    _ ≤ (2 * M / A) * (Real.log (N : ℝ) / Real.log 2) +
        (4 * M / A + 2 * (M / A)) := add_le_add hcentre (add_le_add hshift hend)
    _ = _ := by ring

end

end ImbalancedChen
