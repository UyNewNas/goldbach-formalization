import ImbalancedChen.P2EnhancedNegativeChildModulusPrimePayment

/-! SOURCE ONLY / UNCOMPILED / ZERO CREDIT.
The same physical signed rho has a logarithmic reciprocal-totient norm
relative to the ORIGINAL reciprocal old-prefix mass.  The old d divides
the full q; this information must not be discarded in a PNT payment.
No squarefree full-modulus, p-not-dividing-d or desired AP bound is used. -/

namespace ImbalancedChen.P2EnhancedNegativeChildDensityBudget

noncomputable section
open scoped Classical BigOperators
open P2EnhancedNegativeChildSignedModulus P2EnhancedNegativeChildMultiplicity
open P2EnhancedNegativeChildModulusPrimePayment

/-- G's fibre injection still remembers that the old prefix divides q.
The three original window occurrences remain separate. -/
theorem physicalCoefficient_abs_le_three_divisor_mass (N : ℕ) (Q : ℝ)
    (D : Finset ℕ) (sigma : ℕ → ℝ) (hd : ∀ d ∈ D, 0 < d)
    (hsigma : ∀ d ∈ D, 0 ≤ sigma d) (q : ℕ) :
    |physicalCoefficient N Q D sigma q| ≤
      3 * ∑ d ∈ D.filter (fun d => d ∣ q), sigma d := by
  let I := (modulusFibre N Q D q).image oldTag
  have hI : I ⊆ (D.filter (fun d => d ∣ q)).product
      (Finset.univ : Finset (Fin 3)) := by
    intro t ht
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp ht
    have hmD := (mark_original_data (Finset.mem_filter.mp hm).1).1
    have hmq := (Finset.mem_filter.mp hm).2
    have hdiv : m.1.1 ∣ q := by
      rw [← hmq]
      exact ⟨m.1.2.2 * m.2, by simp only [physicalModulus, mul_assoc]⟩
    exact Finset.mem_product.mpr
      ⟨Finset.mem_filter.mpr ⟨hmD, hdiv⟩, Finset.mem_univ _⟩
  apply (physicalCoefficient_abs_le_marked_mass N Q D sigma hsigma q).trans
  calc
    markedMultiplicityMass N Q D sigma q = ∑ t ∈ I, sigma t.1 := by
      unfold markedMultiplicityMass I
      rw [Finset.sum_image (oldTag_injective_on_fibre hd q)]
      rfl
    _ ≤ ∑ t ∈ (D.filter (fun d => d ∣ q)).product
        (Finset.univ : Finset (Fin 3)), sigma t.1 :=
      Finset.sum_le_sum_of_subset_of_nonneg hI (fun t ht _ =>
        hsigma t.1 (Finset.mem_filter.mp (Finset.mem_product.mp ht).1).1)
    _ = _ := by
      rw [Finset.sum_product, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hmem
      simp <;> ring

theorem sum_reciprocal_Icc_eq_harmonic (N : ℕ) :
    (∑ r ∈ Finset.Icc 1 N, 1 / (r : ℝ)) = (harmonic N : ℝ) := by
  simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
    Rat.cast_natCast, one_div]

/-- A selected set of multiples costs one reciprocal d, not its
cardinality. Division is injective only on the retained divisible rows. -/
theorem sum_reciprocal_multiples_le (N d : ℕ) (S : Finset ℕ)
    (hS : S ⊆ Finset.Icc 1 N) (hd : 0 < d) :
    (∑ q ∈ S.filter (fun q => d ∣ q), 1 / (q : ℝ)) ≤
      (1 / (d : ℝ)) * (1 + Real.log (N : ℝ)) := by
  let F := S.filter (fun q => d ∣ q)
  let I := F.image (fun q => q / d)
  have hdiv (q : ℕ) (hq : q ∈ F) : d ∣ q := (Finset.mem_filter.mp hq).2
  have hmul (q : ℕ) (hq : q ∈ F) : d * (q / d) = q :=
    Nat.mul_div_cancel' (hdiv q hq)
  have hinj : Set.InjOn (fun q : ℕ => q / d) (F : Set ℕ) := by
    intro x hx y hy hxy
    calc
      x = d * (x / d) := (hmul x hx).symm
      _ = d * (y / d) := by rw [hxy]
      _ = y := hmul y hy
  have hI : I ⊆ Finset.Icc 1 N := by
    intro r hr
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hr
    have hqI := Finset.mem_Icc.mp (hS (Finset.mem_filter.mp hq).1)
    have hqp : 0 < q := by omega
    have hrp : 0 < q / d := by
      by_contra hz
      have hz' : q / d = 0 := by omega
      have he := hmul q hq
      rw [hz', mul_zero] at he
      omega
    exact Finset.mem_Icc.mpr ⟨by omega, (Nat.div_le_self q d).trans hqI.2⟩
  calc
    _ = ∑ q ∈ F, (1 / (d : ℝ)) * (1 / ((q / d : ℕ) : ℝ)) := by
      apply Finset.sum_congr rfl
      intro q hq
      have heq : (d : ℝ) * ((q / d : ℕ) : ℝ) = q := by
        exact_mod_cast hmul q hq
      rw [← heq]
      simp only [one_div, mul_inv_rev]
      ring
    _ = ∑ r ∈ I, (1 / (d : ℝ)) * (1 / (r : ℝ)) :=
      (Finset.sum_image hinj).symm
    _ ≤ ∑ r ∈ Finset.Icc 1 N, (1 / (d : ℝ)) * (1 / (r : ℝ)) :=
      Finset.sum_le_sum_of_subset_of_nonneg hI (fun _ _ _ => by positivity)
    _ = (1 / (d : ℝ)) * (harmonic N : ℝ) := by
      rw [← Finset.mul_sum, sum_reciprocal_Icc_eq_harmonic]
    _ ≤ _ := mul_le_mul_of_nonneg_left (harmonic_le_one_add_log N) (by positivity)

/-- The existing finite divisor majorant gives a pointwise log/q
envelope for phi(q)^{-1}, without any squarefreeness requirement. -/
theorem reciprocal_totient_le_log_over {N q : ℕ} (hq : 0 < q) (hqN : q ≤ N) :
    1 / (Nat.totient q : ℝ) ≤ 2 * (1 + Real.log (N : ℝ)) * (1 / (q : ℝ)) := by
  have hsub : q.divisors ⊆ Finset.Icc 1 N := by
    intro r hr
    exact Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hr,
      (Nat.le_of_dvd hq (Nat.dvd_of_mem_divisors hr)).trans hqN⟩
  have hsum : (∑ r ∈ q.divisors, 1 / (r : ℝ)) ≤ 1 + Real.log (N : ℝ) := by
    calc
      _ ≤ ∑ r ∈ Finset.Icc 1 N, 1 / (r : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
      _ = (harmonic N : ℝ) := sum_reciprocal_Icc_eq_harmonic N
      _ ≤ _ := harmonic_le_one_add_log N
  calc
    _ ≤ 2 * ((1 / (q : ℝ)) * ∑ r ∈ q.divisors, 1 / (r : ℝ)) :=
      reciprocal_totient_le_divisor_sum hq
    _ ≤ 2 * ((1 / (q : ℝ)) * (1 + Real.log (N : ℝ))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum (by positivity))
        (by norm_num)
    _ = _ := by ring

/-- Uniform actual-rho norm on every selected physical subset.  It costs
only two logarithms relative to the original sigma(d)/d mass. -/
theorem physical_absolute_density_le (N : ℕ) (Q : ℝ) (D S : Finset ℕ)
    (sigma : ℕ → ℝ) (hN : 1 ≤ N) (hQN : Q ≤ (N : ℝ))
    (hd : ∀ d ∈ D, 0 < d) (hsigma : ∀ d ∈ D, 0 ≤ sigma d)
    (hS : S ⊆ modulusSupport N Q D) :
    (∑ q ∈ S, |physicalCoefficient N Q D sigma q| / (Nat.totient q : ℝ)) ≤
      6 * (1 + Real.log (N : ℝ)) ^ 2 * ∑ d ∈ D, sigma d / (d : ℝ) := by
  have hSI : S ⊆ Finset.Icc 1 N := by
    intro q hq
    have hp := physical_support hd (hS hq)
    exact Finset.mem_Icc.mpr ⟨by omega, by exact_mod_cast hp.2.le.trans hQN⟩
  have hL : 0 ≤ 1 + Real.log (N : ℝ) := by
    have := Real.log_nonneg (by exact_mod_cast hN : (1 : ℝ) ≤ N)
    linarith
  have hweighted : (∑ q ∈ S, (∑ d ∈ D.filter (fun d => d ∣ q), sigma d) * (1 / (q : ℝ))) ≤
      (1 + Real.log (N : ℝ)) * ∑ d ∈ D, sigma d / (d : ℝ) := by
    calc
      _ = ∑ d ∈ D, sigma d * ∑ q ∈ S.filter (fun q => d ∣ q), 1 / (q : ℝ) := by
        simp only [Finset.sum_filter, Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro d hdD
        apply Finset.sum_congr rfl
        intro q hqS
        by_cases hdiv : d ∣ q <;> simp [hdiv]
      _ ≤ ∑ d ∈ D, sigma d * ((1 / (d : ℝ)) * (1 + Real.log (N : ℝ))) :=
        Finset.sum_le_sum (fun d hdD => mul_le_mul_of_nonneg_left
          (sum_reciprocal_multiples_le N d S hSI (hd d hdD)) (hsigma d hdD))
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d hdD
        ring
  calc
    _ ≤ ∑ q ∈ S, (3 * ∑ d ∈ D.filter (fun d => d ∣ q), sigma d) *
        (2 * (1 + Real.log (N : ℝ)) * (1 / (q : ℝ))) := by
      apply Finset.sum_le_sum
      intro q hqS
      have hq := Finset.mem_Icc.mp (hSI hqS)
      rw [div_eq_mul_inv, ← one_div]
      exact mul_le_mul
        (physicalCoefficient_abs_le_three_divisor_mass N Q D sigma hd hsigma q)
        (reciprocal_totient_le_log_over (by omega : 0 < q) hq.2)
        (by positivity)
        (mul_nonneg (by norm_num) (Finset.sum_nonneg
          (fun d hdD => hsigma d (Finset.mem_filter.mp hdD).1)))
    _ = (6 * (1 + Real.log (N : ℝ))) *
        ∑ q ∈ S, (∑ d ∈ D.filter (fun d => d ∣ q), sigma d) * (1 / (q : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      ring
    _ ≤ (6 * (1 + Real.log (N : ℝ))) *
        ((1 + Real.log (N : ℝ)) * ∑ d ∈ D, sigma d / (d : ℝ)) :=
      mul_le_mul_of_nonneg_left hweighted (by positivity)
    _ = _ := by ring

/-- In particular this controls G's independently defined primitive
physical density; no replacement density or h-rho hypothesis is used. -/
theorem primitivePhysicalDensity_abs_le (N : ℕ) (Q : ℝ) (D : Finset ℕ)
    (sigma : ℕ → ℝ) (hlog : 1 ≤ Real.log (N : ℝ)) (hQN : Q ≤ (N : ℝ))
    (hd : ∀ d ∈ D, 0 < d) (hsigma : ∀ d ∈ D, 0 ≤ sigma d) :
    |primitivePhysicalDensity N Q D sigma| ≤
      24 * Real.log (N : ℝ) ^ 2 * ∑ d ∈ D, sigma d / (d : ℝ) := by
  have hN : 1 ≤ N := by
    by_contra hn
    have hzero : N = 0 := by omega
    simpa [hzero] using hlog
  have hm : 0 ≤ ∑ d ∈ D, sigma d / (d : ℝ) :=
    Finset.sum_nonneg (fun d hdD => div_nonneg (hsigma d hdD) (Nat.cast_nonneg d))
  calc
    _ ≤ ∑ q ∈ (modulusSupport N Q D).filter (fun q => q.Coprime N),
        |physicalCoefficient N Q D sigma q| / (Nat.totient q : ℝ) := by
      unfold primitivePhysicalDensity
      simpa only [abs_div, abs_of_nonneg (Nat.cast_nonneg _)] using
        Finset.abs_sum_le_sum_abs
          (fun q => physicalCoefficient N Q D sigma q / (Nat.totient q : ℝ))
          ((modulusSupport N Q D).filter (fun q => q.Coprime N))
    _ ≤ 6 * (1 + Real.log (N : ℝ)) ^ 2 * ∑ d ∈ D, sigma d / (d : ℝ) :=
      physical_absolute_density_le N Q D _ sigma hN hQN hd hsigma (Finset.filter_subset _ _)
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ hm
      have hlog0 : 0 ≤ Real.log (N : ℝ) := by linarith
      nlinarith [sq_nonneg (Real.log (N : ℝ) - 1)]

end
end ImbalancedChen.P2EnhancedNegativeChildDensityBudget
