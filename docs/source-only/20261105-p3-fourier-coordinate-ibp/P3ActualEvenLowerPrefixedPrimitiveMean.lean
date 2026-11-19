import ImbalancedChen.P3ActualEvenLowerEulerMass
import ImbalancedChen.CurrentChenP5CausalRhoQuotientBridge
import Mathlib.Tactic

/-!
P3.6 — original U6 even-first-exit LOWER: exact *full physical-prefix*
coprime primitive mean, with no substitution of the quotient modulus k
for the true AP modulus b*k.

Frozen manuscript: chen-imbalanced-semiprimes@
9731290e8f53cffda44129906cde6a965eaa869b,
distribution-prime-product-completion §§1,3(T),4(F).

The primitive product B in this file is NEVER identified with the U6
two-prime prefix b, nor is it replaced by an auxiliary level.  The
existing integer even-lower rho(k), including its original retained
policy and sign-sensitive Rosser branch, is used at the literal k.
The P5 receiver checks the FULL physical modulus (b*k).

Only the actual P5 rough-prefix lemma licenses gcd(b,k)=1.  Under this
proved arithmetic condition the full physical Euler factor splits,
and the complete-product coprime filter splits exactly.  In particular
gcd(B,b) failing makes the primitive mean ZERO, not an artificial
unfiltered density.  This is finite mean algebra, not a bound for
the nonzero-shift arithmetic PP discrepancy and not a final compiler
rho_N identity.

SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.
-/

namespace ImbalancedChen.P3ActualEvenLowerPrefixedPrimitiveMean

noncomputable section
open scoped Classical BigOperators
open ImbalancedChen
open ImbalancedChen.P3ActualEvenLowerIntegerRho
open ImbalancedChen.P3ActualEvenLowerEulerMass
open ImbalancedChen.P3ActualRetainedRoughEulerMass
open ImbalancedChen.P3ActualRawActiveLevelTotientCap
open ImbalancedChen.P3ActualWholeProductPrimitiveMeanPayment

/-- Keep exactly the full physical modulus b*q, not just the quotient q.
B is a distinct complete prime-product parameter and is not simplified. -/
def prefixedPrimitiveMean (B b : ℕ) (Q : Finset ℕ)
    (rho : ℕ → ℤ) : ℂ :=
  ∑ q ∈ Q.filter (fun q => Nat.Coprime B (b * q)),
    (rho q : ℂ) * ((((Nat.totient (b * q) : ℝ)⁻¹ : ℝ) : ℂ))

/-- Exact gcd and Euler-totient factorization at the SAME physical
integer b*q.  No sign, uniformity, and no PP conclusion is presumed. -/
theorem prefixedPrimitiveMean_factor
    (B b : ℕ) (Q : Finset ℕ) (rho : ℕ → ℤ)
    (hcop : ∀ q ∈ Q, Nat.Coprime b q) :
    prefixedPrimitiveMean B b Q rho =
      if Nat.Coprime B b then
        ((((Nat.totient b : ℝ)⁻¹ : ℝ) : ℂ)) *
          primitivePhysicalMean B Q rho
      else 0 := by
  classical
  by_cases hB : Nat.Coprime B b
  · simp only [if_pos hB]
    have hfilter :
        Q.filter (fun q => Nat.Coprime B (b * q)) =
          Q.filter (fun q => Nat.Coprime B q) := by
      ext q
      constructor
      · intro hq
        obtain ⟨hqQ, hqcop⟩ := Finset.mem_filter.mp hq
        exact Finset.mem_filter.mpr
          ⟨hqQ, (Nat.coprime_mul_iff_right.mp hqcop).2⟩
      · intro hq
        obtain ⟨hqQ, hqcop⟩ := Finset.mem_filter.mp hq
        exact Finset.mem_filter.mpr
          ⟨hqQ, Nat.coprime_mul_iff_right.mpr ⟨hB, hqcop⟩⟩
    unfold prefixedPrimitiveMean primitivePhysicalMean
    rw [hfilter, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q hq
    have hqQ : q ∈ Q := (Finset.mem_filter.mp hq).1
    have hphi : ((Nat.totient (b * q) : ℝ)⁻¹) =
        (Nat.totient b : ℝ)⁻¹ * (Nat.totient q : ℝ)⁻¹ := by
      rw [Nat.totient_mul (hcop q hqQ), Nat.cast_mul, mul_inv_rev]
    have hphiC := congrArg (fun r : ℝ => (r : ℂ)) hphi
    rw [hphiC, Complex.ofReal_mul]
    ring
  · have hempty :
        Q.filter (fun q => Nat.Coprime B (b * q)) = ∅ := by
      apply Finset.eq_empty_iff_forall_not_mem.mpr
      intro q hq
      exact hB ((Nat.coprime_mul_iff_right.mp
        (Finset.mem_filter.mp hq).2).1)
    simp [prefixedPrimitiveMean, hempty, hB]

/-- The signed mean at b*q has the EXACT reciprocal-totient loss
1/phi(b). It is not the quotient-only mean unless b=1. -/
theorem prefixedPrimitiveMean_norm_le
    (B b : ℕ) (Q : Finset ℕ) (rho : ℕ → ℤ)
    (hcop : ∀ q ∈ Q, Nat.Coprime b q) :
    ‖prefixedPrimitiveMean B b Q rho‖ ≤
      (Nat.totient b : ℝ)⁻¹ * physicalReciprocalTotientMass Q rho := by
  rw [prefixedPrimitiveMean_factor B b Q rho hcop]
  by_cases hB : Nat.Coprime B b
  · rw [if_pos hB, norm_mul]
    have hscalar :
        ‖((((Nat.totient b : ℝ)⁻¹ : ℝ) : ℂ))‖ =
          (Nat.totient b : ℝ)⁻¹ := by
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by positivity)]
    rw [hscalar]
    exact mul_le_mul_of_nonneg_left
      (primitivePhysicalMean_norm_le B Q rho) (by positivity)
  · simp only [if_neg hB, norm_zero]
    exact mul_nonneg (by positivity)
      (physicalReciprocalTotientMass_nonneg Q rho)

/-- The genuine U6 sixthSupport receiver has its original two-prime
prefix b=t.1*t.2 rough at z=N^(417/5000). Thus the ORIGINAL even
lower producer is coprime to that prefix at every original quotient
modulus, with the strict w<=z gate visible. -/
theorem actual_u6_lower_moduli_coprime_prefix
    (N : ℕ) (t : ℕ × ℕ) (ht : t ∈ sixthSupport N)
    (policy : (ℕ × ℕ) → List ℕ → Bool)
    (w : (ℕ × ℕ) → ℝ)
    (hwz : w t ≤ P5CausalRhoQuotientBridge.cutoff N)
    {q : ℕ}
    (hq : q ∈ actualLowerSmallRoughModuli
      (policy t) N (Nat.ceil (P5CausalRhoQuotientBridge.cutoff N))
      (w t) (P5CausalRhoQuotientBridge.cutoff N)) :
    Nat.Coprime (t.1 * t.2) q := by
  exact P5CausalRhoQuotientBridge.moduli_coprime_multiplier
    (policy t) N (Nat.ceil (P5CausalRhoQuotientBridge.cutoff N))
    (t.1 * t.2) (w t) (P5CausalRhoQuotientBridge.cutoff N)
    hwz (P5CausalRhoQuotientBridge.row_multiplier_rough ht) hq

/-- Exact signed, original physical coprime mean for a real sixth row.
The same INTEGER even-lower rho is used at every labelled quotient q.
The full modulus b*q, the independent complete prime product B and
the original policy are kept. No target PP bound is a premise. -/
theorem actual_u6_even_lower_prefixed_mean_factor
    (N B : ℕ) (t : ℕ × ℕ) (ht : t ∈ sixthSupport N)
    (policy : (ℕ × ℕ) → List ℕ → Bool)
    (w L : (ℕ × ℕ) → ℝ)
    (hwz : w t ≤ P5CausalRhoQuotientBridge.cutoff N) :
    let z := P5CausalRhoQuotientBridge.cutoff N
    let cap := Nat.ceil z
    let Q := actualLowerSmallRoughModuli (policy t) N cap (w t) z
    let rho := actualEvenLowerIntegerRho (policy t) N cap (w t) z (L t)
    prefixedPrimitiveMean B (t.1 * t.2) Q rho =
      if Nat.Coprime B (t.1 * t.2) then
        ((((Nat.totient (t.1 * t.2) : ℝ)⁻¹ : ℝ) : ℂ)) *
          primitivePhysicalMean B Q rho
      else 0 := by
  dsimp
  apply prefixedPrimitiveMean_factor
  intro q hq
  exact actual_u6_lower_moduli_coprime_prefix
    N t ht policy w hwz hq

/-- Quantitative finite Euler budget for this EXACT signed U6 lower
row at the full modulus b*q. The bound retains phi(b), unlike the
previous quotient-only mean. It does not claim an arbitrary log saving
or identify the row-dependent rho with global frozen rho_N. -/
theorem actual_u6_even_lower_prefixed_mean_le_euler
    (N A B : ℕ) (t : ℕ × ℕ) (ht : t ∈ sixthSupport N)
    (policy : (ℕ × ℕ) → List ℕ → Bool)
    (w L : (ℕ × ℕ) → ℝ)
    (hwz : w t ≤ P5CausalRhoQuotientBridge.cutoff N)
    (hLA : L t ≤ (A : ℝ)) :
    let z := P5CausalRhoQuotientBridge.cutoff N
    let cap := Nat.ceil z
    let Q := actualLowerSmallRoughModuli (policy t) N cap (w t) z
    let rho := actualEvenLowerIntegerRho (policy t) N cap (w t) z (L t)
    ‖prefixedPrimitiveMean B (t.1 * t.2) Q rho‖ ≤
      (Nat.totient (t.1 * t.2) : ℝ)⁻¹ *
        (logTotientCap A * roughEulerMass N cap (w t) z) := by
  dsimp
  have hcop : ∀ q ∈ actualLowerSmallRoughModuli
      (policy t) N (Nat.ceil (P5CausalRhoQuotientBridge.cutoff N))
      (w t) (P5CausalRhoQuotientBridge.cutoff N),
      Nat.Coprime (t.1 * t.2) q := by
    intro q hq
    exact actual_u6_lower_moduli_coprime_prefix
      N t ht policy w hwz hq
  exact (prefixedPrimitiveMean_norm_le B (t.1 * t.2)
    (actualLowerSmallRoughModuli (policy t) N
      (Nat.ceil (P5CausalRhoQuotientBridge.cutoff N))
      (w t) (P5CausalRhoQuotientBridge.cutoff N))
    (actualEvenLowerIntegerRho (policy t) N
      (Nat.ceil (P5CausalRhoQuotientBridge.cutoff N))
      (w t) (P5CausalRhoQuotientBridge.cutoff N) (L t))
    hcop).trans
    (mul_le_mul_of_nonneg_left
      (actual_even_lower_integer_physical_mass_le_euler
        (policy t) N
        (Nat.ceil (P5CausalRhoQuotientBridge.cutoff N))
        A (w t) (P5CausalRhoQuotientBridge.cutoff N)
        (L t) hLA)
      (by positivity))

end
end ImbalancedChen.P3ActualEvenLowerPrefixedPrimitiveMean
