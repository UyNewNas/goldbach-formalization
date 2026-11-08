import ImbalancedChen.Part5OriginalH430MarkedSourceDegeneracy

/-!
P5.6 / h34: exact homogeneous scaling of the GENUINE finite marked
source and its SAME-PHYSICAL-Q normalizer.

Global multiplication of the marked coefficients by a positive constant
does not improve either normalized Phi/Theta or weightedQuotient/Theta.
The unnormalized arithmetic quotient-prime count does not scale with
sigma; its normalized value instead changes inversely with the scale.

This is not a construction of the manuscript's actual marked family,
a q-to-product match, or a paid selected-count estimate. No mark d is
identified with a quotient prime q. All old analytic/finite inputs are
reused without change.

SOURCE ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430MarkedScalingInvariance

noncomputable section
open scoped Classical BigOperators
open P2EnhancedTwentyOneSameQWeighted
open Part5OriginalH430TaggedArithmeticReceivers

/-- Exact homogeneous scaling of the actual sieve source Phi, at the
same N, Q, marked support, and original sieve cutoff w. -/
theorem literal_phi_homogeneous
    (N : ℕ) (Q : ℝ) (D : Finset ℕ) (sigma : ℕ → ℝ)
    (w c : ℝ) :
    Phi N Q D (fun d => c * sigma d) w =
      c * Phi N Q D sigma w := by
  unfold Phi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  ring

/-- Scale homogeneity for the physical SAME-Q normalizer, including
the singular factor, totient and logarithmic denominator unchanged. -/
theorem literal_theta_homogeneous
    (N : ℕ) (Q : ℝ) (D : Finset ℕ) (sigma : ℕ → ℝ) (c : ℝ) :
    Theta N Q D (fun d => c * sigma d) =
      c * Theta N Q D sigma := by
  have hsum :
      (∑ d ∈ D, (c * sigma d) * wuSingularSeries (d * N) /
          ((Nat.totient d : ℝ) * Real.log (Q / d))) =
        c * (∑ d ∈ D, sigma d * wuSingularSeries (d * N) /
          ((Nat.totient d : ℝ) * Real.log (Q / d))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    ring
  unfold Theta
  rw [hsum]
  ring

/-- The actual marked local quotient numerator has the SAME
homogeneity; this is not a new error or an extra allowance. -/
theorem literal_quotient_homogeneous
    (N : ℕ) (Q : ℝ) (D : Finset ℕ) (sigma : ℕ → ℝ) (c : ℝ) :
    weightedQuotient N Q D (fun d => c * sigma d) =
      c * weightedQuotient N Q D sigma := by
  unfold weightedQuotient
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  ring

/-- Positive rescaling cannot change the normalized sieve-source
coefficient. Positivity is from the existing primitive finite-family
gates, not from an assumed count theorem. -/
theorem normalized_phi_unchanged_by_global_rescaling
    {N : ℕ} (hN : 4 ≤ N) (Q : ℝ) (D : Finset ℕ)
    (sigma : ℕ → ℝ)
    (hdpos : ∀ d ∈ D, 0 < d)
    (hsigma : ∀ d ∈ D, 0 ≤ sigma d)
    (hR : ∀ d ∈ D, 1 < Q / (d : ℝ))
    (hpositive : ∃ d ∈ D, 0 < sigma d)
    (c : ℝ) (hc : 0 < c) :
    Phi N Q D (fun d => c * sigma d) (11/5) /
        Theta N Q D (fun d => c * sigma d) =
      Phi N Q D sigma (11/5) / Theta N Q D sigma := by
  have ht : 0 < Theta N Q D sigma :=
    Theta_pos hN Q D sigma hdpos hsigma hR hpositive
  have hc0 : c ≠ 0 := ne_of_gt hc
  have ht0 : Theta N Q D sigma ≠ 0 := ne_of_gt ht
  rw [literal_phi_homogeneous, literal_theta_homogeneous]
  field_simp [hc0, ht0] <;> ring

/-- Rescaling likewise cannot improve the normalized genuine local
quotient budget. The physical Q and original marked indices persist. -/
theorem normalized_quotient_unchanged_by_global_rescaling
    {N : ℕ} (hN : 4 ≤ N) (Q : ℝ) (D : Finset ℕ)
    (sigma : ℕ → ℝ)
    (hdpos : ∀ d ∈ D, 0 < d)
    (hsigma : ∀ d ∈ D, 0 ≤ sigma d)
    (hR : ∀ d ∈ D, 1 < Q / (d : ℝ))
    (hpositive : ∃ d ∈ D, 0 < sigma d)
    (c : ℝ) (hc : 0 < c) :
    weightedQuotient N Q D (fun d => c * sigma d) /
        Theta N Q D (fun d => c * sigma d) =
      weightedQuotient N Q D sigma / Theta N Q D sigma := by
  have ht : 0 < Theta N Q D sigma :=
    Theta_pos hN Q D sigma hdpos hsigma hR hpositive
  have hc0 : c ≠ 0 := ne_of_gt hc
  have ht0 : Theta N Q D sigma ≠ 0 := ne_of_gt ht
  rw [literal_quotient_homogeneous, literal_theta_homogeneous]
  field_simp [hc0, ht0] <;> ring

/-- Crucial contrast: the ACTUAL original arithmetic q-cardinality
does not scale with sigma. After the very same positive rescaling its
normalization changes by 1/c. This is an exact arithmetic/marked
comparison, not an upper estimate or a paid q-to-source matching. -/
theorem normalized_original_q_count_inverse_rescaling
    {N : ℕ} (hN : 4 ≤ N) (Q : ℝ) (D : Finset ℕ)
    (sigma : ℕ → ℝ)
    (hdpos : ∀ d ∈ D, 0 < d)
    (hsigma : ∀ d ∈ D, 0 ≤ sigma d)
    (hR : ∀ d ∈ D, 1 < Q / (d : ℝ))
    (hpositive : ∃ d ∈ D, 0 < sigma d)
    (p : ℕ) (c : ℝ) (hc : 0 < c) :
    ((originalReceiver N p).card : ℝ) /
        Theta N Q D (fun d => c * sigma d) =
      (1/c) * (((originalReceiver N p).card : ℝ) /
        Theta N Q D sigma) := by
  have ht : 0 < Theta N Q D sigma :=
    Theta_pos hN Q D sigma hdpos hsigma hR hpositive
  have hc0 : c ≠ 0 := ne_of_gt hc
  have ht0 : Theta N Q D sigma ≠ 0 := ne_of_gt ht
  rw [literal_theta_homogeneous]
  field_simp [hc0, ht0] <;> ring

end
end ImbalancedChen.Part5OriginalH430MarkedScalingInvariance
