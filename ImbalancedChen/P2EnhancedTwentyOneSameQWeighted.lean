import ImbalancedChen.P2EnhancedTwentyOneQuotientFinite
import MathlibNt.Wu2008DoubleSieve.BoxMassTheta

/-!
SOURCE_ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The original second-seed parameters are used literally. Every physical
cutoff is a power of the SAME Q/d. The finite prefix weights are the given
nonnegative sigma(d), not an independent replacement convolution weight.
The normalization is exactly

  4 li(N) sum_d sigma(d) C(d*N) / (phi(d) log(Q/d)).

The finite weighted 21-term comparison is proved from literal source and
quotient carriers. Both selected-square collisions and the three negative
bad-prime windows remain explicit. Positivity of this exact normalization
is derived from primitive positivity and support conditions, before the
normalized finite inequality is stated.

Full and selected square tests, retained cap data, alpha transport and the
stable ceiling belong to the subsequent signed-distribution/product-count
step. This finite lemma does not discharge that analytic step or identify
the enhanced family with wuSourceBox. In particular no enhanced H/h value,
native count licence, or Upsilon6 lower mean without its product gate is
assumed or concluded.
-/

namespace ImbalancedChen.P2EnhancedTwentyOneSameQWeighted

noncomputable section

open Finset Wu2008DoubleSieve
open P2EnhancedTwentyOneQuotientFinite
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418
open scoped Classical

/-- The actual physical cutoff at residual level Q/d. -/
def cutoff (Q : ℝ) (d : ℕ) (w : ℝ) : ℝ :=
  (Q / (d : ℝ)) ^ (1 / w)

/-- The source Phi average with its given finite nonnegative prefix weight. -/
def Phi (N : ℕ) (Q : ℝ) (D : Finset ℕ) (sigma : ℕ → ℝ) (w : ℝ) : ℝ :=
  ∑ d ∈ D, sigma d * (sourceSieveCount N d (d * N) (cutoff Q d w) : ℝ)

/-- Literal original parameter tuple (11/5,227/50,353/100,29/10,61/25). -/
def localQuotient (N : ℕ) (Q : ℝ) (d : ℕ) : ℝ :=
  quotientLocal N d N (cutoff Q d (227/50)) (cutoff Q d (353/100))
    (cutoff Q d (29/10)) (cutoff Q d (61/25)) (cutoff Q d (11/5))

def localCollisions (N : ℕ) (Q : ℝ) (d : ℕ) : ℝ :=
  collisionSwitched N d N (cutoff Q d (227/50)) (cutoff Q d (353/100))
    (cutoff Q d (29/10)) (cutoff Q d (61/25)) (cutoff Q d (11/5))

def localBadPrimes (N : ℕ) (Q : ℝ) (d : ℕ) : ℝ :=
  fourthRowMotherBadPrime N d (cutoff Q d (227/50)) (cutoff Q d (11/5)) +
    fourthRowMotherBadPrime N d (cutoff Q d (227/50)) (cutoff Q d (29/10)) +
    fourthRowMotherBadPrime N d (cutoff Q d (227/50)) (cutoff Q d (61/25))

def weightedQuotient (N : ℕ) (Q : ℝ) (D : Finset ℕ) (sigma : ℕ → ℝ) : ℝ :=
  ∑ d ∈ D, sigma d * localQuotient N Q d

def weightedCollisions (N : ℕ) (Q : ℝ) (D : Finset ℕ) (sigma : ℕ → ℝ) : ℝ :=
  ∑ d ∈ D, sigma d * localCollisions N Q d

def weightedBadPrimes (N : ℕ) (Q : ℝ) (D : Finset ℕ) (sigma : ℕ → ℝ) : ℝ :=
  ∑ d ∈ D, sigma d * localBadPrimes N Q d

/-- The exact manuscript Theta_Q; Q is not replaced by an individual child level. -/
def Theta (N : ℕ) (Q : ℝ) (D : Finset ℕ) (sigma : ℕ → ℝ) : ℝ :=
  4 * logarithmicIntegral N *
    ∑ d ∈ D, sigma d * wuSingularSeries (d * N) /
      ((Nat.totient d : ℝ) * Real.log (Q / d))

/-- This normalization specializes to the existing original convolution Theta. -/
theorem Theta_eq_boxTheta {i : ℕ} (N : ℕ) (Q : ℝ) (W : Fin i → Finset ℕ) :
    Theta N Q (boxConvolutionSupport W) (fun d => (convolutionCoeff W d : ℝ)) =
      boxTheta N Q W := rfl

/-- Endpoint order comes from the literal fixed parameters and common residual level. -/
theorem cutoff_order (Q : ℝ) (d : ℕ) (hR : 1 ≤ Q / (d : ℝ)) :
    cutoff Q d (227/50) ≤ cutoff Q d (353/100) ∧
      cutoff Q d (353/100) ≤ cutoff Q d (29/10) ∧
      cutoff Q d (29/10) ≤ cutoff Q d (61/25) ∧
      cutoff Q d (61/25) ≤ cutoff Q d (11/5) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    apply Real.rpow_le_rpow_of_exponent_le hR <;> norm_num

theorem local_sameQ_finite (N : ℕ) (Q : ℝ) (d : ℕ)
    (hR : 1 ≤ Q / (d : ℝ)) :
    5 * (sourceSieveCount N d (d * N) (cutoff Q d (11/5)) : ℝ) ≤
      localQuotient N Q d + localCollisions N Q d + localBadPrimes N Q d := by
  obtain ⟨h01, h12, h23, h3s⟩ := cutoff_order Q d hR
  simpa only [localQuotient, localCollisions, localBadPrimes, add_assoc] using
    twentyOne_quotient_finite N d h01 h12 h23 h3s

/-- The original finite sigma-weighted comparison. The support and sigma
are fixed before this statement; no child count estimate is supplied as a premise. -/
theorem weighted_sameQ_finite (N : ℕ) (Q : ℝ) (D : Finset ℕ) (sigma : ℕ → ℝ)
    (hsigma : ∀ d ∈ D, 0 ≤ sigma d) (hR : ∀ d ∈ D, 1 ≤ Q / (d : ℝ)) :
    5 * Phi N Q D sigma (11/5) ≤
      weightedQuotient N Q D sigma + weightedCollisions N Q D sigma +
        weightedBadPrimes N Q D sigma := by
  calc
    5 * Phi N Q D sigma (11/5) =
        ∑ d ∈ D, sigma d *
          (5 * (sourceSieveCount N d (d * N) (cutoff Q d (11/5)) : ℝ)) := by
      unfold Phi
      rw [mul_sum]
      apply sum_congr rfl
      intro d _
      ring
    _ ≤ ∑ d ∈ D, sigma d *
        (localQuotient N Q d + localCollisions N Q d + localBadPrimes N Q d) := by
      apply sum_le_sum
      intro d hd
      exact mul_le_mul_of_nonneg_left (local_sameQ_finite N Q d (hR d hd))
        (hsigma d hd)
    _ = weightedQuotient N Q D sigma + weightedCollisions N Q D sigma +
        weightedBadPrimes N Q D sigma := by
      simp only [weightedQuotient, weightedCollisions, weightedBadPrimes,
        mul_add, sum_add_distrib]

/-- Positivity of the exact normalizer follows from primitive support and
weight positivity, not from an assumed sieve improvement. -/
theorem Theta_pos {N : ℕ} (hN : 4 ≤ N) (Q : ℝ) (D : Finset ℕ)
    (sigma : ℕ → ℝ) (hdpos : ∀ d ∈ D, 0 < d)
    (hsigma : ∀ d ∈ D, 0 ≤ sigma d) (hR : ∀ d ∈ D, 1 < Q / (d : ℝ))
    (hpositive : ∃ d ∈ D, 0 < sigma d) : 0 < Theta N Q D sigma := by
  have hNpos : 0 < N := by omega
  have hNreal : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hli : 0 < logarithmicIntegral N :=
    (div_pos (Nat.cast_pos.mpr hNpos)
      (mul_pos (by norm_num) (Real.log_pos hNreal))).trans_le (box_trueLi_lower hN)
  have hden (d : ℕ) (hd : d ∈ D) :
      0 < (Nat.totient d : ℝ) * Real.log (Q / d) := by
    exact mul_pos (Nat.cast_pos.mpr (Nat.totient_pos.mpr (hdpos d hd)))
      (Real.log_pos (hR d hd))
  have hseries (d : ℕ) (hd : d ∈ D) : 0 < wuSingularSeries (d * N) :=
    wuSingularSeries_pos _ (mul_pos (hdpos d hd) hNpos)
  unfold Theta
  apply mul_pos (mul_pos (by norm_num) hli)
  apply sum_pos'
  · intro d hd
    exact div_nonneg (mul_nonneg (hsigma d hd) (hseries d hd).le) (hden d hd).le
  · obtain ⟨d, hd, hp⟩ := hpositive
    exact ⟨d, hd, div_pos (mul_pos hp (hseries d hd)) (hden d hd)⟩

/-- Every term is divided by the same, proved-positive original Theta_Q. -/
theorem normalized_sameQ_finite {N : ℕ} (hN : 4 ≤ N) (Q : ℝ) (D : Finset ℕ)
    (sigma : ℕ → ℝ) (hdpos : ∀ d ∈ D, 0 < d)
    (hsigma : ∀ d ∈ D, 0 ≤ sigma d) (hR : ∀ d ∈ D, 1 < Q / (d : ℝ))
    (hpositive : ∃ d ∈ D, 0 < sigma d) :
    5 * Phi N Q D sigma (11/5) / Theta N Q D sigma ≤
      weightedQuotient N Q D sigma / Theta N Q D sigma +
        weightedCollisions N Q D sigma / Theta N Q D sigma +
        weightedBadPrimes N Q D sigma / Theta N Q D sigma := by
  have htheta := Theta_pos hN Q D sigma hdpos hsigma hR hpositive
  have hfinite := weighted_sameQ_finite N Q D sigma hsigma (fun d hd => (hR d hd).le)
  simpa only [add_div] using div_le_div_of_nonneg_right hfinite htheta.le

end
end ImbalancedChen.P2EnhancedTwentyOneSameQWeighted
