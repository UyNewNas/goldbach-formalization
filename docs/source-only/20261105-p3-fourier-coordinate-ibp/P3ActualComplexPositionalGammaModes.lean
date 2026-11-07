import ImbalancedChen.P3ActualBoundedGroupWeightGamma
import ImbalancedChen.P3ActualFineLabelThreeGammaTensor

/-!
P3.6 — COMPLEX positional gamma coefficients of actual fine-prime groups.
SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.

The manuscript's Fourier modes are complex.  The previous REAL ordered-tuple
coefficient interface is not sufficient for a genuine Fourier phase.
This file pays the finite-group complex norm and the finite-mode L1 charge,
without assuming a Fourier factorisation of any actual original W_T.

The denominators are the original per-label factorials M_j, not the total
number-of-slots factorial.  Repeated primes inside a group are retained.
No arithmetic distribution estimate, Fourier inversion, rho identification,
W_T-admission or mode-to-group decomposition is claimed.
-/

namespace ImbalancedChen.P3ActualComplexPositionalGammaModes
noncomputable section
open scoped Classical BigOperators
open ImbalancedChen
open ImbalancedChen.P5Z.ActualNormalizedPrimeLabelCoefficient

/-- Original normalized finite product fibre, with a genuinely complex
ordered tuple multiplier; no symmetry of repeated-label positions. -/
def complexWeightedLabelGamma (B : ℕ → Finset ℕ)
    (blocks : List (ℕ × ℕ)) (v : List ℕ → ℂ) (n : ℕ) : ℂ :=
  (∑ ps ∈ (actualPrimeSlotBox B (actualPrimeLabelBlocksWord blocks)).filter
      (fun ps => ps.prod = n), v ps) /
    (actualPrimeLabelBlocksFactorial blocks : ℂ)

/-- Literal complex triangle inequality controls every complete-product
fibre by the EXISTING real nonnegative gamma, including empty fibres. -/
theorem complexWeightedLabelGamma_norm_le_gamma
    (B : ℕ → Finset ℕ) (blocks : List (ℕ × ℕ))
    (v : List ℕ → ℂ)
    (hv : ∀ ps ∈ actualPrimeSlotBox B
      (actualPrimeLabelBlocksWord blocks), ‖v ps‖ ≤ 1)
    (n : ℕ) :
    ‖complexWeightedLabelGamma B blocks v n‖ ≤ gamma B blocks n := by
  let T := actualPrimeSlotBox B (actualPrimeLabelBlocksWord blocks)
  let F := T.filter (fun ps => ps.prod = n)
  have hmass : ‖∑ ps ∈ F, v ps‖ ≤ (F.card : ℝ) := by
    calc
      _ ≤ ∑ ps ∈ F, ‖v ps‖ := norm_sum_le _ _
      _ ≤ ∑ ps ∈ F, (1 : ℝ) := Finset.sum_le_sum (by
        intro ps hps
        exact hv ps (Finset.mem_filter.mp hps).1)
      _ = (F.card : ℝ) := by simp
  have hM : (0 : ℝ) <
      (actualPrimeLabelBlocksFactorial blocks : ℝ) := by
    exact_mod_cast actualPrimeLabelBlocksFactorial_pos blocks
  have hnormM :
      ‖(actualPrimeLabelBlocksFactorial blocks : ℂ)‖ =
        (actualPrimeLabelBlocksFactorial blocks : ℝ) := by simp
  have hdiv :
      ‖∑ ps ∈ F, v ps‖ /
        (actualPrimeLabelBlocksFactorial blocks : ℝ) ≤
      (F.card : ℝ) /
        (actualPrimeLabelBlocksFactorial blocks : ℝ) :=
    (div_le_div_iff_of_pos_right hM).2 hmass
  change ‖(∑ ps ∈ F, v ps) /
      (actualPrimeLabelBlocksFactorial blocks : ℂ)‖ ≤
    (F.card : ℝ) /
      (actualPrimeLabelBlocksFactorial blocks : ℝ)
  rw [norm_div, hnormM]
  exact hdiv

/-- Genuine disjoint half-open fine labels give a complex one-bound.
This does not assert the original geometric W_T has this representation. -/
theorem complexWeightedLabelGamma_norm_le_one
    (N : ℕ) (hN : 1 ≤ N) (τ : ℝ) (hτ : 0 ≤ τ)
    (blocks : List (ℕ × ℕ))
    (hlabels : blocks.Pairwise (fun b d => b.1 ≠ d.1))
    (v : List ℕ → ℂ)
    (hv : ∀ ps ∈ actualPrimeSlotBox
      (actualPrimeFineLabelFinset N τ)
      (actualPrimeLabelBlocksWord blocks), ‖v ps‖ ≤ 1)
    (n : ℕ) :
    ‖complexWeightedLabelGamma
      (actualPrimeFineLabelFinset N τ) blocks v n‖ ≤ 1 := by
  have hdom := complexWeightedLabelGamma_norm_le_gamma
    (actualPrimeFineLabelFinset N τ) blocks v hv n
  have hgamma :=
    ImbalancedChen.P3ActualFineLabelThreeGammaTensor.fine_gamma_mem_Icc
      N hN τ hτ blocks hlabels n
  exact hdom.trans hgamma.2

/-- Exact finite Fourier-mode L1 charge for THREE individually bounded
COMPLEX positional gamma groups.  The number of modes is not inserted as
H^m, and each coefficient retains its own literal complex amplitude.

This only controls the coefficient at a fixed triple of product integers.
A genuine Fourier representation and continuous L1/Fubini remain separate
manuscript-internal obligations. -/
theorem finite_three_complex_modes_norm_le_l1
    {κ : Type*} (K : Finset κ) (amp : κ → ℂ)
    (N : ℕ) (hN : 1 ≤ N) (τ : ℝ) (hτ : 0 ≤ τ)
    (g₀ g₁ g₂ : List (ℕ × ℕ))
    (hl₀ : g₀.Pairwise (fun b d => b.1 ≠ d.1))
    (hl₁ : g₁.Pairwise (fun b d => b.1 ≠ d.1))
    (hl₂ : g₂.Pairwise (fun b d => b.1 ≠ d.1))
    (v₀ v₁ v₂ : κ → List ℕ → ℂ)
    (hv₀ : ∀ k ∈ K, ∀ ps ∈ actualPrimeSlotBox
      (actualPrimeFineLabelFinset N τ)
      (actualPrimeLabelBlocksWord g₀), ‖v₀ k ps‖ ≤ 1)
    (hv₁ : ∀ k ∈ K, ∀ ps ∈ actualPrimeSlotBox
      (actualPrimeFineLabelFinset N τ)
      (actualPrimeLabelBlocksWord g₁), ‖v₁ k ps‖ ≤ 1)
    (hv₂ : ∀ k ∈ K, ∀ ps ∈ actualPrimeSlotBox
      (actualPrimeFineLabelFinset N τ)
      (actualPrimeLabelBlocksWord g₂), ‖v₂ k ps‖ ≤ 1)
    (a b d : ℕ) :
    ‖∑ k ∈ K, amp k *
      complexWeightedLabelGamma (actualPrimeFineLabelFinset N τ)
        g₀ (v₀ k) a *
      complexWeightedLabelGamma (actualPrimeFineLabelFinset N τ)
        g₁ (v₁ k) b *
      complexWeightedLabelGamma (actualPrimeFineLabelFinset N τ)
        g₂ (v₂ k) d‖ ≤ ∑ k ∈ K, ‖amp k‖ := by
  classical
  let G₀ : κ → ℂ := fun k =>
    complexWeightedLabelGamma (actualPrimeFineLabelFinset N τ)
      g₀ (v₀ k) a
  let G₁ : κ → ℂ := fun k =>
    complexWeightedLabelGamma (actualPrimeFineLabelFinset N τ)
      g₁ (v₁ k) b
  let G₂ : κ → ℂ := fun k =>
    complexWeightedLabelGamma (actualPrimeFineLabelFinset N τ)
      g₂ (v₂ k) d
  have h₀ (k : κ) (hk : k ∈ K) : ‖G₀ k‖ ≤ 1 :=
    complexWeightedLabelGamma_norm_le_one N hN τ hτ g₀ hl₀
      (v₀ k) (hv₀ k hk) a
  have h₁ (k : κ) (hk : k ∈ K) : ‖G₁ k‖ ≤ 1 :=
    complexWeightedLabelGamma_norm_le_one N hN τ hτ g₁ hl₁
      (v₁ k) (hv₁ k hk) b
  have h₂ (k : κ) (hk : k ∈ K) : ‖G₂ k‖ ≤ 1 :=
    complexWeightedLabelGamma_norm_le_one N hN τ hτ g₂ hl₂
      (v₂ k) (hv₂ k hk) d
  have hprod (k : κ) (hk : k ∈ K) :
      ‖G₀ k * G₁ k * G₂ k‖ ≤ 1 := by
    have h01 : ‖G₀ k‖ * ‖G₁ k‖ ≤ 1 := by
      calc
        _ ≤ 1 * ‖G₁ k‖ :=
          mul_le_mul_of_nonneg_right (h₀ k hk) (norm_nonneg _)
        _ ≤ 1 * 1 :=
          mul_le_mul_of_nonneg_left (h₁ k hk) (by norm_num)
        _ = 1 := by ring
    calc
      _ = (‖G₀ k‖ * ‖G₁ k‖) * ‖G₂ k‖ := by
        simp only [norm_mul]
      _ ≤ 1 * ‖G₂ k‖ :=
        mul_le_mul_of_nonneg_right h01 (norm_nonneg _)
      _ ≤ 1 * 1 :=
        mul_le_mul_of_nonneg_left (h₂ k hk) (by norm_num)
      _ = 1 := by ring
  have hterm (k : κ) (hk : k ∈ K) :
      ‖amp k * G₀ k * G₁ k * G₂ k‖ ≤ ‖amp k‖ := by
    calc
      _ = ‖amp k * (G₀ k * G₁ k * G₂ k)‖ := by
        simp only [mul_assoc]
      _ = ‖amp k‖ * ‖G₀ k * G₁ k * G₂ k‖ := by
        rw [norm_mul]
      _ ≤ ‖amp k‖ * 1 :=
        mul_le_mul_of_nonneg_left (hprod k hk) (norm_nonneg _)
      _ = ‖amp k‖ := by ring
  change ‖∑ k ∈ K, amp k * G₀ k * G₁ k * G₂ k‖ ≤
    ∑ k ∈ K, ‖amp k‖
  calc
    _ ≤ ∑ k ∈ K, ‖amp k * G₀ k * G₁ k * G₂ k‖ :=
      norm_sum_le _ _
    _ ≤ ∑ k ∈ K, ‖amp k‖ :=
      Finset.sum_le_sum (by
        intro k hk
        exact hterm k hk)

end
end ImbalancedChen.P3ActualComplexPositionalGammaModes
