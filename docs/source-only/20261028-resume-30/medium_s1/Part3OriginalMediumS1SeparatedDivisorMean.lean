import ImbalancedChen.Part3OriginalMediumS1WeightedRemainder
import ImbalancedChen.Part3TransposedPrimitiveUMoment
import ImbalancedChen.P5RoughSquareWeightedBudget
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The S1 ordinary divisor-mean step in the original medium calculation.
Unlike a pointwise divisor bound by x^epsilon, the following separation
keeps both physical totient denominators, hence q^2*d^2*r*s, before any
summation.  The actual alpha coprime masses and Lambda_d factors are
removed only by the original one-bounded-alpha and tau(d*w) bounds.

The resulting q sum keeps q^(-2); the two rough sums keep r^(-1).
This is the necessary finite bridge to ordinary one-variable divisor
moments and, after summing d~D, the source's factor 1/(Q*D).
-/

namespace ImbalancedChen.Part3.OriginalMediumS1SeparatedDivisorMean

open Classical Finset
open scoped BigOperators
open OriginalMediumPhysicalE3Block OriginalMediumS1CommonMCount
open OriginalMediumS1WeightedRemainder
open TransposedPrimitiveUMoment
open ImbalancedChen.P5Z.RoughSquareWeightedBudget
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

noncomputable section

def tauR (n : ℕ) : ℝ := n.divisors.card

theorem tauR_mul_le (a b : ℕ) : tauR (a * b) ≤ tauR a * tauR b := by
  exact_mod_cast card_divisors_mul_le a b

theorem tauR_four_mul_le (a b c d : ℕ) :
    tauR (a * b * c * d) ≤ tauR a * tauR b * tauR c * tauR d := by
  calc
    _ ≤ tauR (a * b * c) * tauR d := tauR_mul_le _ _
    _ ≤ (tauR (a * b) * tauR c) * tauR d :=
      mul_le_mul_of_nonneg_right (tauR_mul_le _ _)
        (by dsimp [tauR]; positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (tauR_mul_le a b)
        (by dsimp [tauR]; positivity)) (by dsimp [tauR]; positivity)

/-- Positive carrier indices follow from the physical fixed block, not
from a separately asserted positivity property of an abstract array. -/
theorem carrier_positive (B : FixedBlock) {q r : ℕ}
    (hq : q ∈ B.qCarrier) (hr : r ∈ B.wCarrier) :
    0 < q ∧ 0 < r := by
  have hqlo : B.qLo ≤ q := (Finset.mem_Icc.mp hq).1
  have hqR : 0 < (B.qLo : ℝ) := lt_of_lt_of_le B.q0_pos B.qLo_block
  have hqN : 0 < B.qLo := by exact_mod_cast hqR
  have hrlo : Nat.ceil B.roughLength ≤ r := (Finset.mem_Icc.mp hr).1
  have hrR : 0 < (Nat.ceil B.roughLength : ℝ) :=
    lt_of_lt_of_le B.rough_pos (Nat.le_ceil B.roughLength)
  have hrN : 0 < Nat.ceil B.roughLength := by exact_mod_cast hrR
  omega

/-- Both reciprocal totients are bounded with their own physical
integer denominators. The common logarithmic cap is used only in the
Euler-factor numerator. -/
theorem reciprocal_totient_pair_le {u v P : ℕ}
    (hu : 0 < u) (hv : 0 < v) (huP : u ≤ P) (hvP : v ≤ P) :
    1 / ((u.totient : ℝ) * (v.totient : ℝ)) ≤
      4 * logBudget P ^ 2 / ((u : ℝ) * (v : ℝ)) := by
  have hu' := reciprocal_totient_le_logBudget hu huP
  have hv' := reciprocal_totient_le_logBudget hv hvP
  calc
    _ = (1 / (u.totient : ℝ)) * (1 / (v.totient : ℝ)) := by ring
    _ ≤ (2 * ((1 / (u : ℝ)) * logBudget P)) *
        (2 * ((1 / (v : ℝ)) * logBudget P)) :=
      mul_le_mul hu' hv' (by positivity) (by positivity)
    _ = _ := by ring

/-- The literal q/r/s positive kernel after the common-m count. The
coefficient hypotheses are exactly pointwise source bounds, not an S1
estimate, an error envelope, or a desired aggregate divisor mean. -/
theorem S1DivisorKernel_le_separated
    (B : FixedBlock) (P : ℕ) (A : ℝ) (hA : 0 ≤ A)
    (hpsi : ∀ q ∈ B.qCarrier, ‖actualQWeight B q‖ ≤ 1)
    (hlambda : ∀ r ∈ B.wCarrier, ‖B.lambdaD r‖ ≤ tauR (B.d * r))
    (halpha : ∀ q ∈ B.qCarrier, ∀ r ∈ B.wCarrier,
      ‖alphaMean B (q * B.d) r‖ ≤ A)
    (hP : ∀ q ∈ B.qCarrier, ∀ r ∈ B.wCarrier, q * B.d * r ≤ P) :
    S1DivisorKernel B ≤
      4 * A ^ 2 * logBudget P ^ 2 *
        (tauR B.d ^ 3 / (B.d : ℝ) ^ 2) *
        (∑ q ∈ B.qCarrier, tauR q / (q : ℝ) ^ 2) *
        (∑ r ∈ B.wCarrier, tauR r ^ 2 / (r : ℝ)) ^ 2 := by
  have hpoint (q r s : ℕ) (hq : q ∈ B.qCarrier)
      (hr : r ∈ B.wCarrier) (hs : s ∈ B.wCarrier) :
      ‖actualQWeight B q‖ * ‖B.lambdaD r‖ * ‖B.lambdaD s‖ *
        (tauR (q * B.d * r * s) /
          (((q * B.d * r).totient : ℝ) * ((q * B.d * s).totient : ℝ))) *
        ‖alphaMean B (q * B.d) r‖ * ‖alphaMean B (q * B.d) s‖ ≤
      4 * A ^ 2 * logBudget P ^ 2 * (tauR B.d ^ 3 / (B.d : ℝ) ^ 2) *
        (tauR q / (q : ℝ) ^ 2) *
        ((tauR r ^ 2 / (r : ℝ)) * (tauR s ^ 2 / (s : ℝ))) := by
    obtain ⟨hqpos, hrpos⟩ := carrier_positive B hq hr
    have hspos := (carrier_positive B hq hs).2
    have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hqpos.ne'
    have hdR : (B.d : ℝ) ≠ 0 := by exact_mod_cast B.d_pos.ne'
    have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast hrpos.ne'
    have hsR : (s : ℝ) ≠ 0 := by exact_mod_cast hspos.ne'
    have htq : 0 ≤ tauR q := by dsimp [tauR]; positivity
    have htd : 0 ≤ tauR B.d := by dsimp [tauR]; positivity
    have htr : 0 ≤ tauR r := by dsimp [tauR]; positivity
    have hts : 0 ≤ tauR s := by dsimp [tauR]; positivity
    have hlr : ‖B.lambdaD r‖ ≤ tauR B.d * tauR r :=
      (hlambda r hr).trans (tauR_mul_le _ _)
    have hls : ‖B.lambdaD s‖ ≤ tauR B.d * tauR s :=
      (hlambda s hs).trans (tauR_mul_le _ _)
    have hphi := reciprocal_totient_pair_le
      (mul_pos (mul_pos hqpos B.d_pos) hrpos)
      (mul_pos (mul_pos hqpos B.d_pos) hspos)
      (hP q hq r hr) (hP q hq s hs)
    have hquot : tauR (q * B.d * r * s) /
        (((q * B.d * r).totient : ℝ) * ((q * B.d * s).totient : ℝ)) ≤
      (tauR q * tauR B.d * tauR r * tauR s) *
        (4 * logBudget P ^ 2 /
          (((q * B.d * r : ℕ) : ℝ) * ((q * B.d * s : ℕ) : ℝ))) := by
      rw [div_eq_mul_one_div]
      exact mul_le_mul (tauR_four_mul_le q B.d r s) hphi
        (by positivity) (by dsimp [tauR]; positivity)
    calc
      _ ≤ 1 * (tauR B.d * tauR r) * (tauR B.d * tauR s) *
          ((tauR q * tauR B.d * tauR r * tauR s) *
            (4 * logBudget P ^ 2 /
              (((q * B.d * r : ℕ) : ℝ) * ((q * B.d * s : ℕ) : ℝ)))) * A * A := by
        gcongr
        · exact hpsi q hq
        · exact hlr
        · exact hls
        · exact hquot
        · exact halpha q hq r hr
        · exact halpha q hq s hs
      _ = _ := by
        push_cast
        field_simp [hqR, hdR, hrR, hsR]
        <;> ring
  unfold S1DivisorKernel
  calc
    _ ≤ ∑ q ∈ B.qCarrier, ∑ r ∈ B.wCarrier, ∑ s ∈ B.wCarrier,
        4 * A ^ 2 * logBudget P ^ 2 * (tauR B.d ^ 3 / (B.d : ℝ) ^ 2) *
          (tauR q / (q : ℝ) ^ 2) *
          ((tauR r ^ 2 / (r : ℝ)) * (tauR s ^ 2 / (s : ℝ))) := by
      apply Finset.sum_le_sum
      intro q hq
      apply Finset.sum_le_sum
      intro r hr
      apply Finset.sum_le_sum
      intro s hs
      exact hpoint q r s hq hr hs
    _ = _ := by
      simp only [Finset.mul_sum, Finset.sum_mul, pow_two]
      ring

/-- Apply the same uniform common-m counting constant directly to
the separated ordinary divisor sums. In particular no per-d remainder
with an arbitrary logarithmic saving has been inserted. -/
theorem S1ActualRemainder_le_separated :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : FixedBlock) (M A : ℝ) (P : ℕ)
      (S : Finset ℕ), 0 < M → 0 ≤ A →
      (∀ m, CommonSmoothCutoff.scaledDyadicCutoff M m ≠ 0 → m ∈ S) →
      (∀ q ∈ B.qCarrier, ‖actualQWeight B q‖ ≤ 1) →
      (∀ r ∈ B.wCarrier, ‖B.lambdaD r‖ ≤ tauR (B.d * r)) →
      (∀ q ∈ B.qCarrier, ∀ r ∈ B.wCarrier,
        ‖alphaMean B (q * B.d) r‖ ≤ A) →
      (∀ q ∈ B.qCarrier, ∀ r ∈ B.wCarrier, q * B.d * r ≤ P) →
      ‖S1ActualRemainder B S M‖ ≤ C *
        (A ^ 2 * logBudget P ^ 2 * (tauR B.d ^ 3 / (B.d : ℝ) ^ 2) *
          (∑ q ∈ B.qCarrier, tauR q / (q : ℝ) ^ 2) *
          (∑ r ∈ B.wCarrier, tauR r ^ 2 / (r : ℝ)) ^ 2) := by
  obtain ⟨C, hC, hcount⟩ := S1ActualRemainder_le_uniform_divisor_kernel
  refine ⟨4 * C, by positivity, ?_⟩
  intro B M A P S hM hA hS hpsi hlambda halpha hP
  calc
    _ ≤ C * S1DivisorKernel B := hcount B M hM S hS
    _ ≤ C * (4 * A ^ 2 * logBudget P ^ 2 *
        (tauR B.d ^ 3 / (B.d : ℝ) ^ 2) *
        (∑ q ∈ B.qCarrier, tauR q / (q : ℝ) ^ 2) *
        (∑ r ∈ B.wCarrier, tauR r ^ 2 / (r : ℝ)) ^ 2) :=
      mul_le_mul_of_nonneg_left
        (S1DivisorKernel_le_separated B P A hA hpsi hlambda halpha hP) hC.le
    _ = _ := by ring

/-- The physical q0 lower bound yields a literal inverse q0 before
the q mean is enlarged. This is the Q saving required by the manuscript. -/
theorem q_divisor_square_sum_le (B : FixedBlock) :
    (∑ q ∈ B.qCarrier, tauR q / (q : ℝ) ^ 2) ≤
      (1 / B.q0) * ∑ q ∈ B.qCarrier, tauR q / (q : ℝ) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro q hq
  have hq0 : B.q0 ≤ (q : ℝ) :=
    B.qLo_block.trans (by exact_mod_cast (Finset.mem_Icc.mp hq).1)
  have hqpos : 0 < (q : ℝ) := lt_of_lt_of_le B.q0_pos hq0
  have hi : 1 / (q : ℝ) ≤ 1 / B.q0 :=
    one_div_le_one_div_of_le B.q0_pos hq0
  calc
    _ = (tauR q / (q : ℝ)) * (1 / (q : ℝ)) := by ring
    _ ≤ (tauR q / (q : ℝ)) * (1 / B.q0) :=
      mul_le_mul_of_nonneg_left hi (by dsimp [tauR]; positivity)
    _ = _ := by ring

/-- Ordinary divisor moments are paid by the existing all-integer
Fouvry convolution functions. No squarefree restriction is introduced. -/
theorem tauR_sq_le_tauFour (n : ℕ) :
    tauR n ^ 2 ≤ (fouvryTau 4 n : ℝ) := by
  have h : (n.divisors.card : ℝ) * (n.divisors.card : ℝ) ≤
      (fouvryTau 4 n : ℝ) := by
    rw [← fouvryTau_two]
    exact_mod_cast fouvryTau_mul_le 2 2 n
  simpa [tauR, pow_two] using h

theorem tauR_cube_le_tauEight (n : ℕ) :
    tauR n ^ 3 ≤ (fouvryTau 8 n : ℝ) := by
  calc
    _ = tauR n ^ 2 * tauR n := by ring
    _ ≤ (fouvryTau 4 n : ℝ) * (fouvryTau 2 n : ℝ) := by
      rw [fouvryTau_two]
      exact mul_le_mul_of_nonneg_right (tauR_sq_le_tauFour n) (by positivity)
    _ ≤ _ := by exact_mod_cast fouvryTau_mul_le 4 2 n

/-- The elementary `phi(n) <= n` comparison is used after retaining
the inverse physical modulus. It does not discard either dyadic saving. -/
theorem divisor_weight_to_totient (n : ℕ) (hn : 0 < n)
    (a : ℝ) (ha : 0 ≤ a) :
    a / (n : ℝ) ≤ a / (n.totient : ℝ) := by
  have hphi : (0 : ℝ) < n.totient := by
    exact_mod_cast Nat.totient_pos.mpr hn
  have hle : (n.totient : ℝ) ≤ n := by exact_mod_cast Nat.totient_le n
  exact div_le_div_of_nonneg_left ha hphi hle

theorem sum_tauR_div_le_log (T : Finset ℕ) (X : ℝ)
    (hX : 1 ≤ X) (hT : T ⊆ Finset.Ioc 0 (Nat.floor X)) :
    (∑ n ∈ T, tauR n / (n : ℝ)) ≤ (1 + Real.log X) ^ 4 := by
  calc
    _ ≤ ∑ n ∈ T, (fouvryTau 2 n : ℝ) / (n.totient : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      rw [fouvryTau_two]
      exact divisor_weight_to_totient n (Finset.mem_Ioc.mp (hT hn)).1
        (tauR n) (by dsimp [tauR]; positivity)
    _ ≤ ∑ n ∈ Finset.Ioc 0 (Nat.floor X),
        (fouvryTau 2 n : ℝ) / (n.totient : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hT (fun _ _ _ => by positivity)
    _ ≤ _ := sum_fouvryTau_div_totient_le_real 2 hX

theorem sum_tauR_sq_div_le_log (T : Finset ℕ) (X : ℝ)
    (hX : 1 ≤ X) (hT : T ⊆ Finset.Ioc 0 (Nat.floor X)) :
    (∑ n ∈ T, tauR n ^ 2 / (n : ℝ)) ≤ (1 + Real.log X) ^ 8 := by
  calc
    _ ≤ ∑ n ∈ T, (fouvryTau 4 n : ℝ) / (n.totient : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      have hnpos : 0 < n := (Finset.mem_Ioc.mp (hT hn)).1
      exact (divisor_weight_to_totient n hnpos (tauR n ^ 2) (by positivity)).trans
        (div_le_div_of_nonneg_right (tauR_sq_le_tauFour n) (by positivity))
    _ ≤ ∑ n ∈ Finset.Ioc 0 (Nat.floor X),
        (fouvryTau 4 n : ℝ) / (n.totient : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hT (fun _ _ _ => by positivity)
    _ ≤ _ := sum_fouvryTau_div_totient_le_real 4 hX

/-- The d~D ordinary mean supplies the second dyadic denominator.
Its numerator is a fixed logarithmic power, not x^epsilon. -/
theorem sum_tauR_cube_div_square_le_log (T : Finset ℕ) (D X : ℝ)
    (hD : 0 < D) (hX : 1 ≤ X)
    (hT : T ⊆ Finset.Ioc 0 (Nat.floor X))
    (hlo : ∀ n ∈ T, D ≤ (n : ℝ)) :
    (∑ n ∈ T, tauR n ^ 3 / (n : ℝ) ^ 2) ≤
      (1 / D) * (1 + Real.log X) ^ 16 := by
  calc
    _ ≤ (1 / D) * ∑ n ∈ T, (fouvryTau 8 n : ℝ) / (n.totient : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro n hn
      have hnpos : 0 < n := (Finset.mem_Ioc.mp (hT hn)).1
      have hi : 1 / (n : ℝ) ≤ 1 / D :=
        one_div_le_one_div_of_le hD (hlo n hn)
      calc
        _ = (1 / (n : ℝ)) * (tauR n ^ 3 / (n : ℝ)) := by ring
        _ ≤ (1 / D) * (tauR n ^ 3 / (n : ℝ)) :=
          mul_le_mul_of_nonneg_right hi (by dsimp [tauR]; positivity)
        _ ≤ (1 / D) * ((fouvryTau 8 n : ℝ) / (n.totient : ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact (divisor_weight_to_totient n hnpos (tauR n ^ 3) (by positivity)).trans
            (div_le_div_of_nonneg_right (tauR_cube_le_tauEight n) (by positivity))
    _ ≤ (1 / D) * ∑ n ∈ Finset.Ioc 0 (Nat.floor X),
        (fouvryTau 8 n : ℝ) / (n.totient : ℝ) :=
      mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum_of_subset_of_nonneg hT (fun _ _ _ => by positivity))
        (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (sum_fouvryTau_div_totient_le_real 8 hX) (by positivity)

/-- Completed fixed-d divisor payment for the literal S1 kernel.
The remaining d mean is exactly the preceding theorem, of order eight. -/
theorem S1DivisorKernel_le_log
    (B : FixedBlock) (P : ℕ) (A Qcap Rcap : ℝ) (hA : 0 ≤ A)
    (hQ : 1 ≤ Qcap) (hR : 1 ≤ Rcap)
    (hqcap : B.qCarrier ⊆ Finset.Ioc 0 (Nat.floor Qcap))
    (hrcap : B.wCarrier ⊆ Finset.Ioc 0 (Nat.floor Rcap))
    (hpsi : ∀ q ∈ B.qCarrier, ‖actualQWeight B q‖ ≤ 1)
    (hlambda : ∀ r ∈ B.wCarrier, ‖B.lambdaD r‖ ≤ tauR (B.d * r))
    (halpha : ∀ q ∈ B.qCarrier, ∀ r ∈ B.wCarrier,
      ‖alphaMean B (q * B.d) r‖ ≤ A)
    (hP : ∀ q ∈ B.qCarrier, ∀ r ∈ B.wCarrier, q * B.d * r ≤ P) :
    S1DivisorKernel B ≤
      4 * A ^ 2 * logBudget P ^ 2 * (tauR B.d ^ 3 / (B.d : ℝ) ^ 2) *
        ((1 + Real.log Qcap) ^ 4 / B.q0) * (1 + Real.log Rcap) ^ 16 := by
  have hqsum : (∑ q ∈ B.qCarrier, tauR q / (q : ℝ) ^ 2) ≤
      (1 + Real.log Qcap) ^ 4 / B.q0 := by
    calc
      _ ≤ (1 / B.q0) * ∑ q ∈ B.qCarrier, tauR q / (q : ℝ) :=
        q_divisor_square_sum_le B
      _ ≤ (1 / B.q0) * (1 + Real.log Qcap) ^ 4 :=
        mul_le_mul_of_nonneg_left
          (sum_tauR_div_le_log B.qCarrier Qcap hQ hqcap) (by positivity)
      _ = _ := by ring
  have hrsum := sum_tauR_sq_div_le_log B.wCarrier Rcap hR hrcap
  have htd : 0 ≤ tauR B.d := by dsimp [tauR]; positivity
  have hroughsum : 0 ≤ ∑ r ∈ B.wCarrier, tauR r ^ 2 / (r : ℝ) :=
    Finset.sum_nonneg (fun r _ => by positivity)
  calc
    _ ≤ 4 * A ^ 2 * logBudget P ^ 2 *
        (tauR B.d ^ 3 / (B.d : ℝ) ^ 2) *
        (∑ q ∈ B.qCarrier, tauR q / (q : ℝ) ^ 2) *
        (∑ r ∈ B.wCarrier, tauR r ^ 2 / (r : ℝ)) ^ 2 :=
      S1DivisorKernel_le_separated B P A hA hpsi hlambda halpha hP
    _ ≤ 4 * A ^ 2 * logBudget P ^ 2 *
        (tauR B.d ^ 3 / (B.d : ℝ) ^ 2) *
        ((1 + Real.log Qcap) ^ 4 / B.q0) *
        ((1 + Real.log Rcap) ^ 8) ^ 2 := by
      gcongr
    _ = _ := by rw [← pow_mul]

/-- The alpha hypothesis in the kernel payment is supplied by the
original atom's admissibility, including its original interval. -/
theorem actual_alpha_mean_bound {k : ℕ} {σ κ c0 : ℝ}
    (B : FixedBlock) (hB : MediumAdmissible k σ κ c0 B.atom) (q r : ℕ) :
    ‖alphaMean B (q * B.d) r‖ ≤ 2 * B.atom.U := by
  exact TransposedPrimitiveU.coprimeMass_norm_le_twice_U hB _

/-- Sum every physical d in one preliminary dispersion block. The
four fixed-order ordinary divisor means give the source denominator
Q*D. This is not a sum of D arbitrary-logarithmic black-box errors. -/
theorem S1DivisorKernel_family_le_log
    (T : Finset ℕ) (F : ℕ → FixedBlock) (P : ℕ)
    (A Q D Qcap Rcap Dcap : ℝ)
    (hA : 0 ≤ A) (hQ : 0 < Q) (hD : 0 < D)
    (hQc : 1 ≤ Qcap) (hRc : 1 ≤ Rcap) (hDc : 1 ≤ Dcap)
    (hT : T ⊆ Finset.Ioc 0 (Nat.floor Dcap))
    (hdlo : ∀ d ∈ T, D ≤ (d : ℝ))
    (hfd : ∀ d ∈ T, (F d).d = d)
    (hqlo : ∀ d ∈ T, Q ≤ (F d).q0)
    (hqcap : ∀ d ∈ T, (F d).qCarrier ⊆ Finset.Ioc 0 (Nat.floor Qcap))
    (hrcap : ∀ d ∈ T, (F d).wCarrier ⊆ Finset.Ioc 0 (Nat.floor Rcap))
    (hpsi : ∀ d ∈ T, ∀ q ∈ (F d).qCarrier, ‖actualQWeight (F d) q‖ ≤ 1)
    (hlambda : ∀ d ∈ T, ∀ r ∈ (F d).wCarrier,
      ‖(F d).lambdaD r‖ ≤ tauR ((F d).d * r))
    (halpha : ∀ d ∈ T, ∀ q ∈ (F d).qCarrier, ∀ r ∈ (F d).wCarrier,
      ‖alphaMean (F d) (q * (F d).d) r‖ ≤ A)
    (hP : ∀ d ∈ T, ∀ q ∈ (F d).qCarrier, ∀ r ∈ (F d).wCarrier,
      q * (F d).d * r ≤ P) :
    (∑ d ∈ T, S1DivisorKernel (F d)) ≤
      4 * A ^ 2 * logBudget P ^ 2 * (1 + Real.log Qcap) ^ 4 *
        (1 + Real.log Rcap) ^ 16 * (1 + Real.log Dcap) ^ 16 / (Q * D) := by
  let C : ℝ := 4 * A ^ 2 * logBudget P ^ 2 *
    (1 + Real.log Qcap) ^ 4 * (1 + Real.log Rcap) ^ 16 / Q
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hpoint (d : ℕ) (hd : d ∈ T) :
      S1DivisorKernel (F d) ≤ C * (tauR d ^ 3 / (d : ℝ) ^ 2) := by
    have hq : (1 + Real.log Qcap) ^ 4 / (F d).q0 ≤
        (1 + Real.log Qcap) ^ 4 / Q :=
      div_le_div_of_nonneg_left (by positivity) hQ (hqlo d hd)
    have htd : 0 ≤ tauR d := by dsimp [tauR]; positivity
    calc
      _ ≤ 4 * A ^ 2 * logBudget P ^ 2 *
          (tauR (F d).d ^ 3 / ((F d).d : ℝ) ^ 2) *
          ((1 + Real.log Qcap) ^ 4 / (F d).q0) *
          (1 + Real.log Rcap) ^ 16 :=
        S1DivisorKernel_le_log (F d) P A Qcap Rcap hA hQc hRc
          (hqcap d hd) (hrcap d hd) (hpsi d hd) (hlambda d hd)
          (halpha d hd) (hP d hd)
      _ ≤ 4 * A ^ 2 * logBudget P ^ 2 *
          (tauR d ^ 3 / (d : ℝ) ^ 2) *
          ((1 + Real.log Qcap) ^ 4 / Q) *
          (1 + Real.log Rcap) ^ 16 := by
        rw [hfd d hd]
        gcongr
      _ = _ := by dsimp [C]; ring
  calc
    _ ≤ ∑ d ∈ T, C * (tauR d ^ 3 / (d : ℝ) ^ 2) :=
      Finset.sum_le_sum hpoint
    _ = C * ∑ d ∈ T, tauR d ^ 3 / (d : ℝ) ^ 2 := by rw [Finset.mul_sum]
    _ ≤ C * ((1 / D) * (1 + Real.log Dcap) ^ 16) :=
      mul_le_mul_of_nonneg_left
        (sum_tauR_cube_div_square_le_log T D Dcap hD hDc hT hdlo) hC
    _ = _ := by dsimp [C]; ring

/-- The same single common-m constant controls the full d-block
remainder before the just-proved ordinary divisor mean is inserted. -/
theorem S1ActualRemainder_family_le_kernel :
    ∃ C : ℝ, 0 < C ∧ ∀ (T : Finset ℕ) (F : ℕ → FixedBlock)
      (M : ℝ) (S : Finset ℕ), 0 < M →
      (∀ m, CommonSmoothCutoff.scaledDyadicCutoff M m ≠ 0 → m ∈ S) →
      ‖∑ d ∈ T, S1ActualRemainder (F d) S M‖ ≤
        C * ∑ d ∈ T, S1DivisorKernel (F d) := by
  obtain ⟨C, hC, hcount⟩ := S1ActualRemainder_le_uniform_divisor_kernel
  refine ⟨C, hC, ?_⟩
  intro T F M S hM hS
  calc
    _ ≤ ∑ d ∈ T, ‖S1ActualRemainder (F d) S M‖ := norm_sum_le _ _
    _ ≤ ∑ d ∈ T, C * S1DivisorKernel (F d) :=
      Finset.sum_le_sum (fun d _ => hcount (F d) M hM S hS)
    _ = _ := by rw [Finset.mul_sum]

end

end ImbalancedChen.Part3.OriginalMediumS1SeparatedDivisorMean
