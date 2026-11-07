import ImbalancedChen.ChenQuotientSieveRemainders
import MathlibNt.AnalyticNumberTheory.BombieriVinogradov.Bombieri1965Richert418Unconditional

/-!
# Genuine prime AP distribution for the below-half physical modulus range

The actual inclusive prime count is identified with the pinned standard BV
count, whose centre is the genuine logarithmic integral.  A single BV
threshold then precedes every smaller physical modulus cap, endpoint,
primitive moving-residue selector and bounded signed coefficient.

These are zero-additive-phase prime AP estimates.  They do not assert the
manuscript's high-modulus factorized prime-product distribution theorem.
In particular the physical cap remains `panModulusCutoff N B`, not an
auxiliary factorization range, and the prime-product source is not replaced
by the prime source proved here.
-/

namespace ImbalancedChen

noncomputable section

open Filter
open scoped BigOperators
open MathlibNt.SieveTheory.BombieriVinogradov
open MathlibNt.SieveTheory.LiuWeight (panModulusCutoff)

/-- The local and upstream counts contain precisely the same primes,
including the upper endpoint and without an inserted coprimality mask. -/
theorem part3_chenPrimeAPCount_eq_primesInAP (Y a d : ℕ) :
    chenPrimeAPCount Y a d = (primesInAP Y d a : ℝ) := by
  simp only [chenPrimeAPCount, chenPrimePrefix, primesInAP, Finset.filter_filter]

/-- Genuine inclusive prime AP discrepancy, centred at the pinned `li`.
The residue is an arbitrary natural number, before canonical reduction. -/
def part3PrimeAPError (Y a d : ℕ) : ℝ :=
  chenPrimeAPCount Y a d - trueLogarithmicIntegral Y / (Nat.totient d : ℝ)

theorem part3PrimeAPError_eq_standard (Y a d : ℕ) :
    part3PrimeAPError Y a d = standardPrimeAPError Y d (a % d) := by
  simp only [part3PrimeAPError, part3_chenPrimeAPCount_eq_primesInAP,
    standardPrimeAPError, primesInAP, Nat.ModEq, Nat.mod_mod]

theorem part3PrimeAPError_target_eq_chenQuotientPrimeAPError (N d : ℕ) :
    part3PrimeAPError N N d =
      chenQuotientPrimeAPError N (trueLogarithmicIntegral N) d := by
  rfl

/-- Every smaller endpoint is controlled by the same outer prefix maximum. -/
theorem part3_standardPrimeAPMaxError_le_prefix
    {N Y d : ℕ} (hY : Y ≤ N) :
    standardPrimeAPMaxError Y d ≤ standardPrimeAPPrefixMaxError N d := by
  classical
  unfold standardPrimeAPPrefixMaxError
  exact Finset.le_max' _ _ (Finset.mem_image.mpr
    ⟨Y, Finset.mem_range.mpr (Nat.lt_succ_of_le hY), rfl⟩)

/-- The target may move independently of the prime endpoint.  Only its
literal coprimality with the physical modulus is required. -/
theorem part3_abs_primeAPError_le_prefix
    {N Y a d : ℕ} (hY : Y ≤ N) (hd : 0 < d) (ha : Nat.Coprime a d) :
    |part3PrimeAPError Y a d| ≤ standardPrimeAPPrefixMaxError N d := by
  rw [part3PrimeAPError_eq_standard]
  have hres : a % d ∈ AnalyticNumberTheory.Sieve.unitResidues d := by
    change a % d ∈ finiteReducedResidues d
    exact (mod_mem_finiteReducedResidues_iff a d hd).mpr ha
  exact (abs_standardPrimeAPError_le_max hres).trans
    (part3_standardPrimeAPMaxError_le_prefix hY)

/-- The literal target-`N` AP error in the quotient sieve is one of the
standard BV errors, with exactly the same logarithmic-integral centre. -/
theorem part3_abs_chenQuotientPrimeAPError_le_prefix
    {N d : ℕ} (hd : 0 < d) (hNd : Nat.Coprime N d) :
    |chenQuotientPrimeAPError N (trueLogarithmicIntegral N) d| ≤
      standardPrimeAPPrefixMaxError N d := by
  rw [← part3PrimeAPError_target_eq_chenQuotientPrimeAPError]
  exact part3_abs_primeAPError_le_prefix le_rfl hd hNd

/-- Finite primitive pooling, allowing an independently chosen residue at
every modulus while retaining one common prime endpoint. -/
theorem part3_sum_abs_primeAPError_le_prefix
    (N D : ℕ) (S : Finset ℕ) (hS : S ⊆ Finset.Icc 1 D)
    (Y : ℕ) (hY : Y ≤ N) (a : ℕ → ℕ)
    (ha : ∀ d ∈ S, Nat.Coprime (a d) d) :
    (∑ d ∈ S, |part3PrimeAPError Y (a d) d|) ≤
      ∑ d ∈ Finset.Icc 1 D, standardPrimeAPPrefixMaxError N d := by
  calc
    _ ≤ ∑ d ∈ S, standardPrimeAPPrefixMaxError N d := by
      apply Finset.sum_le_sum
      intro d hd
      exact part3_abs_primeAPError_le_prefix hY
        (Finset.mem_Icc.mp (hS hd)).1 (ha d hd)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hS
      (fun d _ _ => standardPrimeAPPrefixMaxError_nonneg N d)

/-- Keeping a bounded signed coefficient inside the physical-modulus sum
costs no cardinality factor in the ordinary BV range. -/
theorem part3_abs_sum_mul_primeAPError_le_sum_abs
    (S : Finset ℕ) (Y : ℕ) (a : ℕ → ℕ) (w : ℕ → ℝ)
    (hw : ∀ d ∈ S, |w d| ≤ 1) :
    |∑ d ∈ S, w d * part3PrimeAPError Y (a d) d| ≤
      ∑ d ∈ S, |part3PrimeAPError Y (a d) d| := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  apply Finset.sum_le_sum
  intro d hd
  rw [abs_mul]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right
    (hw d hd) (abs_nonneg (part3PrimeAPError Y (a d) d))

/-- An unconditional simultaneous prime-distribution estimate.  The
constants and eventual threshold are chosen before every displayed finite
support, endpoint and moving residue selector. -/
theorem part3_sum_abs_primeAPError_log_saving (A : ℝ) (hA : 0 < A) :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ C : ℝ, 0 < C ∧
      ∀ᶠ N : ℕ in atTop, ∀ Q : ℕ, Q ≤ panModulusCutoff N B →
        ∀ S : Finset ℕ, S ⊆ Finset.Icc 1 Q →
          ∀ Y : ℕ, Y ≤ N → ∀ a : ℕ → ℕ,
            (∀ d ∈ S, Nat.Coprime (a d) d) →
            (∑ d ∈ S, |part3PrimeAPError Y (a d) d|) ≤
              C * (N : ℝ) / Real.log (N : ℝ) ^ A := by
  obtain ⟨B, hB, C, hC, hBV⟩ :=
    AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418.standardBombieriVinogradov
      A hA
  refine ⟨B, hB, C, hC, ?_⟩
  filter_upwards [hBV, eventually_ge_atTop (2 : ℕ)] with N hN hN2
  intro Q hQ S hS Y hY a ha
  have hSD : S ⊆ Finset.Icc 1 (panModulusCutoff N B) := by
    intro d hd
    obtain ⟨hd1, hdQ⟩ := Finset.mem_Icc.mp (hS hd)
    exact Finset.mem_Icc.mpr ⟨hd1, hdQ.trans hQ⟩
  exact (part3_sum_abs_primeAPError_le_prefix N _ S hSD Y hY a ha).trans
    (hN hN2)

/-- The same simultaneous supplier for signed bounded physical weights.
No positivity assumption on the coefficient is needed. -/
theorem part3_abs_sum_mul_primeAPError_log_saving (A : ℝ) (hA : 0 < A) :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ C : ℝ, 0 < C ∧
      ∀ᶠ N : ℕ in atTop, ∀ Q : ℕ, Q ≤ panModulusCutoff N B →
        ∀ S : Finset ℕ, S ⊆ Finset.Icc 1 Q →
          ∀ Y : ℕ, Y ≤ N → ∀ a : ℕ → ℕ,
            (∀ d ∈ S, Nat.Coprime (a d) d) →
            ∀ w : ℕ → ℝ, (∀ d ∈ S, |w d| ≤ 1) →
            |∑ d ∈ S, w d * part3PrimeAPError Y (a d) d| ≤
              C * (N : ℝ) / Real.log (N : ℝ) ^ A := by
  obtain ⟨B, hB, C, hC, h⟩ := part3_sum_abs_primeAPError_log_saving A hA
  refine ⟨B, hB, C, hC, ?_⟩
  filter_upwards [h] with N hN
  intro Q hQ S hS Y hY a ha w hw
  exact (part3_abs_sum_mul_primeAPError_le_sum_abs S Y a w hw).trans
    (hN Q hQ S hS Y hY a ha)

/-- Genuine common-interval discrepancy for `L < p ≤ U`, expressed through
the two literal inclusive prime counts with their common `li` normalization. -/
def part3PrimeAPIntervalError (L U a d : ℕ) : ℝ :=
  (chenPrimeAPCount U a d - chenPrimeAPCount L a d) -
    (trueLogarithmicIntegral U - trueLogarithmicIntegral L) / (Nat.totient d : ℝ)

theorem part3PrimeAPIntervalError_eq_sub (L U a d : ℕ) :
    part3PrimeAPIntervalError L U a d =
      part3PrimeAPError U a d - part3PrimeAPError L a d := by
  unfold part3PrimeAPIntervalError part3PrimeAPError
  ring

/-- Common interval endpoints and all signed weights may vary after the
same threshold.  The two endpoint errors account for the explicit factor 2. -/
theorem part3_abs_sum_mul_primeAPIntervalError_log_saving
    (A : ℝ) (hA : 0 < A) :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ C : ℝ, 0 < C ∧
      ∀ᶠ N : ℕ in atTop, ∀ Q : ℕ, Q ≤ panModulusCutoff N B →
        ∀ S : Finset ℕ, S ⊆ Finset.Icc 1 Q →
          ∀ L U : ℕ, L ≤ U → U ≤ N → ∀ a : ℕ → ℕ,
            (∀ d ∈ S, Nat.Coprime (a d) d) →
            ∀ w : ℕ → ℝ, (∀ d ∈ S, |w d| ≤ 1) →
            |∑ d ∈ S, w d * part3PrimeAPIntervalError L U (a d) d| ≤
              2 * (C * (N : ℝ) / Real.log (N : ℝ) ^ A) := by
  obtain ⟨B, hB, C, hC, h⟩ := part3_abs_sum_mul_primeAPError_log_saving A hA
  refine ⟨B, hB, C, hC, ?_⟩
  filter_upwards [h] with N hN
  intro Q hQ S hS L U hLU hUN a ha w hw
  simp only [part3PrimeAPIntervalError_eq_sub, mul_sub, Finset.sum_sub_distrib]
  exact (abs_sub _ _).trans (by
    have hU := hN Q hQ S hS U hUN a ha w hw
    have hL := hN Q hQ S hS L (hLU.trans hUN) a ha w hw
    linarith)

/-- Exact ordinary-BV supplier for the primitive error pool already used
by the actual quotient sieves.  The full physical modulus is `k`. -/
theorem part3_chenQuotientPrimeAPError_pool_log_saving
    (A : ℝ) (hA : 0 < A) :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ C : ℝ, 0 < C ∧
      ∀ᶠ N : ℕ in atTop, ∀ Q : ℕ, Q ≤ panModulusCutoff N B →
        (∑ k ∈ Finset.Icc 1 Q with Nat.Coprime k N,
          |chenQuotientPrimeAPError N (trueLogarithmicIntegral N) k|) ≤
            C * (N : ℝ) / Real.log (N : ℝ) ^ A := by
  obtain ⟨B, hB, C, hC, h⟩ := part3_sum_abs_primeAPError_log_saving A hA
  refine ⟨B, hB, C, hC, ?_⟩
  filter_upwards [h] with N hN
  intro Q hQ
  have hpool := hN Q hQ
    ((Finset.Icc 1 Q).filter (fun k => Nat.Coprime k N))
    (Finset.filter_subset _ _) N le_rfl (fun _ => N)
    (fun k hk => (Finset.mem_filter.mp hk).2.symm)
  simpa only [part3PrimeAPError_target_eq_chenQuotientPrimeAPError] using hpool

end

end ImbalancedChen
