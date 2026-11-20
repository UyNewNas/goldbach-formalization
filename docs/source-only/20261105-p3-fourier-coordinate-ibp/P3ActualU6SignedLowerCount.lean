import ImbalancedChen.P3ActualU6LiteralParameterAndLedger
import ImbalancedChen.P3ActualEvenLowerIntegerRho
import Mathlib.Tactic

/-!
P3.6 manuscript-INTERNAL; frozen source:
UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b,
paper/source/manuscript-body.tex (current PP) and
paper/source/modules/distribution-prime-product-completion-20261010.txt §§1,3,4.

The previous packet supplied a literal U6 reserve epsilon, an all-label
INTEGER even-first-exit LOWER signed primitive ledger and a finite
quotient-prime correction bound, but only presented a *rowwise* sieve
minorant. The present packet proves the missing link between the literal
integer pair expansion and the actual real `rowEstimator`, sums that
minorant over the ORIGINAL labelled sixthSupport, then derives a genuine
signed lower inequality for the ORIGINAL sixth-weight count. The signed
primitive discrepancy remains on the right of the budget; it is NOT
controlled, replaced by a hypothesis, or re-labelled an external input.

This is a candidate source proof. It neither identifies the selected
LOWER subsource with the global final rho_N nor proves PP.
SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.
-/

namespace ImbalancedChen.P3ActualU6SignedLowerCount

noncomputable section
open scoped Classical BigOperators
open ImbalancedChen
open ImbalancedChen.P3ActualEvenLowerIntegerRho
open ImbalancedChen.P3ActualU6AllRowsPrimitiveLedger
open ImbalancedChen.P3ActualU6EnhancedPowerLevel
open ImbalancedChen.P3ActualU6LiteralParameterAndLedger

/-- The original real quotient-row estimator equals the literal
SIGNED INTEGER first-exit pair expansion at the full physical modulus
(t.1*t.2)*(small*rough). In particular multiplicity is not discarded by
first collecting an arbitrary set of distinct moduli. -/
theorem rowEstimator_eq_literal_integer_labelledAP
    (N : ℕ) (policy : (ℕ × ℕ) → List ℕ → Bool)
    (w L : (ℕ × ℕ) → ℝ) (t : ℕ × ℕ) :
    P5CausalRhoQuotientBridge.rowEstimator N policy w L t =
      labelledRowAP N policy w L t := by
  change
    (∑ q ∈ actualLowerSmallRoughModuli (policy t) N
        (Nat.ceil (P5CausalRhoQuotientBridge.cutoff N))
        (w t) (P5CausalRhoQuotientBridge.cutoff N),
      actualLowerSmallRoughRho (policy t) N
        (Nat.ceil (P5CausalRhoQuotientBridge.cutoff N))
        (w t) (P5CausalRhoQuotientBridge.cutoff N) (L t) q *
        (chenPrimeAPCount N N ((t.1 * t.2) * q) -
         chenCentrePrimeAPCount N N ((t.1 * t.2) * q))) =
      ∑ x ∈ P5CausalRhoFactorization.pairs (policy t) N
          (Nat.ceil (P5CausalRhoQuotientBridge.cutoff N))
          (w t) (P5CausalRhoQuotientBridge.cutoff N),
        (actualEvenLowerPairInt (policy t) N
          (Nat.ceil (P5CausalRhoQuotientBridge.cutoff N))
          (w t) (P5CausalRhoQuotientBridge.cutoff N) (L t) x : ℝ) *
          (chenPrimeAPCount N N (((t.1 * t.2) * x.1) * x.2) -
           chenCentrePrimeAPCount N N (((t.1 * t.2) * x.1) * x.2))
  calc
    _ = ∑ q ∈ actualLowerSmallRoughModuli (policy t) N
          (Nat.ceil (P5CausalRhoQuotientBridge.cutoff N))
          (w t) (P5CausalRhoQuotientBridge.cutoff N),
          (actualEvenLowerIntegerRho (policy t) N
            (Nat.ceil (P5CausalRhoQuotientBridge.cutoff N))
            (w t) (P5CausalRhoQuotientBridge.cutoff N) (L t) q : ℝ) *
          (chenPrimeAPCount N N ((t.1 * t.2) * q) -
           chenCentrePrimeAPCount N N ((t.1 * t.2) * q)) := by
          apply Finset.sum_congr rfl
          intro q hq
          rw [actualEvenLowerIntegerRho_cast]
    _ = _ :=
      actualEvenLowerIntegerRho_prefix_fubini (policy t) N
        (Nat.ceil (P5CausalRhoQuotientBridge.cutoff N))
        (t.1 * t.2) (w t) (P5CausalRhoQuotientBridge.cutoff N)
        (L t)
        (fun d => chenPrimeAPCount N N d - chenCentrePrimeAPCount N N d)

/-- Monotonicity of finite sums over EACH original labelled U6 pair,
not a sum over distinct prefix-products. No PP estimate is required. -/
theorem literal_integer_labelledAP_le_actual_U6_count
    (N : ℕ) (policy : (ℕ × ℕ) → List ℕ → Bool)
    (w L : (ℕ × ℕ) → ℝ)
    (hgates : ∀ t ∈ sixthSupport N,
      1 < L t ∧ w t ≤ L t ∧
        w t ≤ P5CausalRhoQuotientBridge.cutoff N) :
    (∑ t ∈ sixthSupport N, labelledRowAP N policy w L t) ≤
      ∑ t ∈ sixthSupport N, sixthWeight N t := by
  calc
    _ = ∑ t ∈ sixthSupport N,
          P5CausalRhoQuotientBridge.rowEstimator N policy w L t := by
          apply Finset.sum_congr rfl
          intro t ht
          exact (rowEstimator_eq_literal_integer_labelledAP N policy w L t).symm
    _ ≤ ∑ t ∈ sixthSupport N, sixthWeight N t := by
          apply Finset.sum_le_sum
          intro t ht
          exact P5CausalRhoQuotientBridge.rowEstimator_le_actual
            N policy w L t (hgates t ht)

/-- A TRUE lower bound on the original U6 count from the same labelled
integer LOWER coefficient: exact primitive main + signed discrepancy,
minus the already derived polylog quotient-prime correction budget.
Neither the signed discrepancy nor the final global PP rho_N is paid.
The epsilon and N0 are existentially selected from the genuine reserve
producer, and C precedes eta/epsilon/N/policy as before. -/
theorem exists_literal_U6_count_lower_with_unpaid_signed_discrepancy :
    ∃ C : ℝ, 0 < C ∧
      ∀ eta : ℝ, 0 < eta →
        ∃ epsilon : ℝ,
          0 < epsilon ∧ epsilon < 1 / 8 ∧
          epsilon ^ 2 ≤ (417 / 5000 : ℝ) ∧ epsilon ≤ 1 ∧
          ∃ N₀ : ℕ, 2 ≤ N₀ ∧
            ∀ N : ℕ, N₀ ≤ N → Even N →
              ∀ policy : (ℕ × ℕ) → List ℕ → Bool,
                let w : (ℕ × ℕ) → ℝ :=
                  fun _ => enhancedSmallW N 1 epsilon
                let L : (ℕ × ℕ) → ℝ :=
                  fun _ => enhancedRosserL N 1 epsilon
                (∑ t ∈ sixthSupport N, rowPrimitiveMean N policy w L t) +
                  (∑ t ∈ sixthSupport N,
                    rowPrimitiveDiscrepancy N policy w L t) -
                  ((logTotientCap N) ^ 3 *
                    (C * (1 + Real.log (N : ℝ))) *
                    ((Nat.log 2 N : ℝ) +
                      C * (1 + Real.log (N : ℝ)))) ≤
                ∑ t ∈ sixthSupport N, sixthWeight N t := by
  obtain ⟨C, hC, hselected⟩ :=
    exists_literal_U6_reserve_ledger_and_correction
  refine ⟨C, hC, ?_⟩
  intro eta heta
  obtain ⟨epsilon, heps, heps8, hepsr, heps1,
      N₀, hN₀, hselectedN⟩ := hselected eta heta
  refine ⟨epsilon, heps, heps8, hepsr, heps1, N₀, hN₀, ?_⟩
  intro N hN hEven policy
  dsimp only
  obtain ⟨hminor, hledger, hcorrection, hreserve⟩ :=
    hselectedN N hN hEven policy
  have hN2 : 2 ≤ N := le_trans hN₀ hN
  have hgates := enhanced_power_gates 1 (417 / 5000) epsilon
    (by norm_num) heps heps8 hepsr (by ring) N hN2
  have hcount :
      (∑ t ∈ sixthSupport N,
        labelledRowAP N policy
          (fun _ => enhancedSmallW N 1 epsilon)
          (fun _ => enhancedRosserL N 1 epsilon) t) ≤
        ∑ t ∈ sixthSupport N, sixthWeight N t := by
    apply literal_integer_labelledAP_le_actual_U6_count
    intro t ht
    exact hgates
  rw [hledger] at hcount
  have hRle :
      (∑ t ∈ sixthSupport N,
        rowQuotientPrimeCorrection N policy
          (fun _ => enhancedSmallW N 1 epsilon)
          (fun _ => enhancedRosserL N 1 epsilon) t) ≤
        (logTotientCap N) ^ 3 *
          (C * (1 + Real.log (N : ℝ))) *
          ((Nat.log 2 N : ℝ) +
            C * (1 + Real.log (N : ℝ))) :=
    (le_abs_self _).trans hcorrection
  linarith only [hcount, hRle]

end
end ImbalancedChen.P3ActualU6SignedLowerCount
