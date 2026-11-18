import ImbalancedChen.P3ActualHybridHBPrimeDiagonal

/-!
P3.6 — same-rho diagonal with the genuine HB *coefficient degree of freedom*.
Frozen manuscript UyNewNas/chen-imbalanced-semiprimes
@9731290e8f53cffda44129906cde6a965eaa869b;
manuscript-body.tex eq:current-PP; completion note §§2–4 (HB),(T),(F).

CRITICAL SCOPE CORRECTION: the former `hybrid_prime_free_hb_exact_diagonal`
has `ArithmeticFunction.moebius` of the COMPLETE integer product. The
frozen HB identity instead assigns its mu factors to individual truncated
HB variables, plus individual log slots and signed combinatorial scalars.
For example mu(3)*mu(3)=1 whereas mu(9)=0. Thus the old finite theorem is
correct for its specially chosen mu(total) coefficient, but its RHS
cannot be substituted for the genuine full HB compiler's coefficient.

This packet allows any occurrence-dependent coefficient `a marked hb ps`
and any original labelled geometric weight `W marked hb ps`. It DOES NOT
assume a closed form for the actual HB coefficient. The physical product,
strict sorted residual selector, original fine-prime marked box, physical Q,
SAME rho and exact coprime mean are retained verbatim. A later compiler
admission theorem must instantiate a from the original HB occurrence
word, retaining all coefficients and rough/smooth masks.

SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.
-/

namespace ImbalancedChen.P3ActualHybridCoefficientFaithfulDiagonal
noncomputable section
open scoped Classical BigOperators
open ImbalancedChen
open ImbalancedChen.P3ActualHybridHBPrimeDiagonal
open ImbalancedChen.P3ActualEmptyPrimeExceptionalFibre
open ImbalancedChen.P3ActualWeightedFineSameRho

/-- Complete physical target diagonal with a FULL occurrence-dependent
arithmetic coefficient, not mu(completeProduct). Every q sees the SAME
signed rho and the exact indicator-minus-coprime-mean fineKernel. -/
def faithfulHybridDiagonal
    (N : ℕ) (τm τr : ℝ) (markedWord : List ℕ)
    (blocks : List (ℕ × ℕ)) (H : Finset (List ℕ))
    (Q : Finset ℕ) (rho : ℕ → ℝ)
    (a W : List ℕ → List ℕ → List ℕ → ℝ) : ℝ :=
  ∑ marked ∈ actualPrimeSlotBox
      (actualPrimeFineLabelFinset N τm) markedWord,
    ∑ hb ∈ H,
      ∑ q ∈ Q, rho q *
        ∑ ps ∈ (actualPrimeFineLabelSortedTuples N τr blocks).filter
            (fun ps => (marked.prod * hb.prod) * ps.prod = N),
          (a marked hb ps * W marked hb ps) *
            fineKernel N q ((marked.prod * hb.prod) * ps.prod)

/-- Whenever a genuine fine-prime slot is present, the entire diagonal
vanishes for EVERY coefficient, not merely one modeled by mu(total).
There is no coprime assumption on HB integers and no rho sign assumption. -/
theorem faithfulHybridDiagonal_zero_of_prime_present
    (N : ℕ) (τm τr : ℝ) (markedWord : List ℕ)
    (blocks : List (ℕ × ℕ)) (H : Finset (List ℕ))
    (Q : Finset ℕ) (rho : ℕ → ℝ)
    (a W : List ℕ → List ℕ → List ℕ → ℝ)
    (hprime : markedWord ≠ [] ∨
      actualPrimeLabelBlocksWord blocks ≠ []) :
    faithfulHybridDiagonal N τm τr markedWord blocks H Q rho a W = 0 := by
  unfold faithfulHybridDiagonal
  apply Finset.sum_eq_zero
  intro marked hm
  apply Finset.sum_eq_zero
  intro hb hhb
  have hzero := hybrid_full_target_fibre_empty
    N τm τr markedWord blocks marked hb hm hprime
  simp [hzero]

/-- With BOTH original PRIME words empty, the surviving diagonal is
exactly the HB-only product=N fibre with its FULL arithmetic coefficient.
No mu(N) factor is introduced. The exact coprime test is left intact
and does not require Coprime N q to compute this finite identity. -/
theorem faithfulHybridDiagonal_prime_free
    (N : ℕ) (τm τr : ℝ) (markedWord : List ℕ)
    (blocks : List (ℕ × ℕ)) (H : Finset (List ℕ))
    (Q : Finset ℕ) (rho : ℕ → ℝ)
    (a W : List ℕ → List ℕ → List ℕ → ℝ)
    (hmarked : markedWord = [])
    (hresidual : actualPrimeLabelBlocksWord blocks = []) :
    faithfulHybridDiagonal N τm τr markedWord blocks H Q rho a W =
      ∑ hb ∈ H.filter (fun hb => hb.prod = N),
        (a [] hb [] * W [] hb []) *
          (∑ q ∈ Q, rho q * fineKernel N q N) := by
  subst markedWord
  unfold faithfulHybridDiagonal
  have hbox : actualPrimeSlotBox
      (actualPrimeFineLabelFinset N τm) ([] : List ℕ) =
      {([] : List ℕ)} := by
    simp [actualPrimeSlotBox]
  rw [hbox]
  simp only [Finset.sum_singleton, List.prod_nil, one_mul]
  rw [sorted_empty_word_singleton N τr blocks hresidual]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro hb hhb
  by_cases heq : hb.prod = N
  · simp only [Finset.filter_singleton, List.prod_nil, mul_one]
    simp [heq, Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm]
  · simp [heq]

/-- Under the physically admitted coprime modulus condition, only the
literal mean factor is simplified. Crucially the actual HB coefficient
a [] hb [] does NOT turn into mu(N) by this algebraic step. -/
theorem faithfulHybridDiagonal_prime_free_coprime
    (N : ℕ) (τm τr : ℝ) (markedWord : List ℕ)
    (blocks : List (ℕ × ℕ)) (H : Finset (List ℕ))
    (Q : Finset ℕ) (rho : ℕ → ℝ)
    (a W : List ℕ → List ℕ → List ℕ → ℝ)
    (hmarked : markedWord = [])
    (hresidual : actualPrimeLabelBlocksWord blocks = [])
    (hcop : ∀ q ∈ Q, Nat.Coprime N q) :
    faithfulHybridDiagonal N τm τr markedWord blocks H Q rho a W =
      ∑ hb ∈ H.filter (fun hb => hb.prod = N),
        (a [] hb [] * W [] hb []) *
          (∑ q ∈ Q, rho q * (1 - (Nat.totient q : ℝ)⁻¹)) := by
  rw [faithfulHybridDiagonal_prime_free
    N τm τr markedWord blocks H Q rho a W hmarked hresidual]
  apply Finset.sum_congr rfl
  intro hb hhb
  congr 1
  apply Finset.sum_congr rfl
  intro q hq
  rw [fineKernel_exact N q (hcop q hq)]

end
end ImbalancedChen.P3ActualHybridCoefficientFaithfulDiagonal
