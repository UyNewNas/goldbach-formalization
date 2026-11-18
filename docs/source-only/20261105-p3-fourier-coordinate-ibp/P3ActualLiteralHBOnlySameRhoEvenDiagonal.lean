import ImbalancedChen.P3HBEvenRoughTarget
import ImbalancedChen.P3ActualHybridCoefficientFaithfulDiagonal

/-!
P3.6 — literal HB-only full-product=N diagonal under the SAME physical rho.
Frozen manuscript: UyNewNas/chen-imbalanced-semiprimes
@9731290e8f53cffda44129906cde6a965eaa869b,
paper/source/modules/distribution-prime-product-completion-20261010.txt
§2 (HB) and §4 (F); manuscript-body.tex eq:current-PP.

This is the ACTUAL literal order-three occurrence weight from
P5ActualRoughHeathBrownWords: j+1 separate mu_Z slots, j one-slots,
ONE log slot, strict rough projector on every HB variable, original
signed coefficients +3,-3,+1, ordered occurrences and arbitrary
tuple-dependent geometry. It DOES NOT replace this weight by mu(N).

For an EVEN target N and genuine rough cutoff z >= 2, all HB-only
complete-product=N occurrences vanish before summing any modulus.
The statement keeps the exact fineKernel (count minus coprime mean),
the SAME signed rho(q) in all three HB terms, and the physical Q.
It does not pay mixed sources with unmasked outside integers, infer
that the compiler emits only HB-only words, or bound off-diagonal
discrepancy. Empty Gamma mother words remain a different obligation.

SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.
-/

namespace ImbalancedChen.P3ActualLiteralHBOnlySameRhoEvenDiagonal

noncomputable section
open scoped Classical BigOperators
open ImbalancedChen
open ImbalancedChen.P3HBEvenRoughTarget
open ImbalancedChen.P3ActualHybridCoefficientFaithfulDiagonal
open ImbalancedChen.P5Z.LiteralHeathBrownOccurrenceWords
open ImbalancedChen.P5Z.ActualRoughHeathBrownWords
open ImbalancedChen.P3ActualWeightedFineSameRho

/-- Literal HB-only target fibre at ONE physical modulus.
The filtered fibre is kept explicitly, including all ordered slots.
The actual rough occurrence coefficient is complex-valued, so this
does not take its real part or multiply by an extra mu(total). -/
def literalHBOnlyAtQ (N j q : ℕ) (z y : ℝ)
    (W : List ℕ → ℂ) : ℂ :=
  ∑ hb ∈ (factorTuples (2 * (j + 1)) N).filter
      (fun hb => hb.prod = N),
    (W hb * roughTupleWeight z y (roles j) hb) *
      (((fineKernel N q hb.prod : ℝ) : ℂ))

/-- The exact complete-product target allows the ORIGINAL kernel at N
to factor outside an arbitrary positional geometric weight. No
coprime approximation and no sign/absolute-value replacement. -/
theorem literalHBOnlyAtQ_exact_factor
    (N j q : ℕ) (z y : ℝ) (W : List ℕ → ℂ) :
    literalHBOnlyAtQ N j q z y W =
      (((fineKernel N q N : ℝ) : ℂ)) *
        (∑ hb ∈ (factorTuples (2 * (j + 1)) N).filter
            (fun hb => hb.prod = N),
          W hb * roughTupleWeight z y (roles j) hb) := by
  unfold literalHBOnlyAtQ
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro hb hhb
  have hfull : hb.prod = N := (Finset.mem_filter.mp hhb).2
  rw [hfull]
  ring

/-- The actual strict rough projector, NOT mu(N), kills every ordered
HB-only target occurrence when N is even and z >= 2. This also works
with arbitrary complex tuple-dependent W and at each individual q. -/
theorem literalHBOnlyAtQ_zero_of_even
    (N j q : ℕ) (z y : ℝ) (W : List ℕ → ℂ)
    (hz : (2 : ℝ) ≤ z) (hN : Even N) :
    literalHBOnlyAtQ N j q z y W = 0 := by
  unfold literalHBOnlyAtQ
  apply Finset.sum_eq_zero
  intro hb hhb
  have hword : hb ∈ factorTuples (2 * (j + 1)) N :=
    (Finset.mem_filter.mp hhb).1
  have hzero : roughTupleWeight z y (roles j) hb = 0 :=
    literal_occurrence_target_zero z y j N hz hN hb hword
  simp [hzero]

/-- Exactly one signed physical rho is used, with the original
+3,-3,+1 HB scalars and the exact full-product=N coprime mean.
No positivity or absolute values are imposed on rho or W. -/
def literalHBOnlySignedSameRhoTarget
    (N : ℕ) (z y : ℝ) (Q : Finset ℕ) (rho : ℕ → ℤ)
    (W : ℕ → List ℕ → ℂ) : ℂ :=
  ∑ q ∈ Q, (rho q : ℂ) *
    (∑ j ∈ Finset.range 3,
      (((( -1 : ℝ) ^ j * (Nat.choose 3 (j + 1) : ℝ) : ℝ) : ℂ)) *
        literalHBOnlyAtQ N j q z y (W j))

/-- The same physical rho-kernel factors out AFTER the full signed HB
sum, leaving all occurrence-dependent weights in the HB fibre.
The remaining scalar is not asserted to be small for odd targets. -/
theorem literalHBOnlySignedSameRhoTarget_factor
    (N : ℕ) (z y : ℝ) (Q : Finset ℕ) (rho : ℕ → ℤ)
    (W : ℕ → List ℕ → ℂ) :
    literalHBOnlySignedSameRhoTarget N z y Q rho W =
      (∑ q ∈ Q, (rho q : ℂ) *
        (((fineKernel N q N : ℝ) : ℂ))) *
      (∑ j ∈ Finset.range 3,
        (((( -1 : ℝ) ^ j * (Nat.choose 3 (j + 1) : ℝ) : ℝ) : ℂ)) *
        (∑ hb ∈ (factorTuples (2 * (j + 1)) N).filter
            (fun hb => hb.prod = N),
          W j hb * roughTupleWeight z y (roles j) hb)) := by
  unfold literalHBOnlySignedSameRhoTarget
  calc
    _ = ∑ q ∈ Q, (rho q : ℂ) *
          ((((fineKernel N q N : ℝ) : ℂ)) *
            (∑ j ∈ Finset.range 3,
              (((( -1 : ℝ) ^ j * (Nat.choose 3 (j + 1) : ℝ) : ℝ) : ℂ)) *
              (∑ hb ∈ (factorTuples (2 * (j + 1)) N).filter
                  (fun hb => hb.prod = N),
                W j hb * roughTupleWeight z y (roles j) hb))) := by
      apply Finset.sum_congr rfl
      intro q hq
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [literalHBOnlyAtQ_exact_factor]
      ring
    _ = _ := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro q hq
      ring

/-- Real, source-level payment of the fully rough HB-only diagonal
for every even N, at the SAME physical rho and exact coprime mean.
No squarefreeness of N and no new classical distribution input. -/
theorem literalHBOnlySignedSameRhoTarget_zero_even
    (N : ℕ) (z y : ℝ) (Q : Finset ℕ) (rho : ℕ → ℤ)
    (W : ℕ → List ℕ → ℂ)
    (hz : (2 : ℝ) ≤ z) (hN : Even N) :
    literalHBOnlySignedSameRhoTarget N z y Q rho W = 0 := by
  unfold literalHBOnlySignedSameRhoTarget
  apply Finset.sum_eq_zero
  intro q hq
  have hterms :
      (∑ j ∈ Finset.range 3,
        (((( -1 : ℝ) ^ j * (Nat.choose 3 (j + 1) : ℝ) : ℝ) : ℂ)) *
          literalHBOnlyAtQ N j q z y (W j)) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [literalHBOnlyAtQ_zero_of_even N j q z y (W j) hz hN]
    simp
  simp [hterms]

end
end ImbalancedChen.P3ActualLiteralHBOnlySameRhoEvenDiagonal
