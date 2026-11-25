import ImbalancedChen.P2LowerFiniteCellBetaCompiler
import ImbalancedChen.P5OriginalU5PhysicalRho

/-!
# The actual finite-cell rounded output in the original U5 count

SOURCE ONLY / UNCOMPILED / NO KERNEL ACCEPTANCE.

The coefficient below is the existing finite-cell compiler's output,
including its original sign-sensitive small Rosser attachment. It is not
identified with the raw rho of any newly chosen retained policy.

The existing physical minorant, the original attachment gates, exact
quotient-source Fubini and the original labelled U5 count dictionary
give a genuine finite count entrance for this output. Its primitive mean
is kept literally as the coprime prime mass divided by phi of the FULL
physical modulus. The same rounded rho remains in that mean, the signed
primitive discrepancy and the signed centre correction.

No numerical density estimate, small rounding loss, physical support cap,
whole-word tensor identity, common Q, family admission or PP estimate is
assumed or obtained here. The old rounding is still on residual fibres
for each outer pair; this does not turn it into a whole-word atomization.
-/

namespace ImbalancedChen.P3OriginalU5RoundedCountInsertion

noncomputable section
open scoped Classical BigOperators
open P5OriginalU5CausalFinite (cutoff pairSupport smallCutoff smallLevel attachment_gates)
open P5OriginalU5PlateauPrimeBV (Policy markedProduct fullModulus)

/-- The compiler's actual complete small/rough carrier. -/
abbrev roundedSupport (N : ℕ) (epsilon : ℝ) : Finset ℕ :=
  P2LowerFiniteCellBetaCompiler.support N (Nat.ceil (cutoff N))
    (smallCutoff N epsilon) (cutoff N)

/-- The existing signed rounded coefficient, with exactly the original
U5 small-cutoff and small-level choices. -/
abbrev roundedRho (N : ℕ) (epsilon tau : ℝ) (policy : List ℕ → Bool) : ℕ → ℝ :=
  P2LowerFiniteCellBetaCompiler.rho policy N (Nat.ceil (cutoff N))
    (smallCutoff N epsilon) (cutoff N) tau (smallLevel N epsilon)

def rowEstimator (N : ℕ) (epsilon tau : ℝ) (policy : List ℕ → Bool)
    (t : ℕ × ℕ) : ℝ :=
  ∑ k ∈ roundedSupport N epsilon, roundedRho N epsilon tau policy k *
    (chenPrimeAPCount N N (fullModulus t k) -
      chenCentrePrimeAPCount N N (fullModulus t k))

/-- The EXACT coprime mean at the original full modulus. No replacement
by the total prime mass, li(N), or a different rho is made. -/
def rowExactMean (N : ℕ) (epsilon tau : ℝ) (policy : List ℕ → Bool)
    (t : ℕ × ℕ) : ℝ :=
  ∑ k ∈ roundedSupport N epsilon, roundedRho N epsilon tau policy k *
    (finiteCoprimeMass (chenPrimePrefix N) (fun _ => 1) (fullModulus t k) /
      (Nat.totient (fullModulus t k) : ℝ))

def rowSignedPrimitive (N : ℕ) (epsilon tau : ℝ) (policy : List ℕ → Bool)
    (t : ℕ × ℕ) : ℝ :=
  ∑ k ∈ roundedSupport N epsilon, roundedRho N epsilon tau policy k *
    finitePrimitiveDiscrepancy (chenPrimePrefix N) (fun _ => 1) N (fullModulus t k)

def rowSignedCentre (N : ℕ) (epsilon tau : ℝ) (policy : List ℕ → Bool)
    (t : ℕ × ℕ) : ℝ :=
  ∑ k ∈ roundedSupport N epsilon, roundedRho N epsilon tau policy k *
    chenCentrePrimeAPCount N N (fullModulus t k)

/-- This is a derived minorant for the ACTUAL rounded output. The input
does not supply a raw count inequality or an equality with a raw policy rho. -/
theorem rowEstimator_le_sifted {N : ℕ} (hN : 2 ≤ N) {epsilon : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon8 : epsilon < 1 / 8)
    (tau : ℝ) (policy : List ℕ → Bool) (t : ℕ × ℕ) :
    rowEstimator N epsilon tau policy t ≤
      ((chenSiftedQuotientPrimeSource N (markedProduct t) (cutoff N)).card : ℝ) := by
  have hg := attachment_gates hN hepsilon hepsilon8
  have hfub := P5CausalRhoQuotientBridge.quotient_sum_physicalDivisorSum
    N (markedProduct t) (roundedSupport N epsilon) (roundedRho N epsilon tau policy)
  change (∑ q ∈ chenQuotientPrimeSource N (markedProduct t),
    physicalDivisorSum (roundedSupport N epsilon) (roundedRho N epsilon tau policy) q) =
      rowEstimator N epsilon tau policy t at hfub
  rw [← hfub]
  have hind (q : ℕ) : actualSmallRoughIndicator N (cutoff N) (q : ℤ) =
      if Nat.Coprime q (sieveProduct N (Nat.ceil (cutoff N))) then (1 : ℝ) else 0 := by
    unfold actualSmallRoughIndicator
    rw [← actualSmallPrimeProduct_coprime_natAbs_iff N (Nat.ceil (cutoff N))
      (cutoff N) (Nat.le_ceil _) (q : ℤ)]
    simp only [Int.natAbs_natCast,
      currentChen_actualSmallPrimeProduct_eq_sieveProduct N (Nat.ceil (cutoff N))
        (cutoff N) (Nat.le_ceil _), Nat.coprime_comm]
  calc
    _ ≤ ∑ q ∈ chenQuotientPrimeSource N (markedProduct t),
        if Nat.Coprime q (sieveProduct N (Nat.ceil (cutoff N))) then (1 : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro q _
      have h := P2LowerFiniteCellBetaCompiler.rho_minorant policy N
        (Nat.ceil (cutoff N)) (smallCutoff N epsilon) (cutoff N) tau
        (smallLevel N epsilon) hg.1 hg.2.1 hg.2.2 (Nat.le_ceil _) (q : ℤ)
      simpa only [Int.natAbs_natCast, hind q] using h
    _ = _ := by
      rw [← Finset.sum_filter, ← chenSiftedQuotientPrimeSource_eq_coprime_filter]
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one]

/-- Exact finite decomposition with the SAME rounded coefficient. The
coprime mean is retained, so no modulus-prime correction is discarded. -/
theorem rowEstimator_eq_exact_mean_and_signed (N : ℕ) (epsilon tau : ℝ)
    (policy : List ℕ → Bool) (t : ℕ × ℕ) :
    rowEstimator N epsilon tau policy t = rowExactMean N epsilon tau policy t +
      rowSignedPrimitive N epsilon tau policy t - rowSignedCentre N epsilon tau policy t := by
  simp only [rowEstimator, rowExactMean, rowSignedPrimitive, rowSignedCentre,
    ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  have hAP : finiteCongruenceMass (chenPrimePrefix N) (fun _ => 1) N (fullModulus t k) =
      chenPrimeAPCount N N (fullModulus t k) := by
    simp [finiteCongruenceMass, chenPrimeAPCount]
  rw [finitePrimitiveDiscrepancy, hAP]
  ring

/-- Original U5 ordered pair labels and their original multiplicities
are unchanged. Each row uses its actual finite-cell rounded output. -/
theorem original_U5_rounded_count_lower {N : ℕ} (hN : 2 ≤ N) {epsilon : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon8 : epsilon < 1 / 8)
    (tau : ℝ) (policy : Policy) :
    (∑ t ∈ pairSupport N, rowEstimator N epsilon tau (policy t) t) ≤
      currentChenUpsilon5 N := by
  rw [currentChenUpsilon5_eq_siftedQuotientPrimeSource]
  exact Finset.sum_le_sum (fun t _ => rowEstimator_le_sifted
    hN hepsilon hepsilon8 tau (policy t) t)

/-- A finite count entrance for the actual rounded U5 output, retaining
its exact primitive mean, signed discrepancy and signed centre term.
The remaining density and distribution estimates are not hypotheses. -/
theorem original_U5_rounded_exact_mean_lower {N : ℕ} (hN : 2 ≤ N) {epsilon : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon8 : epsilon < 1 / 8)
    (tau : ℝ) (policy : Policy) :
    (∑ t ∈ pairSupport N, rowExactMean N epsilon tau (policy t) t) +
      (∑ t ∈ pairSupport N, rowSignedPrimitive N epsilon tau (policy t) t) -
      (∑ t ∈ pairSupport N, rowSignedCentre N epsilon tau (policy t) t) ≤
        currentChenUpsilon5 N := by
  have h := original_U5_rounded_count_lower hN hepsilon hepsilon8 tau policy
  simpa only [rowEstimator_eq_exact_mean_and_signed,
    Finset.sum_add_distrib, Finset.sum_sub_distrib] using h

end
end ImbalancedChen.P3OriginalU5RoundedCountInsertion
