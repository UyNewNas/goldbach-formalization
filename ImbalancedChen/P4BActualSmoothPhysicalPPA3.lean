import ImbalancedChen.P4BLabelledOuterPPUpperAssembly
import ImbalancedChen.P4BSmoothPhysicalPairOuterRamp

/-!
# The exact A = 3 input for the actual smooth physical source

SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

All source and coefficient data are fixed before the positive constant and
threshold are selected. The attachment epsilon is distinct from the eventual
error tolerance. The labelled-prime cap is N, while cap is the independent
enumeration cap used to construct the literal attached coefficient.

This file proves only the exact signed full-product pushforward and its
log-saving budget from the displayed A = 3 estimate. That genuine P3 estimate,
including its licensing for this physical source and attached rho, remains
OPEN. No upper-count, spectral, or distribution conclusion is assumed to have
been proved. Smoothness alone supplies none of this estimate.

The existing smooth mass reserve chooses physicalWidth before this predicate
is invoked. No interchange of forall width with exists C,N0 is needed for
the original fixed-real-b upper consumer; its final threshold may depend on
that selected width and on the requested error tolerance.
-/

namespace ImbalancedChen.P4BActualSmoothPhysicalPPA3

noncomputable section
open Filter Topology
open scoped BigOperators
open Part3 P4BLabelledOuterPushforward

/-- Minimal concrete P3 input: a single exponent, genuine rank two, the
actual smooth physical weight, and the identical attached signed rho.
All arguments precede C,N0. No uniformity in epsilon or width is asserted. -/
def ActualSmoothPhysicalPPA3
    (b kappa nu r epsilon : ℝ)
    (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ) (physicalWidth : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → Even N →
    |primeProductSignedError 2 N N
      (attachedUpperModuli nu r epsilon retain cap N)
      (attachedUpperCoefficient nu r epsilon retain cap N)
      (P4B.smoothPhysicalPairOuterRamp b N
        (manuscriptHalfProductCutoff kappa N) physicalWidth)| ≤
      C * (N : ℝ) / (Real.log (N : ℝ)) ^ (3 : ℕ)

/-- The existing all-exponent target implies the minimal A = 3 input.
The reverse implication is neither used nor claimed. -/
theorem actualSmoothPhysicalPPA3_of_uniformPP
    (b kappa nu r epsilon : ℝ)
    (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ) (physicalWidth : ℝ)
    (hUniformPP : UniformPrimeProductTarget (ι := Unit) 2 (fun N : ℕ => N)
      (attachedUpperModuli nu r epsilon retain cap)
      (attachedUpperCoefficient nu r epsilon retain cap)
      (fun N _ => P4B.smoothPhysicalPairOuterRamp b N
        (manuscriptHalfProductCutoff kappa N) physicalWidth)) :
    ActualSmoothPhysicalPPA3 b kappa nu r epsilon retain cap physicalWidth := by
  obtain ⟨C, hC, N0, hPP⟩ := hUniformPP (3 : ℝ) (by norm_num)
  refine ⟨C, hC, N0, ?_⟩
  intro N hN hEven
  rw [← Real.rpow_natCast (Real.log (N : ℝ)) (3 : ℕ)]
  exact hPP N hN hEven Unit.unit

/-- Exact same-rho primitive discrepancy budget from A = 3 alone.
The carrier retains every labelled product, including products above N.
All modulus signs remain inside one absolute value. The fresh tolerance
does not alter the fixed attachment epsilon, width, or rho. -/
theorem eventually_signed_full_productWeight_le_of_actualSmoothPhysicalPPA3
    (b kappa nu r epsilon : ℝ)
    (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ) (physicalWidth : ℝ)
    (hA3 : ActualSmoothPhysicalPPA3 b kappa nu r epsilon retain cap physicalWidth)
    (tolerance : ℝ) (htolerance : 0 < tolerance) :
    ∀ᶠ N : ℕ in atTop, Even N →
      |∑ d ∈ attachedUpperModuli nu r epsilon retain cap N,
        attachedUpperCoefficient nu r epsilon retain cap N d *
          finitePrimitiveDiscrepancy (productCarrier N)
            (productWeight N (P4B.smoothPhysicalPairOuterRamp b N
              (manuscriptHalfProductCutoff kappa N) physicalWidth)) N d| ≤
        tolerance * singularNormalization N := by
  obtain ⟨C, hC, N0, hPP⟩ := hA3
  filter_upwards
    [eventually_logSaving_le_singularNormalization C hC.le 3 (by norm_num)
      tolerance htolerance, eventually_ge_atTop N0] with N hbudget hN
  intro hEven
  rw [signed_productWeight_eq_primeProductSignedError]
  exact (hPP N hN hEven).trans hbudget.2

end
end ImbalancedChen.P4BActualSmoothPhysicalPPA3
