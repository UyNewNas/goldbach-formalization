import ImbalancedChen.RealPhysicalUpperWeightBridge
import ImbalancedChen.CoprimeRecentering
import ImbalancedChen.Part3DistributionTargets
import ImbalancedChen.Part3SmoothCoprimeError

/-!
# P4B: exact transport of reference centres for the actual real product source

SOURCE-ONLY / YELLOW / UNCOMPILED. No analytic distribution estimate is
asserted here. The actual supplier expression required by the upper assembly
is `realPhysicalDistributionError`, defined in `FiniteUpperCarrierCore` with
the literal coprime mass as centre. The `UniformPrimeProductTarget` in
`Part3DistributionTargets` is an unproved obligation, not a supplier theorem.
The smooth coprime/progression bounds in `Part3SmoothCoprimeError` concern
their displayed smooth cutoff; they do not supply the real product error.

These identities transport an arbitrary reference centre to that exact
physical expression. The same rho is retained everywhere. A change of the
aggregate density centre costs exactly source mass times density difference.
All errors stay signed through the identities; absolute values first occur
in the final finite comparison lemmas. No estimate, goal-equivalence premise,
positivity of rho, or positive source mass is assumed.
-/

namespace ImbalancedChen.P4BCentreIdentity

noncomputable section

open scoped BigOperators

/-- Local reference densities are common to all residues. -/
def finiteSignedReferenceError
    (S Q : Finset ℕ) (weight rho : ℕ → ℝ) (a : ℕ)
    (centre : ℕ → ℝ) : ℝ :=
  ∑ d ∈ Q, rho d *
    finiteCommonMainError S weight (finiteSourceMass S weight * centre d) a d

/-- Changing the local reference density introduces exactly a signed
density correction multiplied by the actual source mass. -/
theorem finiteSignedReferenceError_change_centre
    (S Q : Finset ℕ) (weight rho : ℕ → ℝ) (a : ℕ)
    (centre₀ centre₁ : ℕ → ℝ) :
    finiteSignedReferenceError S Q weight rho a centre₀ =
      finiteSignedReferenceError S Q weight rho a centre₁ +
        finiteSourceMass S weight *
          (∑ d ∈ Q, rho d * (centre₁ d - centre₀ d)) := by
  unfold finiteSignedReferenceError finiteCommonMainError
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  ring

/-- The aggregate reference centre can be chosen without choosing a local
density profile. This formulation avoids dividing by the source mass. -/
def finiteAggregateReferenceError
    (S Q : Finset ℕ) (weight rho : ℕ → ℝ) (a : ℕ) (density : ℝ) : ℝ :=
  (∑ d ∈ Q, rho d * finiteCongruenceMass S weight a d) -
    finiteSourceMass S weight * density

theorem finiteAggregateReferenceError_change_centre
    (S Q : Finset ℕ) (weight rho : ℕ → ℝ) (a : ℕ)
    (density₀ density₁ : ℝ) :
    finiteAggregateReferenceError S Q weight rho a density₀ =
      finiteAggregateReferenceError S Q weight rho a density₁ +
        finiteSourceMass S weight * (density₁ - density₀) := by
  unfold finiteAggregateReferenceError
  ring

/-- Both reference-centre interfaces represent the identical signed sum. -/
theorem finiteSignedReferenceError_eq_aggregate
    (S Q : Finset ℕ) (weight rho : ℕ → ℝ) (a : ℕ)
    (centre : ℕ → ℝ) :
    finiteSignedReferenceError S Q weight rho a centre =
      finiteAggregateReferenceError S Q weight rho a
        (∑ d ∈ Q, rho d * centre d) := by
  unfold finiteSignedReferenceError finiteAggregateReferenceError finiteCommonMainError
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  ring

/-- Literal actual real half-product progression error with a reference
aggregate density. Its source retains the original inclusive endpoint. -/
def realReferenceCentreError
    (b : ℝ) (N : ℕ) (T : ℝ) (Q : Finset ℕ)
    (rho : ℕ → ℝ) (density : ℝ) : ℝ :=
  (∑ d ∈ Q, rho d * realHalfProductCongruenceMass b N T d) -
    ((realHalfProductSource b N T).card : ℝ) * density

/-- No source replacement occurs in the general finite specialization. -/
theorem realReferenceCentreError_eq_finiteAggregate
    (b : ℝ) (N : ℕ) (T : ℝ) (Q : Finset ℕ)
    (rho : ℕ → ℝ) (density : ℝ) :
    realReferenceCentreError b N T Q rho density =
      finiteAggregateReferenceError (realHalfProductSource b N T) Q
        (fun _ => 1) rho N density := by
  simp [realReferenceCentreError, finiteAggregateReferenceError,
    finiteSourceMass, finiteCongruenceMass, realHalfProductCongruenceMass]

theorem realReferenceCentreError_change_centre
    (b : ℝ) (N : ℕ) (T : ℝ) (Q : Finset ℕ)
    (rho : ℕ → ℝ) (density₀ density₁ : ℝ) :
    realReferenceCentreError b N T Q rho density₀ =
      realReferenceCentreError b N T Q rho density₁ +
        ((realHalfProductSource b N T).card : ℝ) * (density₁ - density₀) := by
  unfold realReferenceCentreError
  ring

/-- The physical error is precisely the primitive discrepancy of this
actual source, and not a smooth outer source or an independent coefficient. -/
theorem realPhysicalDistributionError_eq_actual_finitePrimitive
    (b : ℝ) (N : ℕ) (T : ℝ) (Q : Finset ℕ) (rho : ℕ → ℝ) :
    realPhysicalDistributionError b N T Q rho =
      ∑ d ∈ Q, rho d *
        finitePrimitiveDiscrepancy (realHalfProductSource b N T) (fun _ => 1) N d := by
  simp [realPhysicalDistributionError, finitePrimitiveDiscrepancy,
    finiteCongruenceMass, finiteCoprimeMass,
    realHalfProductCongruenceMass, realHalfProductCoprimeMass]

/-- The missing signed centre identity: the coprime correction and the
density correction have different meanings and both remain explicit. -/
theorem realReferenceCentreError_eq_physical_add_corrections
    (b : ℝ) (N : ℕ) (T : ℝ) (Q : Finset ℕ)
    (rho : ℕ → ℝ) (density : ℝ) :
    realReferenceCentreError b N T Q rho density =
      realPhysicalDistributionError b N T Q rho +
        realPhysicalCoprimeCorrection b N T Q rho +
        ((realHalfProductSource b N T).card : ℝ) *
          (physicalDensitySum Q rho - density) := by
  unfold realReferenceCentreError
  rw [sum_rho_mul_realHalfProductCongruenceMass_eq]
  ring

/-- Under the actual source roughness gate the coprime correction vanishes
by the existing theorem, including for signed rho and displayed zero terms. -/
theorem realReferenceCentreError_eq_physical_add_density_of_gate
    {b T : ℝ} {N z : ℕ} (Q : Finset ℕ) (rho : ℕ → ℝ) (density : ℝ)
    (hb : 0 < b) (hT : 0 < T) (hcap : (z : ℝ) ≤ T ^ (b / (1 + b)))
    (hsupport : ∀ d ∈ Q, rho d ≠ 0 → d ∣ sieveProduct N z) :
    realReferenceCentreError b N T Q rho density =
      realPhysicalDistributionError b N T Q rho +
        ((realHalfProductSource b N T).card : ℝ) *
          (physicalDensitySum Q rho - density) := by
  rw [realReferenceCentreError_eq_physical_add_corrections,
    realPhysicalCoprimeCorrection_eq_zero_of_gate Q rho hb hT hcap hsupport,
    add_zero]

/-- Literal specialization to the attached small/rough product coefficient.
This is a finite identity with its exact actual product source. -/
theorem actualSmallRough_referenceCentreError_eq_physical_add_corrections
    (b : ℝ) (N cap : ℕ) (T : ℝ) (retainOdd : List ℕ → Bool)
    (w z L density : ℝ) :
    realReferenceCentreError b N T (actualSmallRoughModuli retainOdd N cap w z)
        (actualSmallRoughRho retainOdd N cap w z L) density =
      realPhysicalDistributionError b N T
        (actualSmallRoughModuli retainOdd N cap w z)
        (actualSmallRoughRho retainOdd N cap w z L) +
      realPhysicalCoprimeCorrection b N T
        (actualSmallRoughModuli retainOdd N cap w z)
        (actualSmallRoughRho retainOdd N cap w z L) +
      ((realHalfProductSource b N T).card : ℝ) *
        (physicalDensitySum (actualSmallRoughModuli retainOdd N cap w z)
          (actualSmallRoughRho retainOdd N cap w z L) - density) := by
  exact realReferenceCentreError_eq_physical_add_corrections b N T _ _ density

/-- The active support condition is proved for this literal coefficient;
only the geometric gate and actual cutoff ordering remain hypotheses. -/
theorem actualSmallRough_referenceCentreError_eq_physical_add_density_of_gate
    {b T : ℝ} (N cap : ℕ) (retainOdd : List ℕ → Bool)
    (w z L density : ℝ) (hb : 0 < b) (hT : 0 < T) (hwz : w ≤ z)
    (hcap : (Nat.ceil z : ℝ) ≤ T ^ (b / (1 + b))) :
    realReferenceCentreError b N T (actualSmallRoughModuli retainOdd N cap w z)
        (actualSmallRoughRho retainOdd N cap w z L) density =
      realPhysicalDistributionError b N T
        (actualSmallRoughModuli retainOdd N cap w z)
        (actualSmallRoughRho retainOdd N cap w z L) +
      ((realHalfProductSource b N T).card : ℝ) *
        (physicalDensitySum (actualSmallRoughModuli retainOdd N cap w z)
          (actualSmallRoughRho retainOdd N cap w z L) - density) := by
  apply realReferenceCentreError_eq_physical_add_density_of_gate _ _ density hb hT hcap
  intro d hd hactive
  exact actualSmallRoughModuli_dvd_sieveProduct_ceil retainOdd N cap w z hwz hd

/-- Absolute values are introduced only after the full signed centre
transport has been proved. No termwise absolute modulus sum is used. -/
theorem abs_realReferenceCentreError_le_physical_add_corrections
    (b : ℝ) (N : ℕ) (T : ℝ) (Q : Finset ℕ)
    (rho : ℕ → ℝ) (density : ℝ) :
    |realReferenceCentreError b N T Q rho density| ≤
      |realPhysicalDistributionError b N T Q rho| +
        |realPhysicalCoprimeCorrection b N T Q rho| +
        ((realHalfProductSource b N T).card : ℝ) *
          |physicalDensitySum Q rho - density| := by
  rw [realReferenceCentreError_eq_physical_add_corrections]
  calc
    _ ≤ |realPhysicalDistributionError b N T Q rho +
          realPhysicalCoprimeCorrection b N T Q rho| +
        |((realHalfProductSource b N T).card : ℝ) *
          (physicalDensitySum Q rho - density)| := abs_add_le _ _
    _ ≤ (|realPhysicalDistributionError b N T Q rho| +
          |realPhysicalCoprimeCorrection b N T Q rho|) +
        |((realHalfProductSource b N T).card : ℝ) *
          (physicalDensitySum Q rho - density)| :=
      add_le_add_right (abs_add_le _ _) _
    _ = _ := by
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]

/-- The reverse signed identity is the direction needed if an independent
supplier estimates the reference-centred error. -/
theorem realPhysicalDistributionError_eq_reference_sub_corrections
    (b : ℝ) (N : ℕ) (T : ℝ) (Q : Finset ℕ)
    (rho : ℕ → ℝ) (density : ℝ) :
    realPhysicalDistributionError b N T Q rho =
      realReferenceCentreError b N T Q rho density -
        realPhysicalCoprimeCorrection b N T Q rho -
        ((realHalfProductSource b N T).card : ℝ) *
          (physicalDensitySum Q rho - density) := by
  rw [realReferenceCentreError_eq_physical_add_corrections]
  ring

theorem abs_realPhysicalDistributionError_le_reference_add_corrections
    (b : ℝ) (N : ℕ) (T : ℝ) (Q : Finset ℕ)
    (rho : ℕ → ℝ) (density : ℝ) :
    |realPhysicalDistributionError b N T Q rho| ≤
      |realReferenceCentreError b N T Q rho density| +
        |realPhysicalCoprimeCorrection b N T Q rho| +
        ((realHalfProductSource b N T).card : ℝ) *
          |physicalDensitySum Q rho - density| := by
  rw [realPhysicalDistributionError_eq_reference_sub_corrections b N T Q rho density]
  simp only [sub_eq_add_neg]
  calc
    _ ≤ |realReferenceCentreError b N T Q rho density +
          -realPhysicalCoprimeCorrection b N T Q rho| +
        |-(((realHalfProductSource b N T).card : ℝ) *
          (physicalDensitySum Q rho + -density))| := abs_add_le _ _
    _ ≤ (|realReferenceCentreError b N T Q rho density| +
          |-realPhysicalCoprimeCorrection b N T Q rho|) +
        |-(((realHalfProductSource b N T).card : ℝ) *
          (physicalDensitySum Q rho + -density))| :=
      add_le_add_right (abs_add_le _ _) _
    _ = _ := by
      rw [abs_neg, abs_neg, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]

end

end ImbalancedChen.P4BCentreIdentity
