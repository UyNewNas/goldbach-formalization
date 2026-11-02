import ImbalancedChen.P5All16ComputedWholeWordAssignment
import ImbalancedChen.P5All16MarkedCommonFineAssembly
import ImbalancedChen.P5ActualMarkedSameAssignmentTensor

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The actual original all16 common-beta coefficient is expanded using the
computed selected/W whole-word groups, with its genuine arithmetic
remainder unchanged.  The restoring scalar L1 norm is proved for those
VERY tensors.  Every marked prime and every small beta value is inside
the three convolutions, and only M_res appears in the restoring scalar.

No partition, scalar budget, gamma bound, source equality, independent-u
Family cover, wall estimate or PP estimate is an input.  The result is
finite algebra on the certified whole-cell subsource plus its exact
complement.  Paying that complement and licensing all endpoint groups
analytically remain separate internal obligations.
-/

namespace ImbalancedChen.P5Z.All16ComputedMarkedTensorBudget
noncomputable section
open Classical Set
open scoped BigOperators
open ImbalancedChen
open OriginalJointPresievedCompiler
open All16MarkedCommonFineSource All16MarkedFineScalarBudget
open All16MarkedCommonFineAssembly All16ComputedWholeWordAssignment
open ActualInnerPerLabelGamma SameWholeAssignmentPerLabel

/-- Literal original signed restoring scalar.  The marked factorial
has not been divided out; G derives it to be one on these strict cells. -/
def scalar (n N m r : ℕ) (eta : ℚ) (epsilon A : ℝ) (k : Key n m r) : ℝ :=
  restoringScalar epsilon k.2.2 (labelGroups n N m r eta A k)

/-- Normalized real three-group convolution at the complete modulus.
Group3 contains the entire original common beta sum.  No marked prime,
owner indicator, or residual support test is hidden in F. -/
def tensor (n N m r : ℕ) (eta : ℚ) (rho B A : ℝ) (k : Key n m r)
    (F : ℕ → ℝ) : ℝ :=
  let out := labelGroups n N m r eta A k
  ∑ x ∈ support (commonAlphabet N m) out.1,
    ∑ y ∈ support (commonAlphabet N m) out.2.1,
      ∑ q3 ∈ attachedSupport (commonAlphabet N m) out.2.2
        N (cellCap n N eta k.1) ((N : ℝ) ^ rho),
        gamma (commonAlphabet N m) out.1 x * gamma (commonAlphabet N m) out.2.1 y *
          attachedGamma (commonAlphabet N m) out.2.2
            N (cellCap n N eta k.1) r ((N : ℝ) ^ rho) B q3 * F (x * y * q3)

/-- These are exactly the sequences in `tensor`, including rank zero
and the beta-attached third group, bounded on ALL natural integers. -/
theorem computed_gamma_one_bounds {n N m r : ℕ} (hN : 1 < N)
    {eta : ℚ} {rho B : ℝ} {M : Set (ℝ × ℝ)} {k : Key n m r}
    (hk : k ∈ certifiedKeys n m r eta rho M) (A : ℝ) :
    let out := labelGroups n N m r eta A k
    (∀ x, |gamma (commonAlphabet N m) out.1 x| ≤ 1) ∧
      (∀ y, |gamma (commonAlphabet N m) out.2.1 y| ≤ 1) ∧
      (∀ q3, |attachedGamma (commonAlphabet N m) out.2.2
        N (cellCap n N eta k.1) r ((N : ℝ) ^ rho) B q3| ≤ 1) := by
  have h := (Finset.mem_filter.mp hk).2
  exact ActualMarkedSameAssignmentTensor.actual_marked_whole_gamma_bounds (betaLevel := B) hN h.1 h.2
    (labelGroups n N m r eta A k) (labelGroups_partition n N m r eta A k)

theorem scalar_eq_mul (n N m r : ℕ) (eta : ℚ) (epsilon A : ℝ) (k : Key n m r) :
    scalar n N m r eta epsilon A k = epsilon * scalar n N m r eta 1 A k := by
  dsimp only [scalar, restoringScalar]
  ring

/-- The restoring scalar on the actual computed groups has the exact
absolute value |epsilon|.  Residual parity and the sign of epsilon are
retained; no positive replacement of the source coefficient occurs. -/
theorem computed_scalar_abs {n N m r : ℕ} {eta : ℚ} {rho : ℝ}
    {M : Set (ℝ × ℝ)} {k : Key n m r}
    (hk : k ∈ certifiedKeys n m r eta rho M) (epsilon A : ℝ) :
    |scalar n N m r eta epsilon A k| = |epsilon| := by
  exact restoring_scalar_abs (Finset.mem_filter.mp hk).2.1 epsilon
    (labelGroups n N m r eta A k) (labelGroups_partition n N m r eta A k)

/-- Exact L1 norm of the computed restoring scalars.  This is a count
of fixed geometric cells, never of arithmetic prime tuples or beta e. -/
theorem computed_scalar_mass_eq (R n N m : ℕ) (eta : ℚ) (rho epsilon : ℝ)
    (M : Set (ℝ × ℝ)) (A : ∀ r, Key n m r → ℝ) :
    (∑ r ∈ Finset.range (R + 1), ∑ k ∈ certifiedKeys n m r eta rho M,
      |scalar n N m r eta epsilon (A r k) k|) =
      |epsilon| * ∑ r ∈ Finset.range (R + 1),
        ((certifiedKeys n m r eta rho M).card : ℝ) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  calc
    _ = ∑ _k ∈ certifiedKeys n m r eta rho M, |epsilon| := by
      apply Finset.sum_congr rfl
      intro k hk
      exact computed_scalar_abs hk epsilon (A r k)
    _ = _ := by simp [mul_comm]

/-- The requested N-independent restoring L1 budget, now for the SAME
actual selected/W tensors used in the full original source identity.
A may vary with N and the atom, but is frozen before any prime tuple or
discrepancy test.  The right side contains neither N nor A nor beta. -/
theorem computed_scalar_mass_le (R n N m : ℕ) (eta : ℚ) (rho epsilon : ℝ)
    (M : Set (ℝ × ℝ)) (A : ∀ r, Key n m r → ℝ) :
    (∑ r ∈ Finset.range (R + 1), ∑ k ∈ certifiedKeys n m r eta rho M,
      |scalar n N m r eta epsilon (A r k) k|) ≤ |epsilon| * scalarBudget R n m := by
  exact complete_cartesian_scalar_mass R n m eta rho epsilon M
    (fun r k => labelGroups n N m r eta (A r k) k)
    (fun r hr k hk => labelGroups_partition n N m r eta (A r k) k)

/-- The independently defined G raw atom is converted to these computed
groups.  The local physical source equality is used in its proved
direction, not supplied as an assumption or encoded in F. -/
theorem raw_atom_eq_computed_tensor {n N m r : ℕ} (hN : 1 < N)
    {eta : ℚ} (heta : 0 < eta) (rho B : ℝ) (M : Set (ℝ × ℝ))
    {k : Key n m r} (hk : k ∈ certifiedKeys n m r eta rho M)
    (A : ℝ) (F : ℕ → ℝ) :
    rawAtomLinear n N m r eta rho B k F =
      scalar n N m r eta 1 A k * tensor n N m r eta rho B A k F := by
  have h := (Finset.mem_filter.mp hk).2
  have ht := ActualMarkedSameAssignmentTensor.actual_marked_whole_source_tensor
    (betaLevel := B) hN heta h.1 h.2 (labelGroups n N m r eta A k)
    (labelGroups_partition n N m r eta A k) F
  rw [whole_cell_source_eq_raw_full_box (B := B) hN heta h.1 F] at ht
  change rawAtomLinear n N m r eta rho B k F = _ at ht
  calc
    _ = _ := ht
    _ = _ := by simp only [scalar, tensor, Finset.mul_sum, mul_assoc]

/-- Full original coefficient at its SAME physical q, including the
entire independent arithmetic complement of the certified whole boxes.
There is no arbitrary allocation, hpart, L1 budget or cover premise. -/
theorem actual_all16_computed_tensor_plus_remainder
    (R n N m : ℕ) (hN : 1 < N) (eta : ℚ) (heta : 0 < eta)
    (rho B : ℝ) (M : Set (ℝ × ℝ)) (A : ∀ r, Key n m r → ℝ) (F : ℕ → ℝ) :
    (∑ q ∈ jointSupport n N eta ((N : ℝ) ^ rho)
      (U1011OriginalPairedRowPrimeTests.nativeMask M N),
      jointPresievedSigma n N eta ((N : ℝ) ^ rho) B
        (U1011OriginalPairedRowPrimeTests.nativeMask M N) q * F q) =
      (∑ r ∈ Finset.range (R + 1), ∑ k ∈ certifiedKeys n m r eta rho M,
        scalar n N m r eta 1 (A r k) k * tensor n N m r eta rho B (A r k) k F) +
      ∑ q ∈ remainderSupport R n N m eta rho M,
        remainderRho R n N m eta rho B M q * F q := by
  rw [actual_all16_common_fine_plus_remainder R n N m hN eta heta rho B M F]
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro k hk
  exact raw_atom_eq_computed_tensor hN heta rho B M hk (A r k) F

/-- Original external state signs multiply BOTH the actual coefficient
and the genuine remainder.  The sign is kept in the restoring scalar,
so the companion L1 estimate uses |epsilon| and applies to signed rows. -/
theorem actual_signed_computed_tensor_plus_remainder
    (R n N m : ℕ) (hN : 1 < N) (eta : ℚ) (heta : 0 < eta)
    (rho B epsilon : ℝ) (M : Set (ℝ × ℝ)) (A : ∀ r, Key n m r → ℝ) (F : ℕ → ℝ) :
    epsilon * (∑ q ∈ jointSupport n N eta ((N : ℝ) ^ rho)
      (U1011OriginalPairedRowPrimeTests.nativeMask M N),
      jointPresievedSigma n N eta ((N : ℝ) ^ rho) B
        (U1011OriginalPairedRowPrimeTests.nativeMask M N) q * F q) =
      (∑ r ∈ Finset.range (R + 1), ∑ k ∈ certifiedKeys n m r eta rho M,
        scalar n N m r eta epsilon (A r k) k * tensor n N m r eta rho B (A r k) k F) +
      epsilon * ∑ q ∈ remainderSupport R n N m eta rho M,
        remainderRho R n N m eta rho B M q * F q := by
  rw [actual_all16_computed_tensor_plus_remainder R n N m hN eta heta rho B M A F]
  rw [mul_add, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [scalar_eq_mul n N m r eta epsilon (A r k) k]
  ring

/-- Concrete physical-density consumer with the actual adopted pair
mask, at the original complete q and original reciprocal totient. -/
theorem adopted_jointDensity_computed
    (R n N m : ℕ) (hN : 1 < N) (eta : ℚ) (heta : 0 < eta)
    (rho B : ℝ) (A : ∀ r, Key n m r → ℝ) :
    jointDensity n N eta ((N : ℝ) ^ rho) B (FullMask.P1E0E1.deletionMask (N : ℝ)) =
      (∑ r ∈ Finset.range (R + 1),
        ∑ k ∈ certifiedKeys n m r eta rho FullMask.P1E0E1.pairRegion,
          scalar n N m r eta 1 (A r k) k *
            tensor n N m r eta rho B (A r k) k (fun q => 1 / (Nat.totient q : ℝ))) +
      ∑ q ∈ remainderSupport R n N m eta rho FullMask.P1E0E1.pairRegion,
        remainderRho R n N m eta rho B FullMask.P1E0E1.pairRegion q / (Nat.totient q : ℝ) := by
  simpa only [jointDensity, physicalDensitySum,
    U1011OriginalPairedRowPrimeTests.nativeMask_actual_adopted, div_eq_mul_inv, one_mul] using
    actual_all16_computed_tensor_plus_remainder R n N m hN eta heta rho B
      FullMask.P1E0E1.pairRegion A (fun q => 1 / (Nat.totient q : ℝ))

/-- Concrete original AP-error consumer: the same actual coefficient,
same adopted mask, and the original true-Li/totient mean.  No analytic
estimate is asserted or imported by this exact finite substitution. -/
theorem adopted_jointAP_computed
    (R n N m : ℕ) (hN : 1 < N) (eta : ℚ) (heta : 0 < eta)
    (rho B : ℝ) (A : ∀ r, Key n m r → ℝ) :
    jointAP n N eta ((N : ℝ) ^ rho) B (FullMask.P1E0E1.deletionMask (N : ℝ)) =
      (∑ r ∈ Finset.range (R + 1),
        ∑ k ∈ certifiedKeys n m r eta rho FullMask.P1E0E1.pairRegion,
          scalar n N m r eta 1 (A r k) k * tensor n N m r eta rho B (A r k) k
            (chenQuotientPrimeAPError N (MathlibNt.SieveTheory.BombieriVinogradov.trueLogarithmicIntegral N))) +
      ∑ q ∈ remainderSupport R n N m eta rho FullMask.P1E0E1.pairRegion,
        remainderRho R n N m eta rho B FullMask.P1E0E1.pairRegion q *
          chenQuotientPrimeAPError N (MathlibNt.SieveTheory.BombieriVinogradov.trueLogarithmicIntegral N) q := by
  simpa only [jointAP, U1011OriginalPairedRowPrimeTests.nativeMask_actual_adopted] using
    actual_all16_computed_tensor_plus_remainder R n N m hN eta heta rho B
      FullMask.P1E0E1.pairRegion A
      (chenQuotientPrimeAPError N (MathlibNt.SieveTheory.BombieriVinogradov.trueLogarithmicIntegral N))

end
end ImbalancedChen.P5Z.All16ComputedMarkedTensorBudget
