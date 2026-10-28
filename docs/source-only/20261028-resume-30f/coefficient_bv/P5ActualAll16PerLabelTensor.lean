import ImbalancedChen.P5ActualRetainedInnerPerLabelConvolution
import ImbalancedChen.P5All16InnerCartesianAssembly

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

One-direction consumption of the independently frozen actual ALL16
canonical-inner/Cartesian source reconstruction. Every residual atom now
uses the ORIGINAL per-label factorial gamma, not E's slot-count gamma.
The original full prefix, common beta, all16 marked carrier and explicit
actual arithmetic wall are preserved. Rank exhaustion comes from the
independent actual compiler caller; it is not assumed here.

The marked prefix sum and arbitrary original E remain visible. No common
marked-colour scalar L1 budget or analytic factorability is inferred from
this exact residual tensor identity. Its residual-only assignment is not
identified with the full marked+rough REAL numerical assignment.
-/

namespace ImbalancedChen.P5Z.ActualAll16PerLabelTensor
noncomputable section
open Classical
open scoped BigOperators
open ImbalancedChen
open U1011OriginalSixteenArithmeticProducts
open OriginalOrdinaryPresievedSigma OriginalJointPresievedCompiler
open All16PhysicalOwnerDiscrepancy All16ActualInnerWallReconstruction
open All16InnerCartesianAssembly All16FineMeshGateScalar PresievedRoughGateMeshReserve
open ActualInnerPerLabelGamma ActualRetainedInnerPerLabelConvolution

def all16PerLabelInner (R n N m : ℕ) (eta : ℚ) (w B : ℝ)
    (E : ℕ × ℕ → Prop) (D A : Four → ℝ) (yz : Four → Bool) (F : ℕ → ℝ) : ℝ :=
  ∑ t ∈ U1011OriginalSixteenJointNearCapCompiler.ordinaryTuples n N E,
    ∑ r ∈ Finset.range (R + 1), ∑ j ∈ innerCells r 0 1 (rowEll n N eta t) m,
      let cap := Nat.ceil (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t)
      let Z := U1011OriginalSixteenJointNearCapCompiler.Z n N eta t
      let out := computedGroups (D t) (A t) (yz t) (meshUpper N m) (List.ofFn j)
      ∑ a ∈ ActualInnerMeshSeparatedGamma.groupSupport N cap m w Z out.1,
        ∑ b ∈ ActualInnerMeshSeparatedGamma.groupSupport N cap m w Z out.2.1,
          ∑ q3 ∈ ActualInnerMeshSeparatedGamma.attachedSupport N cap m w Z out.2.2,
            atomScalar j out * meshGamma N cap m w Z out.1 a * meshGamma N cap m w Z out.2.1 b *
              ActualInnerPerLabelGamma.attachedGamma N cap m r w Z B out.2.2 q3 *
                F (fullPrefix t * (a * b * q3))

/-- The SAME independently reconstructed full Cartesian all16 source,
now using original M1*M2*M3/M_all, with beta wholly in the third gamma. -/
theorem actual_cartesian_all16_eq_per_label {R n N m : ℕ} {eta : ℚ} {w B : ℝ}
    (hN : 1 < N) (heta : 0 < eta) (E : ℕ × ℕ → Prop)
    (D A : Four → ℝ) (yz : Four → Bool) (F : ℕ → ℝ) :
    all16CartesianInner R n N m eta w B E F =
      all16PerLabelInner R n N m eta w B E D A yz F := by
  unfold all16CartesianInner all16PerLabelInner
  apply Finset.sum_congr rfl
  intro t ht
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro j hj
  exact actual_inner_beta_per_label hN w
    (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t) (rowEll n N eta t) B
    (U1011OriginalSixteenJointNearCapCompiler.compiled_legality hN heta ht).2.1 hj
    (D t) (A t) (yz t) (fullPrefix t) F

/-- Full actual all16 inner source; the rank bound is derived by the
independent signed-owner physical caller, including the genuine W row. -/
theorem actual_all16_inner_eq_per_label {n N m : ℕ} {eta : ℚ} {B : ℝ}
    (hN : 1 < N) (heta : 0 < eta) (rho : ℝ) (hrho : 0 < rho)
    (E : ℕ × ℕ → Prop)
    (hw : ∀ t ∈ U1011OriginalSixteenJointNearCapCompiler.ordinaryTuples n N E,
      (N : ℝ) ^ rho ≤ U1011OriginalSixteenJointNearCapCompiler.Z n N eta t)
    (D A : Four → ℝ) (yz : Four → Bool) (F : ℕ → ℝ) :
    innerAtomLinear n N m eta ((N : ℝ) ^ rho) B E F =
      all16PerLabelInner (actualRoughVectorRankBound rho) n N m eta
        ((N : ℝ) ^ rho) B E D A yz F := by
  rw [actual_all16_inner_eq_cartesian hN heta rho hrho E hw,
    actual_cartesian_all16_eq_per_label hN heta E D A yz]

/-- The original independently defined all16 physical signed functional
equals ORIGINAL per-label residual tensors plus its actual wall rho.
Both count and exact coprime-mean tests use the SAME complete q. -/
theorem actual_all16_per_label_tensor_plus_wall {n N m : ℕ} {eta : ℚ} {B : ℝ}
    (hN : 1 < N) (heta : 0 < eta) (rho : ℝ) (hrho : 0 < rho)
    (E : ℕ × ℕ → Prop)
    (hw : ∀ t ∈ U1011OriginalSixteenJointNearCapCompiler.ordinaryTuples n N E,
      (N : ℝ) ^ rho ≤ U1011OriginalSixteenJointNearCapCompiler.Z n N eta t)
    (D A : Four → ℝ) (yz : Four → Bool) (F : ℕ → ℝ) :
    (∑ q ∈ jointSupport n N eta ((N : ℝ) ^ rho) E,
      jointPresievedSigma n N eta ((N : ℝ) ^ rho) B E q * F q) =
      all16PerLabelInner (actualRoughVectorRankBound rho) n N m eta
        ((N : ℝ) ^ rho) B E D A yz F +
      ∑ q ∈ wallSupport n N eta ((N : ℝ) ^ rho) m E,
        wallRho n N eta ((N : ℝ) ^ rho) B m E q * F q := by
  rw [actual_all16_inner_plus_wall,
    actual_all16_inner_eq_per_label hN heta rho hrho E hw D A yz]

end
end ImbalancedChen.P5Z.ActualAll16PerLabelTensor
