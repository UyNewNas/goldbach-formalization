import ImbalancedChen.P5All16InnerCartesianDictionary
import ImbalancedChen.P5All16SquarefreeRawProjection

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

This is the actual all16 caller of the independent inner Cartesian source
dictionary.  Its local rank guard is discharged from the original physical
all16 modulus bound, including W.  The precise original rowCoefficient,
small beta level, rough cutoff and marked prefix are preserved.

The E independently constructed inner-source theorem then absorbs the
ENTIRE small-beta sum into the third true group convolution.  No card(e)
loss and no rho/gate remains in that residual product test.  The original
marked tuple sum remains explicit: arbitrary E is not silently declared
geometric/factorable, and no independent-of-N complete marked restoring
scalar mass is claimed from a per-prefix body identity.
-/

namespace ImbalancedChen.P5Z.All16InnerCartesianAssembly
noncomputable section
open Classical
open scoped BigOperators
open ImbalancedChen
open U1011OriginalSixteenArithmeticProducts
open OriginalOrdinaryCommonBetaModel OriginalOrdinaryPresievedSigma
open OriginalJointPresievedCompiler OriginalPresievedRoughPrimeSlots
open All16PhysicalOwnerDiscrepancy All16SquarefreeRawProjection
open All16ActualInnerWallReconstruction All16InnerCartesianDictionary
open All16FineMeshGateScalar PresievedRoughGateMeshReserve
open ActualInnerMeshSeparatedGamma

/-- The actual original residual exponent of the same physical row. -/
def rowEll (n N : ℕ) (eta : ℚ) (t : Four) : ℝ :=
  (U1011OriginalSixteenNearCapBoxProfiles.physicalResidual
    (U1011OriginalSixteenStaticNativeCompiler.selectedPolicy n N t)
    (U1011OriginalSixteenStaticNativeCompiler.ownerBox n N t) eta : ℝ)

/-- Reorder only finite sums, after the actual divisor/whole-box
bijection. The small-beta support is its independent original carrier. -/
theorem actual_inner_beta_source_eq_complete_boxes {R N cap m : ℕ}
    (hN : 1 < N) (w Z ell B : ℝ) (hL : 1 < (N : ℝ) ^ ell)
    (hrank : ∀ d ∈ fixedRoughSupport (ordinaryRetainOdd ((N : ℝ) ^ ell)) N cap w Z,
      d.primeFactors.card ≤ R) (prefix : ℕ) (F : ℕ → ℝ) :
    (∑ e ∈ actualSmallRosserSupport N cap w,
      ∑ d ∈ fixedRoughSupport (ordinaryRetainOdd ((N : ℝ) ^ ell)) N cap w Z,
        if retainedInner N cap m w Z ell d then
          presievedCoefficient N cap w Z ((N : ℝ) ^ ell) B (e * d) * F (prefix * (e * d)) else 0) =
      ∑ r ∈ Finset.range (R + 1), ∑ j ∈ innerCells r 0 1 ell m,
        ∑ e ∈ actualSmallRosserSupport N cap w,
          (1 / (meshMultiplicity j : ℝ)) *
            ∑ ps ∈ meshPrimeBox N cap w Z m j,
              presievedCoefficient N cap w Z ((N : ℝ) ^ ell) B (e * ps.prod) *
                F (prefix * (e * ps.prod)) := by
  simp_rw [actual_retained_inner_source_eq_cartesian hN w Z ell B hL hrank prefix F]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  rw [Finset.sum_comm]

/-- Whole inner Cartesian atoms of the independently defined actual
all16 common-beta source. No gate or coefficient equality is an input. -/
def all16CartesianInner (R n N m : ℕ) (eta : ℚ) (w B : ℝ)
    (E : ℕ × ℕ → Prop) (F : ℕ → ℝ) : ℝ :=
  ∑ t ∈ U1011OriginalSixteenJointNearCapCompiler.ordinaryTuples n N E,
    ∑ r ∈ Finset.range (R + 1), ∑ j ∈ innerCells r 0 1 (rowEll n N eta t) m,
      ∑ e ∈ rowSmall n N eta w t,
        (1 / (meshMultiplicity j : ℝ)) *
          ∑ ps ∈ meshPrimeBox N
            (Nat.ceil (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t)) w
            (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t) m j,
            rowCoefficient n N eta w B t (e * ps.prod) * F (fullPrefix t * (e * ps.prod))

/-- All E actual innerPairs, including W and zero rows, equal complete
fine Cartesian atoms of the SAME source. The fixed rank is derived from
the actual physical compiler, not supplied as a support-equivalence guard. -/
theorem actual_all16_inner_eq_cartesian {n N m : ℕ} {eta : ℚ} {B : ℝ}
    (hN : 1 < N) (heta : 0 < eta) (rho : ℝ) (hrho : 0 < rho)
    (E : ℕ × ℕ → Prop)
    (hw : ∀ t ∈ U1011OriginalSixteenJointNearCapCompiler.ordinaryTuples n N E,
      (N : ℝ) ^ rho ≤ U1011OriginalSixteenJointNearCapCompiler.Z n N eta t)
    (F : ℕ → ℝ) :
    innerAtomLinear n N m eta ((N : ℝ) ^ rho) B E F =
      all16CartesianInner (actualRoughVectorRankBound rho) n N m eta ((N : ℝ) ^ rho) B E F := by
  unfold innerAtomLinear pairMarks all16CartesianInner
  rw [Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro t ht
  rw [Finset.sum_product]
  simp_rw [inner_cell_sum_eq_indicator]
  let cap := Nat.ceil (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t)
  let Z := U1011OriginalSixteenJointNearCapCompiler.Z n N eta t
  let ell := rowEll n N eta t
  let w := (N : ℝ) ^ rho
  have hL : 1 < (N : ℝ) ^ ell :=
    (U1011OriginalSixteenJointNearCapCompiler.compiled_legality hN heta ht).2.1
  have hrank : ∀ d ∈ fixedRoughSupport (ordinaryRetainOdd ((N : ℝ) ^ ell)) N cap w Z,
      d.primeFactors.card ≤ actualRoughVectorRankBound rho := by
    intro d hd
    exact actual_all16_rough_rank_bound hN heta rho hrho ht (hw t ht) hd
  exact actual_inner_beta_source_eq_complete_boxes hN w Z ell B hL hrank (fullPrefix t) F

/-- Residual three-group tensor bodies, with the complete beta sum in
attachedGamma3. The marked source sum remains explicit and unchanged. -/
def all16BetaAbsorbedInner (R n N m : ℕ) (eta : ℚ) (w B : ℝ)
    (E : ℕ × ℕ → Prop) (D A : Four → ℝ) (yz : Four → Bool) (F : ℕ → ℝ) : ℝ :=
  ∑ t ∈ U1011OriginalSixteenJointNearCapCompiler.ordinaryTuples n N E,
    ∑ r ∈ Finset.range (R + 1), ∑ j ∈ innerCells r 0 1 (rowEll n N eta t) m,
      let cap := Nat.ceil (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t)
      let Z := U1011OriginalSixteenJointNearCapCompiler.Z n N eta t
      let out := computedGroups (D t) (A t) (yz t) (meshUpper N m) (List.ofFn j)
      ∑ a ∈ groupSupport N cap m w Z out.1,
        ∑ b ∈ groupSupport N cap m w Z out.2.1,
          ∑ q3 ∈ attachedSupport N cap m w Z out.2.2,
            atomScalar j out * gamma N cap m w Z out.1 a * gamma N cap m w Z out.2.1 b *
              attachedGamma N cap m r w Z B out.2.2 q3 * F (fullPrefix t * (a * b * q3))

/-- Small beta is truly summed and absorbed into the third convolution;
this identity has no fixed-prefix/e mass or cardinality assumption. -/
theorem actual_cartesian_inner_eq_beta_absorbed {R n N m : ℕ} {eta : ℚ} {w B : ℝ}
    (hN : 1 < N) (heta : 0 < eta) (E : ℕ × ℕ → Prop)
    (D A : Four → ℝ) (yz : Four → Bool) (F : ℕ → ℝ) :
    all16CartesianInner R n N m eta w B E F =
      all16BetaAbsorbedInner R n N m eta w B E D A yz F := by
  unfold all16CartesianInner all16BetaAbsorbedInner
  apply Finset.sum_congr rfl
  intro t ht
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro j hj
  exact actual_ordinary_inner_source_three_convolution hN w
    (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t) (rowEll n N eta t) B
    (U1011OriginalSixteenJointNearCapCompiler.compiled_legality hN heta ht).2.1 hj
    (D t) (A t) (yz t) (fullPrefix t) F

/-- Actual FULL all16 physical signed coefficient = residual tensors
with all small beta absorbed + the independently defined actual arithmetic
wall coefficient. Arbitrary E is still visible in the marked tuple sum. -/
theorem actual_all16_beta_tensor_plus_wall {n N m : ℕ} {eta : ℚ} {B : ℝ}
    (hN : 1 < N) (heta : 0 < eta) (rho : ℝ) (hrho : 0 < rho)
    (E : ℕ × ℕ → Prop)
    (hw : ∀ t ∈ U1011OriginalSixteenJointNearCapCompiler.ordinaryTuples n N E,
      (N : ℝ) ^ rho ≤ U1011OriginalSixteenJointNearCapCompiler.Z n N eta t)
    (D A : Four → ℝ) (yz : Four → Bool) (F : ℕ → ℝ) :
    (∑ q ∈ jointSupport n N eta ((N : ℝ) ^ rho) E,
      jointPresievedSigma n N eta ((N : ℝ) ^ rho) B E q * F q) =
      all16BetaAbsorbedInner (actualRoughVectorRankBound rho) n N m eta
        ((N : ℝ) ^ rho) B E D A yz F +
      ∑ q ∈ wallSupport n N eta ((N : ℝ) ^ rho) m E,
        wallRho n N eta ((N : ℝ) ^ rho) B m E q * F q := by
  rw [actual_all16_inner_plus_wall,
    actual_all16_inner_eq_cartesian hN heta rho hrho E hw,
    actual_cartesian_inner_eq_beta_absorbed hN heta E D A yz]

end
end ImbalancedChen.P5Z.All16InnerCartesianAssembly
