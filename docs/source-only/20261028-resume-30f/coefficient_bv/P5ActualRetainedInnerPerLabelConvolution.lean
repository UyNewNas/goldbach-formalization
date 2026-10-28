import ImbalancedChen.P5ActualInnerPerLabelGamma
import ImbalancedChen.P5All16InnerCartesianDictionary

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The independently frozen signed-owner dictionary is consumed in one
direction: actual retained canonical inner source -> complete Cartesian
atoms -> ORIGINAL per-label three-convolutions. No equality to the tensor
is assumed. This source port preserves its explicit physical rank bound.
Actual all16 rank exhaustion and marked common-colour/scalar absorption
belong to the independently constructed caller, not a final premise here.
-/

namespace ImbalancedChen.P5Z.ActualRetainedInnerPerLabelConvolution
noncomputable section
open Classical
open scoped BigOperators
open ImbalancedChen
open OriginalOrdinaryCommonBetaModel PresievedRoughGateMeshReserve
open All16FineMeshGateScalar All16InnerCartesianDictionary
open ActualInnerPerLabelGamma

/-- Every actual inner atom has three ORIGINAL label-normalized
one-bounded coefficients, with actual beta only in group3. The original
factorial-ratio scalar has absolute value exactly one on these cells. -/
theorem actual_inner_per_label_one_bounds {r N cap m : ℕ} (hN : 1 < N)
    (w Z ell B : ℝ) {j : Grid r m} (hj : j ∈ innerCells r 0 1 ell m)
    (D A : ℝ) (yz : Bool) :
    let out := computedGroups D A yz (meshUpper N m) (List.ofFn j)
    (∀ a, |meshGamma N cap m w Z out.1 a| ≤ 1) ∧
      (∀ b, |meshGamma N cap m w Z out.2.1 b| ≤ 1) ∧
      (∀ q3, |ActualInnerPerLabelGamma.attachedGamma N cap m r w Z B out.2.2 q3| ≤ 1) ∧
      |atomScalar j out| = 1 := by
  have hinj := inner_mesh_labels_injective ell hj
  obtain ⟨h1, h2, h3⟩ := computed_groups_nodup N j hinj D A yz
  exact ⟨meshGamma_abs_le_one hN w Z _ h1, meshGamma_abs_le_one hN w Z _ h2,
    ActualInnerPerLabelGamma.attachedGamma_abs_le_one hN w Z B _ h3,
    computed_atomScalar_abs j hinj D A yz⟩

/-- Exact actual retained inner coefficient reconstruction followed by
literal original M1*M2*M3/M_all factorization on the SAME fine atoms.
The common beta and the marked full-prefix test are unchanged. -/
theorem actual_retained_inner_per_label_convolution {R N cap m : ℕ} (hN : 1 < N)
    (w Z ell B : ℝ) (hL : 1 < (N : ℝ) ^ ell)
    (hrank : ∀ d ∈ fixedRoughSupport (ordinaryRetainOdd ((N : ℝ) ^ ell)) N cap w Z,
      d.primeFactors.card ≤ R) (D A : ℝ) (yz : Bool) (prefix : ℕ) (F : ℕ → ℝ) :
    (∑ e ∈ actualSmallRosserSupport N cap w,
      ∑ d ∈ fixedRoughSupport (ordinaryRetainOdd ((N : ℝ) ^ ell)) N cap w Z,
        if retainedInner N cap m w Z ell d then
          presievedCoefficient N cap w Z ((N : ℝ) ^ ell) B (e * d) *
            F (prefix * (e * d)) else 0) =
    ∑ r ∈ Finset.range (R + 1), ∑ j ∈ innerCells r 0 1 ell m,
      let out := computedGroups D A yz (meshUpper N m) (List.ofFn j)
      ∑ a ∈ ActualInnerMeshSeparatedGamma.groupSupport N cap m w Z out.1,
        ∑ b ∈ ActualInnerMeshSeparatedGamma.groupSupport N cap m w Z out.2.1,
          ∑ q3 ∈ ActualInnerMeshSeparatedGamma.attachedSupport N cap m w Z out.2.2,
            atomScalar j out * meshGamma N cap m w Z out.1 a * meshGamma N cap m w Z out.2.1 b *
              ActualInnerPerLabelGamma.attachedGamma N cap m r w Z B out.2.2 q3 *
                F (prefix * (a * b * q3)) := by
  calc
    _ = ∑ e ∈ actualSmallRosserSupport N cap w,
        ∑ r ∈ Finset.range (R + 1), ∑ j ∈ innerCells r 0 1 ell m,
          (1 / (multiplicity (List.ofFn j) : ℝ)) *
            ∑ ps ∈ meshPrimeBox N cap w Z m j,
              presievedCoefficient N cap w Z ((N : ℝ) ^ ell) B (e * ps.prod) *
                F (prefix * (e * ps.prod)) := by
      apply Finset.sum_congr rfl
      intro e he
      simpa only [multiplicity, meshMultiplicity] using
        (actual_retained_inner_source_eq_cartesian (e := e) hN w Z ell B hL hrank prefix F)
    _ = ∑ r ∈ Finset.range (R + 1), ∑ j ∈ innerCells r 0 1 ell m,
        ∑ e ∈ actualSmallRosserSupport N cap w,
          (1 / (multiplicity (List.ofFn j) : ℝ)) *
            ∑ ps ∈ meshPrimeBox N cap w Z m j,
              presievedCoefficient N cap w Z ((N : ℝ) ^ ell) B (e * ps.prod) *
                F (prefix * (e * ps.prod)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r hr
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r hr
      apply Finset.sum_congr rfl
      intro j hj
      exact actual_inner_beta_per_label hN w Z ell B hL hj D A yz prefix F

end
end ImbalancedChen.P5Z.ActualRetainedInnerPerLabelConvolution
